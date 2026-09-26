#!/usr/bin/env python3
"""Evaluate candidate k = 4 statements on every instance of the counterexample suite (k4/suite/instances/*.json).

usage:
  python3 k4/suite/run.py --list                          the predicates (statement, source, implementations)
  python3 k4/suite/run.py PRED [PRED ...] [--only=ID,ID] [--impl=suite,gap] [--timeout=S]
  python3 k4/suite/run.py --expected                      every instance against the predicates listed in its record's
                                                          "expect_fail": each must come out False (both implementations)
  python3 k4/suite/run.py --pred=FILE.py:FUNC             a new candidate: FUNC(record) -> (True/False/None, detail)
Every predicate runs with each of its implementations (k4/suite/predicates.py: 'suite' is k4/suite/model.py, the
others are the independent tools of other workstreams, k4/suite/ext.py). A line is marked DISAGREE when two
implementations give different non-None verdicts; the exit status is 1 if any disagreement (or, with --expected, any
instance that does not refute what its record says) occurs.
"""
import glob, importlib.util, json, os, signal, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import predicates as PR


def load_instances(only=None):
    out = []
    for f in sorted(glob.glob(os.path.join(HERE, 'instances', '*.json'))):
        d = json.load(open(f))
        if only and d['id'] not in only: continue
        if 'kind' in d: continue      # a local configuration, not a complete instance
        d.setdefault('m', 1 + max(g for S in d['sets'] for g in S))
        out.append(d)
    return out


class Timeout(Exception): pass


def _alarm(signum, frame): raise Timeout()


def evaluate(fn, d, timeout):
    signal.signal(signal.SIGALRM, _alarm); signal.alarm(timeout)
    t0 = time.time()
    try:
        v, det = fn(d)
    except Timeout:
        v, det = None, 'timeout %ds' % timeout
    except Exception as e:          # reported, never silently counted as a verdict
        v, det = None, 'ERROR %s: %s' % (type(e).__name__, e)
    finally:
        signal.alarm(0)
    return v, det, time.time() - t0


def fmt(v): return {True: 'holds', False: 'FAILS', None: 'n/a'}[v]


def run(preds, insts, impls=None, timeout=600, out=print):
    bad = 0
    for name, P in preds:
        out('## %s: %s [%s]' % (name, P['statement'], P['source']))
        for d in insts:
            res = {}
            for iname, fn in P['impls'].items():
                if impls and iname not in impls: continue
                res[iname] = evaluate(fn, d, timeout)
            vs = {r[0] for r in res.values() if r[0] is not None}
            flag = '  DISAGREE' if len(vs) > 1 else ''
            bad += bool(flag)
            out('  %-28s n=%d m=%-2d  %s%s' % (d['id'], len(d['sets']), d['m'],
                '  '.join('%s: %s (%s%s)' % (k, fmt(v), det + '; ' if det else '', '%.1fs' % t) for k, (v, det, t) in res.items()), flag))
    return bad


def main(argv):
    only = impls = None; timeout = 600; names = []; custom = []; expected = False
    for a in argv:
        if a.startswith('--only='): only = set(a[7:].split(','))
        elif a.startswith('--impl='): impls = set(a[7:].split(','))
        elif a.startswith('--timeout='): timeout = int(a[10:])
        elif a.startswith('--pred='):
            path, func = a[7:].rsplit(':', 1)
            spec = importlib.util.spec_from_file_location('custom_pred', path); mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
            custom.append((func, dict(statement=(getattr(mod, func).__doc__ or func).strip().split('\n')[0], source=path,
                                      impls={'custom': getattr(mod, func)})))
        elif a == '--list':
            for k, P in PR.PREDICATES.items(): print('%-18s %s [%s] impls: %s' % (k, P['statement'], P['source'], ', '.join(P['impls'])))
            return 0
        elif a == '--expected': expected = True
        else: names.append(a)
    insts = load_instances(only)
    print('# command: python3 k4/suite/run.py ' + ' '.join(argv))
    print('# instances: %d' % len(insts))
    if expected:
        bad = 0
        for d in insts:
            for p in d.get('expect_fail', []):
                P = PR.PREDICATES[p]
                res = {k: evaluate(fn, d, timeout) for k, fn in P['impls'].items() if not impls or k in impls}
                vs = [v for v, _, _ in res.values()]
                ok = all(v is False for v in vs if v is not None) and any(v is False for v in vs)
                bad += not ok
                print('%-28s %-18s %s  %s' % (d['id'], p, 'refuted' if ok else 'NOT REFUTED',
                      '  '.join('%s: %s (%s)' % (k, fmt(v), det) for k, (v, det, t) in res.items())))
        print('# expected refutations not reproduced: %d' % bad)
        return 1 if bad else 0
    preds = [(k, PR.PREDICATES[k]) for k in names] + custom
    bad = run(preds, insts, impls, timeout)
    print('# disagreements: %d' % bad)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
