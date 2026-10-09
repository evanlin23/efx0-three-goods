"""Which branch of rule sec_small (rules.py) decides each run, on the profiles where K3S with index leaders needs the
rotation, and the number of reruns of iter_r.

  secured    at some insertion step the run was already secured, or a leader was chosen whose (non-last) block
             secures it: success is PROVED (Lemmas NX, FF of NOTES.md)
  full       a leader was chosen whose block takes every remaining agent and whose finished run succeeds (checked)
  fallback   neither ever fired: the run succeeded (or failed) without a guarantee
"""
import sys, os, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', '..'))
from fl import run, index_leader, first_then_index
from rules import sim_block, secured, block_size_rule
from survey import cases


def sec_small_traced(n, m, rank):
    tag = {'b': 'fallback'}
    small = block_size_rule(+1)
    def lead(st, unproc):
        if secured(rank, st.blocks, st.leaders, st.Y, st.free, True):
            tag['b'] = 'secured'; return unproc[0]
        full = []
        for x in unproc:
            un2, fr2, Y2, blk = sim_block(rank, x, unproc, st.free, st.Y)
            if un2:
                if secured(rank, st.blocks + [blk], st.leaders + [x], Y2, fr2, True):
                    tag['b'] = 'secured'; return x
            else:
                full.append(x)
        for x in full:
            pref = list(st.leaders)
            def ch(s2, u2, pref=pref, x=x):
                t = len(s2.leaders)
                return pref[t] if t < len(pref) else x
            if run(n, m, rank, ch).ok:
                tag['b'] = 'full'; return x
        if tag['b'] == 'fallback': tag['fb_steps'] = tag.get('fb_steps', 0) + 1
        return small(st, unproc)
    st = run(n, m, rank, lead)
    return st, tag['b'] + ('' if not tag.get('fb_steps') else ' after %d fallback step(s)' % tag['fb_steps'])


def main(argv):
    c = collections.Counter(); ex = {}
    every = '--all' in argv
    argv = [a for a in argv if a != '--all']
    for n, m, rank in cases(argv):
        st0 = run(n, m, rank, index_leader)
        if every:
            st, b = sec_small_traced(n, m, rank)
            c['ALL profiles: sec_small %s %s' % (b, 'ok' if st.ok else 'FAILS')] += 1
            if b == 'fallback': ex.setdefault('ALL fallback', (n, m, rank, st.leaders))
        if st0.ok: continue
        c['rotation cases'] += 1
        st, b = sec_small_traced(n, m, rank)
        c['sec_small %s %s' % (b, 'ok' if st.ok else 'FAILS')] += 1
        if b == 'fallback': ex.setdefault('fallback', (n, m, rank, st.leaders))
        s = st0; seen = set(); it = 0
        while not s.ok and s.r not in seen:
            seen.add(s.r); s = run(n, m, rank, first_then_index(s.r)); it += 1
        c['iter_r reruns=%d %s' % (it, 'ok' if s.ok else 'FAILS')] += 1
        if it >= 2: ex.setdefault('iter_r reruns>=2', (n, m, rank))
    print(' '.join(argv))
    for k in sorted(c): print('  %-36s %d' % (k, c[k]))
    for k, v in ex.items(): print('  example', k, v)


if __name__ == '__main__':
    main(sys.argv[1:])
