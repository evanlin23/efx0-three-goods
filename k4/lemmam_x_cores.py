"""Run k4/lemmam_x.c on selected cores of a certificate file and print its tagged lines (k4/lemmam_x.md §7.3).
Usage: lemmam_x_cores.py FILE CORE[,CORE...] [C options]     e.g. -A46 -Y1 -r1 -D46 [-W1]
Prints, per core, n, m, the L46 / ADP / FA statistics lines and the dumped profiles (L46, ADPBAD, ADPRUN lines)."""
import gzip, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import adaptive_run as AR
import lemmam_x_run as LR


def main():
    f, cores = sys.argv[1], [int(c) for c in sys.argv[2].split(',')]
    opts = sys.argv[3:]
    LR.build()
    print('#', 'lemmam_x_cores.py', ' '.join(sys.argv[1:]), '# lemmam_x.c sha256', LR.SHA, flush=True)
    data = json.load(gzip.open(f, 'rt'))
    for i in cores:
        c = data['cores'][i]
        lines = LR.run(AR.encode_core(c['sets'], c['m']), opts)
        print(f"core {i}: n={len(c['sets'])} m={c['m']} sets={json.dumps(c['sets'])}", flush=True)
        for l in lines:
            if l.startswith(('L46', 'ADP', 'FA')):
                print('  ' + l, flush=True)


if __name__ == '__main__':
    main()
