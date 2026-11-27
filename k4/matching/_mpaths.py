"""Import paths for k4/matching: this folder, k4/sdc (data loaders, the coordinator's raw Inst and move generator),
k4/de4 and k3 (needed by the k4/sdc loaders)."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SDC = os.path.join(ROOT, 'k4', 'sdc')
for p in (os.path.join(ROOT, 'k3'), os.path.join(ROOT, 'k4', 'de4'), SDC, HERE):
    if p in sys.path: sys.path.remove(p)
    sys.path.insert(0, p)
