"""Import paths for k4/sdind: this folder, k4/sdc (SD-C code), k4/de4 (screen set, generators)."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SDC = os.path.join(ROOT, 'k4', 'sdc')
DE4 = os.path.join(ROOT, 'k4', 'de4')
for p in (os.path.join(ROOT, 'k3'), DE4, SDC, HERE):
    if p not in sys.path:
        sys.path.insert(0, p)
