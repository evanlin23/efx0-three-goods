"""Import paths for k4/sdc: this folder, k4/de4 (screen set, cores, adversarial generators) and k3 (K3ALG)."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
DE4 = os.path.join(ROOT, 'k4', 'de4')
for p in (os.path.join(ROOT, 'k3'), DE4, HERE):
    if p not in sys.path:
        sys.path.insert(0, p)
