"""Import paths for k4/ksens: this folder and k4/sdc (sdclib's EFX0 encoding, de_free's chains, oc_absorb)."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SDC = os.path.join(ROOT, 'k4', 'sdc')
DE4 = os.path.join(ROOT, 'k4', 'de4')
for p in (SDC, HERE):
    if p not in sys.path:
        sys.path.insert(0, p)
