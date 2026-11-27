#!/bin/sh
# Referee runs for Lemma B3 (base-phantom §5.1 at 172e8568), RF-B' (Hall §24.10) and RF-T (girth §7). $1: the n = 4 export.
cd "$(dirname "$0")"
python3 b3_ref.py "$1" 8000 1 4 none
python3 b3_ref.py "$1" 2000 2 4 noLstar
python3 b3_ref.py "$1" 2000 3 4 noP2
python3 rfbp_rft_ref.py rfbp 40000 1
python3 rfbp_rft_ref.py rft 1500000 2
