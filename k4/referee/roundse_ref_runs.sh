#!/bin/sh
# Referee runs for K4.MULTI.ROUNDE.SEL2. $1: round_e_sel2_witnesses.json.gz (proof/k4-oc1max-multi-2 at 4f8a9922);
# $2: two_move_starts_n5_sel2.json.gz (compute/k4-oc1max-cert; the same bytes on proof/k4-matching).
cd "$(dirname "$0")"
python3 roundse_ref.py "$1" "$2" 1
python3 roundse_ref.py mut "$1" 50
