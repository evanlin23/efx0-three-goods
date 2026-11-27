#!/bin/sh
# Referee runs for Theorem N2's type reduction (k4/haxell.md §6 on claude/k4-haxell at 158b4d9).
cd "$(dirname "$0")"
python3 haxell_n2_ref.py count
python3 haxell_n2_ref.py td 1500 1
python3 haxell_n2_ref.py n2 4000 2 7 &
python3 haxell_n2_ref.py n2 300 3 8 &
wait
