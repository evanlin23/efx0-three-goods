#!/bin/sh
# Referee runs for k4/referee/oc1cert.md (log: results/k4_referee/cert_ref.log).
# Data read from the certifier's branch (compute/k4-oc1max-cert at fa8e971):
#   git show origin/compute/k4-oc1max-cert:results/k4_oc1max/cert_4_depth2.json.gz > cert4d2.json.gz
#   git show origin/compute/k4-oc1max-cert:results/k4_oc1max/oc1max_cex_n4.json > cex.json
cd "$(dirname "$0")"
C=${CERT:-cert4d2.json.gz}; X=${CEX:-cex.json}
python3 cert_ref.py $C $X cex
python3 cert_ref.py $C $X 2500 1 > "${TMPDIR:-/tmp}"/cr1.out &
python3 cert_ref.py $C $X 2500 2 > "${TMPDIR:-/tmp}"/cr2.out &
python3 cert_ref.py $C $X near 4000 3 > "${TMPDIR:-/tmp}"/cr3.out &
python3 cert_ref.py $C $X near 4000 4 > "${TMPDIR:-/tmp}"/cr4.out &
wait
cat "${TMPDIR:-/tmp}"/cr1.out "${TMPDIR:-/tmp}"/cr2.out "${TMPDIR:-/tmp}"/cr3.out "${TMPDIR:-/tmp}"/cr4.out
