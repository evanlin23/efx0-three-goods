#!/usr/bin/env bash
# Build the EFX library and fail unless: no source file contains the word `sorry`; the build is
# error-free and warning-free; every `#print axioms` certificate lists only the three standard
# axioms and the number of certificates equals the number of `#print axioms` commands in the
# sources; every declaration of the library (not only the certified ones) depends only on the
# standard axioms (CheckAxioms.lean); and the project has no dependencies (core Lean only).
# Modelled on check.sh in evanlin23/mrd-efx.
set -u
cd "$(dirname "$0")"
sources=$(find EFX -name '*.lean' | sort; echo EFX.lean)
if grep -n 'sorry' $sources CheckAxioms.lean; then
  echo "CHECK FAILED: the word 'sorry' occurs in a source file"; exit 1
fi
if grep -nE '^\s*require' lakefile.toml || grep -q '"name"' <(python3 -c 'import json;print(json.load(open("lake-manifest.json"))["packages"])' 2>/dev/null); then
  echo "CHECK FAILED: the project has a dependency; core Lean only"; exit 1
fi
lake build 2>&1 | tee build.log
status=${PIPESTATUS[0]}
errors=$(grep -c '^error' build.log || true)
warnings=$(grep -c '^warning' build.log || true)
sorries=$(grep -ci 'sorry' build.log || true)
axioms=$(grep -c -E 'depends on axioms|does not depend on any axioms' build.log || true)
expected=$(cat $sources | grep -c '^#print axioms' || true)
theorems=$(cat $sources | grep -cE '^[[:space:]]*(private |protected )?theorem ' || true)
bad_axioms=$(grep 'depends on axioms' build.log | grep -v -c -E '\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]' || true)
echo "lake build exit=$status errors=$errors warnings=$warnings sorry-mentions=$sorries axiom-lines=$axioms expected=$expected nonstandard-axiom-lines=$bad_axioms theorems=$theorems"
if [ "$status" != "0" ] || [ "$errors" != "0" ] || [ "$warnings" != "0" ] || [ "$sorries" != "0" ] || [ "$bad_axioms" != "0" ] || [ "$axioms" != "$expected" ]; then
  echo "CHECK FAILED"; exit 1
fi
if ! lake env lean CheckAxioms.lean 2>&1 | tee -a build.log; then
  echo "CHECK FAILED: a declaration uses a non-standard axiom"; exit 1
fi
if [ "${PIPESTATUS[0]}" != "0" ]; then echo "CHECK FAILED: CheckAxioms.lean"; exit 1; fi
echo "CHECK PASSED: $axioms audited statements, $theorems theorems, standard axioms only"
