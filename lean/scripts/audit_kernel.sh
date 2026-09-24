#!/usr/bin/env bash
# Adversarial re-check of the Lean proofs of TARGET and D (workstream formal/audit).
#
#  1. Fresh clone of this repository at HEAD, clean `.lake`, `lake build` on the pinned toolchain.
#  2. Lean's own replay checker: `leanchecker --fresh EFX.Target` and `leanchecker --fresh EFX`
#     (the root module imports the whole library, including EFX.CorollaryD and EFX.Audit).
#  3. `#print axioms` from a scratch file for EFX.target, EFX.LB.corollaryD and the audit bridges.
#  4. A second, independently implemented kernel: export with lean4export (pinned to the commit
#     whose toolchain is v4.34.0) and check with nanoda (Rust), admitting only propext,
#     Classical.choice and Quot.sound. nanoda prints back the checked statements.
#  5. Negative controls: a `native_decide` proof and a proof of `1 = 2` smuggled in with
#     `set_option debug.skipKernelTC true`. Both checkers must reject them (the second one is
#     accepted by `lake build` and `#print axioms` reports no axioms at all).
#
# Needs git, elan (the toolchain of lean/lean-toolchain), cargo and network access to github.com
# and crates.io. Usage, from the repository root:
#     lean/scripts/audit_kernel.sh 2>&1 | tee results/audit_kernel.log
set -u
REPO=$(cd "$(dirname "$0")/../.." && pwd)
WORK=${WORK:-$(mktemp -d)}
LEAN4EXPORT_REV=076e8e5   # leanprover/lean4export "chore: bump toolchain to v4.34.0 (#49)"
NANODA_REV=3a24072        # ammkrn/nanoda_lib v0.4.19
fail=0
step() { echo; echo "=== $* ==="; }
ok() { if [ "$1" = "$2" ]; then echo "RESULT: $3: as expected (exit $1)"; else echo "RESULT: $3: UNEXPECTED (exit $1, expected $2)"; fail=1; fi; }

step "environment"
date -u; echo "work dir: $WORK"
echo "commit under test: $(git -C "$REPO" rev-parse HEAD)"
echo "toolchain: $(cat "$REPO/lean/lean-toolchain")"

step "1. fresh clone, clean .lake, lake build"
git clone -q --no-local "$REPO" "$WORK/clone" && git -C "$WORK/clone" checkout -q "$(git -C "$REPO" rev-parse HEAD)"
cd "$WORK/clone/lean" || exit 1
rm -rf .lake
lean --version
lake build 2>&1 | grep -vE '^[✔⚠] |^info: ' | tail -5; ok "${PIPESTATUS[0]}" 0 "lake build"
warnings=$(lake build 2>&1 | grep -cE '^warning' || true); echo "warnings replayed: $warnings"; ok "$warnings" 0 "warning count"

step "2. leanchecker --fresh"
for mod in EFX.Target EFX; do
  t0=$SECONDS; lake env leanchecker --fresh "$mod" 2>&1 | tail -3; st=${PIPESTATUS[0]}
  echo "($((SECONDS - t0)) s)"; ok "$st" 0 "leanchecker --fresh $mod"
done

step "3. #print axioms (scratch file)"
cat > "$WORK/axioms.lean" <<'EOF'
import EFX
#check @EFX.target
#check @EFX.LB.corollaryD
#check @Audit.target_audit
#check @Audit.corollaryD_audit
#print axioms EFX.target
#print axioms EFX.LB.corollaryD
#print axioms Audit.target_audit
#print axioms Audit.corollaryD_audit
EOF
lake env lean "$WORK/axioms.lean" 2>&1; ok "$?" 0 "scratch #print axioms"
bad=$(lake env lean "$WORK/axioms.lean" 2>&1 | grep 'axioms' | grep -vc 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' || true)
ok "$bad" 0 "every certificate is exactly [propext, Classical.choice, Quot.sound]"

step "4. second kernel: lean4export + nanoda"
git clone -q https://github.com/leanprover/lean4export "$WORK/lean4export" && git -C "$WORK/lean4export" checkout -q $LEAN4EXPORT_REV
echo "lean4export $(git -C "$WORK/lean4export" log -1 --format='%h %s') ; toolchain $(cat "$WORK/lean4export/lean-toolchain")"
(cd "$WORK/lean4export" && lake build lean4export 2>&1 | tail -1)
git clone -q https://github.com/ammkrn/nanoda_lib "$WORK/nanoda_lib" && git -C "$WORK/nanoda_lib" checkout -q $NANODA_REV
echo "nanoda_lib $(git -C "$WORK/nanoda_lib" log -1 --format='%h %s')"
(cd "$WORK/nanoda_lib" && cargo build --release 2>&1 | tail -1)
EXPORT=$WORK/lean4export/.lake/build/bin/lean4export
NANODA=$WORK/nanoda_lib/target/release/nanoda_bin
# Every non-internal declaration of the EFX library (internal ones are exported as dependencies).
cat > "$WORK/decls.lean" <<'EOF'
import EFX
import Lean
open Lean Elab Command in
elab "#list_EFX" : command => do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if (`EFX).isPrefixOf env.header.moduleNames[idx.toNat]! && !name.isInternal then
        IO.println name
#list_EFX
EOF
lake env lean "$WORK/decls.lean" > "$WORK/decls.txt"
echo "declarations exported: $(wc -l < "$WORK/decls.txt") named EFX-library declarations and their dependencies"
lake env "$EXPORT" EFX -- $(cat "$WORK/decls.txt") > "$WORK/efx.ndjson"; ok "$?" 0 "lean4export"
nanoda_cfg() { # $1 export file, $2 JSON list of declarations to print back
  cat <<EOF
{"export_file_path": "$1", "use_stdin": false,
 "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
 "unpermitted_axiom_hard_error": false, "nat_extension": true, "string_extension": true,
 "pp_declars": $2, "pp_to_stdout": true,
 "pp_options": {"all": false, "explicit": false, "universes": false, "notation": true, "proofs": false,
                "indent": 2, "width": 100, "declar_sep": "\n\n"},
 "print_success_message": true}
EOF
}
nanoda_cfg "$WORK/efx.ndjson" '["EFX.finSum", "EFX.Inst.bundleVal", "EFX.Inst.EFX0", "EFX.numRelevant",
  "EFX.target", "EFX.LB.corollaryD", "Audit.lsum", "Audit.IsPartition", "Audit.IsEFX0", "Audit.relevant",
  "Audit.total", "Audit.Balanced", "Audit.TargetStmt", "Audit.DStmt", "Audit.target_audit",
  "Audit.corollaryD_audit"]' > "$WORK/nanoda.json"
"$NANODA" "$WORK/nanoda.json" 2>&1; ok "$?" 0 "nanoda on the EFX library"

step "5. negative controls (both checkers must reject)"
mkdir -p "$WORK/neg" && cd "$WORK/neg" || exit 1
cp "$REPO/lean/lean-toolchain" .
printf 'name = "Neg"\ndefaultTargets = ["Neg"]\n\n[[lean_lib]]\nname = "Neg"\n' > lakefile.toml
cat > Neg.lean <<'EOF'
import Lean
open Lean

theorem negNative : 2 + 2 = 4 := by native_decide

-- An ill-typed proof of `False`, added with the kernel type checker switched off.
set_option debug.skipKernelTC true in
run_meta addDecl (Declaration.thmDecl
  { name := `negFalse, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })

theorem negOneEqTwo : (1 : Nat) = 2 := negFalse.elim

#print axioms negNative
#print axioms negOneEqTwo
EOF
lake build 2>&1 | grep -E '^(error|warning|info)'; ok "${PIPESTATUS[0]}" 0 "lake build accepts the negative controls"
lake env leanchecker --fresh Neg 2>&1 | tail -4; st=${PIPESTATUS[0]}
ok "$([ "$st" != 0 ] && echo rejected || echo accepted)" rejected "leanchecker --fresh Neg"
for d in negOneEqTwo negNative; do
  lake env "$EXPORT" Neg -- $d > "$WORK/$d.ndjson"
  nanoda_cfg "$WORK/$d.ndjson" '[]' > "$WORK/$d.json"
  "$NANODA" "$WORK/$d.json" > "$WORK/$d.out" 2>&1; st=$?
  grep -E 'panicked|assertion|not found|Checked' "$WORK/$d.out" | head -2
  ok "$([ "$st" != 0 ] && echo rejected || echo accepted)" rejected "nanoda on $d"
done

step "summary"
if [ $fail = 0 ]; then echo "AUDIT KERNEL CHECK PASSED"; else echo "AUDIT KERNEL CHECK FAILED"; fi
exit $fail
