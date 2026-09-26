# Verification record

Date: 2026-09-25 (UTC-7).

Toolchain:

- Lean `v4.35.0-rc2` (the minimum Palomar supports), with its bundled `lake comparator`,
  `leanexport`, NanoDa (`nanoda_bin`) and con-ron kernels;
- Mathlib tag `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`), pinned in
  `lake-manifest.json`.

Commands, run from the repository root on macOS (Apple Silicon):

```bash
lake build                                  # Lovasz, Challenge, Solution
# Comparator, with the toolchain's bundled NanoDa and con-ron kernels registered exactly as
# scripts/verify-comparator.sh (Palomar's template) registers them. macOS has no bubblewrap,
# so this local run passes --inadvisably-no-sandbox; the sandbox isolates the build only and
# does not change the judgement. On Linux use ./scripts/verify-comparator.sh.
lake comparator --config <generated config> --inadvisably-no-sandbox
printf 'import Solution\n#print axioms Lovasz.hamiltonian_of_polylog_degree\n' > /tmp/axioms.lean
lake env lean /tmp/axioms.lean
ruby scripts/validate-formalization.rb
check-jsonschema --schemafile <formalization.yaml v0.4 schema, pinned commit> formalization.yaml
rg -n 'sorry' --glob '*.lean'
```

Results:

- The build succeeds: all 49 `Lovasz.*` modules, `Challenge` and `Solution` compile. The only
  `sorry` warning is the deliberate hole in `Challenge.lean`.
- Comparator: "con-ron kernel accepts the solution", "nanoda kernel accepts the solution",
  "Lean default kernel accepts the solution", "Your solution is okay!". It checks that
  `Lovasz.hamiltonian_of_polylog_degree` has the same statement in `Solution` as in
  `Challenge`, that the definitions it uses (`Lovasz.IsConnectionSet`, `Lovasz.cayleyGraph`) are
  identical in both environments, and that only the permitted axioms are used.
- `#print axioms Lovasz.hamiltonian_of_polylog_degree` (in `Solution`) reports exactly
  `propext`, `Classical.choice`, `Quot.sound`.
- `formalization.yaml` passes the template validator, the upstream v0.4 JSON schema, and
  Palomar's mechanical metadata contract (`PalomarSubmission/scripts/submission_contract.py`,
  `load_formalization_metadata` and `normalized_provenance`: result origin `source-based`,
  repository role `substantive-development`).
- `rg -n sorry --glob '*.lean'` finds only `Challenge.lean`. There is no `axiom` declaration,
  `native_decide`, `admit` or `set_option` in the repository's Lean files.
