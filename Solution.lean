/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.Main

/-!
# Proved solution

This module imports the proof development and restates Theorem 1.1 under the name used in
`Challenge.lean`. Comparator checks that `Lovasz.hamiltonian_of_polylog_degree` has exactly the
same statement here as in `Challenge.lean`, that the definitions it uses (`Lovasz.IsConnectionSet`
and `Lovasz.cayleyGraph`, defined here by `Lovasz/Statement.lean`) are identical in both modules,
and that the proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

The proof is `Lovasz.main_proof` in `Lovasz/Main.lean`, which assembles the lemma DAG of
`docs/BLUEPRINT.md`.
-/

universe u

namespace Lovasz

/-- **Theorem 1.1** of `docs/Polylog_Cayley.pdf`, proved. -/
theorem hamiltonian_of_polylog_degree :
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S : Finset G),
        IsConnectionSet S →
        (cayleyGraph S).Connected →
        n₀ ≤ Fintype.card G →
        C * Real.log (Fintype.card G) ^ 13 / Real.log (Real.log (Fintype.card G)) ≤ S.card →
        (cayleyGraph S).IsHamiltonian :=
  main_proof

end Lovasz
