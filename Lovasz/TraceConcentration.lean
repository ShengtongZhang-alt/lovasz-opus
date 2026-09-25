/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 4.3: bounded-support concentration

DAG node `L4.3` of `docs/BLUEPRINT.md` (trace-exponential supermartingale).
-/

namespace Lovasz

open Finset

/-- **Lemma 4.3 (Bounded-support concentration).** Let a line process start at `x` and suppose
each of its directions has at most four nonzero coordinates in `S`. For positive semidefinite
`q × q` matrices `A_j` (zero for `j ∉ S`) with `‖A_j‖ ≤ b`, put `M = ∑ x_j A_j` and
`Z = ∑ z_j A_j` for the terminal point `z`. If `‖M‖ ≤ ν`, then for `t > 0`,
`P(λ_max(Z - M) ≥ t) ≤ q exp(-t² / (32 b (ν + t)))`, and the same bound holds for
`P(λ_min(Z - M) ≤ -t)`. -/
theorem bounded_support_concentration {ι : Type*} [Fintype ι] {q : ℕ}
    (S : Finset ι) (ok : (ι → ℝ) → Prop)
    (hok : ∀ h, ok h → (S.filter fun i => h i ≠ 0).card ≤ 4)
    (x : ι → ℝ) (μ : FinDist (ι → ℝ)) (hμ : LineProcess ok x μ)
    (A : ι → Matrix (Fin q) (Fin q) ℝ) (hA : ∀ i, (A i).PosSemidef) (b ν t : ℝ) (hb : 0 < b)
    (hAb : ∀ i, QuadLe (A i) b) (hAS : ∀ i ∉ S, A i = 0)
    (hM : QuadLe (∑ i, x i • A i) ν) (ht : 0 < t) :
    μ.P (fun z => LamMaxGe (∑ i, z i • A i - ∑ i, x i • A i) t) ≤
        q * Real.exp (-(t ^ 2) / (32 * b * (ν + t))) ∧
      μ.P (fun z => LamMinLe (∑ i, z i • A i - ∑ i, x i • A i) (-t)) ≤
        q * Real.exp (-(t ^ 2) / (32 * b * (ν + t))) := by
  sorry

end Lovasz
