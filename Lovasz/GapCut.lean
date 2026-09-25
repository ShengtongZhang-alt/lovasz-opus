/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Equation (2.2): the gap bounds edge boundaries; cut density

DAG nodes `E2.2` and `E2.2c` of `docs/BLUEPRINT.md`.
-/

namespace Lovasz

open Finset

namespace WGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Equation (2.2).** A normalized gap of at least `σ` implies
`e_H(U, Uᶜ) ≥ σ vol_H(U) vol_H(Uᶜ) / vol_H(V)` (stated without division). -/
theorem edgeWeight_compl_ge_of_hasGap (H : WGraph V) {σ : ℝ} (hσ : H.HasGap σ) (hσ0 : 0 ≤ σ)
    (U : Finset V) :
    σ * H.vol U * H.vol (univ \ U) ≤ H.edgeWeight U (univ \ U) * H.vol univ := by
  sorry

/-- **Section 2.3.** Degrees in `[aD, bD]` and gap `σ` imply `(σ a² D / (b h))`-cut-density,
where `h = |V(H)|`. -/
theorem isCutDense_of_hasGap (H : WGraph V) {σ a b D : ℝ} (hσ : H.HasGap σ) (hσ0 : 0 ≤ σ)
    (ha : 0 < a) (hD : 0 < D) (hdeg : H.DegBetween (a * D) (b * D)) :
    H.IsCutDense (σ * a ^ 2 * D / (b * Fintype.card V)) := by
  sorry

end WGraph

end Lovasz
