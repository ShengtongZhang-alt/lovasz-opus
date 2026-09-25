/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 4.2: signed swap rounding

DAG node `L4.2` of `docs/BLUEPRINT.md`, and the mean-preservation property of line processes
(node `L4.2m`).
-/

namespace Lovasz

open Finset

/-- **Mean preservation.** The terminal distribution of a line process has mean equal to its
starting point, and is supported in `[0,1]^ι`. -/
theorem LineProcess.expect_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {ok : (ι → ℝ) → Prop}
    {x : ι → ℝ} {μ : FinDist (ι → ℝ)} (h : LineProcess ok x μ) (i : ι) :
    μ.expect (fun z => z i) = x i := by
  sorry

/-- The terminal distribution of a line process has exact support. -/
theorem LineProcess.isExact {ι : Type*} [DecidableEq ι] {ok : (ι → ℝ) → Prop}
    {x : ι → ℝ} {μ : FinDist (ι → ℝ)} (h : LineProcess ok x μ) : μ.IsExact := by
  sorry

open Classical in
/-- **Lemma 4.2 (Signed swap rounding).** If `x ∈ conv {z ∈ {0,1}^E : Bz = b}`, then `x` can be
rounded to one of these integral points by a finite sequence of mean-preserving two-point line
moves, each of which changes at most four edge variables incident with any fixed vertex. -/
theorem signed_swap_rounding {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (Γ : SignedGraph V E) (b : V → ℝ) (x : E → ℝ)
    (hx : x ∈ convexHull ℝ (Γ.integralSolutions b)) :
    ∃ μ : FinDist (E → ℝ),
      LineProcess (fun h => ∀ v, (univ.filter fun e =>
        h e ≠ 0 ∧ (Γ.fst e = v ∨ Γ.snd e = v)).card ≤ 4) x μ ∧
      ∀ z ∈ μ.support, z ∈ Γ.integralSolutions b := by
  sorry

end Lovasz
