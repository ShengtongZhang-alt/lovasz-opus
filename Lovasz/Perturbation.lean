/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 2.1: deleting vertices and edges

DAG node `L2.1` of `docs/BLUEPRINT.md`.
-/

universe u

namespace Lovasz

open Finset

/-- **Lemma 2.1.** Suppose `H` has degrees in `[aD, bD]` and normalized upper gap `σ`. Delete
vertices (keep the set `A`) and delete or decrease edge weights (`H' ≤ H` on `A`) so that every
remaining vertex loses at most `β ≤ c' D` weighted degree. The remaining graph has normalized
upper gap at least `σ - C' β / D`. -/
theorem hasGap_of_deletion (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (A : Finset V) (H' : WGraph A)
        (D σ β : ℝ),
        0 < D → H.DegBetween (a * D) (b * D) → H.HasGap σ →
        (∀ x y : A, H'.w x y ≤ H.w x y) → (∀ x : A, H.deg x - H'.deg x ≤ β) →
        0 ≤ β → β ≤ c' * D →
        H'.HasGap (σ - C' * β / D) := by
  sorry

end Lovasz
