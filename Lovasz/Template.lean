/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Cheeger

/-!
# Lemma 5.1: penalized extraction of a template

DAG node `L5.1` of `docs/BLUEPRINT.md`. Depends on the normalized Cheeger inequality.
-/

universe u

namespace Lovasz

open Finset

/-- **Lemma 5.1 (Penalized extraction).** There are disjoint sets `A⁺, A⁻ ⊆ G` and a symmetric
`T ⊆ S` such that `F = Cay(G, T)[A⁺, A⁻]` is connected and `cd ≤ d_F(v) ≤ d`,
`1 - λ₂(N_F) ≥ c L^{-2}`, `f_s(F) ≥ 1/8` for `s ∈ T`, and `|T| ≥ cd`. -/
theorem penalized_extraction :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G]
      (S : Finset G), IsConnectionSet S → S.Nonempty → n₀ ≤ Fintype.card G →
      ∃ T Ap Am : Finset G, T ⊆ S ∧ (∀ s ∈ T, s⁻¹ ∈ T) ∧ Disjoint Ap Am ∧
        ((templateGraph T Ap Am).induce ((Ap ∪ Am : Finset G) : Set G)).Connected ∧
        (∀ v ∈ Ap ∪ Am, c * S.card ≤ ((templateGraph T Ap Am).neighborSet v).ncard) ∧
        ((WGraph.ofSimpleGraph (templateGraph T Ap Am)).induce (Ap ∪ Am)).HasGap
          (c / Real.log (Fintype.card G) ^ 2) ∧
        (∀ s ∈ T, 1 / 8 ≤ labelDensity T Ap Am s) ∧ c * S.card ≤ T.card := by
  sorry

end Lovasz
