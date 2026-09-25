/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 3.3: distances after deletion

DAG node `L3.3` of `docs/BLUEPRINT.md`.
-/

universe u

namespace Lovasz

open Finset

/-- **Lemma 3.3 (Distances after deletion).** Let `F` be a weighted graph on `M` vertices with
degrees between `aD` and `bD` and normalized upper gap at least `σ ∈ (0, 1]`. There are
constants `c, C > 0` (depending on `a, b`) such that whenever `|U| ≤ cσM` there is a set
`K ⊆ V(F) \ U` with `|V(F) \ K| ≤ C|U|/σ` such that every two vertices of `K` are joined in
`F - U` by a walk (hence a path) of length at most `C σ^{-1/2} log (2M)`. -/
theorem distances_after_deletion (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (F : WGraph V) (D σ : ℝ),
        0 < D → F.DegBetween (a * D) (b * D) → F.HasGap σ → 0 < σ → σ ≤ 1 →
        ∀ U : Finset V, (U.card : ℝ) ≤ c * σ * Fintype.card V →
          ∃ K : Finset V, Disjoint K U ∧ ((univ \ K).card : ℝ) ≤ C * U.card / σ ∧
            ∀ x ∈ K, ∀ y ∈ K, ∃ p : F.supp.Walk x y, (∀ z ∈ p.support, z ∉ U) ∧
              (p.length : ℝ) ≤ C * σ ^ (-(1 / 2 : ℝ)) * Real.log (2 * Fintype.card V) := by
  sorry

end Lovasz
