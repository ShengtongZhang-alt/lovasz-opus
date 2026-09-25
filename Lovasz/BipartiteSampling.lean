/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.ColumnSampling
import Lovasz.Chernoff
import Lovasz.Perturbation

/-!
# Lemma 2.3: bipartite sampling

DAG node `L2.3` of `docs/BLUEPRINT.md`.
-/

universe u

namespace Lovasz

open Finset

open Classical in
/-- **Lemma 2.3 (Bipartite sampling).** Let `H` be bipartite with classes `A, B` of size `N`,
weights in `[ω, 1]`, degrees `(1 ± η) D`, and normalized upper gap `σ`, with `η ≤ cσ` and
`L ≥ log (2N)`. Choose independent uniform `k`-subsets `U ⊆ A`, `W ⊆ B` (`p = k/N`). If
`pD ≥ C σ^{-2} L`, then with failure probability at most `e^{-aL}` the graph between `U` and `W`
has degrees `(1 ± c₁σ) pD` and normalized upper gap at least `c₂σ`. Here `a` can be any fixed
constant and `c₁` any small constant, by increasing `C` (and decreasing `c`). -/
theorem bipartite_sampling (ω : ℝ) (hω : 0 < ω) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ a c₁ : ℝ, 0 < a → 0 < c₁ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (A B : Finset V) (N k : ℕ)
        (η D σ L : ℝ),
        Disjoint A B → A ∪ B = univ → A.card = N → B.card = N →
        (∀ x ∈ A, ∀ y ∈ A, H.w x y = 0) → (∀ x ∈ B, ∀ y ∈ B, H.w x y = 0) →
        H.WeightsIn ω → H.DegNear D η → H.HasGap σ → 0 < σ → σ ≤ 1 → η ≤ c * σ →
        Real.log (2 * N) ≤ L → k ≤ N → C * σ ^ (-2 : ℝ) * L ≤ (k : ℝ) / N * D →
        (((A.powersetCard k ×ˢ B.powersetCard k).filter fun UW =>
            ¬ ((H.induce (UW.1 ∪ UW.2)).DegNear ((k : ℝ) / N * D) (c₁ * σ) ∧
              (H.induce (UW.1 ∪ UW.2)).HasGap (c₂ * σ))).card : ℝ) ≤
          Real.exp (-(a * L)) * ((N.choose k : ℕ) : ℝ) ^ 2 := by
  sorry

end Lovasz
