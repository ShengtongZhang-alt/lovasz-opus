/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Absorption.Basic

/-!
# Lemma 2.4: fixed boundary, fresh layer

DAG node `L2.4` of `docs/BLUEPRINT.md`.
-/

universe u

namespace Lovasz

open Finset

namespace LocalAbsorption

open Classical in
/-- **Lemma 2.4 (Fixed boundary, fresh layer)** (DAG node `L2.4`), the per-transition input of
the fresh-layer step `T3.2f`. Let `H` be bipartite with classes `A, B` of size `N`, weights in
`[ω, 1]`, degrees `(1 ± η) D`, gap `σ`, `η ≤ cσ`, `L ≥ log (2N)`. Let `U ⊆ A` be a fixed set of
`k = pN` rows satisfying the one-sided events (2.9) (`OneSided`, constants `K, δ`), and let
`B' ⊆ B` be any column pool with `|B'| ≥ (1 - cσ) N` from which every vertex has lost at most
`cσD` weighted neighbours, and `pD ≥ C σ^{-2} L`. Then all but an `e^{-aL}` fraction of the
`k`-subsets `W ⊆ B'` give a graph `H[U ∪ W]` with degrees `(1 ± δσ) pD` and gap at least
`c₂ σ`. The pool is deterministic: no independence of its choice is assumed. -/
theorem fixed_boundary_fresh_layer (ω : ℝ) (hω : 0 < ω) :
    ∃ c₂ δ₀ : ℝ, 0 < c₂ ∧ 0 < δ₀ ∧ ∀ a K δ : ℝ, 0 < a → 0 < K → 0 < δ → δ ≤ δ₀ →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (A B U B' : Finset V)
        (N k : ℕ) (η D σ L : ℝ),
        Disjoint A B → A ∪ B = univ → A.card = N → B.card = N →
        (∀ x ∈ A, ∀ y ∈ A, H.w x y = 0) → (∀ x ∈ B, ∀ y ∈ B, H.w x y = 0) →
        H.WeightsIn ω → H.DegNear D η → H.HasGap σ → 0 < σ → σ ≤ 1 → η ≤ c * σ →
        Real.log (2 * N) ≤ L → U ⊆ A → U.card = k →
        OneSided H A B U ((k : ℝ) / N) D σ L K δ →
        B' ⊆ B → (1 - c * σ) * N ≤ B'.card → (∀ v, H.degOn v (B \ B') ≤ c * σ * D) →
        C * σ ^ (-2 : ℝ) * L ≤ (k : ℝ) / N * D →
        (((B'.powersetCard k).filter fun W =>
            ¬ ((H.induce (U ∪ W)).DegNear ((k : ℝ) / N * D) (δ * σ) ∧
              (H.induce (U ∪ W)).HasGap (c₂ * σ))).card : ℝ) ≤
          Real.exp (-(a * L)) * (B'.card.choose k : ℕ) := by
  sorry

end LocalAbsorption

end Lovasz
