/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.DistanceDeletion
import Lovasz.Haxell

/-!
# Lemma 3.4: spectral connection

DAG node `L3.4` of `docs/BLUEPRINT.md`. Depends on Lemma 3.3 and Haxell's theorem.
-/

universe u

namespace Lovasz

open Finset

/-- **Lemma 3.4 (Spectral connection).** Suppose the weighted graph induced by a reservoir `R`
has degrees in `[aΔ, Δ]` and normalized upper gap at least `σ ∈ (0,1]`, `L ≥ log (2|R|)`, and
`(a_j, b_j)` are pairs of distinct vertices outside `R`, each vertex occurring in at most ten
pairs, with endpoint set `T`, such that `d(x, R) ≥ βΔ` for `x ∈ T` and
`d(v, T) ≤ c β σ^{3/2} Δ / L` for `v ∈ R`, where `0 < β < 1`. Then the pairs can be joined by
paths with pairwise disjoint internal vertex sets in `R`, each of length at most `C L / √σ`. -/
theorem spectral_connection (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (R : Finset V) (Δ σ L β : ℝ)
        {κ : Type*} [Fintype κ] [DecidableEq κ] (pa pb : κ → V),
        0 < Δ → (H.induce R).DegBetween (a * Δ) Δ → (H.induce R).HasGap σ → 0 < σ → σ ≤ 1 →
        Real.log (2 * R.card) ≤ L → 0 < β → β < 1 →
        (∀ j, pa j ∉ R ∧ pb j ∉ R ∧ pa j ≠ pb j) →
        (∀ x, (univ.filter fun j => pa j = x ∨ pb j = x).card ≤ 10) →
        (∀ j, β * Δ ≤ H.degOn (pa j) R ∧ β * Δ ≤ H.degOn (pb j) R) →
        (∀ v ∈ R, H.degOn v (univ.image pa ∪ univ.image pb) ≤
          c * β * σ ^ (3 / 2 : ℝ) * Δ / L) →
        ∃ p : ∀ j, H.supp.Walk (pa j) (pb j),
          (∀ j, (p j).IsPath) ∧ (∀ j, ((p j).length : ℝ) ≤ C * L / Real.sqrt σ) ∧
          (∀ j, ∀ z ∈ (p j).support, z ≠ pa j → z ≠ pb j → z ∈ R) ∧
          (∀ j k, j ≠ k → ∀ z ∈ R, z ∈ (p j).support → z ∉ (p k).support) := by
  sorry

end Lovasz
