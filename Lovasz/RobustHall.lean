/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 2.5: robust Hall

DAG node `L2.5` of `docs/BLUEPRINT.md`. Uses Hall's theorem (Mathlib:
`Finset.all_card_le_biUnion_card_iff_exists_injective`).
-/

namespace Lovasz

open Finset

/-- **Lemma 2.5 (Robust Hall).** Let `H₀` be the bipartite weighted graph between `L₀, R₀`
(each of size `m`) with degrees `(1 ± η) D₀` and cut-density `ξ`; put `α = ξ m / D₀` with
`0 < α ≤ 1/2` and `η ≤ α / 10`. Add sets `X, Y` of equal size to the two classes, each added
vertex having at least `D₀ / 2` weighted neighbours in the opposite old class and each old
vertex at most `α D₀ / 20` weighted neighbours in the opposite added class. Then the support of
the enlarged bipartite graph between `L₀ ∪ X` and `R₀ ∪ Y` has a perfect matching. -/
theorem robust_hall {V : Type*} [Fintype V] [DecidableEq V] (H : WGraph V)
    (L₀ R₀ X Y : Finset V) (m : ℕ) (D₀ η ξ : ℝ)
    (hLR : Disjoint L₀ R₀) (hLX : Disjoint L₀ X) (hLY : Disjoint L₀ Y) (hRX : Disjoint R₀ X)
    (hRY : Disjoint R₀ Y) (hXY : Disjoint X Y)
    (hL : L₀.card = m) (hR : R₀.card = m) (hcardXY : X.card = Y.card)
    (hbipL : ∀ x ∈ L₀, ∀ y ∈ L₀, H.w x y = 0) (hbipR : ∀ x ∈ R₀, ∀ y ∈ R₀, H.w x y = 0)
    (hD₀ : 0 < D₀)
    (hdegL : ∀ v ∈ L₀, |H.degOn v R₀ - D₀| ≤ η * D₀)
    (hdegR : ∀ v ∈ R₀, |H.degOn v L₀ - D₀| ≤ η * D₀)
    (hcut : ∀ A ⊆ L₀ ∪ R₀, ξ * A.card * ((L₀ ∪ R₀) \ A).card ≤ H.edgeWeight A ((L₀ ∪ R₀) \ A))
    (hα : 0 < ξ * m / D₀) (hα' : ξ * m / D₀ ≤ 1 / 2) (hη : η ≤ ξ * m / D₀ / 10)
    (hX : ∀ x ∈ X, D₀ / 2 ≤ H.degOn x R₀) (hY : ∀ y ∈ Y, D₀ / 2 ≤ H.degOn y L₀)
    (hLY' : ∀ v ∈ L₀, H.degOn v Y ≤ ξ * m / D₀ * D₀ / 20)
    (hRX' : ∀ v ∈ R₀, H.degOn v X ≤ ξ * m / D₀ * D₀ / 20) :
    ∃ f : (L₀ ∪ X : Finset V) → V, Function.Injective f ∧ (∀ x, f x ∈ R₀ ∪ Y) ∧
      ∀ x : (L₀ ∪ X : Finset V), 0 < H.w x (f x) := by
  sorry

end Lovasz
