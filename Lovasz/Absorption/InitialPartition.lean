/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Absorption.Basic

/-!
# `T3.2b`: the initial random partition of Section 3.3

DAG node `T3.2b` of `docs/BLUEPRINT.md`.
-/

universe u

namespace Lovasz

open Finset

namespace LocalAbsorption

variable {V : Type*}

/-- **`T3.2b` (the initial random partition).** For all constants of the later steps there are
`c, C` such that, under the hypotheses of Theorem 3.2 with `c, C`, for every perfect matching
`J` of `E` an initial partition with all the required events exists. (Paper: "Ordinary
concentration and a union bound establish all the events just listed", using Lemmas 2.2, 2.3
and the scalar Chernoff bounds.) -/
theorem initial_partition (ω : ℝ) (hω : 0 < ω) (εR c₇ C₇ εA cdfs δ κ : ℝ) (hεR : 0 < εR)
    (hc₇ : 0 < c₇) (hC₇ : 0 < C₇) (hεA : 0 < εA) (hcdfs : 0 < cdfs) (hδ : 0 < δ)
    (hκ : 0 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ CF : ℝ, 0 < CF → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (col : V → Bool) (N ℓ : ℕ)
        (η D σ L g : ℝ) (E : Finset V) (J : SimpleGraph V),
        LocalAbsorptionHyp ω c C H col N ℓ η D σ L g E → IsPerfectMatchingOn J ↑E →
        Nonempty (InitPartition εR c₇ C₇ εA cdfs δ κ K CF H col E J (N - ℓ) D σ L g) := by
  sorry

end LocalAbsorption

end Lovasz
