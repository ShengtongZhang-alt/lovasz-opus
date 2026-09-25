/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 3.7: many disjoint short cycles

DAG node `L3.7` of `docs/BLUEPRINT.md`.
-/

universe u

namespace Lovasz

open Finset

/-- **Lemma 3.7.** A bipartite weighted graph on `M` vertices with weights in `[ω, 1]` and
degrees comparable to `D_C ≥ C` (in `[a D_C, b D_C]`) contains at least `cM/g` vertex-disjoint
cycles of length at most `g`, provided `g ≥ C log (2M) / log (2 + D_C)`. -/
theorem many_short_cycles (ω a b : ℝ) (hω : 0 < ω) (ha : 0 < a) (hab : a ≤ b) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (col : V → Bool) (DC g : ℝ),
        H.IsBipartiteWith col → H.WeightsIn ω → H.DegBetween (a * DC) (b * DC) → C ≤ DC →
        C * Real.log (2 * Fintype.card V) / Real.log (2 + DC) ≤ g →
        ∃ Z : Finset (Finset V), c * Fintype.card V / g ≤ Z.card ∧
          (Z : Set (Finset V)).PairwiseDisjoint id ∧
          ∀ z ∈ Z, ∃ x, ∃ p : H.supp.Walk x x, p.IsCycle ∧ (p.length : ℝ) ≤ g ∧
            p.support.toFinset = z := by
  sorry

end Lovasz
