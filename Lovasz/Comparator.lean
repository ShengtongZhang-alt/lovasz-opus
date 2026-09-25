/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 3.5: even-cycle comparators

DAG node `L3.5` of `docs/BLUEPRINT.md`.
-/

namespace Lovasz

open Finset

/-- The endpoints of the pairing (3.4) of a `2r`-cycle. -/
def comparatorPairEnds {V : Type*} {r : ℕ} (hr : 0 < r) (c : Fin (2 * r) → V) : Set V :=
  {v | ∃ p ∈ comparatorPairs r, v = cyc hr c p.1 ∨ v = cyc hr c p.2}

/-- **Lemma 3.5 (Even-cycle comparator).** Let `c₀ c₁ ⋯ c_{2r-1}` be an even cycle, `r ≥ 2`.
Take inputs `c₀, c₂` and outputs `c₁, c₃` (for `r = 2`) or `c₁, c₄` (for `r ≥ 3`), and pair
the remaining cycle vertices by (3.4). If `Q` is any system of vertex-disjoint paths (on a
vertex set `B` meeting the cycle exactly in the paired vertices) joining the pairs, then the
cycle together with `Q` is a comparator. -/
theorem even_cycle_comparator {V : Type*} [Fintype V] [DecidableEq V] (r : ℕ) (hr : 2 ≤ r)
    (c : Fin (2 * r) → V) (hc : Function.Injective c) (Q : SimpleGraph V) (B : Set V)
    (hQ : IsPathSystem Q B (comparatorPairEnds (by omega) c))
    (hpairs : ∀ p ∈ comparatorPairs r,
      Q.Reachable (cyc (by omega) c p.1) (cyc (by omega) c p.2))
    (hB : B ∩ Set.range c = comparatorPairEnds (by omega) c) :
    IsComparator (cycleOn c ⊔ Q) (Set.range c ∪ B) (cyc (by omega) c 0) (cyc (by omega) c 2)
      (cyc (by omega) c 1) (cyc (by omega) c (if r = 2 then 3 else 4)) := by
  sorry

end Lovasz
