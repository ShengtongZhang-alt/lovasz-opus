/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 6.2: coset cuts

DAG node `L6.2` of `docs/BLUEPRINT.md`.
-/

universe u

namespace Lovasz

open Finset

/-- **Lemma 6.2 (Coset cuts).** In a connected Cayley graph on `G`, every nontrivial cut whose
shore `Z` is a union of left `U`-cosets has at least `|U|/2` physical edges. (Physical edges
across the cut are counted as ordered pairs `(x, y)` with `x ∈ Z`, `y ∉ Z`.) -/
theorem coset_cut {G : Type u} [Group G] [Fintype G] [DecidableEq G] (S : Finset G)
    (hS : IsConnectionSet S) (hconn : (cayleyGraph S).Connected) (U : Subgroup G)
    (Z : Finset G) (hZ : ∀ x ∈ Z, ∀ y ∈ U, x * y ∈ Z) (hne : Z.Nonempty) (hne' : Z ≠ univ) :
    (Nat.card U : ℝ) / 2 ≤
      ((Z ×ˢ (univ \ Z)).filter fun p => (cayleyGraph S).Adj p.1 p.2).card := by
  sorry

end Lovasz
