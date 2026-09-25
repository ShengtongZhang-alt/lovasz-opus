/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 3.8: cycle merging

DAG node `L3.8` of `docs/BLUEPRINT.md`.
-/

universe u

namespace Lovasz

/-- **Lemma 3.8 (Cycle merging).** Suppose the parts partition `V(X) \ W`, `M` is a family of
edges and paths with mutually distinct endpoints in the parts whose interiors partition `W`,
the contraction of `M` on the parts is connected, and for every part `i` the pair
`(H i, E_i)` is matching-absorbing, where `H i` is a spanning graph on the part using no edge of
`M` and `E_i` is the set of endpoints of `M` in the part. Then `X` is Hamiltonian. -/
theorem cycle_merging {V : Type u} [Fintype V] [DecidableEq V] (X : SimpleGraph V)
    {ι : Type*} (part : ι → Finset V) (W : Set V) (M : SimpleGraph V)
    (H : ∀ i, SimpleGraph (part i)) (hdata : IsMergingData X part W M H)
    (habs : ∀ i, IsMatchingAbsorbing (H i) (connectorEnds M (part i))) :
    X.IsHamiltonian := by
  sorry

end Lovasz
