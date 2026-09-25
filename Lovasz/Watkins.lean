/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Watkins's connectivity bound for Cayley graphs (classical input)

DAG node `K.watkins` of `docs/BLUEPRINT.md`; M. E. Watkins, *Connectivity of transitive
graphs*, JCT 8 (1970), in the weak form "vertex connectivity at least `k/2`" used in Section 5.1,
applied to each connected component of a Cayley graph.
-/

universe u

namespace Lovasz

open Finset

/-- **Watkins.** In a Cayley graph `Cay(G, T)` of degree `k = |T|`, deleting fewer than `k/2`
vertices leaves every connected component (a left coset of `⟨T⟩`) connected. -/
theorem watkins_cayley {G : Type u} [Group G] [Fintype G] [DecidableEq G] (T : Finset G)
    (hT : IsConnectionSet T) (B : Finset G) (hB : 2 * B.card < T.card) (x y : G) (hx : x ∉ B)
    (hy : y ∉ B) (hxy : x⁻¹ * y ∈ Subgroup.closure (T : Set G)) :
    ((cayleyGraph T).induce ((B : Set G)ᶜ)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  sorry

end Lovasz
