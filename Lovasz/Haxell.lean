/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Haxell's hypergraph matching theorem (classical input)

DAG node `K.haxell` of `docs/BLUEPRINT.md`; P. E. Haxell, *A condition for matchability in
hypergraphs*, Graphs Combin. 11 (1995), in the form stated before Lemma 3.4 of the paper.
-/

namespace Lovasz

open Finset

/-- **Haxell's theorem.** A hypergraph on `A ∪ B` in which every edge meets `A` in one vertex
`a` and `B` in at most `r - 1` vertices (the `B`-parts of the edges at `a` are `edges a`).
If for every nonempty `I ⊆ A` the family of `B`-parts of edges meeting `I` has vertex-cover
number greater than `(2r - 3)(|I| - 1)`, then there is a matching saturating `A`. -/
theorem haxell {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β] (r : ℕ) (hr : 2 ≤ r)
    (edges : α → Finset (Finset β)) (hsize : ∀ a, ∀ e ∈ edges a, e.card ≤ r - 1)
    (hcover : ∀ I : Finset α, I.Nonempty → ∀ C : Finset β,
      C.card ≤ (2 * r - 3) * (I.card - 1) → ∃ a ∈ I, ∃ e ∈ edges a, Disjoint e C) :
    ∃ f : α → Finset β, (∀ a, f a ∈ edges a) ∧ ∀ a a', a ≠ a' → Disjoint (f a) (f a') := by
  sorry

end Lovasz
