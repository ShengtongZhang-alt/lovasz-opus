/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# The Nash-Williams–Tutte tree-packing theorem (classical input) and cut counting (6.4)

DAG nodes `K.trees` and `E6.4` of `docs/BLUEPRINT.md`; T. Kaiser, *A short proof of the
tree-packing theorem*, arXiv:0911.2809.
-/

namespace Lovasz

open Finset

open Classical in
/-- The edge set `F` of a multigraph (edge ends `ends`) is a spanning tree. -/
def IsSpanningTreeEdges {V E : Type*} [Fintype V] (ends : E → V × V) (F : Finset E) : Prop :=
  F.card = Fintype.card V - 1 ∧
    (SimpleGraph.fromEdgeSet {z | ∃ e ∈ F, z = s((ends e).1, (ends e).2)}).Connected

open Classical in
/-- **Tree packing.** A finite multigraph in which every nontrivial cut has at least `2k`
edges has `k` edge-disjoint spanning trees. -/
theorem tree_packing {V E : Type*} [Fintype V] [Nonempty V] [DecidableEq V] [Fintype E]
    (ends : E → V × V) (k : ℕ)
    (hcut : ∀ U : Finset V, U.Nonempty → U ≠ univ →
      2 * k ≤ (univ.filter fun e => ((ends e).1 ∈ U) ≠ ((ends e).2 ∈ U)).card) :
    ∃ F : Fin k → Finset E, (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧
      ∀ i, IsSpanningTreeEdges ends (F i) := by
  sorry

open Classical in
/-- **Cut counting (6.4).** In a finite multigraph of minimum cut at least `μ ≥ 6`, the number
of vertex sets `U` whose cut has fewer than `(j+1) μ` edges is at most
`(2(|V| + |E|))^{4(j+1)}`. -/
theorem cut_count {V E : Type*} [Fintype V] [Nonempty V] [DecidableEq V] [Fintype E]
    (ends : E → V × V) (μ : ℕ) (hμ : 6 ≤ μ)
    (hcut : ∀ U : Finset V, U.Nonempty → U ≠ univ →
      μ ≤ (univ.filter fun e => ((ends e).1 ∈ U) ≠ ((ends e).2 ∈ U)).card) (j : ℕ) :
    ((univ : Finset (Finset V)).filter fun U =>
      (univ.filter fun e => ((ends e).1 ∈ U) ≠ ((ends e).2 ∈ U)).card < (j + 1) * μ).card ≤
      (2 * (Fintype.card V + Fintype.card E)) ^ (4 * (j + 1)) := by
  sorry

end Lovasz
