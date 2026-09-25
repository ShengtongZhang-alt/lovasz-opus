/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# The unit-capacitated perfect b-matching polytope (classical input)

DAG node `K.bmatch` of `docs/BLUEPRINT.md`; Edmonds' theorem as stated in Section 4.1 of the
paper (Letchford–Reinelt–Theis, Section 1; Schrijver, *Combinatorial Optimization*, Cor. 33.2a).
-/

namespace Lovasz

open Finset

open Classical in
/-- **Capacitated b-matching polytope.** For a loopless multigraph with edge ends `u e ≠ v e` and
a demand `b : V → ℕ`, the convex hull of the edge sets with degree `b_v` at every vertex consists
of the vectors `y` with the degree equations, `0 ≤ y ≤ 1`, and the blossom inequalities (4.1):
`y(δ(U) \ J) + (1 - y)(J) ≥ 1` whenever `J ⊆ δ(U)` and `b(U) + |J|` is odd. -/
theorem bmatching_polytope {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (u v : E → V) (hloop : ∀ e, u e ≠ v e) (b : V → ℕ) (y : E → ℝ)
    (hy : ∀ e, 0 ≤ y e ∧ y e ≤ 1)
    (hdeg : ∀ x, ∑ e ∈ univ.filter (fun e => u e = x ∨ v e = x), y e = b x)
    (hblossom : ∀ (U : Finset V) (J : Finset E), (∀ e ∈ J, (u e ∈ U) ≠ (v e ∈ U)) →
      Odd (∑ x ∈ U, b x + J.card) →
      1 ≤ ∑ e ∈ univ.filter (fun e => (u e ∈ U) ≠ (v e ∈ U) ∧ e ∉ J), y e +
        ∑ e ∈ J, (1 - y e)) :
    y ∈ convexHull ℝ {z : E → ℝ | (∀ e, z e = 0 ∨ z e = 1) ∧
      ∀ x, ∑ e ∈ univ.filter (fun e => u e = x ∨ v e = x), z e = b x} := by
  sorry

end Lovasz
