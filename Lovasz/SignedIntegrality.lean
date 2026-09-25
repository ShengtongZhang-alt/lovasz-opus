/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.BMatchingPolytope

/-!
# Lemma 4.1: robust signed integrality

DAG node `L4.1` of `docs/BLUEPRINT.md`. Depends on the b-matching polytope.
-/

namespace Lovasz

open Finset

open Classical in
/-- **Lemma 4.1 (Robust signed integrality).** Let `B` be a signed incidence matrix and
`b ∈ ℤ^V` with `∑_{v ∈ K} b_v` even on every connected component `K` of the underlying graph.
If `Bx = b`, `x ∈ [0,1]^E`, and within every component every nonempty proper vertex set `U`
has `∑_{e ∈ δ(U)} min {x_e, 1 - x_e} ≥ 1`, then `x ∈ conv {z ∈ {0,1}^E : Bz = b}`. -/
theorem robust_signed_integrality {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (Γ : SignedGraph V E) (b : V → ℤ)
    (hpar : ∀ v, Even (∑ w ∈ univ.filter (fun w => Γ.underlying.Reachable v w), b w))
    (x : E → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (hBx : ∀ v, Γ.apply x v = b v)
    (hslack : ∀ U : Finset V, (∀ v ∈ U, ∀ w ∈ U, Γ.underlying.Reachable v w) →
      (∃ v ∈ U, ∃ w ∉ U, Γ.underlying.Reachable v w) →
      1 ≤ ∑ e ∈ univ.filter (fun e => Γ.crosses (U : Set V) e), min (x e) (1 - x e)) :
    x ∈ convexHull ℝ (Γ.integralSolutions fun v => (b v : ℝ)) := by
  sorry

end Lovasz
