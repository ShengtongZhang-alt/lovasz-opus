/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 4.4: signed fractional circulations

DAG node `L4.4` of `docs/BLUEPRINT.md`.
-/

namespace Lovasz

open Finset

/-- **Lemma 4.4.** If the two-state directed graph (4.5) of a signed multigraph, with both twins
of an edge given the edge's capacities `[l_e, u_e]`, admits a feasible circulation `g`, then the
signed graph admits a fractional vector `f` with `Bf = 0` and `l ≤ f ≤ u`. -/
theorem signed_circulation {V E : Type*} [Fintype E] [DecidableEq V]
    (Γ : SignedGraph V E) (l u : E → ℝ) (g : E × Bool → ℝ)
    (hg : ∀ e s, l e ≤ g (e, s) ∧ g (e, s) ≤ u e)
    (hcons : ∀ p : V × Bool, ∑ a ∈ univ.filter (fun a => Γ.twinHead a = p), g a =
      ∑ a ∈ univ.filter (fun a => Γ.twinTail a = p), g a) :
    ∃ f : E → ℝ, (∀ e, l e ≤ f e ∧ f e ≤ u e) ∧ ∀ v, Γ.apply f v = 0 := by
  sorry

end Lovasz
