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
  refine ⟨fun e => (g (e, false) + g (e, true)) / 2, fun e => ⟨?_, ?_⟩, fun v => ?_⟩
  · linarith [(hg e false).1, (hg e true).1]
  · linarith [(hg e false).2, (hg e true).2]
  · have h1 := hcons (v, true)
    have h2 := hcons (v, false)
    rw [Finset.sum_filter, Finset.sum_filter, ← sub_eq_zero, ← Finset.sum_sub_distrib,
      Fintype.sum_prod_type] at h1 h2
    have key : Γ.apply (fun e => (g (e, false) + g (e, true)) / 2) v =
        (1 / 2) * (∑ e, ∑ b : Bool,
          (((if Γ.twinHead (e, b) = (v, false) then g (e, b) else 0) -
            (if Γ.twinTail (e, b) = (v, false) then g (e, b) else 0)) -
          ((if Γ.twinHead (e, b) = (v, true) then g (e, b) else 0) -
            (if Γ.twinTail (e, b) = (v, true) then g (e, b) else 0)))) := by
      rw [SignedGraph.apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [Fintype.sum_bool, SignedGraph.twinHead, SignedGraph.twinTail,
        SignedGraph.incidence, SignedGraph.signVal, Prod.mk.injEq]
      cases Γ.sfst e <;> cases Γ.ssnd e <;> by_cases hf : Γ.fst e = v <;>
        by_cases hs : Γ.snd e = v <;> simp [hf, hs] <;> ring
    rw [key]
    simp only [Finset.sum_sub_distrib] at h1 h2 ⊢
    rw [h1, h2]
    ring

end Lovasz
