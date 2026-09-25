/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Hoffman's circulation theorem (classical input, via max-flow/min-cut)

DAG node `K.hoffman` of `docs/BLUEPRINT.md`: the circulation criterion (4.6), which the paper
derives from max-flow/min-cut.
-/

namespace Lovasz

open Finset

/-- **Circulation criterion (4.6).** A finite directed multigraph with capacities
`l ≤ u` has a feasible circulation if `l(δ⁻(J)) ≤ u(δ⁺(J))` for every vertex set `J`. -/
theorem hoffman_circulation {N A : Type*} [Fintype A] [DecidableEq N]
    (tail head : A → N) (l u : A → ℝ) (hlu : ∀ a, l a ≤ u a)
    (hcut : ∀ J : Finset N,
      ∑ a ∈ univ.filter (fun a => head a ∈ J ∧ tail a ∉ J), l a ≤
        ∑ a ∈ univ.filter (fun a => tail a ∈ J ∧ head a ∉ J), u a) :
    ∃ g : A → ℝ, (∀ a, l a ≤ g a ∧ g a ≤ u a) ∧
      ∀ v, ∑ a ∈ univ.filter (fun a => head a = v), g a =
        ∑ a ∈ univ.filter (fun a => tail a = v), g a := by
  sorry

end Lovasz
