/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Absorption.Basic

/-!
# `T3.2c`: the Hamilton router of Section 3.3

DAG node `T3.2c` of `docs/BLUEPRINT.md` (from Lemmas 3.4–3.7).
-/

universe u

namespace Lovasz

open Finset

namespace LocalAbsorption

variable {V : Type*}

/-- **`T3.2c` (the router).** Lemma 3.7 gives at least `w` disjoint short even cycles in `C`;
Lemma 3.5 turns `w - 1` of them into comparators, Lemma 3.6 arranges them, and Lemma 3.4 in `Q`
supplies all the internally disjoint connections. The result is an `I, O`-Hamilton router on
a vertex set inside `C ∪ Q ∪ I ∪ O`. -/
theorem router_step (ω : ℝ) (hω : 0 < ω) :
    ∃ ε c₇ C₇ : ℝ, 0 < ε ∧ 0 < c₇ ∧ 0 < C₇ ∧ RouterSpec.{u} ω ε c₇ C₇ := by
  sorry

end LocalAbsorption

end Lovasz
