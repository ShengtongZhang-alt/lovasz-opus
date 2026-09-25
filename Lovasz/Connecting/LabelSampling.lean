/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Connecting.Basic

/-!
# Label sampling (6.2)

DAG node `E6.1` of `docs/BLUEPRINT.md` (Section 6.1 of the paper).
-/

universe u

noncomputable section

namespace Lovasz

open Finset Classical

namespace Connector

/-- **Label sampling (6.2).** Retain the inverse label classes of `T` independently with
probability `t₀/d`, `t₀ = A₁ λ L`. For a successful allocation, with probability at least `3/4`
every full-copy vertex has at least `c₂ L = Ω(t₀/λ)` neighbours in the part via retained labels,
and at most `2t₀` classes (so at most `4t₀` labels) are retained. -/
theorem label_sampling (cT A₀ cN : ℝ) (hcT : 0 < cT) (hA₀ : 0 < A₀) (hcN : 0 < cN) :
    ∃ A₁ c₂ : ℝ, 0 < A₁ ∧ 0 < c₂ ∧ ∃ n₀ : ℕ,
      ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S T Ap Am : Finset G)
        (𝒜 : Allocation G) (D σ η ω CN : ℝ),
        n₀ ≤ Fintype.card G → IsConnectionSet S →
        Real.log (Fintype.card G) ^ 12 ≤ S.card → IsTemplate S T Ap Am cT →
        𝒜.Good S T Ap Am (A₀ * Real.log (Fintype.card G)) D σ η ω cN CN →
        (labelLaw G (A₁ * A₀ * Real.log (Fintype.card G) ^ 2 / S.card)).P (fun ξ =>
          ¬ (Sampled62 𝒜 T Ap Am ξ (c₂ * Real.log (Fintype.card G)) ∧
            ((sampled T ξ).card : ℝ) ≤ 4 * A₁ * A₀ * Real.log (Fintype.card G) ^ 2)) ≤ 1 / 4 := by
  sorry

/-! ### Step E6.5: the reservation estimates (6.5)–(6.6) -/

end Connector

end Lovasz
