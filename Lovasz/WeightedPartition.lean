/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Allocation
import Lovasz.SignedIntegrality
import Lovasz.SwapRounding
import Lovasz.TraceConcentration
import Lovasz.Chernoff
import Lovasz.Perturbation

/-!
# Proposition 5.3: the weighted partition

DAG node `P5.3` of `docs/BLUEPRINT.md` (Sections 5.2–5.3 of the paper). Its proof uses the
translate cover (5.2), Lemma 5.2, Lemmas 4.1–4.3, the positive-part bound (2.4), and Chernoff
bounds.
-/

universe u

namespace Lovasz

open Finset

/-- **Proposition 5.3 (Weighted partition).** Given the template of Lemma 5.1 (constant `cT`),
there are constants such that, for every `c₁ > 0`, if `d ≥ K L^{12}` and `n` is large, there is a
reference degree `D = Θ(d/L)` and a random allocation (the outcome of the rounding experiment of
Sections 5.2–5.3, for a fixed good translate cover) which, with probability at least `7/8`,
satisfies (5.15)–(5.16) with `λ = A₀ L`, `σ = cσ L^{-2}`, degree error `c₁ σ` and weights in
`[ω, 1]`; moreover, when `u = |⟨T⟩|` is odd, the reserved set is a uniformly random transversal
of the left `⟨T⟩`-cosets (5.7). -/
theorem weighted_partition (cT : ℝ) (hcT : 0 < cT) :
    ∃ ω A₀ cσ cD CD cN CN : ℝ, 0 < ω ∧ 0 < A₀ ∧ 0 < cσ ∧ 0 < cD ∧ cD ≤ CD ∧ 0 < cN ∧
      cN ≤ CN ∧
      ∀ c₁ : ℝ, 0 < c₁ → ∃ K : ℝ, ∃ n₀ : ℕ,
        ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S T Ap Am : Finset G),
          IsConnectionSet S → (cayleyGraph S).Connected → n₀ ≤ Fintype.card G →
          K * Real.log (Fintype.card G) ^ 12 ≤ S.card →
          IsTemplate S T Ap Am cT →
          ∃ D : ℝ, cD * S.card / Real.log (Fintype.card G) ≤ D ∧
            D ≤ CD * S.card / Real.log (Fintype.card G) ∧
            ∃ μ : FinDist (Allocation G),
              μ.P (fun 𝒜 => ¬ 𝒜.Good S T Ap Am (A₀ * Real.log (Fintype.card G)) D
                (cσ / Real.log (Fintype.card G) ^ 2)
                (c₁ * (cσ / Real.log (Fintype.card G) ^ 2)) ω cN CN) ≤ 1 / 8 ∧
              ReservationLaw μ T := by
  sorry

end Lovasz
