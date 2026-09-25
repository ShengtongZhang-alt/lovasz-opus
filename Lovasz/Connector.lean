/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Allocation

/-!
# Proposition 6.1: the sparse connecting system

DAG node `P6.1` of `docs/BLUEPRINT.md` (Section 6 of the paper). Its proof uses label sampling,
the reservation estimates (6.5)–(6.6), Lemmas 6.2–6.4, cut counting (6.4), directional balance
(6.9), Lemma 4.4, the circulation criterion (4.6) and Lemma 4.1.
-/

universe u

namespace Lovasz

open Finset

/-- **Proposition 6.1 (Connecting system).** Assume (1.1) with a large constant `C₀`. For a
random allocation as produced by Proposition 5.3 (successful with probability at least `7/8`,
reserved set distributed by (5.7)), some successful outcome admits a connecting system `M`: a
physical matching on `G \ W` plus a path `a_H w_H b_H` through each reserved vertex, with
distinct endpoints, connected contraction on the parts, and endpoint sets `E_i` that are
nonempty, balanced between the local sides, and satisfy (6.1):
`|E_i| ≤ a Λ |V_i| / L⁷` and `|N_{F_i}(v) ∩ V_i ∩ E_i| ≤ a D / L⁶`, where `Λ = log L`. -/
theorem connecting_system (cT ω A₀ cσ cD CD cN CN : ℝ) (hcT : 0 < cT) (hω : 0 < ω)
    (hA₀ : 0 < A₀) (hcσ : 0 < cσ) (hcD : 0 < cD) (hCD : cD ≤ CD) (hcN : 0 < cN) (hCN : cN ≤ CN)
    (a : ℝ) (ha : 0 < a) :
    ∃ C₀ : ℝ, ∃ n₀ : ℕ, 0 < C₀ ∧
      ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S T Ap Am : Finset G) (c₁ D : ℝ)
        (μ : FinDist (Allocation G)),
        IsConnectionSet S → (cayleyGraph S).Connected → n₀ ≤ Fintype.card G →
        C₀ * Real.log (Fintype.card G) ^ 13 / Real.log (Real.log (Fintype.card G)) ≤ S.card →
        IsTemplate S T Ap Am cT →
        cD * S.card / Real.log (Fintype.card G) ≤ D →
        D ≤ CD * S.card / Real.log (Fintype.card G) →
        μ.P (fun 𝒜 => ¬ 𝒜.Good S T Ap Am (A₀ * Real.log (Fintype.card G)) D
          (cσ / Real.log (Fintype.card G) ^ 2)
          (c₁ * (cσ / Real.log (Fintype.card G) ^ 2)) ω cN CN) ≤ 1 / 8 →
        ReservationLaw μ T →
        ∃ 𝒜 ∈ μ.support, 𝒜.Good S T Ap Am (A₀ * Real.log (Fintype.card G)) D
            (cσ / Real.log (Fintype.card G) ^ 2)
            (c₁ * (cσ / Real.log (Fintype.card G) ^ 2)) ω cN CN ∧
          ∃ M : SimpleGraph G, 𝒜.IsConnector S T Ap Am M
            (a * Real.log (Real.log (Fintype.card G)) / Real.log (Fintype.card G) ^ 7)
            (a * D / Real.log (Fintype.card G) ^ 6) := by
  sorry

end Lovasz
