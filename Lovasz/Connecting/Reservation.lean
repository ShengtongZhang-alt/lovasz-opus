/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Connecting.Basic

/-!
# Reservation estimates (6.5)–(6.6)

DAG node `E6.5` of `docs/BLUEPRINT.md` (Section 6.1 of the paper).
-/

universe u

noncomputable section

namespace Lovasz

open Finset Classical

namespace Connector

/-- **Reservation estimates (6.5)–(6.6).** Let `X₀ = Cay(G, S₀)` be connected of degree at most
`k`, and let `u = |⟨T⟩|` be odd with `u ≥ C k L`. If the reserved set is a uniformly random
transversal of the left `⟨T⟩`-cosets (5.7), then with probability at least `3/4` every coset-union
cut retains half its edges in `X₀ - W` (6.5), and `e_{X₀}(H \ W, W) ≤ B_* = C k L` for every
coset `H` (6.6). The proof uses Lemma 6.2 and cut counting (6.4) on the coset quotient, and
exponential moments of independent variables in `[0, k]`. -/
theorem reservation_estimates :
    ∃ Cres CB : ℝ, 0 < Cres ∧ 0 < CB ∧ ∃ n₀ : ℕ,
      ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (T S₀ : Finset G)
        (μ : FinDist (Allocation G)) (k : ℕ),
        n₀ ≤ Fintype.card G → IsConnectionSet S₀ → (cayleyGraph S₀).Connected → S₀.card ≤ k →
        Cres * k * Real.log (Fintype.card G) ≤ Nat.card (Subgroup.closure (T : Set G)) →
        ReservationLaw μ T → Odd (Nat.card (Subgroup.closure (T : Set G))) →
        μ.P (fun 𝒜 => ¬ (Res65 T S₀ 𝒜.W ∧
          Res66 T S₀ 𝒜.W (CB * k * Real.log (Fintype.card G)))) ≤ 1 / 4 := by
  sorry

/-! ### Lemma 6.3: allocation cuts -/

end Connector

end Lovasz
