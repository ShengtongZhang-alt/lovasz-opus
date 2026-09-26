/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent)
-/
import Lovasz.CycleMerging
import Lovasz.LocalAbsorption
import Lovasz.GlobalDecomposition

/-!
# Main theorem

Theorem 1.1 of `docs/Polylog_Cayley.pdf`, derived from the top-level DAG nodes: the global
decomposition of Sections 5–7 (`global_decomposition`), local absorption (Theorem 3.2,
`local_absorption`) and cycle merging (Lemma 3.8, `cycle_merging`).
-/

universe u

namespace Lovasz

/-- Theorem 1.1, with exactly the statement of `Lovasz.hamiltonian_of_polylog_degree` in
`Challenge.lean`; `Solution.lean` restates it under that name. -/
theorem main_proof :
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S : Finset G),
        IsConnectionSet S →
        (cayleyGraph S).Connected →
        n₀ ≤ Fintype.card G →
        C * Real.log (Fintype.card G) ^ 13 / Real.log (Real.log (Fintype.card G)) ≤ S.card →
        (cayleyGraph S).IsHamiltonian := by
  obtain ⟨ω, hω, hglobal⟩ := global_decomposition.{u}
  obtain ⟨c, C, hc, hC, hlocal⟩ := local_absorption.{u} ω hω
  obtain ⟨C₀, n₀, hC₀, hn₀, hdec⟩ := hglobal c C hc hC
  refine ⟨C₀, n₀, hC₀, hn₀, ?_⟩
  intro G _ _ _ S hS hconn hn hd
  obtain ⟨t, part, W, M, H, col, E, N, ℓ, η, D, σ, L, g, hmerge, hE, hloc⟩ :=
    hdec G S hS hconn hn hd
  refine cycle_merging (cayleyGraph S) part W M (fun i => (H i).supp) hmerge fun i => ?_
  rw [← hE i]
  exact hlocal (part i) (H i) (col i) (N i) (ℓ i) η D σ L g (E i) (hloc i)

end Lovasz
