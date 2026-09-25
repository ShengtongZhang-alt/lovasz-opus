/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Connecting.Basic

/-!
# Lemma 6.3: allocation cuts

DAG node `L6.3` of `docs/BLUEPRINT.md` (Section 6.2 of the paper).
-/

universe u

noncomputable section

namespace Lovasz

open Finset Classical

namespace Connector

/-- **Lemma 6.3 (Allocation cuts).** Let `X₀ = Cay(G, S₁ ∪ S_s)` with `S_s ⊆ T` the retained
labels satisfying (6.2) and `S₁` the added labels, and let `Y = X₀ - W` with (6.5) when `u` is
odd. Put `µ = c₃ d / L`.
* In the nonbipartite case, the contracted double cover (the two-state graph) has minimum cut at
  least `µ`.
* If `u` is odd, the same holds within any single `⟨T⟩`-coset `H`, using only edges with both
  endpoints in `H`, for state sets that are nontrivial on the states of the parts in `H`.
* In the bipartite case, the ordinary contraction of `Y` on the parts has minimum cut at
  least `µ`.

Proof sketch (paper, §6.2): for a nontrivial union `Z` of states let `B` be the remaining lifted
vertices lying in a full lifted copy whose allocated state is across the cut. By (6.2) and
`cover_mult`, `e(Z, Zᶜ) ≥ c₂ L |B| / (4λ)`, which is `Ω(d/L)` when `|B| ≥ c₀ d/λ`. Otherwise every
lifted `T`-edge avoiding `B` stays on one side (it is covered by a full lifted copy), and by
Watkins (applied inside each `⟨(s,1) : s ∈ T⟩`-coset, deleting `B` and the at most two reserved
lifts) the cut agrees off `B` with a nontrivial union of such cosets; Lemma 6.2 in the connected
double cover of `X₀` and (6.5) give `≥ u/4 ≥ c_T d/4` edges there, of which at most `|S₁| |B|`
(the added labels) are lost. In an odd coset only the first case can occur. -/
theorem allocation_cuts (cT A₀ cN c₂ Cg : ℝ) (hcT : 0 < cT) (hA₀ : 0 < A₀) (hcN : 0 < cN)
    (hc₂ : 0 < c₂) (hCg : 0 < Cg) :
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∃ n₀ : ℕ,
      ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S T Ap Am S₁ Ss : Finset G)
        (𝒜 : Allocation G) (D σ η ω CN : ℝ) (π : G → Fin 𝒜.t),
        n₀ ≤ Fintype.card G → IsConnectionSet S → (cayleyGraph S).Connected →
        Real.log (Fintype.card G) ^ 12 ≤ S.card → IsTemplate S T Ap Am cT →
        𝒜.Good S T Ap Am (A₀ * Real.log (Fintype.card G)) D σ η ω cN CN →
        (∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v)) →
        IsConnectionSet (S₁ ∪ Ss) → S₁ ∪ Ss ⊆ S → Ss ⊆ T →
        Subgroup.closure (S₁ : Set G) = ⊤ → (IsNonbip S → IsNonbip S₁) →
        (S₁.card : ℝ) ≤ Cg * Real.log (Fintype.card G) →
        (∀ i, ∀ v ∈ copyVerts Ap Am (𝒜.g i), c₂ * Real.log (Fintype.card G) ≤
          ((𝒜.part i).filter fun y => (copyGraph Ss Ap Am (𝒜.g i)).Adj v y).card) →
        (Odd (Nat.card (Subgroup.closure (T : Set G))) → Res65 T (S₁ ∪ Ss) 𝒜.W) →
        (IsNonbip S → ∀ J : Finset (Fin 𝒜.t × Bool), J.Nonempty → J ≠ univ →
          c₃ * S.card / Real.log (Fintype.card G) ≤
            cutCnt π (sgnOf 𝒜 Ap π) J (conY (S₁ ∪ Ss) 𝒜.W).edgeFinset) ∧
        (Odd (Nat.card (Subgroup.closure (T : Set G))) →
          ∀ (H : G ⧸ Subgroup.closure (T : Set G)) (J : Finset (Fin 𝒜.t × Bool)),
            (∃ v, v ∉ 𝒜.W ∧ (v : G ⧸ Subgroup.closure (T : Set G)) = H ∧ ∃ β, (π v, β) ∈ J) →
            (∃ v, v ∉ 𝒜.W ∧ (v : G ⧸ Subgroup.closure (T : Set G)) = H ∧ ∃ β, (π v, β) ∉ J) →
            c₃ * S.card / Real.log (Fintype.card G) ≤
              cutCnt π (sgnOf 𝒜 Ap π) J ((conY (S₁ ∪ Ss) 𝒜.W).edgeFinset.filter fun e =>
                ∀ v ∈ e, (v : G ⧸ Subgroup.closure (T : Set G)) = H)) ∧
        (¬ IsNonbip S → ∀ I : Finset (Fin 𝒜.t), I.Nonempty → I ≠ univ →
          c₃ * S.card / Real.log (Fintype.card G) ≤
            ((conY (S₁ ∪ Ss) 𝒜.W).edgeFinset.filter (PartCross π I)).card) := by
  sorry

end Connector

end Lovasz
