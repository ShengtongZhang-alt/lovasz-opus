/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Connecting.Basic

/-!
# State cuts in the bipartite case

DAG node `E6.bip` of `docs/BLUEPRINT.md` (Sections 6.2–6.3 of the paper, bipartite case).
-/

universe u

noncomputable section

namespace Lovasz

open Finset Classical

namespace Connector

section CutCount

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

/-- **State cuts in the bipartite case (§6.3).** If `X = Cay(G, S)` is bipartite, the two-state
graph of `Y` splits into two copies of the ordinary contraction (one oriented from the global
positive side to the negative side, one reversed). Hence, if the ordinary contraction has minimum
cut at least `µ ≥ 6`, every state cut has `0` or at least `µ` arcs, and the state cuts with fewer
than `(j+1)µ` arcs number at most `(4 (t + |E(Y)|))^{16(j+1)}`.

Proof sketch: `¬ IsNonbip S` gives a character `χ : G → C₂` with `χ(s) = 1` on `S`; `W = ∅` since
`χ` maps `⟨T⟩` onto `C₂`, so `u` is even. By connectivity of the template, the local sign of `v`
in its part is `ε_{π v} + χ(v)`. Hence the arc of an edge `xy` with tail at `x` joins
`π x, π y` inside the component `χ(x)` of the state graph, where component `c` consists of the
states `(i, c + ε_i)`. Writing `J_c = {i : (i, c + ε_i) ∈ J}`, the state cut of `J` is the sum of
the two ordinary part cuts of `J₀, J₁`, and `J ↦ (J₀, J₁)` is injective; apply (6.4) to the
ordinary contraction. -/
theorem bip_state_cuts (S T Ap Am S₀ : Finset G) (cT : ℝ) (𝒜 : Allocation G)
    (lam D σ η ω cN CN μ : ℝ) (π : G → Fin 𝒜.t) (hS : IsConnectionSet S)
    (hconn : (cayleyGraph S).Connected) (hbip : ¬ IsNonbip S)
    (hT : IsTemplate S T Ap Am cT) (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN)
    (hπ : ∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v)) (hS₀ : S₀ ⊆ S) (hμ : 6 ≤ μ)
    (hcut : ∀ I : Finset (Fin 𝒜.t), I.Nonempty → I ≠ univ →
      μ ≤ ((conY S₀ 𝒜.W).edgeFinset.filter (PartCross π I)).card) :
    (∀ J : Finset (Fin 𝒜.t × Bool),
      cutCnt π (sgnOf 𝒜 Ap π) J (conY S₀ 𝒜.W).edgeFinset = 0 ∨
        μ ≤ cutCnt π (sgnOf 𝒜 Ap π) J (conY S₀ 𝒜.W).edgeFinset) ∧
    ∀ j : ℕ, (((univ : Finset (Finset (Fin 𝒜.t × Bool))).filter fun J =>
      (cutCnt π (sgnOf 𝒜 Ap π) J (conY S₀ 𝒜.W).edgeFinset : ℝ) < (j + 1) * μ).card : ℝ) ≤
        (4 * (𝒜.t + (conY S₀ 𝒜.W).edgeFinset.card)) ^ (16 * (j + 1)) := by
  sorry

end CutCount

end Connector

end Lovasz
