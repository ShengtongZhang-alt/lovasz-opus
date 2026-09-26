/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent)
-/
import Lovasz.IncidenceCuts

/-!
# Allocations and connecting systems (interfaces of Sections 5 and 6)

The objects produced by Proposition 5.3 (a weighted partition of `G \ W` into parts of
translated template copies) and Proposition 6.1 (a sparse connecting system), as used by the
parameter check of Section 7 (`Lovasz.global_decomposition`).
-/

universe u

noncomputable section

namespace Lovasz

open Finset Classical

variable {G : Type u} [Group G]

/-- The translated copy `gF` of the template `F = Cay(G,T)[A⁺, A⁻]`: `x ∼ y` iff
`g⁻¹x ∼ g⁻¹y` in `F`. -/
def copyGraph (T Ap Am : Finset G) (g : G) : SimpleGraph G where
  Adj x y := (templateGraph T Ap Am).Adj (g⁻¹ * x) (g⁻¹ * y)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.ne rfl⟩

/-- The left cosets of `U = ⟨T⟩` meet `W` in exactly one vertex each (the reserved vertices
`w_H` of Section 5.2). -/
def IsTransversal (T W : Finset G) : Prop :=
  ∀ x : G, (W.filter fun w => x⁻¹ * w ∈ Subgroup.closure (T : Set G)).card = 1

/-- An outcome of the allocation experiment of Section 5: indexed translates `g i • F`, the
parts `V_i = part i`, the reserved set `W`, and the weighted graphs `H_i` on the parts. -/
structure Allocation (G : Type u) [Group G] where
  /-- Number of selected copies. -/
  t : ℕ
  /-- The copy `i` is `g i • F`. -/
  g : Fin t → G
  /-- The allocated part `V_i ⊆ V(F_i)`. -/
  part : Fin t → Finset G
  /-- The reserved vertices. -/
  W : Finset G
  /-- The weighted graph `H_i = F_i[V_i]` with weights (5.8). -/
  H : ∀ i, WGraph (part i)

variable [Fintype G] [DecidableEq G]

/-- The success event of Proposition 5.3, with `λ = lam`, reference degree `D`, gap `σ`,
relative degree error `η`, weight floor `ω`, and the constants `cN, CN` of (5.16) (also used
for the part sizes `|V_i| ≥ cN d / λ`). -/
structure Allocation.Good (𝒜 : Allocation G) (S T Ap Am : Finset G)
    (lam D σ η ω cN CN : ℝ) : Prop where
  part_sub : ∀ i, 𝒜.part i ⊆ copyVerts Ap Am (𝒜.g i)
  part_unique : ∀ v, v ∉ 𝒜.W → ∃! i, v ∈ 𝒜.part i
  part_disjoint : ∀ i, Disjoint (𝒜.part i) 𝒜.W
  /-- `|A_i| = |B_i|`: the part is balanced between the two local sides of `F_i`. -/
  balanced : ∀ i, ((𝒜.part i).filter fun v => (𝒜.g i)⁻¹ * v ∈ Ap).card =
    ((𝒜.part i).filter fun v => (𝒜.g i)⁻¹ * v ∈ Am).card
  size_lower : ∀ i, cN * S.card / lam ≤ (𝒜.part i).card
  H_supp : ∀ i (x y : 𝒜.part i), 0 < (𝒜.H i).w x y → (copyGraph T Ap Am (𝒜.g i)).Adj x y
  H_weights : ∀ i, (𝒜.H i).WeightsIn ω
  H_deg : ∀ i, (𝒜.H i).DegNear D η
  H_gap : ∀ i, (𝒜.H i).HasGap σ
  /-- (5.16) -/
  nbhd_lower : ∀ i, ∀ v ∈ copyVerts Ap Am (𝒜.g i),
    cN * S.card / lam ≤ ((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y).card
  /-- (5.16) -/
  nbhd_upper : ∀ i, ∀ v ∈ copyVerts Ap Am (𝒜.g i),
    ((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y).card ≤ CN * S.card / lam
  cover_mult : ∀ v, ((univ : Finset (Fin 𝒜.t)).filter fun i => v ∈ copyVerts Ap Am (𝒜.g i)).card
    ≤ 2 * lam
  cover_edges : ∀ x : G, ∀ s ∈ T, ∃ i, (copyGraph T Ap Am (𝒜.g i)).Adj x (x * s)
  /-- One reserved vertex per `U`-coset if `u = |⟨T⟩|` is odd, none otherwise. -/
  reserved : (Odd (Nat.card (Subgroup.closure (T : Set G))) → IsTransversal T 𝒜.W) ∧
    (Even (Nat.card (Subgroup.closure (T : Set G))) → 𝒜.W = ∅)

/-- The law (5.7) of the reserved set: when `u = |⟨T⟩|` is odd, `W` is a uniformly random
transversal of the left `U`-cosets (independent uniform choices in the cosets). -/
def ReservationLaw (μ : FinDist (Allocation G)) (T : Finset G) : Prop :=
  Odd (Nat.card (Subgroup.closure (T : Set G))) →
    ∀ Q : Finset G → Prop, μ.P (fun 𝒜 => Q 𝒜.W) =
      (((univ : Finset (Finset G)).filter fun W => IsTransversal T W ∧ Q W).card : ℝ) /
        ((univ : Finset (Finset G)).filter fun W => IsTransversal T W).card

/-- The conclusion of Proposition 6.1 for an allocation `𝒜`: `M` is the union of a physical
matching on `G \ W` and one path `a_H w_H b_H` per reserved vertex; endpoints are distinct; the
contraction on the parts is connected; the endpoint set `E_i` in every part is nonempty and
balanced between the local sides, with `|E_i| ≤ εE |V_i|` and at most `εN` endpoints among the
`F_i`-neighbours in `V_i` of any full-copy vertex (6.1). -/
structure Allocation.IsConnector (𝒜 : Allocation G) (S T Ap Am : Finset G) (M : SimpleGraph G)
    (εE εN : ℝ) : Prop where
  le : M ≤ cayleyGraph S
  deg_W : ∀ w ∈ 𝒜.W, (M.neighborSet w).ncard = 2
  nbr_W : ∀ w ∈ 𝒜.W, ∀ y, M.Adj w y → y ∉ 𝒜.W
  deg_out : ∀ v ∉ 𝒜.W, (M.neighborSet v).ncard ≤ 1
  contraction_connected : (SimpleGraph.fromRel fun i j : Fin 𝒜.t =>
    ∃ x ∈ 𝒜.part i, ∃ y ∈ 𝒜.part j, x ≠ y ∧ M.Reachable x y).Connected
  ends_balanced : ∀ i, ((𝒜.part i).filter fun v =>
      (M.neighborSet v).ncard = 1 ∧ (𝒜.g i)⁻¹ * v ∈ Ap).card =
    ((𝒜.part i).filter fun v => (M.neighborSet v).ncard = 1 ∧ (𝒜.g i)⁻¹ * v ∈ Am).card
  ends_nonempty : ∀ i, ∃ v ∈ 𝒜.part i, (M.neighborSet v).ncard = 1
  ends_few : ∀ i, (((𝒜.part i).filter fun v => (M.neighborSet v).ncard = 1).card : ℝ) ≤
    εE * (𝒜.part i).card
  ends_sparse : ∀ i, ∀ v ∈ copyVerts Ap Am (𝒜.g i),
    (((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y ∧
      (M.neighborSet y).ncard = 1).card : ℝ) ≤ εN

/-- The template properties (5.1) of Lemma 5.1 with constant `c`, for `n = |G|`. -/
structure IsTemplate (S T Ap Am : Finset G) (c : ℝ) : Prop where
  sub : T ⊆ S
  symm : ∀ s ∈ T, s⁻¹ ∈ T
  disjoint : Disjoint Ap Am
  connected : ((templateGraph T Ap Am).induce ((Ap ∪ Am : Finset G) : Set G)).Connected
  deg_lower : ∀ v ∈ Ap ∪ Am, c * S.card ≤ ((templateGraph T Ap Am).neighborSet v).ncard
  gap : ((WGraph.ofSimpleGraph (templateGraph T Ap Am)).induce (Ap ∪ Am)).HasGap
    (c / Real.log (Fintype.card G) ^ 2)
  density : ∀ s ∈ T, 1 / 8 ≤ labelDensity T Ap Am s
  card_T : c * S.card ≤ T.card

end Lovasz
