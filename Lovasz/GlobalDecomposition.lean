/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.Template
import Lovasz.WeightedPartition
import Lovasz.Connector
import Lovasz.Perturbation

/-!
# Sections 5–7: the global decomposition

DAG node `GD` of `docs/BLUEPRINT.md`: the output of the weighted partition (Proposition 5.3),
the connecting system (Proposition 6.1), and the parameter check of Section 7, packaged as the
hypotheses of Lemma 3.8 together with the hypotheses of Theorem 3.2 for every part.
-/

universe u

noncomputable section

namespace Lovasz

section Aux

open Finset Classical

section Helpers

/-- Monotonicity of the normalized gap in the gap parameter. -/
lemma WGraph.hasGap_mono {V : Type*} [Fintype V] (H : WGraph V) {σ₁ σ₂ : ℝ}
    (h : H.HasGap σ₁) (h₂₁ : σ₂ ≤ σ₁) : H.HasGap σ₂ := by
  intro f
  obtain ⟨z, hz⟩ := h f
  refine ⟨z, le_trans ?_ hz⟩
  have hs : 0 ≤ ∑ x, H.deg x * (f x - z) ^ 2 :=
    Finset.sum_nonneg fun x _ =>
      mul_nonneg (Finset.sum_nonneg fun y _ => H.nonneg x y) (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right h₂₁ hs

/-- The gap of `H` equals that of its copy on the subtype `univ`. -/
lemma WGraph.hasGap_of_induce_univ {V : Type*} [Fintype V] (H : WGraph V) {σ : ℝ}
    (h : (H.induce (univ : Finset V)).HasGap σ) : H.HasGap σ := by
  intro f
  obtain ⟨z, hz⟩ := h (fun x => f x)
  refine ⟨z, ?_⟩
  have hdeg : ∀ x : (univ : Finset V), (H.induce univ).deg x = H.deg x := fun x =>
    Finset.sum_coe_sort univ (fun y => H.w x y)
  have e1 : ∑ x : (univ : Finset V), (H.induce univ).deg x * (f x - z) ^ 2 =
      ∑ x, H.deg x * (f x - z) ^ 2 := by
    simp_rw [hdeg]
    exact Finset.sum_coe_sort univ (fun x => H.deg x * (f x - z) ^ 2)
  have e2 : (H.induce univ).dirichlet (fun x => f x) = H.dirichlet f := by
    unfold WGraph.dirichlet
    congr 1
    have : ∀ x : (univ : Finset V), ∑ y : (univ : Finset V), (H.induce univ).w x y *
        ((fun x : (univ : Finset V) => f x) x - (fun x : (univ : Finset V) => f x) y) ^ 2 =
        ∑ y, H.w x y * (f x - f y) ^ 2 := fun x =>
      Finset.sum_coe_sort univ (fun y => H.w x y * (f x - f y) ^ 2)
    simp_rw [this]
    exact Finset.sum_coe_sort univ (fun x => ∑ y, H.w x y * (f x - f y) ^ 2)
  rw [← e1, ← e2]
  exact hz

lemma card_univ_filter_coe {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p]
    [DecidablePred fun x : s => p x] :
    (univ.filter fun x : s => p x).card = (s.filter p).card := by
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext x
  simp [and_comm]

/-- All weights are at most one when the positive weights lie in `[ω, 1]`. -/
lemma WGraph.w_le_one_of_weightsIn {V : Type*} (H : WGraph V) {ω : ℝ} (h : H.WeightsIn ω)
    (x y : V) : H.w x y ≤ 1 := by
  by_cases hp : 0 < H.w x y
  · exact (h x y hp).2
  · linarith [not_lt.1 hp]

variable {G : Type u}

/-- `H` with the weights of the `M`-edges set to zero. -/
def WGraph.deleteAdj {A : Finset G} (H : WGraph A) (M : SimpleGraph G) : WGraph A where
  w x y := if M.Adj x y then 0 else H.w x y
  symm x y := by
    by_cases h : M.Adj (x : G) y
    · simp [h, M.adj_comm]
    · have h' : ¬ M.Adj (y : G) x := fun h' => h h'.symm
      simp only [h, h', ite_false]
      exact H.symm x y
  nonneg x y := by
    split_ifs
    · exact le_rfl
    · exact H.nonneg x y
  loopless x := by simp [H.loopless]

lemma WGraph.deleteAdj_w_le {A : Finset G} (H : WGraph A) (M : SimpleGraph G) (x y : A) :
    (H.deleteAdj M).w x y ≤ H.w x y := by
  simp only [WGraph.deleteAdj]
  split_ifs
  · exact H.nonneg x y
  · exact le_rfl

lemma WGraph.pos_of_deleteAdj {A : Finset G} (H : WGraph A) (M : SimpleGraph G) (x y : A)
    (h : 0 < (H.deleteAdj M).w x y) : 0 < H.w x y ∧ ¬ M.Adj x y := by
  simp only [WGraph.deleteAdj] at h
  split_ifs at h with hM
  · exact absurd h (lt_irrefl 0)
  · exact ⟨h, hM⟩

lemma WGraph.deleteAdj_deg_le {A : Finset G} (H : WGraph A) (M : SimpleGraph G) (x : A) :
    (H.deleteAdj M).deg x ≤ H.deg x :=
  Finset.sum_le_sum fun y _ => H.deleteAdj_w_le M x y

lemma WGraph.deg_sub_deleteAdj_le {A : Finset G} (H : WGraph A) (M : SimpleGraph G)
    [Finite G] (hw : ∀ x y, H.w x y ≤ 1) (x : A) (hx : (M.neighborSet (x : G)).ncard ≤ 1) :
    H.deg x - (H.deleteAdj M).deg x ≤ 1 := by
  unfold WGraph.deg
  rw [← Finset.sum_sub_distrib]
  calc ∑ y, (H.w x y - (H.deleteAdj M).w x y)
      ≤ ∑ y : A, (if M.Adj (x : G) y then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro y _
        simp only [WGraph.deleteAdj]
        split_ifs
        · linarith [hw x y]
        · simp
    _ = ((univ.filter fun y : A => M.Adj (x : G) y).card : ℝ) := by
        rw [Finset.sum_boole]
    _ = ((A.filter (M.Adj (x : G))).card : ℝ) := by
        rw [card_univ_filter_coe]
    _ ≤ ((M.neighborSet (x : G)).ncard : ℝ) := by
        have hsub : ((A.filter (M.Adj (x : G)) : Finset G) : Set G) ⊆ M.neighborSet x := by
          intro y hy
          simp only [coe_filter, Set.mem_ofPred_eq] at hy
          exact hy.2
        have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [Set.ncard_coe_finset] at h2
        exact_mod_cast h2
    _ ≤ 1 := by exact_mod_cast hx

lemma WGraph.deleteAdj_w_of_not_adj {A : Finset G} (H : WGraph A) (M : SimpleGraph G)
    (x y : A) (h : ¬ M.Adj x y) : (H.deleteAdj M).w x y = H.w x y := by
  simp only [WGraph.deleteAdj, h, ite_false]

lemma mem_copyVerts_iff [Group G] [DecidableEq G] {Ap Am : Finset G} {g v : G} :
    v ∈ copyVerts Ap Am g ↔ g⁻¹ * v ∈ Ap ∪ Am := by
  unfold copyVerts
  simp only [mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨g⁻¹ * v, h, by simp⟩

end Helpers

section Part

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G] {S T Ap Am : Finset G}
  {𝒜 : Allocation G} {lam D₀ σ₀ η₀ ω cN CN : ℝ}

omit [Fintype G] in
lemma Allocation.Good.side_of_mem (h𝒜 : 𝒜.Good S T Ap Am lam D₀ σ₀ η₀ ω cN CN)
    {i : Fin 𝒜.t} {v : G} (hv : v ∈ 𝒜.part i) :
    (𝒜.g i)⁻¹ * v ∈ Ap ∨ (𝒜.g i)⁻¹ * v ∈ Am := by
  have := h𝒜.part_sub i hv
  rwa [mem_copyVerts_iff, mem_union] at this

/-- The hypotheses of Theorem 3.2 for one part, from a good allocation and a connector, given
the numerical conditions on the global parameters. -/
lemma localAbsorptionHyp_of_connector (hd : Disjoint Ap Am)
    (h𝒜 : 𝒜.Good S T Ap Am lam D₀ σ₀ η₀ ω cN CN)
    {M : SimpleGraph G} {εE εN : ℝ} (hM : 𝒜.IsConnector S T Ap Am M εE εN)
    (c C η D σ L g : ℝ) (i : Fin 𝒜.t)
    (hdeg : ((𝒜.H i).deleteAdj M).DegNear D η) (hgap : ((𝒜.H i).deleteAdj M).HasGap σ)
    (hσ : 0 < σ) (hσ10 : σ ≤ 1 / 10) (hη : η ≤ c * σ)
    (hL : Real.log (Fintype.card G) ≤ L) (hL10 : 10 ≤ L) (hg : 4 ≤ g)
    (hdl : C * σ ^ (-(9 / 2 : ℝ)) * L ^ 2 * g ≤ D)
    (hgirth : C * L / Real.log (2 + σ ^ (5 / 2 : ℝ) * D / L) ≤ g)
    (hfew : 2 * εE ≤ c * σ ^ (5 / 2 : ℝ) / (L * g))
    (hsparse : εN ≤ c * σ ^ (5 / 2 : ℝ) * D / L) :
    LocalAbsorptionHyp ω c C ((𝒜.H i).deleteAdj M)
      (fun x => decide ((𝒜.g i)⁻¹ * (x : G) ∈ Ap))
      ((𝒜.part i).filter fun v => (𝒜.g i)⁻¹ * v ∈ Ap).card
      ((𝒜.part i).filter fun v => (M.neighborSet v).ncard = 1 ∧ (𝒜.g i)⁻¹ * v ∈ Ap).card
      η D σ L g (univ.filter fun x : 𝒜.part i => (M.neighborSet (x : G)).ncard = 1) := by
  have hnot : ∀ v ∈ 𝒜.part i, ((𝒜.g i)⁻¹ * v ∉ Ap ↔ (𝒜.g i)⁻¹ * v ∈ Am) := by
    intro v hv
    constructor
    · intro h
      exact (h𝒜.side_of_mem hv).resolve_left h
    · intro h h'
      exact Finset.disjoint_left.1 hd h' h
  have hbal := h𝒜.balanced i
  have hcard : (𝒜.part i).card = ((𝒜.part i).filter fun v => (𝒜.g i)⁻¹ * v ∈ Ap).card +
      ((𝒜.part i).filter fun v => (𝒜.g i)⁻¹ * v ∈ Ap).card := by
    have := Finset.card_filter_add_card_filter_not (s := 𝒜.part i)
      (fun v => (𝒜.g i)⁻¹ * v ∈ Ap)
    rw [Finset.filter_congr hnot, ← hbal] at this
    exact this.symm
  refine
    { bipartite := ?_, card_true := ?_, card_false := ?_, weights := ?_, degrees := hdeg,
      gap := hgap, sigma_pos := hσ, sigma_le := hσ10, eta_le := hη, log_le := ?_,
      ten_le := hL10, four_le := hg, deg_large := hdl, girth_param := hgirth,
      ends_true := ?_, ends_false := ?_, one_le := ?_, ends_few := ?_, ends_sparse := ?_ }
  · intro x y hxy
    obtain ⟨hpos, -⟩ := (𝒜.H i).pos_of_deleteAdj M x y hxy
    obtain ⟨-, hs, -⟩ := h𝒜.H_supp i x y hpos
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : (𝒜.g i)⁻¹ * (y : G) ∉ Ap := fun h => Finset.disjoint_left.1 hd h h2
      simp [h1, this]
    · have : (𝒜.g i)⁻¹ * (x : G) ∉ Ap := fun h => Finset.disjoint_left.1 hd h h1
      simp [h2, this]
  · simp only [decide_eq_true_eq]
    exact card_univ_filter_coe (𝒜.part i) (fun v => (𝒜.g i)⁻¹ * v ∈ Ap)
  · simp only [decide_eq_false_iff_not]
    refine (card_univ_filter_coe (𝒜.part i) (fun v => (𝒜.g i)⁻¹ * v ∉ Ap)).trans ?_
    rw [Finset.filter_congr hnot]
    exact hbal.symm
  · intro x y hxy
    obtain ⟨hpos, hM'⟩ := (𝒜.H i).pos_of_deleteAdj M x y hxy
    rw [WGraph.deleteAdj_w_of_not_adj _ _ _ _ hM']
    exact h𝒜.H_weights i x y hpos
  · set N := ((𝒜.part i).filter fun v => (𝒜.g i)⁻¹ * v ∈ Ap).card
    rcases Nat.eq_zero_or_pos N with hN | hN
    · rw [hN]
      simp only [Nat.cast_zero, mul_zero, Real.log_zero]
      linarith
    · refine le_trans (Real.log_le_log (by positivity) ?_) hL
      have : (𝒜.part i).card ≤ Fintype.card G := Finset.card_le_univ _
      have h2 : 2 * N ≤ Fintype.card G := by omega
      exact_mod_cast h2
  · rw [Finset.filter_filter]
    simp only [decide_eq_true_eq]
    exact card_univ_filter_coe (𝒜.part i)
      (fun v => (M.neighborSet v).ncard = 1 ∧ (𝒜.g i)⁻¹ * v ∈ Ap)
  · rw [Finset.filter_filter]
    simp only [decide_eq_false_iff_not]
    refine (card_univ_filter_coe (𝒜.part i)
      (fun v => (M.neighborSet v).ncard = 1 ∧ (𝒜.g i)⁻¹ * v ∉ Ap)).trans ?_
    rw [Finset.filter_congr (fun v hv => and_congr_right' (hnot v hv))]
    exact (hM.ends_balanced i).symm
  · obtain ⟨v, hv, h1⟩ := hM.ends_nonempty i
    rcases h𝒜.side_of_mem hv with h | h
    · exact Finset.card_pos.2 ⟨v, mem_filter.2 ⟨hv, h1, h⟩⟩
    · rw [hM.ends_balanced i]
      exact Finset.card_pos.2 ⟨v, mem_filter.2 ⟨hv, h1, h⟩⟩
  · set N := ((𝒜.part i).filter fun v => (𝒜.g i)⁻¹ * v ∈ Ap).card
    have h1 : ((𝒜.part i).filter fun v => (M.neighborSet v).ncard = 1 ∧
        (𝒜.g i)⁻¹ * v ∈ Ap).card ≤ ((𝒜.part i).filter fun v => (M.neighborSet v).ncard = 1).card :=
      Finset.card_le_card fun v hv => by
        simp only [mem_filter] at hv ⊢
        exact ⟨hv.1, hv.2.1⟩
    have h2 := hM.ends_few i
    have h3 : ((𝒜.part i).card : ℝ) = 2 * N := by
      rw [hcard]
      push_cast
      ring
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    calc (((𝒜.part i).filter fun v => (M.neighborSet v).ncard = 1 ∧
          (𝒜.g i)⁻¹ * v ∈ Ap).card : ℝ)
        ≤ (((𝒜.part i).filter fun v => (M.neighborSet v).ncard = 1).card : ℝ) := by
          exact_mod_cast h1
      _ ≤ εE * (𝒜.part i).card := h2
      _ = (2 * εE) * N := by rw [h3]; ring
      _ ≤ (c * σ ^ (5 / 2 : ℝ) / (L * g)) * N := mul_le_mul_of_nonneg_right hfew hN
      _ = c * σ ^ (5 / 2 : ℝ) * N / (L * g) := by ring
  · intro x
    have hx : (x : G) ∈ copyVerts Ap Am (𝒜.g i) := h𝒜.part_sub i x.2
    have key := hM.ends_sparse i x hx
    have hw1 := (𝒜.H i).w_le_one_of_weightsIn (h𝒜.H_weights i)
    unfold WGraph.degOn
    calc ∑ y ∈ univ.filter (fun x : 𝒜.part i => (M.neighborSet (x : G)).ncard = 1),
          ((𝒜.H i).deleteAdj M).w x y
        ≤ ∑ y ∈ univ.filter (fun x : 𝒜.part i => (M.neighborSet (x : G)).ncard = 1),
          (if (copyGraph T Ap Am (𝒜.g i)).Adj x y then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro y _
          by_cases hp : 0 < ((𝒜.H i).deleteAdj M).w x y
          · obtain ⟨hpos, -⟩ := (𝒜.H i).pos_of_deleteAdj M x y hp
            simp only [h𝒜.H_supp i x y hpos, ↓reduceIte]
            exact ((𝒜.H i).deleteAdj_w_le M x y).trans (hw1 x y)
          · rw [not_lt] at hp
            split_ifs <;> linarith
      _ = (((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj x y ∧
          (M.neighborSet y).ncard = 1).card : ℝ) := by
          rw [Finset.sum_boole, Finset.filter_filter]
          congr 1
          refine (card_univ_filter_coe (𝒜.part i) (fun y => (M.neighborSet y).ncard = 1 ∧
            (copyGraph T Ap Am (𝒜.g i)).Adj x y)).trans ?_
          congr 1
          ext y
          simp [and_comm]
      _ ≤ εN := key
      _ ≤ c * σ ^ (5 / 2 : ℝ) * D / L := hsparse

omit [Fintype G] in
/-- The hypotheses of Lemma 3.8, from a good allocation and a connector. -/
lemma mergingData_of_connector (hTS : T ⊆ S) (h𝒜 : 𝒜.Good S T Ap Am lam D₀ σ₀ η₀ ω cN CN)
    {M : SimpleGraph G} {εE εN : ℝ} (hM : 𝒜.IsConnector S T Ap Am M εE εN) :
    IsMergingData (cayleyGraph S) 𝒜.part (𝒜.W : Set G) M
      (fun i => ((𝒜.H i).deleteAdj M).supp) where
  part_unique v hv := h𝒜.part_unique v (by simpa using hv)
  part_disjoint i := by
    rw [Finset.disjoint_coe]
    exact h𝒜.part_disjoint i
  le := hM.le
  deg_W w hw := hM.deg_W w (by simpa using hw)
  deg_out v hv := hM.deg_out v (by simpa using hv)
  meets_part v := by
    by_cases hv : v ∈ 𝒜.W
    · have h2 := hM.deg_W v hv
      obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero (s := M.neighborSet v) (by omega)
      exact ⟨y, by simpa using hM.nbr_W v hv y hy, hy.reachable⟩
    · exact ⟨v, by simpa using hv, SimpleGraph.Reachable.refl v⟩
  local_le i x y hxy := by
    obtain ⟨hpos, hM'⟩ := (𝒜.H i).pos_of_deleteAdj M x y hxy
    refine ⟨?_, hM'⟩
    obtain ⟨hne, -, hT⟩ := h𝒜.H_supp i x y hpos
    have e : ∀ a b : G, ((𝒜.g i)⁻¹ * a)⁻¹ * ((𝒜.g i)⁻¹ * b) = a⁻¹ * b := by
      intro a b
      group
    rw [e, e] at hT
    rw [SimpleGraph.mulCayley_adj]
    refine ⟨fun h => hne (by rw [h]), ?_⟩
    rcases hT with h | h
    · exact Or.inl (hTS h)
    · exact Or.inr (hTS h)
  contraction_connected := hM.contraction_connected

/-- Degrees after deleting the connector edges: each vertex loses at most one unit. -/
lemma degNear_deleteAdj {D : ℝ} (h𝒜 : 𝒜.Good S T Ap Am lam D σ₀ η₀ ω cN CN)
    {M : SimpleGraph G} {εE εN : ℝ} (hM : 𝒜.IsConnector S T Ap Am M εE εN) (i : Fin 𝒜.t)
    {η : ℝ} (h : η₀ * D + 1 ≤ η * D) : ((𝒜.H i).deleteAdj M).DegNear D η := by
  intro x
  have h1 := h𝒜.H_deg i x
  have h2 := (𝒜.H i).deleteAdj_deg_le M x
  have h3 := (𝒜.H i).deg_sub_deleteAdj_le M
    ((𝒜.H i).w_le_one_of_weightsIn (h𝒜.H_weights i)) x
    (hM.deg_out x (Finset.disjoint_left.1 (h𝒜.part_disjoint i) x.2))
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

lemma WGraph.induce_univ_deg {V : Type*} [Fintype V] (H : WGraph V) (x : (univ : Finset V)) :
    (H.induce univ).deg x = H.deg x :=
  Finset.sum_coe_sort univ (fun y => H.w x y)

/-- The gap after deleting the connector edges (Lemma 2.1 with `β = 1`). -/
lemma hasGap_deleteAdj {c' C' D : ℝ}
    (hdel : ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (A : Finset V)
      (H' : WGraph A) (D σ β : ℝ), 0 < D → H.DegBetween (1 / 2 * D) (2 * D) → H.HasGap σ →
      (∀ x y : A, H'.w x y ≤ H.w x y) → (∀ x : A, H.deg x - H'.deg x ≤ β) →
      0 ≤ β → β ≤ c' * D → H'.HasGap (σ - C' * β / D))
    (h𝒜 : 𝒜.Good S T Ap Am lam D σ₀ η₀ ω cN CN) {M : SimpleGraph G} {εE εN : ℝ}
    (hM : 𝒜.IsConnector S T Ap Am M εE εN) (i : Fin 𝒜.t) {σ : ℝ}
    (hD : 0 < D) (hη₀ : η₀ ≤ 1 / 2) (hc'D : 1 ≤ c' * D) (hσ : σ ≤ σ₀ - C' * 1 / D) :
    ((𝒜.H i).deleteAdj M).HasGap σ := by
  have hDB : (𝒜.H i).DegBetween (1 / 2 * D) (2 * D) := by
    intro x
    have h1 := h𝒜.H_deg i x
    rw [abs_le] at h1
    have : η₀ * D ≤ 1 / 2 * D := mul_le_mul_of_nonneg_right hη₀ hD.le
    constructor <;> linarith [h1.1, h1.2]
  have hloss : ∀ x : (univ : Finset (𝒜.part i)),
      (𝒜.H i).deg x - (((𝒜.H i).deleteAdj M).induce univ).deg x ≤ 1 := by
    intro x
    rw [WGraph.induce_univ_deg]
    exact (𝒜.H i).deg_sub_deleteAdj_le M
      ((𝒜.H i).w_le_one_of_weightsIn (h𝒜.H_weights i)) x
      (hM.deg_out x (Finset.disjoint_left.1 (h𝒜.part_disjoint i) (x : 𝒜.part i).2))
  have h := hdel (𝒜.H i) univ (((𝒜.H i).deleteAdj M).induce univ) D σ₀ 1 hD hDB
    (h𝒜.H_gap i) (fun x y => (𝒜.H i).deleteAdj_w_le M x y) hloss zero_le_one hc'D
  exact WGraph.hasGap_of_induce_univ _ (WGraph.hasGap_mono _ h hσ)

end Part

section Numerics

lemma rpow_div_sq_div_two {x L : ℝ} (hx : 0 ≤ x) (hL : 0 ≤ L) (r : ℝ) :
    (x / L ^ 2 / 2) ^ r = (x / 2) ^ r / L ^ (2 * r) := by
  rw [show x / L ^ 2 / 2 = (x / 2) / L ^ 2 by ring,
    Real.div_rpow (by positivity) (by positivity), ← Real.rpow_two L, ← Real.rpow_mul hL]

lemma rpow_five_halves {x L : ℝ} (hx : 0 ≤ x) (hL : 0 ≤ L) :
    (x / L ^ 2 / 2) ^ (5 / 2 : ℝ) = (x / 2) ^ (5 / 2 : ℝ) / L ^ 5 := by
  rw [rpow_div_sq_div_two hx hL, show (2 : ℝ) * (5 / 2) = ((5 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

lemma rpow_neg_nine_halves {x L : ℝ} (hx : 0 ≤ x) (hL : 0 ≤ L) :
    (x / L ^ 2 / 2) ^ (-(9 / 2 : ℝ)) = L ^ 9 / (x / 2) ^ (9 / 2 : ℝ) := by
  rw [Real.rpow_neg (by positivity), rpow_div_sq_div_two hx hL,
    show (2 : ℝ) * (9 / 2) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_div]

end Numerics

end Aux

open Finset in
/-- **Sections 5–7.** There is a weight floor `ω > 0` such that, for any constants `c, C > 0`
(those of Theorem 3.2 for `ω`), every connected Cayley graph `X = Cay(G, S)` on `n ≥ n₀`
vertices with `d ≥ C₀ L^{13} / log L` admits: a reserved set `W`, a partition of `G \ W` into
parts carrying bipartite weighted graphs `H i` (supported on edges of `X`), and a connecting
system `M` (a matching plus one path `a_H w_H b_H` per reserved vertex), such that the
hypotheses of Lemma 3.8 hold and every `(H i, E_i)` satisfies the hypotheses of Theorem 3.2,
where `E_i` is the set of endpoints of `M` in part `i`. -/
theorem global_decomposition :
    ∃ ω : ℝ, 0 < ω ∧ ∀ c C : ℝ, 0 < c → 0 < C →
      ∃ C₀ : ℝ, ∃ n₀ : ℕ, 0 < C₀ ∧ 0 < n₀ ∧
        ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S : Finset G),
          IsConnectionSet S → (cayleyGraph S).Connected → n₀ ≤ Fintype.card G →
          C₀ * Real.log (Fintype.card G) ^ 13 / Real.log (Real.log (Fintype.card G)) ≤
            S.card →
          ∃ (t : ℕ) (part : Fin t → Finset G) (W : Set G) (M : SimpleGraph G)
            (H : ∀ i, WGraph (part i)) (col : ∀ i, part i → Bool)
            (E : ∀ i, Finset (part i)) (N ℓ : Fin t → ℕ) (η D σ L g : ℝ),
            IsMergingData (cayleyGraph S) part W M (fun i => (H i).supp) ∧
            (∀ i, (E i : Set (part i)) = connectorEnds M (part i)) ∧
            ∀ i, LocalAbsorptionHyp ω c C (H i) (col i) (N i) (ℓ i) η D σ L g (E i) := by
  obtain ⟨cT, hcT, nT, hT⟩ := penalized_extraction.{u}
  obtain ⟨c', C', hc', hC', hdel⟩ :=
    hasGap_of_deletion.{u} (1 / 2) 2 (by norm_num) (by norm_num)
  obtain ⟨ω, A₀, cσ, cD, CD, cN, CN, hω, hA₀, hcσ, hcD, hCD, hcN, hCN, hW⟩ :=
    weighted_partition.{u} cT hcT
  refine ⟨ω, hω, fun c C hc hC => ?_⟩
  obtain ⟨K, nW, hW'⟩ := hW (c / 4) (by positivity)
  obtain ⟨Cg, hCg4, hCgC⟩ : ∃ Cg : ℝ, 4 ≤ Cg ∧ C ≤ Cg :=
    ⟨max C 4, le_max_right _ _, le_max_left _ _⟩
  have hCg0 : 0 < Cg := by linarith
  obtain ⟨k, hk, hk0⟩ : ∃ k : ℝ, k = (cσ / 2) ^ (5 / 2 : ℝ) ∧ 0 < k :=
    ⟨_, rfl, Real.rpow_pos_of_pos (by positivity) _⟩
  obtain ⟨kk, hkk, hkk0⟩ : ∃ kk : ℝ, kk = (cσ / 2) ^ (9 / 2 : ℝ) ∧ 0 < kk :=
    ⟨_, rfl, Real.rpow_pos_of_pos (by positivity) _⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = c * k / (2 * Cg) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  obtain ⟨C₀c, nC, hC₀c, hCon⟩ :=
    connecting_system.{u} cT ω A₀ cσ cD CD cN CN hcT hω hA₀ hcσ hcD hCD hcN hCN a ha0
  obtain ⟨C₀, hC₀1, hC₀K, hC₀c', hA, hB, hC_, hD_, hE_⟩ : ∃ C₀ : ℝ, 1 ≤ C₀ ∧ K ≤ C₀ ∧
      C₀c ≤ C₀ ∧ C * Cg ≤ C₀ * (kk * cD) ∧ 2 * C' ≤ C₀ * (cσ * cD) ∧
      1 ≤ C₀ * (c' * cD) ∧ 4 ≤ C₀ * (c * cσ * cD) ∧ 1 ≤ C₀ * (k * cD) := by
    have h1 : 0 ≤ C * Cg / (kk * cD) := by positivity
    have h2 : 0 ≤ 2 * C' / (cσ * cD) := by positivity
    have h3 : 0 ≤ 1 / (c' * cD) := by positivity
    have h4 : 0 ≤ 4 / (c * cσ * cD) := by positivity
    have h5 : 0 ≤ 1 / (k * cD) := by positivity
    refine ⟨1 + |K| + |C₀c| + C * Cg / (kk * cD) + 2 * C' / (cσ * cD) + 1 / (c' * cD) +
      4 / (c * cσ * cD) + 1 / (k * cD), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith [abs_nonneg K, abs_nonneg C₀c]
    · linarith [le_abs_self K, abs_nonneg C₀c]
    · linarith [le_abs_self C₀c, abs_nonneg K]
    · rw [← div_le_iff₀ (by positivity)]
      linarith [abs_nonneg K, abs_nonneg C₀c]
    · rw [← div_le_iff₀ (by positivity)]
      linarith [abs_nonneg K, abs_nonneg C₀c]
    · rw [← div_le_iff₀ (by positivity)]
      linarith [abs_nonneg K, abs_nonneg C₀c]
    · rw [← div_le_iff₀ (by positivity)]
      linarith [abs_nonneg K, abs_nonneg C₀c]
    · rw [← div_le_iff₀ (by positivity)]
      linarith [abs_nonneg K, abs_nonneg C₀c]
  obtain ⟨Lmin, hLmin⟩ : ∃ Lmin : ℝ, Lmin = 10 + 5 * cσ + c * cσ := ⟨_, rfl⟩
  refine ⟨C₀, nT + nW + nC + ⌈Real.exp Lmin⌉₊ + 1, by linarith, by omega, ?_⟩
  intro G _ _ _ S hS hconn hn hd
  have hnL : Real.exp Lmin ≤ (Fintype.card G : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp Lmin⌉₊ ≤ Fintype.card G by omega))
  have hnpos : (0 : ℝ) < Fintype.card G := lt_of_lt_of_le (Real.exp_pos _) hnL
  obtain ⟨L, hL⟩ : ∃ L, Real.log (Fintype.card G) = L := ⟨_, rfl⟩
  have hLmin' : Lmin ≤ L := by
    rw [← hL]
    exact (Real.le_log_iff_exp_le hnpos).2 hnL
  have hccσ : 0 < c * cσ := by positivity
  have hL10 : 10 ≤ L := by linarith
  have hL1 : 1 < L := by linarith
  have hL0 : 0 < L := by linarith
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Real.log L = Λ := ⟨_, rfl⟩
  have hΛ0 : 0 < Λ := hΛ ▸ Real.log_pos hL1
  have hΛL : Λ ≤ L := by
    rw [← hΛ]
    linarith [Real.log_le_sub_one_of_pos hL0]
  have hsq : 5 * cσ + c * cσ ≤ L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hL1.le hL0.le
    linarith
  have hd' := hd
  rw [hL, hΛ] at hd'
  have hL12 : L ^ 12 ≤ L ^ 13 / Λ := by
    rw [le_div_iff₀ hΛ0]
    calc L ^ 12 * Λ ≤ L ^ 12 * L := mul_le_mul_of_nonneg_left hΛL (by positivity)
      _ = L ^ 13 := by ring
  have hKd : K * L ^ 12 ≤ S.card := by
    calc K * L ^ 12 ≤ C₀ * L ^ 12 := mul_le_mul_of_nonneg_right hC₀K (by positivity)
      _ ≤ C₀ * (L ^ 13 / Λ) := mul_le_mul_of_nonneg_left hL12 (by linarith)
      _ = C₀ * L ^ 13 / Λ := by ring
      _ ≤ S.card := hd'
  have hSpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hd'
  have hSne : S.Nonempty := Finset.card_pos.1 (by exact_mod_cast hSpos)
  obtain ⟨T, Ap, Am, hTS, hTsymm, hdisj, hconnT, hdegT, hgapT, hdens, hcardT⟩ :=
    hT G S hS hSne (by omega)
  have htemp : IsTemplate S T Ap Am cT :=
    ⟨hTS, hTsymm, hdisj, hconnT, hdegT, hgapT, hdens, hcardT⟩
  obtain ⟨D, hD1, hD2, μ, hμ, hres⟩ :=
    hW' G S T Ap Am hS hconn (by omega) (by rw [hL]; exact hKd) htemp
  have hdC : C₀c * Real.log (Fintype.card G) ^ 13 / Real.log (Real.log (Fintype.card G)) ≤
      S.card := by
    rw [hL, hΛ]
    refine le_trans ?_ hd'
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC₀c' (by positivity)) hΛ0.le
  obtain ⟨𝒜, -, h𝒜, M, hM⟩ :=
    hCon G S T Ap Am (c / 4) D μ hS hconn (by omega) hdC htemp hD1 hD2 hμ hres
  rw [hL] at hD1 h𝒜 hM
  rw [hΛ] at hM
  -- lower bounds on `D`
  have hDP : cD * C₀ * L ^ 12 / Λ ≤ D := by
    refine le_trans ?_ hD1
    calc cD * C₀ * L ^ 12 / Λ = cD * (C₀ * L ^ 13 / Λ) / L := by field_simp
      _ ≤ cD * S.card / L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd' hcD.le) hL0.le
  have hDP' : cD * C₀ * L ^ 12 ≤ D * Λ := (div_le_iff₀ hΛ0).1 hDP
  have hD11 : cD * C₀ * L ^ 11 ≤ D := by
    have h1 := mul_le_mul_of_nonneg_left hΛL (show 0 ≤ cD * C₀ * L ^ 11 by positivity)
    have h2 : 0 < D * Λ := lt_of_lt_of_le (by positivity) hDP'
    have h4 : cD * C₀ * L ^ 11 * Λ ≤ D * Λ := by linarith
    exact le_of_mul_le_mul_right h4 hΛ0
  have hL211 : L ^ 2 ≤ L ^ 11 := pow_le_pow_right₀ hL1.le (by norm_num)
  have hDL2 : cD * C₀ * L ^ 2 ≤ D :=
    le_trans (mul_le_mul_of_nonneg_left hL211 (by positivity)) hD11
  have hDC : cD * C₀ ≤ D := by
    have : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL1.le
    linarith [mul_le_mul_of_nonneg_left this (show 0 ≤ cD * C₀ by positivity)]
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hDC
  -- the numerical conditions
  have hη₀ : c / 4 * (cσ / L ^ 2) ≤ 1 / 2 := by
    rw [show c / 4 * (cσ / L ^ 2) = c * cσ / (4 * L ^ 2) by ring, div_le_iff₀ (by positivity)]
    linarith
  have hc'D : 1 ≤ c' * D := by
    have := mul_le_mul_of_nonneg_left hDC hc'.le
    linarith
  have hσgap : cσ / L ^ 2 / 2 ≤ cσ / L ^ 2 - C' * 1 / D := by
    have key : C' * (2 * L ^ 2) ≤ cσ * D := by
      have h1 := mul_le_mul_of_nonneg_left hDL2 hcσ.le
      have h2 := mul_le_mul_of_nonneg_right hB (sq_nonneg L)
      linarith
    have : C' * 1 / D ≤ cσ / L ^ 2 / 2 := by
      rw [mul_one, div_le_iff₀ hDpos, show cσ / L ^ 2 / 2 * D = cσ * D / (2 * L ^ 2) by ring,
        le_div_iff₀ (by positivity)]
      exact key
    linarith
  have hdegN : c / 4 * (cσ / L ^ 2) * D + 1 ≤ c * (cσ / L ^ 2 / 2) * D := by
    have e : c * (cσ / L ^ 2 / 2) * D - c / 4 * (cσ / L ^ 2) * D =
        (c * cσ * D) / (4 * L ^ 2) := by
      field_simp
      ring
    have h1 := mul_le_mul_of_nonneg_left hDL2 hccσ.le
    have h2 := mul_le_mul_of_nonneg_right hD_ (sq_nonneg L)
    have : 1 ≤ (c * cσ * D) / (4 * L ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith
  have hσ'pos : 0 < cσ / L ^ 2 / 2 := by positivity
  have hσ'10 : cσ / L ^ 2 / 2 ≤ 1 / 10 := by
    rw [div_div, div_le_iff₀ (by positivity)]
    linarith
  have hg4 : 4 ≤ Cg * L / Λ := by
    rw [le_div_iff₀ hΛ0]
    have := mul_le_mul_of_nonneg_right hCg4 hL0.le
    linarith
  have hdl : C * (cσ / L ^ 2 / 2) ^ (-(9 / 2 : ℝ)) * L ^ 2 * (Cg * L / Λ) ≤ D := by
    rw [rpow_neg_nine_halves hcσ.le hL0.le, ← hkk]
    have e : C * (L ^ 9 / kk) * L ^ 2 * (Cg * L / Λ) = (C * Cg) * L ^ 12 / (kk * Λ) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have h2 := mul_le_mul_of_nonneg_right hA (pow_nonneg hL0.le 12)
    have h3 := mul_le_mul_of_nonneg_left hDP' hkk0.le
    linarith
  have hgirth : C * L / Real.log (2 + (cσ / L ^ 2 / 2) ^ (5 / 2 : ℝ) * D / L) ≤
      Cg * L / Λ := by
    rw [rpow_five_halves hcσ.le hL0.le, ← hk]
    have hX : L ≤ 2 + k / L ^ 5 * D / L := by
      have e : k / L ^ 5 * D / L = k * D / L ^ 6 := by
        field_simp
      have : L ≤ k * D / L ^ 6 := by
        rw [le_div_iff₀ (by positivity)]
        have h1 := mul_le_mul_of_nonneg_left hD11 hk0.le
        have h2 := mul_le_mul_of_nonneg_right hE_ (pow_nonneg hL0.le 11)
        have h3 : L ^ 7 ≤ L ^ 11 := pow_le_pow_right₀ hL1.le (by norm_num)
        linarith
      rw [e]
      linarith
    have hlog : Λ ≤ Real.log (2 + k / L ^ 5 * D / L) := by
      rw [← hΛ]
      exact Real.log_le_log hL0 hX
    calc C * L / Real.log (2 + k / L ^ 5 * D / L) ≤ C * L / Λ :=
          div_le_div_of_nonneg_left (by positivity) hΛ0 hlog
      _ ≤ Cg * L / Λ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCgC hL0.le) hΛ0.le
  have hfew : 2 * (a * Λ / L ^ 7) ≤
      c * (cσ / L ^ 2 / 2) ^ (5 / 2 : ℝ) / (L * (Cg * L / Λ)) := by
    rw [rpow_five_halves hcσ.le hL0.le, ← hk, ha]
    apply le_of_eq
    field_simp
  have hsparse : a * D / L ^ 6 ≤ c * (cσ / L ^ 2 / 2) ^ (5 / 2 : ℝ) * D / L := by
    rw [rpow_five_halves hcσ.le hL0.le, ← hk]
    have e : c * (k / L ^ 5) * D / L = (c * k) * D / L ^ 6 := by
      field_simp
    rw [e]
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hDpos.le) (by positivity)
    rw [ha, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * Cg by linarith) (mul_pos hc hk0).le
    linarith
  refine ⟨𝒜.t, 𝒜.part, (𝒜.W : Set G), M, fun i => (𝒜.H i).deleteAdj M,
    fun i x => decide ((𝒜.g i)⁻¹ * (x : G) ∈ Ap),
    fun i => univ.filter fun x : 𝒜.part i => (M.neighborSet (x : G)).ncard = 1,
    fun i => ((𝒜.part i).filter fun v => (𝒜.g i)⁻¹ * v ∈ Ap).card,
    fun i => ((𝒜.part i).filter fun v => (M.neighborSet v).ncard = 1 ∧
      (𝒜.g i)⁻¹ * v ∈ Ap).card,
    c * (cσ / L ^ 2 / 2), D, cσ / L ^ 2 / 2, L, Cg * L / Λ,
    mergingData_of_connector hTS h𝒜 hM, fun i => ?_, fun i => ?_⟩
  · ext x
    simp [connectorEnds]
  · exact localAbsorptionHyp_of_connector hdisj h𝒜 hM c C _ D _ L _ i
      (degNear_deleteAdj h𝒜 hM i hdegN) (hasGap_deleteAdj hdel h𝒜 hM i hDpos hη₀ hc'D hσgap)
      hσ'pos hσ'10 le_rfl hL.le hL10 hg4 hdl hgirth hfew hsparse

end Lovasz
