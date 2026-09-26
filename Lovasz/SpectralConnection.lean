/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.DistanceDeletion
import Lovasz.Haxell

/-!
# Lemma 3.4: spectral connection

DAG node `L3.4` of `docs/BLUEPRINT.md`. Depends on Lemma 3.3 and Haxell's theorem.
-/

universe u

namespace Lovasz

open Finset

/-- Weighted incidence count: if every index `j ∈ I` picks an endpoint `g j` with
`d(g j, Y) ≥ b`, where `Y ⊆ R` and `d(v, T) ≤ τ` on `R`, then `|I| b ≤ 10 |Y| τ` (each vertex
lies in at most ten pairs). -/
theorem sc_count {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (R Y : Finset V)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (pa pb : κ → V) (τ b : ℝ)
    (hmult : ∀ x, (univ.filter fun j => pa j = x ∨ pb j = x).card ≤ 10)
    (hT : ∀ v ∈ R, H.degOn v (univ.image pa ∪ univ.image pb) ≤ τ)
    (hY : Y ⊆ R) (I : Finset κ) (g : κ → V) (hg : ∀ j, g j = pa j ∨ g j = pb j)
    (hb : 0 ≤ b) (hdeg : ∀ j ∈ I, b ≤ H.degOn (g j) Y) :
    (I.card : ℝ) * b ≤ 10 * (Y.card * τ) := by
  set X := I.image g with hX
  have h1 : I.card ≤ 10 * X.card := by
    refine card_le_mul_card_image I 10 fun x _ => le_trans (card_le_card ?_) (hmult x)
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    rcases hg j with h | h
    · exact Or.inl (h ▸ hj.2)
    · exact Or.inr (h ▸ hj.2)
  have h2 : (X.card : ℝ) * b ≤ ∑ x ∈ X, H.degOn x Y := by
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hx
    exact hdeg j hj
  have h3 : ∑ x ∈ X, H.degOn x Y = ∑ y ∈ Y, H.degOn y X := by
    unfold WGraph.degOn
    rw [sum_comm]
    exact sum_congr rfl fun y _ => sum_congr rfl fun x _ => H.symm x y
  have h4 : ∑ y ∈ Y, H.degOn y X ≤ Y.card * τ := by
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun y hy => le_trans ?_ (hT y (hY hy))
    refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => H.nonneg _ _
    intro x hx
    obtain ⟨j, -, rfl⟩ := mem_image.1 hx
    rcases hg j with h | h
    · exact mem_union_left _ (h ▸ mem_image_of_mem pa (mem_univ j))
    · exact mem_union_right _ (h ▸ mem_image_of_mem pb (mem_univ j))
  have h1' : (I.card : ℝ) ≤ 10 * X.card := by exact_mod_cast h1
  calc (I.card : ℝ) * b ≤ 10 * X.card * b := mul_le_mul_of_nonneg_right h1' hb
    _ = 10 * (X.card * b) := by ring
    _ ≤ 10 * (Y.card * τ) := by linarith

/-- A path between two distinct vertices outside `R` has at most `length - 1` vertices in `R`. -/
theorem sc_card_interior {V : Type u} [DecidableEq V] {G : SimpleGraph V} (R : Finset V)
    {x y : V} (hx : x ∉ R) (hy : y ∉ R) (hxy : x ≠ y) (p : G.Walk x y) (hp : p.IsPath) :
    (R.filter (· ∈ p.support)).card ≤ p.length - 1 := by
  have hsub : R.filter (· ∈ p.support) ⊆ p.support.toFinset \ {x, y} := by
    intro z hz
    rw [mem_filter] at hz
    rw [mem_sdiff, List.mem_toFinset, mem_insert, mem_singleton]
    refine ⟨hz.2, ?_⟩
    rintro (rfl | rfl)
    · exact hx hz.1
    · exact hy hz.1
  have hxy' : ({x, y} : Finset V) ⊆ p.support.toFinset := by
    intro z hz
    rw [mem_insert, mem_singleton] at hz
    rw [List.mem_toFinset]
    rcases hz with rfl | rfl
    · exact p.start_mem_support
    · exact p.end_mem_support
  have hcard : (p.support.toFinset \ {x, y}).card = p.length + 1 - 2 := by
    rw [card_sdiff_of_subset hxy', List.toFinset_card_of_nodup hp.support_nodup,
      SimpleGraph.Walk.length_support, card_pair hxy]
  have := card_le_card hsub
  omega

/-- A walk in `H[R]` between neighbours `k₁` of `x` and `k₂` of `y` (with `x, y ∉ R`) avoiding
`C` yields a path from `x` to `y` in `supp H` with interior in `R \ C`, two edges longer. -/
theorem sc_build_path {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (R C : Finset V)
    (x y : V) (hx : x ∉ R) (hy : y ∉ R) (k₁ k₂ : R) (h₁ : 0 < H.w x k₁) (h₂ : 0 < H.w y k₂)
    (q : (H.induce R).supp.Walk k₁ k₂) (hq : ∀ z ∈ q.support, (z : V) ∉ C) :
    ∃ p : H.supp.Walk x y, p.IsPath ∧ p.length ≤ q.length + 2 ∧
      (∀ z ∈ p.support, z ≠ x → z ≠ y → z ∈ R) ∧ ∀ z ∈ p.support, z ∈ R → z ∉ C := by
  let f : (H.induce R).supp →g H.supp := ⟨Subtype.val, fun h => h⟩
  have a₁ : H.supp.Adj x k₁ := h₁
  have a₂ : H.supp.Adj (k₂ : V) y := by
    show 0 < H.w k₂ y
    rwa [H.symm]
  let W : H.supp.Walk x y := SimpleGraph.Walk.cons a₁ ((q.map f).concat a₂)
  have hW : ∀ z ∈ W.support, z = x ∨ z = y ∨ ∃ z' ∈ q.support, (z' : V) = z := by
    intro z hz
    simp only [W, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_concat,
      SimpleGraph.Walk.support_map, List.mem_cons, List.mem_append, List.mem_map,
      List.mem_nil_iff, or_false] at hz
    rcases hz with h | ⟨z', hz', h⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨z', hz', h⟩)
    · exact Or.inr (Or.inl h)
  have hWl : W.length = q.length + 2 := by
    simp [W, SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_map]
  refine ⟨W.bypass, W.bypass_isPath, ?_, ?_, ?_⟩
  · exact (W.length_bypass_le_length).trans hWl.le
  · intro z hz hzx hzy
    rcases hW z (W.support_bypass_subset_support hz) with h | h | ⟨z', -, rfl⟩
    · exact absurd h hzx
    · exact absurd h hzy
    · exact z'.2
  · intro z hz hzR
    rcases hW z (W.support_bypass_subset_support hz) with rfl | rfl | ⟨z', hz', rfl⟩
    · exact absurd hzR hx
    · exact absurd hzR hy
    · exact hq z' hz'

/-- A hyperedge `B`-part for the pair `(x, y)`: the set `V(p) ∩ R` of a path `p` from `x` to
`y` of length at most `s` whose internal vertices lie in `R`. -/
def IsSCEdge {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (R : Finset V) (x y : V)
    (s : ℕ) (e : Finset V) : Prop :=
  ∃ p : H.supp.Walk x y, p.IsPath ∧ p.length ≤ s ∧
    (∀ z ∈ p.support, z ≠ x → z ≠ y → z ∈ R) ∧ e = R.filter (· ∈ p.support)

/-- The hyperedge `B`-parts for the pair `(x, y)` (all of them are subsets of `R`). -/
noncomputable def scEdges {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V)
    (R : Finset V) (x y : V) (s : ℕ) : Finset (Finset V) :=
  @Finset.filter _ (IsSCEdge H R x y s) (Classical.decPred _) R.powerset

theorem mem_scEdges {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V)
    (R : Finset V) (x y : V) (s : ℕ) (e : Finset V) :
    e ∈ scEdges H R x y s ↔ ∃ p : H.supp.Walk x y, p.IsPath ∧ p.length ≤ s ∧
      (∀ z ∈ p.support, z ≠ x → z ≠ y → z ∈ R) ∧ e = R.filter (· ∈ p.support) := by
  unfold scEdges
  rw [@mem_filter _ _ (Classical.decPred _), mem_powerset]
  constructor
  · exact fun h => h.2
  · rintro ⟨p, hp⟩
    exact ⟨hp.2.2.2 ▸ filter_subset _ _, p, hp⟩

/-- **Lemma 3.4 (Spectral connection).** Suppose the weighted graph induced by a reservoir `R`
has degrees in `[aΔ, Δ]` and normalized upper gap at least `σ ∈ (0,1]`, `L ≥ log (2|R|)`, and
`(a_j, b_j)` are pairs of distinct vertices outside `R`, each vertex occurring in at most ten
pairs, with endpoint set `T`, such that `d(x, R) ≥ βΔ` for `x ∈ T` and
`d(v, T) ≤ c β σ^{3/2} Δ / L` for `v ∈ R`, where `0 < β < 1`. Then the pairs can be joined by
paths with pairwise disjoint internal vertex sets in `R`, each of length at most `C L / √σ`. -/
theorem spectral_connection (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (R : Finset V) (Δ σ L β : ℝ)
        {κ : Type*} [Fintype κ] [DecidableEq κ] (pa pb : κ → V),
        0 < Δ → (H.induce R).DegBetween (a * Δ) Δ → (H.induce R).HasGap σ → 0 < σ → σ ≤ 1 →
        Real.log (2 * R.card) ≤ L → 0 < β → β < 1 →
        (∀ j, pa j ∉ R ∧ pb j ∉ R ∧ pa j ≠ pb j) →
        (∀ x, (univ.filter fun j => pa j = x ∨ pb j = x).card ≤ 10) →
        (∀ j, β * Δ ≤ H.degOn (pa j) R ∧ β * Δ ≤ H.degOn (pb j) R) →
        (∀ v ∈ R, H.degOn v (univ.image pa ∪ univ.image pb) ≤
          c * β * σ ^ (3 / 2 : ℝ) * Δ / L) →
        ∃ p : ∀ j, H.supp.Walk (pa j) (pb j),
          (∀ j, (p j).IsPath) ∧ (∀ j, ((p j).length : ℝ) ≤ C * L / Real.sqrt σ) ∧
          (∀ j, ∀ z ∈ (p j).support, z ≠ pa j → z ≠ pb j → z ∈ R) ∧
          (∀ j k, j ≠ k → ∀ z ∈ R, z ∈ (p j).support → z ∉ (p k).support) := by
  obtain ⟨c₃, C₃, hc₃, hC₃, h33⟩ := distances_after_deletion.{u} a 1 ha ha1
  set C₀ : ℝ := C₃ + 4 with hC₀
  set m : ℝ := min c₃ (1 / (2 * C₃)) with hm
  have hm0 : 0 < m := lt_min hc₃ (by positivity)
  have hmc₃ : m ≤ c₃ := min_le_left _ _
  have hmC : m * C₃ ≤ 1 / 2 := by
    have : m ≤ 1 / (2 * C₃) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hC₀pos : 0 < C₀ := by rw [hC₀]; linarith
  have hC₀ne : C₀ ≠ 0 := hC₀pos.ne'
  refine ⟨m / (40 * C₀), 2 * C₀, by positivity, by positivity, ?_⟩
  intro V _ _ H R Δ σ L β κ _ _ pa pb hΔ hdeg hgap hσ hσ1 hL hβ hβ1 hpairs hmult hendR hRT
  set c : ℝ := m / (40 * C₀) with hc
  have h40 : 40 * C₀ * c = m := by rw [hc]; field_simp
  rcases isEmpty_or_nonempty κ with hκ | ⟨⟨j₀⟩⟩
  · exact ⟨fun j => isEmptyElim j, fun j => isEmptyElim j, fun j => isEmptyElim j,
      fun j => isEmptyElim j, fun j => isEmptyElim j⟩
  have hβΔ : 0 < β * Δ := mul_pos hβ hΔ
  have hRne : R.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have := (hendR j₀).1
    simp [h, WGraph.degOn] at this
    linarith
  have hRcard : (1 : ℝ) ≤ R.card := by exact_mod_cast hRne.card_pos
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL2 : Real.log 2 ≤ L := le_trans (Real.log_le_log (by norm_num) (by linarith)) hL
  have hLpos : 0 < L := by linarith
  have hsq : 0 < Real.sqrt σ := Real.sqrt_pos.2 hσ
  have hsq1 : Real.sqrt σ ≤ 1 := Real.sqrt_le_one.mpr hσ1
  have hσ32 : σ ^ (3 / 2 : ℝ) = σ * Real.sqrt σ := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hσ, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hσm : σ ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt σ := by
    rw [Real.rpow_neg hσ.le, Real.sqrt_eq_rpow, inv_eq_one_div]
  set ρ : ℝ := L / Real.sqrt σ with hρ
  have hLρ : L ≤ ρ := le_div_self hLpos.le hsq hsq1
  set s : ℕ := ⌈C₀ * ρ⌉₊ with hs
  have hs1 : C₀ * ρ ≤ s := Nat.le_ceil _
  have hs2 : (s : ℝ) < C₀ * ρ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hC₀ρ : 2 ≤ C₀ * ρ := by nlinarith
  have hsle : (s : ℝ) ≤ 2 * C₀ * ρ := by linarith
  have hs2' : 2 ≤ s := by
    have : (2 : ℝ) ≤ s := hC₀ρ.trans hs1
    exact_mod_cast this
  set τ : ℝ := c * β * σ ^ (3 / 2 : ℝ) * Δ / L with hτ
  have hτ0 : 0 ≤ τ := by positivity
  have hsize : ∀ j, ∀ e ∈ scEdges H R (pa j) (pb j) s, e.card ≤ s - 1 := by
    intro j e he
    obtain ⟨p, hp, hlen, -, rfl⟩ := (mem_scEdges _ _ _ _ _ _).1 he
    have := sc_card_interior R (hpairs j).1 (hpairs j).2.1 (hpairs j).2.2 p hp
    omega
  have hcover : ∀ I : Finset κ, I.Nonempty → ∀ Cc : Finset V,
      Cc.card ≤ (2 * s - 3) * (I.card - 1) →
        ∃ j ∈ I, ∃ e ∈ scEdges H R (pa j) (pb j) s, Disjoint e Cc := by
    intro I hI Cc hCc
    have hIpos : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
    set U' : Finset R := Cc.subtype (· ∈ R) with hU'
    have hU'Cc : U'.card ≤ Cc.card := by
      rw [hU', card_subtype]
      exact card_filter_le _ _
    have hCcI : (Cc.card : ℝ) ≤ 2 * s * I.card := by
      have : Cc.card ≤ 2 * s * I.card :=
        hCc.trans (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
      exact_mod_cast this
    have hU2 : (U'.card : ℝ) ≤ 2 * s * I.card := by
      have : (U'.card : ℝ) ≤ Cc.card := by exact_mod_cast hU'Cc
      linarith
    have h2s : 2 * (s : ℝ) * I.card ≤ 4 * C₀ * ρ * I.card := by nlinarith
    have hI1 : (I.card : ℝ) * (β * Δ) ≤ 10 * (R.card * τ) :=
      sc_count H R R pa pb τ (β * Δ) hmult hRT subset_rfl I pa (fun _ => Or.inl rfl)
        hβΔ.le fun j _ => (hendR j).1
    have hIL : (I.card : ℝ) * L ≤ 10 * R.card * c * σ * Real.sqrt σ := by
      have e : 10 * (R.card * τ) = (10 * R.card * c * σ * Real.sqrt σ / L) * (β * Δ) := by
        rw [hτ, hσ32]; field_simp
      rw [e] at hI1
      have := le_of_mul_le_mul_right hI1 hβΔ
      rwa [le_div_iff₀ hLpos] at this
    have hUsmall : (U'.card : ℝ) ≤ c₃ * σ * Fintype.card R := by
      rw [Fintype.card_coe]
      calc (U'.card : ℝ) ≤ 4 * C₀ * ρ * I.card := hU2.trans h2s
        _ = 4 * C₀ * (I.card * L) / Real.sqrt σ := by rw [hρ]; ring
        _ ≤ 4 * C₀ * (10 * R.card * c * σ * Real.sqrt σ) / Real.sqrt σ := by gcongr
        _ = (40 * C₀ * c) * σ * R.card := by field_simp; ring
        _ = m * σ * R.card := by rw [h40]
        _ ≤ c₃ * σ * R.card := by gcongr
    obtain ⟨K, hKU, hKcard, hKwalk⟩ :=
      h33 (H.induce R) Δ σ hΔ (by simpa using hdeg) hgap hσ hσ1 U' hUsmall
    have hexists : ∃ j ∈ I, (∃ k ∈ K, 0 < H.w (pa j) k) ∧ (∃ k ∈ K, 0 < H.w (pb j) k) := by
      by_contra hno
      push Not at hno
      classical
      let g : κ → V := fun j => if ∃ k ∈ K, 0 < H.w (pa j) k then pb j else pa j
      have hg : ∀ j, g j = pa j ∨ g j = pb j := by
        intro j
        by_cases h : ∃ k ∈ K, 0 < H.w (pa j) k
        · exact Or.inr (by simp only [g, h, ite_true])
        · exact Or.inl (by simp only [g, h, ite_false])
      have hgK : ∀ j ∈ I, ∀ k ∈ K, H.w (g j) k = 0 := by
        intro j hj k hk
        by_cases h : ∃ k ∈ K, 0 < H.w (pa j) k
        · have e : g j = pb j := by simp only [g, h, ite_true]
          rw [e]
          exact le_antisymm (hno j hj h k hk) (H.nonneg _ _)
        · have e : g j = pa j := by simp only [g, h, ite_false]
          rw [e]
          push Not at h
          exact le_antisymm (h k hk) (H.nonneg _ _)
      set Y : Finset V := (univ \ K).map (Function.Embedding.subtype _) with hYdef
      have hY : Y ⊆ R := by
        intro v hv
        obtain ⟨v', -, rfl⟩ := mem_map.1 hv
        exact v'.2
      have hYcard : (Y.card : ℝ) ≤ C₃ * U'.card / σ := by
        rw [hYdef, card_map]
        exact hKcard
      have hdegY : ∀ j ∈ I, β * Δ ≤ H.degOn (g j) Y := by
        intro j hj
        have e : H.degOn (g j) Y = H.degOn (g j) R := by
          refine sum_subset hY fun v hvR hvY => ?_
          refine hgK j hj ⟨v, hvR⟩ ?_
          by_contra hvK
          exact hvY (mem_map.2 ⟨⟨v, hvR⟩, mem_sdiff.2 ⟨mem_univ _, hvK⟩, rfl⟩)
        rw [e]
        rcases hg j with h | h <;> rw [h]
        exacts [(hendR j).1, (hendR j).2]
      have h1 := sc_count H R Y pa pb τ (β * Δ) hmult hRT hY I g hg hβΔ.le hdegY
      have key : 10 * (Y.card * τ) ≤ (m * C₃) * (I.card * (β * Δ)) := by
        calc 10 * ((Y.card : ℝ) * τ) ≤ 10 * ((C₃ * (4 * C₀ * ρ * I.card) / σ) * τ) := by
              gcongr
              exact hYcard.trans (by gcongr; exact hU2.trans h2s)
          _ = (40 * C₀ * c) * C₃ * (I.card * (β * Δ)) := by
              rw [hτ, hσ32, hρ]; field_simp; ring
          _ = (m * C₃) * (I.card * (β * Δ)) := by rw [h40]
      have hpos : 0 < (I.card : ℝ) * (β * Δ) := mul_pos hIpos hβΔ
      nlinarith
    obtain ⟨j, hjI, ⟨k₁, hk₁, hw₁⟩, ⟨k₂, hk₂, hw₂⟩⟩ := hexists
    obtain ⟨q, hqU, hqlen⟩ := hKwalk k₁ hk₁ k₂ hk₂
    obtain ⟨p, hp, hplen, hpR, hpC⟩ := sc_build_path H R Cc (pa j) (pb j) (hpairs j).1
      (hpairs j).2.1 k₁ k₂ hw₁ hw₂ q fun z hz hzC => hqU z hz (by rw [hU', mem_subtype]; exact hzC)
    have hqlen' : (q.length : ℝ) ≤ C₃ * ρ := by
      rw [Fintype.card_coe, hσm] at hqlen
      calc (q.length : ℝ) ≤ C₃ * (1 / Real.sqrt σ) * Real.log (2 * R.card) := hqlen
        _ ≤ C₃ * (1 / Real.sqrt σ) * L := by gcongr
        _ = C₃ * ρ := by rw [hρ]; ring
    have hplen' : p.length ≤ s := by
      have : (p.length : ℝ) ≤ s := by
        have h1 : (p.length : ℝ) ≤ q.length + 2 := by exact_mod_cast hplen
        have h2 : C₀ * ρ = C₃ * ρ + 4 * ρ := by rw [hC₀]; ring
        linarith
      exact_mod_cast this
    refine ⟨j, hjI, R.filter (· ∈ p.support), (mem_scEdges _ _ _ _ _ _).2
      ⟨p, hp, hplen', hpR, rfl⟩, ?_⟩
    rw [disjoint_left]
    intro z hz hzC
    rw [mem_filter] at hz
    exact hpC z hz.2 hz.1 hzC
  obtain ⟨f, hf, hdisj⟩ := haxell s hs2' (fun j => scEdges H R (pa j) (pb j) s) hsize hcover
  have hp : ∀ j, ∃ p : H.supp.Walk (pa j) (pb j), p.IsPath ∧ p.length ≤ s ∧
      (∀ z ∈ p.support, z ≠ pa j → z ≠ pb j → z ∈ R) ∧ f j = R.filter (· ∈ p.support) :=
    fun j => (mem_scEdges _ _ _ _ _ _).1 (hf j)
  choose p hpath hlen hint hfeq using hp
  refine ⟨p, hpath, fun j => ?_, hint, ?_⟩
  · have : ((p j).length : ℝ) ≤ s := by exact_mod_cast hlen j
    calc ((p j).length : ℝ) ≤ 2 * C₀ * ρ := this.trans hsle
      _ = 2 * C₀ * L / Real.sqrt σ := by rw [hρ]; ring
  · intro j k hjk z hzR hzj hzk
    have h1 : z ∈ f j := by rw [hfeq j]; exact mem_filter.2 ⟨hzR, hzj⟩
    have h2 : z ∈ f k := by rw [hfeq k]; exact mem_filter.2 ⟨hzR, hzk⟩
    exact disjoint_left.1 (hdisj j k hjk) h1 h2

end Lovasz
