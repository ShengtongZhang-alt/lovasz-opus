/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent)
-/
import Lovasz.Cheeger

/-!
# Lemma 5.1: penalized extraction of a template

DAG node `L5.1` of `docs/BLUEPRINT.md`. Depends on the normalized Cheeger inequality.

The proof follows the paper: with `η = 1 / log n`, maximize the penalized objective
`(d(F) - |T|/8) / m^η = (D - m|T|/8) / m^(1+η)` over all templates `F = Cay(G, T)[A⁺, A⁻]`,
where `D` is the degree sum and `m = |A⁺ ∪ A⁻|`. Comparing the maximizer with a random cut, with
vertex deletions, with label-class deletions and with the two restrictions to a set `B` and its
complement gives all the properties; the spectral gap then follows from Cheeger's inequality.

The combinatorics is phrased with the counts `lcount A⁺ A⁻ t = m f_t` (the number of `v` with
`v, v t` on opposite sides), so that `D = ∑_{t ∈ T} m f_t` for symmetric `T`.
-/

universe u

namespace Lovasz

open Finset

namespace Template

variable {G : Type*} [Group G] [DecidableEq G]

/-- `x, y` lie on opposite sides of `(A⁺, A⁻)`. -/
def side (Ap Am : Finset G) (x y : G) : Prop := (x ∈ Ap ∧ y ∈ Am) ∨ (x ∈ Am ∧ y ∈ Ap)

instance (Ap Am : Finset G) (x y : G) : Decidable (side Ap Am x y) := by
  unfold side; infer_instance

omit [Group G] [DecidableEq G] in
lemma side_comm {Ap Am : Finset G} {x y : G} : side Ap Am x y ↔ side Ap Am y x := by
  unfold side; tauto

omit [Group G] [DecidableEq G] in
lemma side_ne {Ap Am : Finset G} (h : Disjoint Ap Am) {x y : G} (hs : side Ap Am x y) :
    x ≠ y := by
  rintro rfl
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Finset.disjoint_left.1 h h1 h2
  · exact Finset.disjoint_left.1 h h2 h1

omit [Group G] in
lemma side_mem {Ap Am : Finset G} {x y : G} (hs : side Ap Am x y) :
    x ∈ Ap ∪ Am ∧ y ∈ Ap ∪ Am := by
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

omit [Group G] in
lemma side_inter {Ap Am B : Finset G} {x y : G} :
    side (Ap ∩ B) (Am ∩ B) x y ↔ side Ap Am x y ∧ x ∈ B ∧ y ∈ B := by
  unfold side; simp only [mem_inter]; tauto

omit [Group G] in
lemma side_sdiff {Ap Am B : Finset G} {x y : G} :
    side (Ap \ B) (Am \ B) x y ↔ side Ap Am x y ∧ x ∉ B ∧ y ∉ B := by
  unfold side; simp only [mem_sdiff]; tauto

omit [DecidableEq G] in
/-- The adjacency of the template for symmetric `T` and disjoint sides. -/
lemma template_adj_iff {T Ap Am : Finset G} (hT : ∀ t ∈ T, t⁻¹ ∈ T) (hd : Disjoint Ap Am)
    (x y : G) : (templateGraph T Ap Am).Adj x y ↔ side Ap Am x y ∧ x⁻¹ * y ∈ T := by
  constructor
  · rintro ⟨-, hs, ht⟩
    refine ⟨hs, ?_⟩
    rcases ht with ht | ht
    · exact ht
    · simpa using hT _ ht
  · rintro ⟨hs, ht⟩
    exact ⟨side_ne hd hs, hs, Or.inl ht⟩

omit [DecidableEq G] in
lemma template_adj_mul_iff {T Ap Am : Finset G} (hT : ∀ t ∈ T, t⁻¹ ∈ T) (hd : Disjoint Ap Am)
    (x t : G) : (templateGraph T Ap Am).Adj x (x * t) ↔ side Ap Am x (x * t) ∧ t ∈ T := by
  rw [template_adj_iff hT hd, inv_mul_cancel_left]

variable [Fintype G]

/-- `m f_t`: the number of `v` with `v` and `v t` on opposite sides. -/
def lcount (Ap Am : Finset G) (t : G) : ℕ := #{v | side Ap Am v (v * t)}

/-- The degree sum `D = ∑_{t ∈ T} m f_t` of the template. -/
def dsum (T Ap Am : Finset G) : ℕ := ∑ t ∈ T, lcount Ap Am t

/-- The number of template edges leaving `B`. -/
def ecut (T Ap Am B : Finset G) : ℕ :=
  ∑ t ∈ T, #{v | side Ap Am v (v * t) ∧ v ∈ B ∧ v * t ∉ B}

/-- The degree of `v` in the template. -/
def vdeg (T Ap Am : Finset G) (v : G) : ℕ := #{t ∈ T | side Ap Am v (v * t)}

omit [DecidableEq G] in
lemma card_filter_mul_right (p : G → G → Prop) [∀ x y, Decidable (p x y)] (t : G) :
    #{v | p v (v * t)} = #{u | p (u * t⁻¹) u} := by
  refine card_nbij' (· * t) (· * t⁻¹) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    simpa using hv
  · intro u hu
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
    simpa using hu
  · intro v _
    simp
  · intro u _
    simp

lemma lcount_inv (Ap Am : Finset G) (t : G) : lcount Ap Am t⁻¹ = lcount Ap Am t := by
  unfold lcount
  refine Eq.trans ?_ (card_filter_mul_right (fun x y => side Ap Am x y) t).symm
  exact congrArg card (filter_congr fun u _ => side_comm)

lemma ecut_symm {T : Finset G} (hT : ∀ t ∈ T, t⁻¹ ∈ T) (Ap Am B : Finset G) :
    ecut T Ap Am (univ \ B) = ecut T Ap Am B := by
  unfold ecut
  refine sum_nbij' (·⁻¹) (·⁻¹) (fun t ht => hT t ht) (fun t ht => hT t ht) (fun t _ => inv_inv t)
    (fun t _ => inv_inv t) fun t _ => ?_
  refine Eq.trans (card_filter_mul_right
    (fun x y => side Ap Am x y ∧ x ∈ univ \ B ∧ y ∉ univ \ B) t) ?_
  refine congrArg card (filter_congr fun u _ => ?_)
  simp only [mem_sdiff, mem_univ, true_and, not_not]
  rw [side_comm]
  tauto

lemma lcount_split (Ap Am B : Finset G) (t : G) :
    lcount Ap Am t = lcount (Ap ∩ B) (Am ∩ B) t + lcount (Ap \ B) (Am \ B) t +
      #{v | side Ap Am v (v * t) ∧ v ∈ B ∧ v * t ∉ B} +
      #{v | side Ap Am v (v * t) ∧ v ∈ univ \ B ∧ v * t ∉ univ \ B} := by
  unfold lcount
  simp only [card_filter]
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun v _ => ?_
  simp only [side_inter, side_sdiff, mem_sdiff, mem_univ, true_and, not_not]
  by_cases hP : side Ap Am v (v * t) <;> by_cases h5 : v ∈ B <;> by_cases h6 : v * t ∈ B <;>
    simp [hP, h5, h6]

lemma dsum_split (T Ap Am B : Finset G) :
    dsum T Ap Am = dsum T (Ap ∩ B) (Am ∩ B) + dsum T (Ap \ B) (Am \ B) + ecut T Ap Am B +
      ecut T Ap Am (univ \ B) := by
  unfold dsum ecut
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun t _ => lcount_split Ap Am B t

lemma ecut_single {Ap Am : Finset G} (hd : Disjoint Ap Am) (T : Finset G) (v : G) :
    ecut T Ap Am {v} = vdeg T Ap Am v := by
  unfold ecut vdeg
  rw [card_filter]
  refine sum_congr rfl fun t _ => ?_
  by_cases h : side Ap Am v (v * t)
  · rw [ite_eq_left h, card_eq_one]
    refine ⟨v, ?_⟩
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨-, rfl, -⟩
      rfl
    · rintro rfl
      exact ⟨h, rfl, (side_ne hd h).symm⟩
  · rw [ite_eq_right h, card_eq_zero, filter_eq_empty_iff]
    rintro u - ⟨hs, hu, -⟩
    rw [mem_singleton] at hu
    subst hu
    exact h hs

lemma dsum_single {Ap Am : Finset G} (hd : Disjoint Ap Am) (T : Finset G) (v : G) :
    dsum T (Ap ∩ {v}) (Am ∩ {v}) = 0 := by
  unfold dsum
  refine sum_eq_zero fun t _ => ?_
  unfold lcount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro u _ hs
  rw [side_inter, mem_singleton, mem_singleton] at hs
  obtain ⟨hs, hu, hut⟩ := hs
  exact side_ne hd hs (hu.trans hut.symm)

lemma dsum_empty {T Ap Am : Finset G} (h : Ap ∪ Am = ∅) : dsum T Ap Am = 0 := by
  unfold dsum
  refine sum_eq_zero fun t _ => ?_
  unfold lcount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro u _ hs
  have := (side_mem hs).1
  rw [h] at this
  exact notMem_empty _ this

lemma dsum_sdiff {T J : Finset G} (hJ : J ⊆ T) (Ap Am : Finset G) :
    dsum T Ap Am = dsum (T \ J) Ap Am + ∑ t ∈ J, lcount Ap Am t := by
  unfold dsum
  rw [sum_sdiff hJ]

omit [Fintype G] in
lemma vdeg_le (T Ap Am : Finset G) (v : G) : vdeg T Ap Am v ≤ T.card :=
  card_filter_le _ _

/-! ### A cut containing half of the edges -/

omit [Group G] in
lemma side_univ_sdiff (A : Finset G) (x y : G) :
    side A (univ \ A) x y ↔ ((x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A)) := by
  unfold side
  simp only [mem_sdiff, mem_univ, true_and]

omit [Group G] in
/-- For `v ≠ w`, exactly half of all sets separate `v` from `w`. -/
lemma card_separating {v w : G} (hvw : v ≠ w) :
    2 * #{A : Finset G | (v ∈ A ∧ w ∉ A) ∨ (v ∉ A ∧ w ∈ A)} = 2 ^ Fintype.card G := by
  have htog : ∀ A : Finset G, ((v ∈ symmDiff A {v} ∧ w ∉ symmDiff A {v}) ∨
      (v ∉ symmDiff A {v} ∧ w ∈ symmDiff A {v})) ↔ ¬ ((v ∈ A ∧ w ∉ A) ∨ (v ∉ A ∧ w ∈ A)) := by
    intro A
    simp only [mem_symmDiff, mem_singleton, hvw.symm, true_and, not_true_eq_false, and_false,
      or_false, false_and]
    tauto
  have heq : #{A : Finset G | (v ∈ A ∧ w ∉ A) ∨ (v ∉ A ∧ w ∈ A)} =
      #{A : Finset G | ¬ ((v ∈ A ∧ w ∉ A) ∨ (v ∉ A ∧ w ∈ A))} := by
    refine card_nbij' (fun A => symmDiff A {v}) (fun A => symmDiff A {v}) ?_ ?_ ?_ ?_
    · intro A hA
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hA ⊢
      exact fun h => (htog A).1 h hA
    · intro A hA
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hA ⊢
      exact (htog A).2 hA
    · intro A _
      exact symmDiff_symmDiff_cancel_right _ _
    · intro A _
      exact symmDiff_symmDiff_cancel_right _ _
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Finset G)))
    (fun A : Finset G => (v ∈ A ∧ w ∉ A) ∨ (v ∉ A ∧ w ∈ A))
  rw [card_univ, Fintype.card_finset, ← heq] at hsum
  omega

/-- There is a cut `(A, Aᶜ)` of `Cay(G, S)` containing at least half of the edges. -/
lemma exists_half_cut {S : Finset G} (h1 : (1 : G) ∉ S) :
    ∃ A : Finset G, Fintype.card G * S.card ≤ 2 * dsum S A (univ \ A) := by
  have hsep : ∀ s ∈ S, ∀ v : G,
      2 * #{A : Finset G | side A (univ \ A) v (v * s)} = 2 ^ Fintype.card G := by
    intro s hs v
    have hne : v ≠ v * s := by
      intro h
      apply h1
      have : v * s = v * 1 := by rw [mul_one]; exact h.symm
      rw [mul_left_cancel this] at hs
      exact hs
    rw [← card_separating hne]
    congr 2
    exact filter_congr fun A _ => side_univ_sdiff A v (v * s)
  have htot : ∑ A : Finset G, 2 * dsum S A (univ \ A) =
      ∑ _A : Finset G, Fintype.card G * S.card := by
    rw [sum_const, card_univ, Fintype.card_finset, smul_eq_mul]
    unfold dsum lcount
    simp only [mul_sum]
    rw [sum_comm]
    have : ∀ s ∈ S, ∑ A : Finset G, 2 * #{v | side A (univ \ A) v (v * s)} =
        2 ^ Fintype.card G * Fintype.card G := by
      intro s hs
      simp only [card_filter, mul_sum]
      rw [sum_comm]
      have : ∀ v : G, ∑ A : Finset G, 2 * (if side A (univ \ A) v (v * s) then 1 else 0) =
          2 ^ Fintype.card G := by
        intro v
        rw [← mul_sum, ← card_filter]
        exact hsep s hs v
      rw [sum_congr rfl fun v _ => this v, sum_const, card_univ, smul_eq_mul, mul_comm]
    rw [sum_congr rfl this, sum_const, smul_eq_mul]
    ring
  obtain ⟨A, -, hA⟩ := exists_le_of_sum_le (univ_nonempty (α := Finset G)) htot.ge
  exact ⟨A, hA⟩

/-! ### Real inequalities -/

lemma rpow_one_add_eq {x η : ℝ} (hx : 0 ≤ x) (hη : 0 < η) : x ^ (1 + η) = x * x ^ η := by
  rw [Real.rpow_add' hx (by linarith), Real.rpow_one]

/-- `(a + b)^(1+η) - a^(1+η) - b^(1+η) ≥ (η/3) a (a+b)^η` for `0 ≤ a ≤ b`, `0 < η ≤ 1`. -/
lemma rpow_cut_ineq {a b η : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hη : 0 < η) (hη1 : η ≤ 1) :
    η / 3 * a * (a + b) ^ η ≤ (a + b) ^ (1 + η) - a ^ (1 + η) - b ^ (1 + η) := by
  have hb : 0 ≤ b := ha.trans hab
  have hm0 : 0 ≤ a + b := by linarith
  rw [rpow_one_add_eq hm0 hη, rpow_one_add_eq ha hη, rpow_one_add_eq hb hη]
  have hbm : b ^ η ≤ (a + b) ^ η := Real.rpow_le_rpow hb (by linarith) hη.le
  have ham : a ^ η ≤ ((a + b) / 2) ^ η := Real.rpow_le_rpow ha (by linarith) hη.le
  rw [Real.div_rpow hm0 (by norm_num)] at ham
  have h2 : 1 + 2 / 3 * η ≤ (2 : ℝ) ^ η := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have h3 := Real.add_one_le_exp (Real.log 2 * η)
    have h4 := Real.log_two_gt_d9
    nlinarith
  have h2pos : 0 < (2 : ℝ) ^ η := by positivity
  have hmη : 0 ≤ (a + b) ^ η := by positivity
  have key : (a + b) ^ η / 2 ^ η ≤ (a + b) ^ η * (1 - η / 3) := by
    rw [div_le_iff₀ h2pos]
    have : 1 ≤ (1 - η / 3) * 2 ^ η := by nlinarith
    nlinarith
  have h3 : a * a ^ η ≤ a * ((a + b) ^ η * (1 - η / 3)) :=
    mul_le_mul_of_nonneg_left (ham.trans key) ha
  have h4 : b * b ^ η ≤ b * (a + b) ^ η := mul_le_mul_of_nonneg_left hbm hb
  nlinarith

lemma rpow_cut_ineq' {a b η : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hη : 0 < η) (hη1 : η ≤ 1) :
    η / 3 * min a b * (a + b) ^ η ≤ (a + b) ^ (1 + η) - a ^ (1 + η) - b ^ (1 + η) := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab]
    exact rpow_cut_ineq ha hab hη hη1
  · rw [min_eq_right hab, add_comm a b]
    have := rpow_cut_ineq hb hab hη hη1
    linarith

/-- `m^(1+η) - (m-1)^(1+η) ≥ m^η` for `m ≥ 1`. -/
lemma rpow_succ_ineq {m η : ℝ} (hm : 1 ≤ m) (hη : 0 < η) :
    m ^ η ≤ m ^ (1 + η) - (m - 1) ^ (1 + η) := by
  rw [rpow_one_add_eq (by linarith) hη, rpow_one_add_eq (by linarith) hη]
  have : (m - 1) ^ η ≤ m ^ η := Real.rpow_le_rpow (by linarith) (by linarith) hη.le
  have h1 : (m - 1) * (m - 1) ^ η ≤ (m - 1) * m ^ η :=
    mul_le_mul_of_nonneg_left this (by linarith)
  nlinarith

/-! ### Translation to the objects of the statement -/

omit [Fintype G] in
lemma ncard_neighborSet {T Ap Am : Finset G} (hT : ∀ t ∈ T, t⁻¹ ∈ T) (hd : Disjoint Ap Am)
    (v : G) : ((templateGraph T Ap Am).neighborSet v).ncard = vdeg T Ap Am v := by
  have h : (templateGraph T Ap Am).neighborSet v =
      (v * ·) '' ((T.filter fun t => side Ap Am v (v * t) : Finset G) : Set G) := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, template_adj_iff hT hd, Set.mem_image, coe_filter,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hs, ht⟩
      exact ⟨v⁻¹ * w, ⟨ht, by simpa using hs⟩, by simp⟩
    · rintro ⟨t, ⟨ht, hs⟩, rfl⟩
      exact ⟨hs, by simpa using ht⟩
  rw [h, Set.ncard_image_of_injective _ (mul_right_injective v), Set.ncard_coe_finset]
  rfl

lemma labelDensity_eq {T Ap Am : Finset G} (hT : ∀ t ∈ T, t⁻¹ ∈ T) (hd : Disjoint Ap Am)
    {s : G} (hs : s ∈ T) :
    labelDensity T Ap Am s = (lcount Ap Am s : ℝ) / ((Ap ∪ Am).card : ℝ) := by
  unfold labelDensity lcount
  congr 2
  refine congrArg Finset.card ?_
  ext x
  simp only [mem_filter, mem_univ, true_and, template_adj_mul_iff hT hd, hs, and_true]
  exact ⟨fun h => h.2, fun h => ⟨(side_mem h).1, h⟩⟩

omit [Group G] [DecidableEq G] [Fintype G] in
lemma ofSimpleGraph_w_of_adj {V : Type*} {Γ : SimpleGraph V} {x y : V} (h : Γ.Adj x y) :
    (WGraph.ofSimpleGraph Γ).w x y = 1 := by
  simp [WGraph.ofSimpleGraph, h]

omit [Group G] [DecidableEq G] [Fintype G] in
lemma ofSimpleGraph_w_of_not_adj {V : Type*} {Γ : SimpleGraph V} {x y : V} (h : ¬ Γ.Adj x y) :
    (WGraph.ofSimpleGraph Γ).w x y = 0 := by
  simp [WGraph.ofSimpleGraph, h]

lemma template_nbr_sum {T Ap Am : Finset G} (hT : ∀ t ∈ T, t⁻¹ ∈ T) (hd : Disjoint Ap Am)
    (x : G) (f : G → ℝ) :
    ∑ y : ↥(Ap ∪ Am), (WGraph.ofSimpleGraph (templateGraph T Ap Am)).w x y * f y =
      ∑ t ∈ T, if side Ap Am x (x * t) then f (x * t) else 0 := by
  set W := WGraph.ofSimpleGraph (templateGraph T Ap Am)
  have e1 : ∑ y ∈ Ap ∪ Am, W.w x y * f y = ∑ y, W.w x y * f y := by
    refine sum_subset (subset_univ _) fun y _ hy => ?_
    rw [ofSimpleGraph_w_of_not_adj, zero_mul]
    intro h
    exact hy ((side_mem ((template_adj_iff hT hd x y).1 h).1).2)
  refine (Eq.trans (sum_coe_sort (Ap ∪ Am) (fun y => W.w x y * f y)) ?_)
  rw [e1, ← Equiv.sum_comp (Equiv.mulLeft x) (fun y => W.w x y * f y),
    ← Fintype.sum_ite_mem T (fun t => if side Ap Am x (x * t) then f (x * t) else 0)]
  refine sum_congr rfl fun t _ => ?_
  simp only [Equiv.coe_mulLeft]
  by_cases h : side Ap Am x (x * t) ∧ t ∈ T
  · rw [ofSimpleGraph_w_of_adj ((template_adj_mul_iff hT hd x t).2 h), one_mul, ite_eq_left h.2,
      ite_eq_left h.1]
  · rw [ofSimpleGraph_w_of_not_adj (mt (template_adj_mul_iff hT hd x t).1 h), zero_mul]
    by_cases ht : t ∈ T
    · rw [ite_eq_left ht, ite_eq_right (fun hs => h ⟨hs, ht⟩)]
    · rw [ite_eq_right ht]

lemma induce_deg {T Ap Am : Finset G} (hT : ∀ t ∈ T, t⁻¹ ∈ T) (hd : Disjoint Ap Am)
    (x : ↥(Ap ∪ Am)) :
    ((WGraph.ofSimpleGraph (templateGraph T Ap Am)).induce (Ap ∪ Am)).deg x =
      vdeg T Ap Am x := by
  have h := template_nbr_sum hT hd (x : G) (fun _ => 1)
  simp only [mul_one] at h
  unfold WGraph.deg
  change ∑ y : ↥(Ap ∪ Am), (WGraph.ofSimpleGraph (templateGraph T Ap Am)).w x y = _
  rw [h, vdeg, card_filter]
  push_cast
  rfl

lemma induce_edgeWeight {T Ap Am : Finset G} (hT : ∀ t ∈ T, t⁻¹ ∈ T) (hd : Disjoint Ap Am)
    (U : Finset ↥(Ap ∪ Am)) :
    ((WGraph.ofSimpleGraph (templateGraph T Ap Am)).induce (Ap ∪ Am)).edgeWeight U (univ \ U) =
      ecut T Ap Am (U.map (Function.Embedding.subtype _)) := by
  set B := U.map (Function.Embedding.subtype (· ∈ Ap ∪ Am)) with hB
  set W := WGraph.ofSimpleGraph (templateGraph T Ap Am)
  have hmemB : ∀ y : ↥(Ap ∪ Am), (y : G) ∈ B ↔ y ∈ U := by
    intro y
    simp [B]
  have h1 : ∀ x : ↥(Ap ∪ Am), ∑ y ∈ univ \ U, (W.induce (Ap ∪ Am)).w x y =
      ∑ t ∈ T, if side Ap Am x (x * t) ∧ (x : G) * t ∉ B then 1 else 0 := by
    intro x
    have h := template_nbr_sum hT hd (x : G) (fun y => if y ∈ B then 0 else 1)
    rw [sdiff_eq_filter, sum_filter]
    refine Eq.trans ?_ (h.trans (sum_congr rfl fun t _ => ?_))
    · refine sum_congr rfl fun y _ => ?_
      show (if y ∉ U then W.w x y else 0) = W.w x y * if (y : G) ∈ B then 0 else 1
      by_cases hy : y ∈ U
      · simp [hy, (hmemB y).2 hy]
      · simp [hy, (hmemB y).not.2 hy]
    · by_cases h1 : side Ap Am x (x * t) <;> by_cases h2 : (x : G) * t ∈ B <;> simp [h1, h2]
  unfold WGraph.edgeWeight
  rw [sum_congr rfl fun x _ => h1 x]
  have hmap : ∀ g : G → ℝ, ∑ x ∈ U, g x = ∑ x ∈ B, g x := by
    intro g
    rw [hB, sum_map]
    rfl
  rw [hmap (fun x => ∑ t ∈ T, if side Ap Am x (x * t) ∧ x * t ∉ B then (1 : ℝ) else 0),
    sum_comm]
  unfold ecut
  push_cast
  refine sum_congr rfl fun t _ => ?_
  rw [card_filter]
  push_cast
  rw [← Fintype.sum_ite_mem]
  refine sum_congr rfl fun v _ => ?_
  by_cases hv : v ∈ B <;> simp [hv]

omit [Group G] [DecidableEq G] [Fintype G] in
/-- A vertex set is connected in the induced graph if every nonempty proper subset has an edge
leaving it. -/
lemma induce_connected_of_cut {V : Type*} [DecidableEq V] (F : SimpleGraph V) (A : Finset V)
    (hne : A.Nonempty)
    (hcut : ∀ B ⊆ A, B.Nonempty → (A \ B).Nonempty → ∃ x ∈ B, ∃ y ∈ A \ B, F.Adj x y) :
    (F.induce (A : Set V)).Connected := by
  classical
  obtain ⟨a, ha⟩ := hne
  have hV : Nonempty ↥(A : Set V) := ⟨⟨a, ha⟩⟩
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u w => ?_, hV⟩
  by_contra hw
  set B := A.filter fun y => ∃ hy : y ∈ A, (F.induce (A : Set V)).Reachable u ⟨y, hy⟩ with hB
  have huB : (u : V) ∈ B := by
    simp only [hB, mem_filter]
    exact ⟨u.2, u.2, SimpleGraph.Reachable.refl _⟩
  have hwB : (w : V) ∈ A \ B := by
    rw [mem_sdiff]
    refine ⟨w.2, ?_⟩
    simp only [hB, mem_filter, not_and, not_exists]
    intro _ _ h
    exact hw h
  obtain ⟨x, hxB, y, hyAB, hxy⟩ := hcut B (filter_subset _ _) ⟨u, huB⟩ ⟨w, hwB⟩
  simp only [hB, mem_filter] at hxB
  obtain ⟨hxA, hx, hux⟩ := hxB
  rw [mem_sdiff] at hyAB
  apply hyAB.2
  simp only [hB, mem_filter]
  refine ⟨hyAB.1, hyAB.1, hux.trans ?_⟩
  exact SimpleGraph.Adj.reachable (G := F.induce (A : Set V)) (u := ⟨x, hx⟩) (v := ⟨y, hyAB.1⟩)
    hxy

/-- The penalized objective `(d(F) - |T|/8) / m^η = (D - m|T|/8) / m^(1+η)`. -/
noncomputable def obj (η : ℝ) (T Ap Am : Finset G) : ℝ :=
  ((dsum T Ap Am : ℝ) - ((Ap ∪ Am).card : ℝ) * T.card / 8) / ((Ap ∪ Am).card : ℝ) ^ (1 + η)

end Template

open Template in
/-- **Lemma 5.1 (Penalized extraction).** There are disjoint sets `A⁺, A⁻ ⊆ G` and a symmetric
`T ⊆ S` such that `F = Cay(G, T)[A⁺, A⁻]` is connected and `cd ≤ d_F(v) ≤ d`,
`1 - λ₂(N_F) ≥ c L^{-2}`, `f_s(F) ≥ 1/8` for `s ∈ T`, and `|T| ≥ cd`. -/
theorem penalized_extraction :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G]
      (S : Finset G), IsConnectionSet S → S.Nonempty → n₀ ≤ Fintype.card G →
      ∃ T Ap Am : Finset G, T ⊆ S ∧ (∀ s ∈ T, s⁻¹ ∈ T) ∧ Disjoint Ap Am ∧
        ((templateGraph T Ap Am).induce ((Ap ∪ Am : Finset G) : Set G)).Connected ∧
        (∀ v ∈ Ap ∪ Am, c * S.card ≤ ((templateGraph T Ap Am).neighborSet v).ncard) ∧
        ((WGraph.ofSimpleGraph (templateGraph T Ap Am)).induce (Ap ∪ Am)).HasGap
          (c / Real.log (Fintype.card G) ^ 2) ∧
        (∀ s ∈ T, 1 / 8 ≤ labelDensity T Ap Am s) ∧ c * S.card ≤ T.card := by
  refine ⟨1 / 4608, by norm_num, 3, ?_⟩
  intro G _ _ _ S hS hSne hn
  classical
  -- the parameters `n`, `L = log n`, `η = 1 / L`, `d = |S|`
  have hn3 : (3 : ℝ) ≤ (Fintype.card G : ℝ) := by exact_mod_cast hn
  obtain ⟨L, hL_def⟩ : ∃ L, L = Real.log (Fintype.card G) := ⟨_, rfl⟩
  have hL1 : 1 < L := by
    rw [hL_def, Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  obtain ⟨η, hη_def⟩ : ∃ η, η = 1 / L := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη_def]; positivity
  have hη1 : η ≤ 1 := by rw [hη_def, div_le_one (by linarith)]; linarith
  have hd1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hSne.card_pos
  -- a cut with half of the edges
  obtain ⟨A, hA⟩ := exists_half_cut hS.2
  -- the maximizer of the penalized objective
  let dom : Finset (Finset G × Finset G × Finset G) :=
    (S.powerset ×ˢ (univ ×ˢ univ)).filter fun p =>
      (∀ t ∈ p.1, t⁻¹ ∈ p.1) ∧ Disjoint p.2.1 p.2.2 ∧ (p.2.1 ∪ p.2.2).Nonempty
  have hdom : ∀ T' Ap' Am' : Finset G, T' ⊆ S → (∀ t ∈ T', t⁻¹ ∈ T') → Disjoint Ap' Am' →
      (Ap' ∪ Am').Nonempty → (T', Ap', Am') ∈ dom := by
    intro T' Ap' Am' h1 h2 h3 h4
    simp only [dom, mem_filter, mem_product, mem_powerset, mem_univ, and_true]
    exact ⟨h1, h2, h3, h4⟩
  have hAmem : (S, A, univ \ A) ∈ dom := by
    refine hdom _ _ _ subset_rfl hS.1 disjoint_sdiff ?_
    rw [union_sdiff_of_subset (subset_univ A)]
    exact univ_nonempty
  obtain ⟨⟨T, Ap, Am⟩, hmem, hmax⟩ :=
    dom.exists_max_image (fun p => obj η p.1 p.2.1 p.2.2) ⟨_, hAmem⟩
  simp only [dom, mem_filter, mem_product, mem_powerset, mem_univ, and_true] at hmem
  obtain ⟨hTS, hT, hd, hne⟩ := hmem
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = obj η T Ap Am := ⟨_, rfl⟩
  -- consequences of maximality
  have hbound : ∀ T' Ap' Am' : Finset G, T' ⊆ S → (∀ t ∈ T', t⁻¹ ∈ T') → Disjoint Ap' Am' →
      (dsum T' Ap' Am' : ℝ) ≤ ((Ap' ∪ Am').card : ℝ) * T'.card / 8 +
        Φ * ((Ap' ∪ Am').card : ℝ) ^ (1 + η) := by
    intro T' Ap' Am' hT'S hT' hd'
    rcases (Ap' ∪ Am').eq_empty_or_nonempty with he | hne'
    · rw [dsum_empty he, he, card_empty, Nat.cast_zero, Real.zero_rpow (by linarith)]
      simp
    · have hle : obj η T' Ap' Am' ≤ Φ :=
        (hmax (T', Ap', Am') (hdom _ _ _ hT'S hT' hd' hne')).trans_eq hΦ.symm
      have hpos : (0 : ℝ) < ((Ap' ∪ Am').card : ℝ) ^ (1 + η) :=
        Real.rpow_pos_of_pos (by exact_mod_cast hne'.card_pos) _
      unfold obj at hle
      rw [div_le_iff₀ hpos] at hle
      linarith
  have hm1 : (1 : ℝ) ≤ ((Ap ∪ Am).card : ℝ) := by exact_mod_cast hne.card_pos
  have hmpos : (0 : ℝ) < ((Ap ∪ Am).card : ℝ) ^ (1 + η) := Real.rpow_pos_of_pos (by linarith) _
  have hmη : 1 ≤ ((Ap ∪ Am).card : ℝ) ^ η := Real.one_le_rpow hm1 hη0.le
  have heq : (dsum T Ap Am : ℝ) =
      ((Ap ∪ Am).card : ℝ) * T.card / 8 + Φ * ((Ap ∪ Am).card : ℝ) ^ (1 + η) := by
    rw [hΦ, obj, div_mul_cancel₀ _ hmpos.ne']
    ring
  -- the objective is at least `d / 8`
  have hΦlow : (S.card : ℝ) / 8 ≤ Φ := by
    have hle : obj η S A (univ \ A) ≤ Φ := (hmax (S, A, univ \ A) hAmem).trans_eq hΦ.symm
    refine le_trans ?_ hle
    unfold obj
    rw [union_sdiff_of_subset (subset_univ A), card_univ]
    have hnη : ((Fintype.card G : ℕ) : ℝ) ^ η = Real.exp 1 := by
      rw [Real.rpow_def_of_pos (by linarith), hη_def, ← hL_def, mul_one_div_cancel (by linarith)]
    rw [rpow_one_add_eq (by linarith) hη0, hnη, le_div_iff₀ (by positivity)]
    have hA' : ((Fintype.card G : ℕ) : ℝ) * S.card ≤ 2 * dsum S A (univ \ A) := by
      exact_mod_cast hA
    have he := Real.exp_one_lt_d9
    have hnd : 0 ≤ ((Fintype.card G : ℕ) : ℝ) * S.card := by positivity
    have := mul_le_mul_of_nonneg_left he.le hnd
    nlinarith
  have hΦ0 : 0 ≤ Φ := by linarith
  -- edge expansion
  have hcut : ∀ B : Finset G, (S.card : ℝ) * η / 24 *
      min (((Ap ∪ Am) ∩ B).card : ℝ) (((Ap ∪ Am) \ B).card : ℝ) ≤ 2 * (ecut T Ap Am B : ℝ) := by
    intro B
    have hsplit := dsum_split T Ap Am B
    rw [ecut_symm hT] at hsplit
    have h1 := hbound T (Ap ∩ B) (Am ∩ B) hTS hT (hd.mono inter_subset_left inter_subset_left)
    have h2 := hbound T (Ap \ B) (Am \ B) hTS hT (hd.mono sdiff_subset sdiff_subset)
    rw [← union_inter_distrib_right] at h1
    rw [← union_sdiff_distrib] at h2
    have hab : (((Ap ∪ Am) ∩ B).card : ℝ) + (((Ap ∪ Am) \ B).card : ℝ) = (Ap ∪ Am).card := by
      exact_mod_cast card_inter_add_card_sdiff (Ap ∪ Am) B
    have hsplit' : (dsum T Ap Am : ℝ) = dsum T (Ap ∩ B) (Am ∩ B) + dsum T (Ap \ B) (Am \ B) +
        2 * ecut T Ap Am B := by
      rw [hsplit]; push_cast; ring
    have hineq := rpow_cut_ineq' (a := (((Ap ∪ Am) ∩ B).card : ℝ))
      (b := (((Ap ∪ Am) \ B).card : ℝ)) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hη0 hη1
    rw [hab] at hineq
    have hmin0 : 0 ≤ min (((Ap ∪ Am) ∩ B).card : ℝ) (((Ap ∪ Am) \ B).card : ℝ) :=
      le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hTsplit : ((Ap ∪ Am).card : ℝ) * T.card / 8 =
        (((Ap ∪ Am) ∩ B).card : ℝ) * T.card / 8 + (((Ap ∪ Am) \ B).card : ℝ) * T.card / 8 := by
      rw [← hab]; ring
    have step1 : Φ * (((Ap ∪ Am).card : ℝ) ^ (1 + η) - (((Ap ∪ Am) ∩ B).card : ℝ) ^ (1 + η) -
        (((Ap ∪ Am) \ B).card : ℝ) ^ (1 + η)) ≤ 2 * ecut T Ap Am B := by
      nlinarith
    have step2 := mul_le_mul_of_nonneg_left hineq hΦ0
    have step3 : (S.card : ℝ) * η / 24 *
        min (((Ap ∪ Am) ∩ B).card : ℝ) (((Ap ∪ Am) \ B).card : ℝ) ≤
        Φ * (η / 3 * min (((Ap ∪ Am) ∩ B).card : ℝ) (((Ap ∪ Am) \ B).card : ℝ) *
          ((Ap ∪ Am).card : ℝ) ^ η) := by
      have h3 : η / 3 * min (((Ap ∪ Am) ∩ B).card : ℝ) (((Ap ∪ Am) \ B).card : ℝ) ≤
          η / 3 * min (((Ap ∪ Am) ∩ B).card : ℝ) (((Ap ∪ Am) \ B).card : ℝ) *
            ((Ap ∪ Am).card : ℝ) ^ η :=
        le_mul_of_one_le_right (by positivity) hmη
      calc (S.card : ℝ) * η / 24 * min (((Ap ∪ Am) ∩ B).card : ℝ) (((Ap ∪ Am) \ B).card : ℝ)
          = (S.card / 8) * (η / 3 * min (((Ap ∪ Am) ∩ B).card : ℝ)
              (((Ap ∪ Am) \ B).card : ℝ)) := by ring
        _ ≤ Φ * (η / 3 * min (((Ap ∪ Am) ∩ B).card : ℝ) (((Ap ∪ Am) \ B).card : ℝ)) :=
          mul_le_mul_of_nonneg_right hΦlow (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 hΦ0
    linarith
  -- minimum degree
  have hdeg : ∀ v ∈ Ap ∪ Am, (S.card : ℝ) / 16 ≤ vdeg T Ap Am v := by
    intro v hv
    have hsplit := dsum_split T Ap Am {v}
    rw [ecut_symm hT, dsum_single hd, ecut_single hd] at hsplit
    have h2 := hbound T (Ap \ {v}) (Am \ {v}) hTS hT (hd.mono sdiff_subset sdiff_subset)
    rw [← union_sdiff_distrib, sdiff_singleton_eq_erase v (Ap ∪ Am), card_erase_of_mem hv,
      Nat.cast_sub hne.card_pos, Nat.cast_one] at h2
    have hineq := rpow_succ_ineq hm1 hη0
    have hsplit' : (dsum T Ap Am : ℝ) = dsum T (Ap \ {v}) (Am \ {v}) + 2 * vdeg T Ap Am v := by
      rw [hsplit]; push_cast; ring
    have hT0 : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
    have h3 := mul_le_mul_of_nonneg_left hineq hΦ0
    have h4 := mul_le_mul_of_nonneg_left hmη hΦ0
    nlinarith
  -- label densities
  have hlab : ∀ s ∈ T, ((Ap ∪ Am).card : ℝ) / 8 ≤ lcount Ap Am s := by
    intro s hs
    obtain ⟨J, hJ⟩ : ∃ J : Finset G, J = {s, s⁻¹} := ⟨_, rfl⟩
    have hJT : J ⊆ T := by
      intro t ht
      rw [hJ, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl
      exacts [hs, hT _ hs]
    have hJsum : ∑ t ∈ J, lcount Ap Am t = J.card * lcount Ap Am s := by
      rw [← smul_eq_mul, ← sum_const]
      refine sum_congr rfl fun t ht => ?_
      rw [hJ, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl
      · rfl
      · exact lcount_inv Ap Am _
    have hTJ : ∀ t ∈ T \ J, t⁻¹ ∈ T \ J := by
      intro t ht
      rw [mem_sdiff] at ht ⊢
      refine ⟨hT t ht.1, fun h => ht.2 ?_⟩
      rw [hJ, mem_insert, mem_singleton] at h ⊢
      rcases h with h | h
      · right
        rw [← h, inv_inv]
      · left
        exact inv_injective h
    have h1 := hbound (T \ J) Ap Am (sdiff_subset.trans hTS) hTJ hd
    have heq' := heq
    rw [dsum_sdiff hJT, hJsum] at heq'
    have hcardJ : ((T \ J).card : ℝ) = T.card - J.card := by
      rw [card_sdiff_of_subset hJT, Nat.cast_sub (card_le_card hJT)]
    rw [hcardJ] at h1
    have hJ1 : (1 : ℝ) ≤ J.card := by
      exact_mod_cast card_pos.2 ⟨s, by rw [hJ]; exact mem_insert_self _ _⟩
    push_cast at heq'
    have h5 : (J.card : ℝ) * (((Ap ∪ Am).card : ℝ) / 8) ≤ J.card * lcount Ap Am s := by
      nlinarith
    exact le_of_mul_le_mul_left h5 (by linarith)
  refine ⟨T, Ap, Am, hTS, hT, hd, ?_, ?_, ?_, ?_, ?_⟩
  · -- connectivity
    refine induce_connected_of_cut _ _ hne fun B hBV hBne hVB => ?_
    have h := hcut B
    rw [inter_eq_right.2 hBV] at h
    have ha : (1 : ℝ) ≤ B.card := by exact_mod_cast hBne.card_pos
    have hb : (1 : ℝ) ≤ ((Ap ∪ Am) \ B).card := by exact_mod_cast hVB.card_pos
    have hmin : (1 : ℝ) ≤ min (B.card : ℝ) (((Ap ∪ Am) \ B).card : ℝ) := le_min ha hb
    have hpos : (0 : ℝ) < (ecut T Ap Am B : ℝ) := by
      have : (0 : ℝ) < (S.card : ℝ) * η / 24 := by positivity
      nlinarith
    have hne0 : ecut T Ap Am B ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero] at hpos
      exact lt_irrefl _ hpos
    unfold ecut at hne0
    obtain ⟨t, ht, htne⟩ := exists_ne_zero_of_sum_ne_zero hne0
    obtain ⟨x, hx⟩ := card_pos.1 (Nat.pos_of_ne_zero htne)
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨hs, hxB, hxtB⟩ := hx
    exact ⟨x, hxB, x * t, mem_sdiff.2 ⟨(side_mem hs).2, hxtB⟩,
      (template_adj_mul_iff hT hd x t).2 ⟨hs, ht⟩⟩
  · -- degrees
    intro v hv
    rw [ncard_neighborSet hT hd]
    have := hdeg v hv
    have hd0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    linarith
  · -- spectral gap
    set H := (WGraph.ofSimpleGraph (templateGraph T Ap Am)).induce (Ap ∪ Am) with hH
    have hdegH : ∀ x, 0 < H.deg x := fun x => by
      rw [hH, induce_deg hT hd]
      have := hdeg x x.2
      linarith
    have hdegle : ∀ x, H.deg x ≤ S.card := fun x => by
      rw [hH, induce_deg hT hd]
      exact_mod_cast (vdeg_le T Ap Am x).trans (card_le_card hTS)
    have hvolle : ∀ U : Finset ↥(Ap ∪ Am), H.vol U ≤ S.card * U.card := by
      intro U
      unfold WGraph.vol
      calc ∑ x ∈ U, H.deg x ≤ ∑ _x ∈ U, (S.card : ℝ) := sum_le_sum fun x _ => hdegle x
        _ = S.card * U.card := by rw [sum_const, nsmul_eq_mul]; ring
    have hcond : ∀ U : Finset ↥(Ap ∪ Am), 2 * H.vol U ≤ H.vol univ →
        η / 48 * H.vol U ≤ H.edgeWeight U (univ \ U) := by
      intro U hU
      rw [hH, induce_edgeWeight hT hd, ← hH]
      set B := U.map (Function.Embedding.subtype (· ∈ Ap ∪ Am)) with hB
      have h := hcut B
      have hBV : B ⊆ Ap ∪ Am := by
        intro y hy
        rw [hB, mem_map] at hy
        obtain ⟨z, -, rfl⟩ := hy
        exact z.2
      rw [inter_eq_right.2 hBV] at h
      have hBcard : B.card = U.card := card_map _
      have hVB : ((Ap ∪ Am) \ B).card = (univ \ U).card := by
        rw [card_sdiff_of_subset hBV, hBcard, card_univ_sdiff, Fintype.card_coe]
      rw [hBcard, hVB] at h
      have hvolsplit : H.vol univ = H.vol U + H.vol (univ \ U) := by
        unfold WGraph.vol
        exact WGraph.sum_eq_sum_add_sum_sdiff U _
      have hvolmin : H.vol U ≤ S.card * min (U.card : ℝ) ((univ \ U).card : ℝ) := by
        rcases le_total (U.card : ℝ) ((univ \ U).card : ℝ) with h' | h'
        · rw [min_eq_left h']
          exact hvolle U
        · rw [min_eq_right h']
          have := hvolle (univ \ U)
          linarith
      have hη48 : 0 ≤ η / 48 := by positivity
      calc η / 48 * H.vol U ≤ η / 48 * (S.card * min (U.card : ℝ) ((univ \ U).card : ℝ)) :=
            mul_le_mul_of_nonneg_left hvolmin hη48
        _ ≤ ecut T Ap Am B := by linarith
    have hgap := WGraph.hasGap_of_conductance H (η / 48) (by positivity) hdegH hcond
    have hσ : (1 / 4608 : ℝ) / Real.log (Fintype.card G) ^ 2 = (η / 48) ^ 2 / 2 := by
      rw [hη_def, ← hL_def]
      field_simp
      ring
    rw [hσ]
    exact hgap
  · -- label densities
    intro s hs
    rw [labelDensity_eq hT hd hs, le_div_iff₀ (by linarith)]
    have := hlab s hs
    linarith
  · -- the number of labels
    obtain ⟨v, hv⟩ := hne
    have h1 := hdeg v hv
    have h2 : (vdeg T Ap Am v : ℝ) ≤ T.card := by exact_mod_cast vdeg_le T Ap Am v
    have hd0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    linarith

end Lovasz
