/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Connecting.Basic

/-!
# Label sampling (6.2)

DAG node `E6.1` of `docs/BLUEPRINT.md` (Section 6.1 of the paper).
-/

universe u

noncomputable section

namespace Lovasz

open Finset Classical

namespace Connector

section LabelSamplingAux

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

/-! ### Elementary facts about `FinDist.P` -/

private lemma lsP_mono {α : Type*} (μ : FinDist α) {E F : α → Prop} (h : ∀ a, E a → F a) :
    μ.P E ≤ μ.P F := by
  unfold FinDist.P
  apply sum_le_sum
  intro a _
  by_cases hE : E a
  · simp [hE, h a hE]
  · by_cases hF : F a
    · simp [hE, hF, μ.prob_nonneg a]
    · simp [hE, hF]

private lemma lsP_or {α : Type*} (μ : FinDist α) (E F : α → Prop) :
    μ.P (fun a => E a ∨ F a) ≤ μ.P E + μ.P F := by
  unfold FinDist.P
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro a _
  by_cases hE : E a <;> by_cases hF : F a <;> simp [hE, hF, μ.prob_nonneg a]

private lemma lsP_exists {α ι : Type*} (μ : FinDist α) (s : Finset ι) (E : ι → α → Prop) :
    μ.P (fun a => ∃ i ∈ s, E i a) ≤ ∑ i ∈ s, μ.P (E i) := by
  induction s using Finset.induction_on with
  | empty => simp [FinDist.P]
  | insert j s hj ih =>
    rw [sum_insert hj]
    refine (lsP_mono μ (F := fun a => E j a ∨ ∃ i ∈ s, E i a) ?_).trans
      ((lsP_or μ _ _).trans (add_le_add le_rfl ih))
    rintro a ⟨i, hi, h⟩
    rcases mem_insert.1 hi with rfl | hi
    · exact Or.inl h
    · exact Or.inr ⟨i, hi, h⟩

/-! ### Chernoff bounds for weighted sums of the label coins -/

omit [Group G] in
private lemma label_mgf (q : ℝ) (a : G → ℝ) (ha : ∀ g, 0 ≤ a g ∧ a g ≤ 1) (θ : ℝ) :
    ∑ ξ ∈ (labelLaw G q).support, (labelLaw G q).prob ξ *
        Real.exp (θ * ∑ g, a g * (if ξ g = true then 1 else 0)) ≤
      Real.exp ((Real.exp θ - 1) * (max 0 (min q 1) * ∑ g, a g)) := by
  have hp0 : 0 ≤ max 0 (min q 1) := le_max_left _ _
  have hp1 : max 0 (min q 1) ≤ 1 := max_le zero_le_one (min_le_right _ _)
  have h1 : ∑ ξ ∈ (labelLaw G q).support, (labelLaw G q).prob ξ *
        Real.exp (θ * ∑ g, a g * (if ξ g = true then 1 else 0)) =
      ∏ g, ∑ b ∈ (univ : Finset Bool),
        (coinDist q).prob b * Real.exp (θ * (a g * (if b = true then 1 else 0))) := by
    rw [prod_univ_sum]
    show ∑ ξ ∈ Fintype.piFinset (fun _ : G => (univ : Finset Bool)),
        (∏ g, (coinDist q).prob (ξ g)) *
          Real.exp (θ * ∑ g, a g * (if ξ g = true then 1 else 0)) = _
    apply sum_congr rfl
    intro ξ _
    rw [mul_sum, Real.exp_sum, ← prod_mul_distrib]
  rw [h1]
  have h2 : ∀ g, ∑ b ∈ (univ : Finset Bool),
      (coinDist q).prob b * Real.exp (θ * (a g * (if b = true then 1 else 0))) =
      1 - max 0 (min q 1) + max 0 (min q 1) * Real.exp (θ * a g) := by
    intro g
    rw [Fintype.sum_bool]
    simp [coinDist]
    ring
  simp_rw [h2]
  exact prod_one_sub_add_le_exp a ha _ hp0 hp1 θ

omit [Group G] in
private lemma label_lower (q : ℝ) (a : G → ℝ) (ha : ∀ g, 0 ≤ a g ∧ a g ≤ 1) :
    (labelLaw G q).P (fun ξ => ∑ g, a g * (if ξ g = true then 1 else 0) ≤
        (max 0 (min q 1) * ∑ g, a g) / 2) ≤
      Real.exp (-(max 0 (min q 1) * ∑ g, a g) / 8) := by
  set μ := max 0 (min q 1) * ∑ g, a g with hμdef
  have hμ : 0 ≤ μ := mul_nonneg (le_max_left _ _) (sum_nonneg fun g _ => (ha g).1)
  have h := tail_lower (labelLaw G q).support (labelLaw G q).prob
    (fun ξ => ∑ g, a g * (if ξ g = true then 1 else 0))
    (fun ξ _ => (labelLaw G q).prob_nonneg ξ) μ (μ / 2) hμ (by positivity)
    (fun θ _ => by rw [(labelLaw G q).sum_prob, one_mul]; exact label_mgf q a ha (-θ))
  rw [(labelLaw G q).sum_prob, one_mul] at h
  have e1 : μ - μ / 2 = μ / 2 := by ring
  have e2 : -(μ / 2) ^ 2 / (2 * μ) = -μ / 8 := by
    rcases eq_or_ne μ 0 with h0 | h0
    · simp [h0]
    · field_simp
      ring
  rw [e1, e2] at h
  simp only [FinDist.P]
  convert h using 1

omit [Group G] in
private lemma label_upper (q : ℝ) (a : G → ℝ) (ha : ∀ g, 0 ≤ a g ∧ a g ≤ 1) (M : ℝ)
    (hM : 0 < M) (hμM : max 0 (min q 1) * ∑ g, a g ≤ M) :
    (labelLaw G q).P (fun ξ => 4 * M < ∑ g, a g * (if ξ g = true then 1 else 0)) ≤
      Real.exp (-(9 * M / 4)) := by
  set μ := max 0 (min q 1) * ∑ g, a g with hμdef
  have hμ : 0 ≤ μ := mul_nonneg (le_max_left _ _) (sum_nonneg fun g _ => (ha g).1)
  have h := tail_upper (labelLaw G q).support (labelLaw G q).prob
    (fun ξ => ∑ g, a g * (if ξ g = true then 1 else 0))
    (fun ξ _ => (labelLaw G q).prob_nonneg ξ) μ (3 * M) hμ (by positivity)
    (fun θ _ => by rw [(labelLaw G q).sum_prob, one_mul]; exact label_mgf q a ha θ)
  rw [(labelLaw G q).sum_prob, one_mul] at h
  have h' : (labelLaw G q).P (fun ξ => μ + 3 * M ≤ ∑ g, a g * (if ξ g = true then 1 else 0)) ≤
      Real.exp (-(3 * M) ^ 2 / (2 * (μ + 3 * M / 3))) := by
    simp only [FinDist.P]
    convert h using 1
  refine le_trans (lsP_mono _ fun ξ hξ => ?_) (h'.trans (Real.exp_le_exp.2 ?_))
  · linarith
  · have e1 : 9 * M / 4 = (3 * M) ^ 2 / (4 * M) := by
      field_simp
      ring
    have e2 : (3 * M) ^ 2 / (4 * M) ≤ (3 * M) ^ 2 / (2 * (μ + 3 * M / 3)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    rw [neg_div, e1]
    linarith

/-! ### Counting retained neighbours -/

omit [DecidableEq G] in
private lemma classRep_eq (s : G) : classRep s = s ∨ classRep s = s⁻¹ := by
  unfold classRep
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma fiber_card_le (N : Finset G) (f : G → G) (hf : Function.Injective f) (g : G) :
    (N.filter fun y => classRep (f y) = g).card ≤ 2 := by
  have hsub : (N.filter fun y => classRep (f y) = g) ⊆
      (N.filter fun y => f y = g) ∪ (N.filter fun y => f y = g⁻¹) := by
    intro y hy
    rw [mem_filter] at hy
    rw [mem_union, mem_filter, mem_filter]
    rcases classRep_eq (f y) with h | h
    · exact Or.inl ⟨hy.1, h.symm.trans hy.2⟩
    · refine Or.inr ⟨hy.1, ?_⟩
      rw [← hy.2, h, inv_inv]
  have h1 : ∀ c, (N.filter fun y => f y = c).card ≤ 1 := fun c =>
    card_le_one.2 fun y hy y' hy' => hf ((mem_filter.1 hy).2.trans (mem_filter.1 hy').2.symm)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ 1 + 1 := add_le_add (h1 _) (h1 _)

/-- The weights of the label coins in a retained-neighbour count. -/
private def fw (N : Finset G) (f : G → G) (g : G) : ℝ :=
  ((N.filter fun y => classRep (f y) = g).card : ℝ) / 2

private lemma fw_mem (N : Finset G) (f : G → G) (hf : Function.Injective f) (g : G) :
    0 ≤ fw N f g ∧ fw N f g ≤ 1 := by
  unfold fw
  refine ⟨by positivity, ?_⟩
  have : ((N.filter fun y => classRep (f y) = g).card : ℝ) ≤ 2 := by
    exact_mod_cast fiber_card_le N f hf g
  linarith

private lemma fw_sum (N : Finset G) (f : G → G) : ∑ g, fw N f g = (N.card : ℝ) / 2 := by
  unfold fw
  rw [← sum_div]
  congr 1
  have := sum_fiberwise N (fun y => classRep (f y)) (fun _ => (1 : ℝ))
  simpa using this

private lemma count_eq (N : Finset G) (f : G → G) (ξ : G → Bool) :
    ((N.filter fun y => ξ (classRep (f y)) = true).card : ℝ) =
      2 * ∑ g, fw N f g * (if ξ g = true then 1 else 0) := by
  have h := sum_fiberwise' N (fun y => classRep (f y))
    (fun g => if ξ g = true then (1 : ℝ) else 0)
  rw [card_filter, Nat.cast_sum, mul_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← h]
  apply sum_congr rfl
  intro g _
  rw [sum_const, nsmul_eq_mul, fw]
  ring

private lemma copyGraph_sampled_adj (T Ap Am : Finset G) (ξ : G → Bool) (g x y : G) :
    (copyGraph (sampled T ξ) Ap Am g).Adj x y ↔
      (copyGraph T Ap Am g).Adj x y ∧ ξ (classRep (x⁻¹ * y)) = true := by
  show (g⁻¹ * x ≠ g⁻¹ * y ∧ ((g⁻¹ * x ∈ Ap ∧ g⁻¹ * y ∈ Am) ∨ (g⁻¹ * x ∈ Am ∧ g⁻¹ * y ∈ Ap)) ∧
      ((g⁻¹ * x)⁻¹ * (g⁻¹ * y) ∈ sampled T ξ ∨ (g⁻¹ * y)⁻¹ * (g⁻¹ * x) ∈ sampled T ξ)) ↔
    (g⁻¹ * x ≠ g⁻¹ * y ∧ ((g⁻¹ * x ∈ Ap ∧ g⁻¹ * y ∈ Am) ∨ (g⁻¹ * x ∈ Am ∧ g⁻¹ * y ∈ Ap)) ∧
      ((g⁻¹ * x)⁻¹ * (g⁻¹ * y) ∈ T ∨ (g⁻¹ * y)⁻¹ * (g⁻¹ * x) ∈ T)) ∧
      ξ (classRep (x⁻¹ * y)) = true
  have e1 : (g⁻¹ * x)⁻¹ * (g⁻¹ * y) = x⁻¹ * y := by group
  have e2 : (g⁻¹ * y)⁻¹ * (g⁻¹ * x) = (x⁻¹ * y)⁻¹ := by group
  rw [e1, e2]
  simp only [sampled, mem_filter, classRep_inv]
  tauto

/-- One Chernoff test of (6.2): the retained neighbours among `N` of the vertex `v`. -/
private lemma pair_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (N : Finset G) (v : G) (b : ℝ)
    (hb : b ≤ q * N.card / 2) :
    (labelLaw G q).P (fun ξ => ((N.filter fun y => ξ (classRep (v⁻¹ * y)) = true).card : ℝ) < b) ≤
      Real.exp (-(q * N.card / 16)) := by
  have hp : max 0 (min q 1) = q := by rw [min_eq_left hq1, max_eq_right hq0]
  have h := label_lower q (fw N (fun y => v⁻¹ * y)) (fw_mem N _ (mul_right_injective v⁻¹))
  rw [hp, fw_sum] at h
  refine le_trans (lsP_mono _ fun ξ hξ => ?_) (h.trans (le_of_eq ?_))
  · have e := count_eq N (fun y => v⁻¹ * y) ξ
    linarith
  · congr 1
    ring

/-- The number of pairs `(i, v)` with `v` in the copy `i` is at most `2 λ n`. -/
private lemma pair_count {S T Ap Am : Finset G} {𝒜 : Allocation G} {lam D σ η ω cN CN : ℝ}
    (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN) :
    ∑ i, ((copyVerts Ap Am (𝒜.g i)).card : ℝ) ≤ Fintype.card G * (2 * lam) := by
  have e : ∑ i, (copyVerts Ap Am (𝒜.g i)).card =
      ∑ v, ((univ : Finset (Fin 𝒜.t)).filter fun i => v ∈ copyVerts Ap Am (𝒜.g i)).card := by
    simp only [card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    simp
  calc ∑ i, ((copyVerts Ap Am (𝒜.g i)).card : ℝ)
      = ((∑ i, (copyVerts Ap Am (𝒜.g i)).card : ℕ) : ℝ) := by push_cast; rfl
    _ = ((∑ v, ((univ : Finset (Fin 𝒜.t)).filter fun i =>
          v ∈ copyVerts Ap Am (𝒜.g i)).card : ℕ) : ℝ) := by rw [e]
    _ = ∑ v, (((univ : Finset (Fin 𝒜.t)).filter fun i =>
          v ∈ copyVerts Ap Am (𝒜.g i)).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ _v : G, 2 * lam := sum_le_sum fun v _ => hgood.cover_mult v
    _ = Fintype.card G * (2 * lam) := by simp [sum_const, card_univ]

end LabelSamplingAux

/-- **Label sampling (6.2).** Retain the inverse label classes of `T` independently with
probability `t₀/d`, `t₀ = A₁ λ L`. For a successful allocation, with probability at least `3/4`
every full-copy vertex has at least `c₂ L = Ω(t₀/λ)` neighbours in the part via retained labels,
and at most `2t₀` classes (so at most `4t₀` labels) are retained. -/
theorem label_sampling (cT A₀ cN : ℝ) (hcT : 0 < cT) (hA₀ : 0 < A₀) (hcN : 0 < cN) :
    ∃ A₁ c₂ : ℝ, 0 < A₁ ∧ 0 < c₂ ∧ ∃ n₀ : ℕ,
      ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S T Ap Am : Finset G)
        (𝒜 : Allocation G) (D σ η ω CN : ℝ),
        n₀ ≤ Fintype.card G → IsConnectionSet S →
        Real.log (Fintype.card G) ^ 12 ≤ S.card → IsTemplate S T Ap Am cT →
        𝒜.Good S T Ap Am (A₀ * Real.log (Fintype.card G)) D σ η ω cN CN →
        (labelLaw G (A₁ * A₀ * Real.log (Fintype.card G) ^ 2 / S.card)).P (fun ξ =>
          ¬ (Sampled62 𝒜 T Ap Am ξ (c₂ * Real.log (Fintype.card G)) ∧
            ((sampled T ξ).card : ℝ) ≤ 4 * A₁ * A₀ * Real.log (Fintype.card G) ^ 2)) ≤ 1 / 4 := by
  refine ⟨32 / cN, 16, by positivity, by norm_num, ?_⟩
  set A₁ : ℝ := 32 / cN with hA₁def
  have hA₁ : 0 < A₁ := by positivity
  have hA₁cN : A₁ * cN = 32 := by rw [hA₁def]; field_simp
  clear_value A₁
  set L₀ : ℝ := max 1 (max (32 * A₀) (max (A₁ * A₀) (7 / (A₁ * A₀)))) with hL₀def
  refine ⟨⌈Real.exp L₀⌉₊, ?_⟩
  intro G _ _ _ S T Ap Am 𝒜 D σ η ω CN hn hS hd hT hgood
  have hnpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  set L := Real.log (Fintype.card G) with hLdef
  have hLL₀ : L₀ ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hnpos]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hLL₀
  have hL32 : 32 * A₀ ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hLL₀
  have hLA : A₁ * A₀ ≤ L :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hLL₀
  have hL7 : 7 / (A₁ * A₀) ≤ L :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hLL₀
  have hLpos : 0 < L := by linarith
  set d : ℝ := (S.card : ℝ) with hddef
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hd
  set q : ℝ := A₁ * A₀ * L ^ 2 / d with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by
    rw [hqdef, div_le_one hdpos]
    have h1 : A₁ * A₀ * L ^ 2 ≤ L * L ^ 2 := mul_le_mul_of_nonneg_right hLA (sq_nonneg L)
    have h2 : L * L ^ 2 ≤ L ^ 12 := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ hL1 (by norm_num)
    linarith
  have hqd : q * d = A₁ * A₀ * L ^ 2 := by rw [hqdef]; field_simp
  have hp : max 0 (min q 1) = q := by rw [min_eq_left hq1, max_eq_right hq0]
  set M : ℝ := A₁ * A₀ * L ^ 2 / 2 with hMdef
  have hMpos : 0 < M := by positivity
  -- the two failure events
  have hsplit : ∀ ξ : G → Bool,
      ¬ (Sampled62 𝒜 T Ap Am ξ (16 * L) ∧ ((sampled T ξ).card : ℝ) ≤ 4 * A₁ * A₀ * L ^ 2) →
      (∃ i ∈ (univ : Finset (Fin 𝒜.t)), ∃ v ∈ copyVerts Ap Am (𝒜.g i),
        ((((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y).filter
          fun y => ξ (classRep (v⁻¹ * y)) = true).card : ℝ) < 16 * L) ∨
      4 * M < ∑ g, fw T (fun s => s) g * (if ξ g = true then 1 else 0) := by
    intro ξ h
    by_cases h1 : Sampled62 𝒜 T Ap Am ξ (16 * L)
    · right
      have h2 : ¬ ((sampled T ξ).card : ℝ) ≤ 4 * A₁ * A₀ * L ^ 2 := fun h2 => h ⟨h1, h2⟩
      push Not at h2
      have e : ((sampled T ξ).card : ℝ) =
          2 * ∑ g, fw T (fun s => s) g * (if ξ g = true then 1 else 0) :=
        count_eq T (fun s => s) ξ
      rw [hMdef]
      linarith
    · left
      unfold Sampled62 at h1
      push Not at h1
      obtain ⟨i, v, hv, hlt⟩ := h1
      refine ⟨i, mem_univ _, v, hv, ?_⟩
      have e : ((𝒜.part i).filter fun y => (copyGraph (sampled T ξ) Ap Am (𝒜.g i)).Adj v y) =
          (((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y).filter
            fun y => ξ (classRep (v⁻¹ * y)) = true) := by
        rw [filter_filter]
        exact filter_congr fun y _ => copyGraph_sampled_adj T Ap Am ξ _ v y
      rw [← e]
      exact hlt
  -- the first failure event
  have hP1 : (labelLaw G q).P (fun ξ => ∃ i ∈ (univ : Finset (Fin 𝒜.t)),
      ∃ v ∈ copyVerts Ap Am (𝒜.g i),
        ((((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y).filter
          fun y => ξ (classRep (v⁻¹ * y)) = true).card : ℝ) < 16 * L) ≤ 1 / 8 := by
    refine (lsP_exists _ _ _).trans ?_
    have hpair : ∀ i : Fin 𝒜.t, (labelLaw G q).P (fun ξ => ∃ v ∈ copyVerts Ap Am (𝒜.g i),
        ((((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y).filter
          fun y => ξ (classRep (v⁻¹ * y)) = true).card : ℝ) < 16 * L) ≤
        ((copyVerts Ap Am (𝒜.g i)).card : ℝ) * Real.exp (-(2 * L)) := by
      intro i
      refine (lsP_exists _ _ _).trans ?_
      rw [← nsmul_eq_mul, ← sum_const]
      apply sum_le_sum
      intro v hv
      have hN := hgood.nbhd_lower i v hv
      set N := (𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y with hNdef
      have hqN : 32 * L ≤ q * N.card := by
        have h1 : q * (cN * d / (A₀ * L)) = 32 * L := by
          rw [hqdef]
          field_simp
          linear_combination hA₁cN
        rw [← h1]
        exact mul_le_mul_of_nonneg_left hN hq0
      refine (pair_bound q hq0 hq1 N v (16 * L) (by linarith)).trans ?_
      exact Real.exp_le_exp.2 (by linarith)
    refine (sum_le_sum fun i _ => hpair i).trans ?_
    rw [← sum_mul]
    have hc := pair_count hgood
    have hn_eq : (Fintype.card G : ℝ) = Real.exp L := (Real.exp_log hnpos).symm
    rw [hn_eq] at hc
    calc (∑ i, ((copyVerts Ap Am (𝒜.g i)).card : ℝ)) * Real.exp (-(2 * L))
        ≤ Real.exp L * (2 * (A₀ * L)) * Real.exp (-(2 * L)) :=
          mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
      _ = 2 * A₀ * L / Real.exp L := by
          rw [div_eq_mul_inv, ← Real.exp_neg]
          have : Real.exp L * Real.exp (-(2 * L)) = Real.exp (-L) := by
            rw [← Real.exp_add]; ring_nf
          calc Real.exp L * (2 * (A₀ * L)) * Real.exp (-(2 * L))
              = (Real.exp L * Real.exp (-(2 * L))) * (2 * A₀ * L) := by ring
            _ = _ := by rw [this]; ring
      _ ≤ 1 / 8 := by
          rw [div_le_iff₀ (Real.exp_pos L)]
          have hq := Real.quadratic_le_exp_of_nonneg hLpos.le
          nlinarith
  -- the second failure event
  have hP2 : (labelLaw G q).P (fun ξ =>
      4 * M < ∑ g, fw T (fun s => s) g * (if ξ g = true then 1 else 0)) ≤ 1 / 8 := by
    have hμM : max 0 (min q 1) * ∑ g, fw T (fun s => s) g ≤ M := by
      rw [hp, fw_sum, hMdef, ← hqd]
      have hTS : (T.card : ℝ) ≤ d := by rw [hddef]; exact_mod_cast card_le_card hT.sub
      have := mul_le_mul_of_nonneg_left hTS hq0
      linarith
    refine (label_upper q _ (fw_mem T _ fun _ _ h => h) M hMpos hμM).trans ?_
    have h7 : 7 ≤ 9 * M / 4 := by
      have h1 : 7 ≤ A₁ * A₀ * L := by
        rw [div_le_iff₀ (by positivity)] at hL7
        linarith
      have h2 : A₁ * A₀ * L ≤ A₁ * A₀ * L ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      rw [hMdef]
      linarith
    have h8 : 8 ≤ Real.exp (9 * M / 4) := by
      have := Real.add_one_le_exp (9 * M / 4)
      linarith
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h8
  calc (labelLaw G q).P _ ≤ (labelLaw G q).P (fun ξ => (∃ i ∈ (univ : Finset (Fin 𝒜.t)),
      ∃ v ∈ copyVerts Ap Am (𝒜.g i),
        ((((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y).filter
          fun y => ξ (classRep (v⁻¹ * y)) = true).card : ℝ) < 16 * L) ∨
      4 * M < ∑ g, fw T (fun s => s) g * (if ξ g = true then 1 else 0)) := lsP_mono _ hsplit
    _ ≤ _ := lsP_or _ _ _
    _ ≤ 1 / 8 + 1 / 8 := add_le_add hP1 hP2
    _ = 1 / 4 := by norm_num

end Connector

end Lovasz
