/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Scalar Chernoff bounds (classical input)

DAG node `K.chernoff` of `docs/BLUEPRINT.md`: the scalar Chernoff bounds of Section 2.2 of the
paper, for independent variables in `[0,1]` and for sampling without replacement ("their
exponents have the usual order `t² / (µ + t)`").
-/

namespace Lovasz

open Finset

/-- The product of finitely supported distributions (independent coordinates). -/
def FinDist.pi {ι α : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → FinDist α) :
    FinDist (ι → α) where
  support := Fintype.piFinset fun i => (μ i).support
  prob := fun x => ∏ i, (μ i).prob (x i)
  prob_nonneg := fun x => Finset.prod_nonneg fun i _ => (μ i).prob_nonneg (x i)
  sum_prob := by
    rw [← Finset.prod_univ_sum]
    simp [FinDist.sum_prob]

/-! ### Elementary inequalities for `exp` -/

lemma two_mul_three_pow_le_factorial (n : ℕ) : 2 * 3 ^ n ≤ (n + 2).factorial := by
  induction n with
  | zero => simp [Nat.factorial]
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by ring, Nat.factorial_succ, pow_succ]
    nlinarith

/-- Bernstein's bound on the exponential series: `e^θ - 1 - θ ≤ θ² / (2(1 - θ/3))`. -/
lemma exp_sub_one_sub_le {θ : ℝ} (h0 : 0 ≤ θ) (h3 : θ < 3) :
    Real.exp θ - 1 - θ ≤ θ ^ 2 / (2 * (1 - θ / 3)) := by
  have h : HasSum (fun n : ℕ => θ ^ n / (n.factorial : ℝ)) (Real.exp θ) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp θ
  have h2 := (hasSum_nat_add_iff' 2).mpr h
  have hg : HasSum (fun n : ℕ => θ ^ 2 / 2 * (θ / 3) ^ n) (θ ^ 2 / 2 * (1 - θ / 3)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) (by linarith)).mul_left _
  have hle := hasSum_le (fun n => ?_) h2 hg
  · simp [Finset.sum_range_succ] at hle
    have : θ ^ 2 / (2 * (1 - θ / 3)) = θ ^ 2 / 2 * (1 - θ / 3)⁻¹ := by
      field_simp
    rw [this]; linarith
  · have hf := two_mul_three_pow_le_factorial n
    have hf' : (2 * 3 ^ n : ℝ) ≤ ((n + 2).factorial : ℝ) := by exact_mod_cast hf
    have hpos : (0 : ℝ) < 2 * 3 ^ n := by positivity
    rw [div_pow, pow_add]
    rw [div_le_iff₀ (by positivity)]
    calc θ ^ n * θ ^ 2 = θ ^ 2 / 2 * (θ ^ n / 3 ^ n) * (2 * 3 ^ n) := by field_simp
      _ ≤ θ ^ 2 / 2 * (θ ^ n / 3 ^ n) * ((n + 2).factorial : ℝ) := by
        apply mul_le_mul_of_nonneg_left hf' (by positivity)

lemma exp_neg_le_quadratic {θ : ℝ} (h0 : 0 ≤ θ) :
    Real.exp (-θ) ≤ 1 - θ + θ ^ 2 / 2 := by
  have h := Real.quadratic_le_exp_of_nonneg h0
  have hpos : 0 < 1 + θ + θ ^ 2 / 2 := by positivity
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos θ)]
  nlinarith [sq_nonneg θ, sq_nonneg (θ ^ 2), mul_le_mul_of_nonneg_left h
    (show 0 ≤ 1 - θ + θ ^ 2 / 2 by nlinarith [sq_nonneg (θ - 1)])]



lemma exp_mul_le_of_mem_Icc (θ a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    Real.exp (θ * a) ≤ 1 + (Real.exp θ - 1) * a := by
  have := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ θ) (sub_nonneg.2 h1) h0
    (by ring : (1 - a) + a = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at this
  rw [mul_comm]; linarith

/-! ### Tail bounds from exponential moments -/

/-- Markov's inequality for `exp(θ S)`, optimized at `θ = t / (µ + t/3)`. -/
lemma tail_upper {β : Type*} (s : Finset β) (w S : β → ℝ) (hw : ∀ b ∈ s, 0 ≤ w b) (μ t : ℝ)
    (hμ : 0 ≤ μ) (ht : 0 ≤ t)
    (hmgf : ∀ θ : ℝ, 0 ≤ θ → ∑ b ∈ s, w b * Real.exp (θ * S b) ≤
      (∑ b ∈ s, w b) * Real.exp ((Real.exp θ - 1) * μ)) :
    ∑ b ∈ s, (if μ + t ≤ S b then w b else 0) ≤
      (∑ b ∈ s, w b) * Real.exp (-(t ^ 2) / (2 * (μ + t / 3))) := by
  have markov : ∀ θ, 0 ≤ θ → ∑ b ∈ s, (if μ + t ≤ S b then w b else 0) ≤
      (∑ b ∈ s, w b) * Real.exp ((Real.exp θ - 1) * μ - θ * (μ + t)) := by
    intro θ hθ
    calc ∑ b ∈ s, (if μ + t ≤ S b then w b else 0)
        ≤ ∑ b ∈ s, w b * Real.exp (θ * S b) * Real.exp (-(θ * (μ + t))) := by
          apply sum_le_sum
          intro b hb
          have hwb := hw b hb
          split_ifs with h
          · rw [mul_assoc, ← Real.exp_add]
            have : 1 ≤ Real.exp (θ * S b + -(θ * (μ + t))) := Real.one_le_exp (by nlinarith)
            nlinarith
          · positivity
      _ = (∑ b ∈ s, w b * Real.exp (θ * S b)) * Real.exp (-(θ * (μ + t))) := by rw [sum_mul]
      _ ≤ (∑ b ∈ s, w b) * Real.exp ((Real.exp θ - 1) * μ) * Real.exp (-(θ * (μ + t))) :=
          mul_le_mul_of_nonneg_right (hmgf θ hθ) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf
  have hW : 0 ≤ ∑ b ∈ s, w b := sum_nonneg hw
  suffices h : ∃ θ, 0 ≤ θ ∧ (Real.exp θ - 1) * μ - θ * (μ + t) ≤ -(t ^ 2) / (2 * (μ + t / 3)) by
    obtain ⟨θ, hθ, hle⟩ := h
    exact (markov θ hθ).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) hW)
  rcases hμ.eq_or_lt with h | h
  · subst h
    rcases ht.eq_or_lt with h' | h'
    · subst h'
      exact ⟨0, le_rfl, by simp⟩
    · refine ⟨3, by norm_num, ?_⟩
      have : -(t ^ 2) / (2 * (0 + t / 3)) = -(3 / 2 * t) := by
        field_simp
        ring
      rw [this]; linarith
  · refine ⟨t / (μ + t / 3), by positivity, ?_⟩
    set θ := t / (μ + t / 3) with hθdef
    have hθ0 : 0 ≤ θ := by positivity
    have hθ3 : θ < 3 := by rw [hθdef, div_lt_iff₀ (by positivity)]; linarith
    have key := exp_sub_one_sub_le hθ0 hθ3
    have h1 : (Real.exp θ - 1) * μ - θ * (μ + t) ≤ μ * (θ ^ 2 / (2 * (1 - θ / 3))) - θ * t := by
      nlinarith [key]
    refine h1.trans (le_of_eq ?_)
    have h2 : 1 - θ / 3 = μ / (μ + t / 3) := by
      rw [hθdef]; field_simp; ring
    rw [h2, hθdef]
    field_simp
    ring

/-- Markov's inequality for `exp(-θ S)`, optimized at `θ = t / µ`. -/
lemma tail_lower {β : Type*} (s : Finset β) (w S : β → ℝ) (hw : ∀ b ∈ s, 0 ≤ w b) (μ t : ℝ)
    (hμ : 0 ≤ μ) (ht : 0 ≤ t)
    (hmgf : ∀ θ : ℝ, 0 ≤ θ → ∑ b ∈ s, w b * Real.exp (-θ * S b) ≤
      (∑ b ∈ s, w b) * Real.exp ((Real.exp (-θ) - 1) * μ)) :
    ∑ b ∈ s, (if S b ≤ μ - t then w b else 0) ≤
      (∑ b ∈ s, w b) * Real.exp (-(t ^ 2) / (2 * μ)) := by
  rcases hμ.eq_or_lt with h | h
  · subst h
    simp only [mul_zero, div_zero, Real.exp_zero, mul_one]
    apply sum_le_sum
    intro b hb
    split_ifs
    · exact le_rfl
    · exact hw b hb
  set θ := t / μ with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  calc ∑ b ∈ s, (if S b ≤ μ - t then w b else 0)
      ≤ ∑ b ∈ s, w b * Real.exp (-θ * S b) * Real.exp (θ * (μ - t)) := by
        apply sum_le_sum
        intro b hb
        have hwb := hw b hb
        split_ifs with h
        · rw [mul_assoc, ← Real.exp_add]
          have : 1 ≤ Real.exp (-θ * S b + θ * (μ - t)) := Real.one_le_exp (by nlinarith)
          nlinarith
        · positivity
    _ = (∑ b ∈ s, w b * Real.exp (-θ * S b)) * Real.exp (θ * (μ - t)) := by rw [sum_mul]
    _ ≤ (∑ b ∈ s, w b) * Real.exp ((Real.exp (-θ) - 1) * μ) * Real.exp (θ * (μ - t)) :=
        mul_le_mul_of_nonneg_right (hmgf θ hθ0) (Real.exp_pos _).le
    _ = (∑ b ∈ s, w b) * Real.exp ((Real.exp (-θ) - 1) * μ + θ * (μ - t)) := by
        rw [mul_assoc, ← Real.exp_add]
    _ ≤ (∑ b ∈ s, w b) * Real.exp (-(t ^ 2) / (2 * μ)) := by
        apply mul_le_mul_of_nonneg_left _ (sum_nonneg hw)
        apply Real.exp_le_exp.2
        have key := exp_neg_le_quadratic hθ0
        have h1 : (Real.exp (-θ) - 1) * μ + θ * (μ - t) ≤ μ * (θ ^ 2 / 2) - θ * t := by
          nlinarith [key]
        refine h1.trans (le_of_eq ?_)
        rw [hθdef]
        field_simp
        ring

/-! ### Independent variables -/

lemma findist_mgf {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → FinDist ℝ)
    (hμ : ∀ i, ∀ x ∈ (μ i).support, 0 ≤ x ∧ x ≤ 1) (θ : ℝ) :
    ∑ x ∈ (FinDist.pi μ).support, (FinDist.pi μ).prob x * Real.exp (θ * ∑ i, x i) ≤
      Real.exp ((Real.exp θ - 1) * ∑ i, (μ i).expect id) := by
  have h1 : ∑ x ∈ (FinDist.pi μ).support, (FinDist.pi μ).prob x * Real.exp (θ * ∑ i, x i) =
      ∏ i, ∑ a ∈ (μ i).support, (μ i).prob a * Real.exp (θ * a) := by
    rw [prod_univ_sum]
    apply sum_congr rfl
    intro x _
    simp only [FinDist.pi]
    rw [mul_sum, Real.exp_sum, ← prod_mul_distrib]
  rw [h1, mul_sum, Real.exp_sum]
  apply prod_le_prod₀
  · intro i _
    exact sum_nonneg fun a _ => mul_nonneg ((μ i).prob_nonneg a) (Real.exp_pos _).le
  · intro i _
    calc ∑ a ∈ (μ i).support, (μ i).prob a * Real.exp (θ * a)
        ≤ ∑ a ∈ (μ i).support, (μ i).prob a * (1 + (Real.exp θ - 1) * a) := by
          apply sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left
            (exp_mul_le_of_mem_Icc θ a (hμ i a ha).1 (hμ i a ha).2) ((μ i).prob_nonneg a)
      _ = 1 + (Real.exp θ - 1) * (μ i).expect id := by
          simp only [mul_add, mul_one, sum_add_distrib, (μ i).sum_prob, FinDist.expect, id,
            mul_sum]
          congr 1
          apply sum_congr rfl
          intro a _
          ring
      _ ≤ Real.exp ((Real.exp θ - 1) * (μ i).expect id) := by
          linarith [Real.add_one_le_exp ((Real.exp θ - 1) * (μ i).expect id)]

lemma findist_mean_nonneg {ι : Type*} [Fintype ι] (μ : ι → FinDist ℝ)
    (hμ : ∀ i, ∀ x ∈ (μ i).support, 0 ≤ x ∧ x ≤ 1) : 0 ≤ ∑ i, (μ i).expect id :=
  sum_nonneg fun i _ => sum_nonneg fun a ha => mul_nonneg ((μ i).prob_nonneg a) (hμ i a ha).1

/-! ### Sampling without replacement -/

lemma nat_descFactorial_mul_pow_le {k N : ℕ} (hk : k ≤ N) (j : ℕ) :
    k.descFactorial j * N ^ j ≤ N.descFactorial j * k ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    have h1 : (k - j) * N ≤ (N - j) * k := by
      rw [Nat.sub_mul, Nat.sub_mul, mul_comm N k]
      exact Nat.sub_le_sub_left (Nat.mul_le_mul_left j hk) _
    calc (k - j) * k.descFactorial j * (N ^ j * N)
        = ((k - j) * N) * (k.descFactorial j * N ^ j) := by ring
      _ ≤ ((N - j) * k) * (N.descFactorial j * k ^ j) := Nat.mul_le_mul h1 ih
      _ = (N - j) * N.descFactorial j * (k ^ j * k) := by ring

lemma nat_choose_sub_mul_pow_le {k N j : ℕ} (hk : k ≤ N) (hj : j ≤ k) :
    (N - j).choose (k - j) * N ^ j ≤ N.choose k * k ^ j := by
  have hpos : 0 < N.descFactorial j := Nat.descFactorial_pos.2 (hj.trans hk)
  apply Nat.le_of_mul_le_mul_right _ hpos
  have hcm := Nat.choose_mul (n := N) (k := k) (s := j) hj
  have e1 := Nat.descFactorial_eq_factorial_mul_choose N j
  have e2 := Nat.descFactorial_eq_factorial_mul_choose k j
  have key := nat_descFactorial_mul_pow_le hk j
  calc (N - j).choose (k - j) * N ^ j * N.descFactorial j
      = j.factorial * (N.choose j * (N - j).choose (k - j)) * N ^ j := by rw [e1]; ring
    _ = j.factorial * (N.choose k * k.choose j) * N ^ j := by rw [hcm]
    _ = N.choose k * (k.descFactorial j * N ^ j) := by rw [e2]; ring
    _ ≤ N.choose k * (N.descFactorial j * k ^ j) := Nat.mul_le_mul_left _ key
    _ = N.choose k * k ^ j * N.descFactorial j := by ring

lemma card_superset_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι) (k : ℕ)
    (hA : A.card ≤ k) :
    ((powersetCard k (univ : Finset ι)).filter (fun I => A ⊆ I)).card =
      (Fintype.card ι - A.card).choose (k - A.card) := by
  rw [← card_compl, ← card_powersetCard]
  symm
  apply card_nbij' (fun J => J ∪ A) (fun I => I \ A)
  · intro J hJ
    simp only [mem_coe, mem_powersetCard] at hJ
    simp only [mem_coe, mem_filter, mem_powersetCard_univ]
    refine ⟨?_, subset_union_right⟩
    rw [card_union_of_disjoint (subset_compl_iff_disjoint_right.1 hJ.1)]
    omega
  · intro I hI
    simp only [mem_coe, mem_filter, mem_powersetCard_univ] at hI
    simp only [mem_coe, mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [mem_sdiff] at hx
      simpa using hx.2
    · rw [card_sdiff_of_subset hI.2]
      omega
  · intro J hJ
    simp only [mem_coe, mem_powersetCard] at hJ
    exact union_sdiff_cancel_right (subset_compl_iff_disjoint_right.1 hJ.1)
  · intro I hI
    simp only [mem_coe, mem_filter, mem_powersetCard_univ] at hI
    exact sdiff_union_of_subset hI.2

lemma card_superset_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι) (k : ℕ)
    (hk : k ≤ Fintype.card ι) :
    (((powersetCard k (univ : Finset ι)).filter (fun I => A ⊆ I)).card : ℝ) ≤
      (Fintype.card ι).choose k * ((k : ℝ) / Fintype.card ι) ^ A.card := by
  by_cases hA : A.card ≤ k
  · rw [card_superset_eq A k hA]
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with hN | hN
    · have hk0 : k = 0 := by omega
      have hA0 : A.card = 0 := by omega
      simp [hN, hk0, hA0]
    · rw [div_pow, ← mul_div_assoc, le_div_iff₀ (by positivity)]
      exact_mod_cast nat_choose_sub_mul_pow_le hk hA
  · have : (powersetCard k (univ : Finset ι)).filter (fun I => A ⊆ I) = ∅ := by
      rw [filter_eq_empty_iff]
      intro I hI hAI
      rw [mem_powersetCard_univ] at hI
      exact hA (hI ▸ card_le_card hAI)
    rw [this, card_empty, Nat.cast_zero]
    positivity

/-- Negative dependence of sampling without replacement, for increasing functions. -/
lemma sum_prod_one_add_le {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (k : ℕ) (hk : k ≤ Fintype.card ι) :
    ∑ I ∈ powersetCard k (univ : Finset ι), ∏ i ∈ I, (1 + x i) ≤
      (Fintype.card ι).choose k * ∏ i, (1 + (k : ℝ) / Fintype.card ι * x i) := by
  simp_rw [prod_one_add]
  rw [sum_comm' (t' := (univ : Finset ι).powerset)
    (s' := fun A => (powersetCard k (univ : Finset ι)).filter (fun I => A ⊆ I))]
  · rw [mul_sum]
    apply sum_le_sum
    intro A _
    rw [sum_const, nsmul_eq_mul, prod_mul_distrib, prod_const, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (card_superset_le A k hk) (prod_nonneg fun i _ => hx i)
  · intro I A
    simp

lemma hyp_mgf_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (k : ℕ) (hk : k ≤ Fintype.card ι) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∑ I ∈ powersetCard k (univ : Finset ι), Real.exp (θ * ∑ i ∈ I, a i) ≤
      (Fintype.card ι).choose k * ∏ i, (1 - (k : ℝ) / Fintype.card ι +
        (k : ℝ) / Fintype.card ι * Real.exp (θ * a i)) := by
  have h := sum_prod_one_add_le (fun i => Real.exp (θ * a i) - 1)
    (fun i => by simpa using Real.one_le_exp (mul_nonneg hθ (ha i))) k hk
  calc ∑ I ∈ powersetCard k (univ : Finset ι), Real.exp (θ * ∑ i ∈ I, a i)
      = ∑ I ∈ powersetCard k (univ : Finset ι), ∏ i ∈ I, (1 + (Real.exp (θ * a i) - 1)) := by
        apply sum_congr rfl
        intro I _
        rw [mul_sum, Real.exp_sum]
        simp
    _ ≤ _ := h
    _ = _ := by
        congr 1
        apply prod_congr rfl
        intro i _
        ring

/-- The case `θ < 0` reduces to `θ > 0` by passing to the complementary `(N - k)`-subset. -/
lemma hyp_mgf {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (k : ℕ) (hk : k ≤ Fintype.card ι) (θ : ℝ) :
    ∑ I ∈ powersetCard k (univ : Finset ι), Real.exp (θ * ∑ i ∈ I, a i) ≤
      (Fintype.card ι).choose k * ∏ i, (1 - (k : ℝ) / Fintype.card ι +
        (k : ℝ) / Fintype.card ι * Real.exp (θ * a i)) := by
  rcases le_or_gt 0 θ with hθ | hθ
  · exact hyp_mgf_nonneg a ha k hk θ hθ
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hN | hN
  · have hk0 : k = 0 := by omega
    subst hk0
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hN
    simp [univ_eq_empty]
  set N := Fintype.card ι with hNdef
  have e1 : ∑ I ∈ powersetCard k (univ : Finset ι), Real.exp (θ * ∑ i ∈ I, a i) =
      ∑ J ∈ powersetCard (N - k) (univ : Finset ι),
        Real.exp (θ * ∑ i, a i) * Real.exp (-θ * ∑ i ∈ J, a i) := by
    apply sum_nbij' compl compl
    · intro I hI
      rw [mem_powersetCard_univ] at hI ⊢
      rw [card_compl, hI]
    · intro J hJ
      rw [mem_powersetCard_univ] at hJ ⊢
      rw [card_compl, hJ]
      omega
    · intro I _
      exact compl_compl I
    · intro J _
      exact compl_compl J
    · intro I _
      rw [← Real.exp_add, ← sum_compl_add_sum I a]
      ring_nf
  have h2 := hyp_mgf_nonneg a ha (N - k) (Nat.sub_le _ _) (-θ) (by linarith)
  rw [e1, ← mul_sum]
  calc Real.exp (θ * ∑ i, a i) * ∑ J ∈ powersetCard (N - k) (univ : Finset ι),
        Real.exp (-θ * ∑ i ∈ J, a i)
      ≤ Real.exp (θ * ∑ i, a i) * ((N.choose (N - k) : ℝ) * ∏ i, (1 - ((N - k : ℕ) : ℝ) / N +
        ((N - k : ℕ) : ℝ) / N * Real.exp (-θ * a i))) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by
        rw [Nat.choose_symm hk, Nat.cast_sub hk, mul_left_comm, mul_sum, Real.exp_sum,
          ← prod_mul_distrib]
        congr 1
        apply prod_congr rfl
        intro i _
        have hN' : (N : ℝ) ≠ 0 := by positivity
        rw [show Real.exp (-θ * a i) = (Real.exp (θ * a i))⁻¹ by rw [neg_mul, Real.exp_neg]]
        have := (Real.exp_pos (θ * a i)).ne'
        field_simp
        ring

lemma prod_one_sub_add_le_exp {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) :
    ∏ i, (1 - p + p * Real.exp (θ * a i)) ≤ Real.exp ((Real.exp θ - 1) * (p * ∑ i, a i)) := by
  rw [mul_sum, mul_sum, Real.exp_sum]
  apply prod_le_prod₀
  · intro i _
    nlinarith [Real.exp_pos (θ * a i)]
  · intro i _
    have h := exp_mul_le_of_mem_Icc θ (a i) (ha i).1 (ha i).2
    calc 1 - p + p * Real.exp (θ * a i) ≤ 1 + (Real.exp θ - 1) * (p * a i) := by nlinarith
      _ ≤ Real.exp ((Real.exp θ - 1) * (p * a i)) := by
          linarith [Real.add_one_le_exp ((Real.exp θ - 1) * (p * a i))]

lemma hyp_mgf_le_exp {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (k : ℕ) (hk : k ≤ Fintype.card ι) (θ : ℝ) :
    ∑ I ∈ powersetCard k (univ : Finset ι), Real.exp (θ * ∑ i ∈ I, a i) ≤
      (Fintype.card ι).choose k *
        Real.exp ((Real.exp θ - 1) * ((k : ℝ) / Fintype.card ι * ∑ i, a i)) := by
  classical
  have hp0 : 0 ≤ (k : ℝ) / Fintype.card ι := by positivity
  have hp1 : (k : ℝ) / Fintype.card ι ≤ 1 := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with hN | hN
    · simp [hN]
    · exact div_le_one_of_le₀ (by exact_mod_cast hk) (by positivity)
  exact (hyp_mgf a (fun i => (ha i).1) k hk θ).trans
    (mul_le_mul_of_nonneg_left (prod_one_sub_add_le_exp a ha _ hp0 hp1 θ) (Nat.cast_nonneg _))

/-- **Chernoff–Bernstein upper tail.** For independent variables `X_i ∈ [0,1]` with
`µ = ∑ E X_i`, `P(∑ X_i ≥ µ + t) ≤ exp(-t² / (2(µ + t/3)))`. -/
theorem chernoff_upper {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → FinDist ℝ)
    (hμ : ∀ i, ∀ x ∈ (μ i).support, 0 ≤ x ∧ x ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    (FinDist.pi μ).P (fun x => ∑ i, (μ i).expect id + t ≤ ∑ i, x i) ≤
      Real.exp (-(t ^ 2) / (2 * (∑ i, (μ i).expect id + t / 3))) := by
  have hm := findist_mean_nonneg μ hμ
  have h := tail_upper (FinDist.pi μ).support (FinDist.pi μ).prob (fun x => ∑ i, x i)
    (fun b _ => (FinDist.pi μ).prob_nonneg b) (∑ i, (μ i).expect id) t hm ht
    (fun θ _ => by rw [(FinDist.pi μ).sum_prob, one_mul]; exact findist_mgf μ hμ θ)
  rw [(FinDist.pi μ).sum_prob, one_mul] at h
  simp only [FinDist.P]
  convert h

/-- **Chernoff lower tail.** For independent variables `X_i ∈ [0,1]` with `µ = ∑ E X_i`,
`P(∑ X_i ≤ µ - t) ≤ exp(-t² / (2µ))`. -/
theorem chernoff_lower {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → FinDist ℝ)
    (hμ : ∀ i, ∀ x ∈ (μ i).support, 0 ≤ x ∧ x ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    (FinDist.pi μ).P (fun x => ∑ i, x i ≤ ∑ i, (μ i).expect id - t) ≤
      Real.exp (-(t ^ 2) / (2 * ∑ i, (μ i).expect id)) := by
  have hm := findist_mean_nonneg μ hμ
  have h := tail_lower (FinDist.pi μ).support (FinDist.pi μ).prob (fun x => ∑ i, x i)
    (fun b _ => (FinDist.pi μ).prob_nonneg b) (∑ i, (μ i).expect id) t hm ht
    (fun θ _ => by rw [(FinDist.pi μ).sum_prob, one_mul]; exact findist_mgf μ hμ (-θ))
  rw [(FinDist.pi μ).sum_prob, one_mul] at h
  simp only [FinDist.P]
  convert h

/-- **Sampling without replacement, upper tail.** For weights `a_i ∈ [0,1]` and a uniform
`k`-subset `I` of `ι` (`|ι| = N`), with `µ = (k/N) ∑ a_i`,
`P(∑_{i∈I} a_i ≥ µ + t) ≤ exp(-t² / (2(µ + t/3)))` (stated by counting subsets). -/
theorem hypergeometric_upper {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((((univ : Finset ι).powersetCard k).filter fun I =>
        (k : ℝ) / Fintype.card ι * ∑ i, a i + t ≤ ∑ i ∈ I, a i).card : ℝ) ≤
      Real.exp (-(t ^ 2) / (2 * ((k : ℝ) / Fintype.card ι * ∑ i, a i + t / 3))) *
        (Fintype.card ι).choose k := by
  classical
  rcases le_or_gt k (Fintype.card ι) with hk | hk
  swap
  · have : powersetCard k (univ : Finset ι) = ∅ :=
      powersetCard_eq_empty.2 (by rw [card_univ]; exact hk)
    rw [this, filter_empty, card_empty, Nat.cast_zero]
    positivity
  have hμ : 0 ≤ (k : ℝ) / Fintype.card ι * ∑ i, a i :=
    mul_nonneg (by positivity) (sum_nonneg fun i _ => (ha i).1)
  have hW : ∑ I ∈ powersetCard k (univ : Finset ι), (1 : ℝ) = (Fintype.card ι).choose k := by
    simp
  have h := tail_upper (powersetCard k (univ : Finset ι)) (fun _ => (1 : ℝ))
    (fun I => ∑ i ∈ I, a i) (fun _ _ => zero_le_one) _ t hμ ht
    (fun θ _ => by simpa only [hW, one_mul] using hyp_mgf_le_exp a ha k hk θ)
  rw [hW] at h
  rw [card_filter]
  push_cast
  refine le_of_le_of_eq ?_ (mul_comm _ _)
  convert h using 2

/-- **Sampling without replacement, lower tail.** With `µ = (k/N) ∑ a_i`,
`P(∑_{i∈I} a_i ≤ µ - t) ≤ exp(-t² / (2µ))`. -/
theorem hypergeometric_lower {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((((univ : Finset ι).powersetCard k).filter fun I =>
        ∑ i ∈ I, a i ≤ (k : ℝ) / Fintype.card ι * ∑ i, a i - t).card : ℝ) ≤
      Real.exp (-(t ^ 2) / (2 * ((k : ℝ) / Fintype.card ι * ∑ i, a i))) *
        (Fintype.card ι).choose k := by
  classical
  rcases le_or_gt k (Fintype.card ι) with hk | hk
  swap
  · have : powersetCard k (univ : Finset ι) = ∅ :=
      powersetCard_eq_empty.2 (by rw [card_univ]; exact hk)
    rw [this, filter_empty, card_empty, Nat.cast_zero]
    positivity
  have hμ : 0 ≤ (k : ℝ) / Fintype.card ι * ∑ i, a i :=
    mul_nonneg (by positivity) (sum_nonneg fun i _ => (ha i).1)
  have hW : ∑ I ∈ powersetCard k (univ : Finset ι), (1 : ℝ) = (Fintype.card ι).choose k := by
    simp
  have h := tail_lower (powersetCard k (univ : Finset ι)) (fun _ => (1 : ℝ))
    (fun I => ∑ i ∈ I, a i) (fun _ _ => zero_le_one) _ t hμ ht
    (fun θ _ => by simpa only [hW, one_mul] using hyp_mgf_le_exp a ha k hk (-θ))
  rw [hW] at h
  rw [card_filter]
  push_cast
  refine le_of_le_of_eq ?_ (mul_comm _ _)
  convert h using 2

end Lovasz
