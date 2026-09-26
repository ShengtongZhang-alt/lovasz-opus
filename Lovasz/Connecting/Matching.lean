/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.Connecting.Basic

/-!
# The random matching (6.13)–(6.17)

DAG node `E6.13` of `docs/BLUEPRINT.md` (Section 6.4 of the paper).
-/

universe u

noncomputable section

namespace Lovasz

open Finset Classical

namespace Connector

/-! ### Finite probability helpers -/

section ProbHelpers

variable {α ι : Type*}

lemma mt_ite_nonneg (ν : FinDist α) (P : Prop) [Decidable P] (a : α) :
    0 ≤ (if P then ν.prob a else 0) := by
  split_ifs
  · exact ν.prob_nonneg a
  · exact le_rfl

lemma mt_P_mono (ν : FinDist α) {E F : α → Prop} (h : ∀ a ∈ ν.support, E a → F a) :
    ν.P E ≤ ν.P F := by
  unfold FinDist.P
  refine sum_le_sum fun a ha => ?_
  by_cases hE : E a
  · rw [ite_eq_left hE, ite_eq_left (h a ha hE)]
  · rw [ite_eq_right hE]
    exact mt_ite_nonneg ν _ a

lemma mt_P_or_le (ν : FinDist α) (E F : α → Prop) :
    ν.P (fun a => E a ∨ F a) ≤ ν.P E + ν.P F := by
  unfold FinDist.P
  rw [← sum_add_distrib]
  refine sum_le_sum fun a _ => ?_
  have := ν.prob_nonneg a
  by_cases hE : E a <;> by_cases hF : F a <;> simp [hE, hF, this]

lemma mt_P_exists_le (ν : FinDist α) (s : Finset ι) (E : ι → α → Prop) :
    ν.P (fun a => ∃ i ∈ s, E i a) ≤ ∑ i ∈ s, ν.P (E i) := by
  unfold FinDist.P
  rw [sum_comm]
  refine sum_le_sum fun a _ => ?_
  split_ifs with h
  · obtain ⟨i, hi, hE⟩ := h
    calc ν.prob a = (if E i a then ν.prob a else 0) := by rw [ite_eq_left hE]
      _ ≤ ∑ j ∈ s, (if E j a then ν.prob a else 0) :=
        single_le_sum (f := fun j => if E j a then ν.prob a else 0)
          (fun j _ => mt_ite_nonneg ν _ a) hi
  · exact sum_nonneg fun j _ => mt_ite_nonneg ν _ a

lemma mt_exists_not (ν : FinDist α) (B : α → Prop) (h : ν.P B < 1) :
    ∃ a ∈ ν.support, ¬ B a := by
  unfold FinDist.P at h
  rw [← ν.sum_prob] at h
  obtain ⟨a, ha, hlt⟩ := exists_lt_of_sum_lt h
  refine ⟨a, ha, fun hB => ?_⟩
  rw [ite_eq_left hB] at hlt
  exact lt_irrefl _ hlt

end ProbHelpers

/-! ### Numerical facts -/

section Numerics

lemma num_lower4 {m a : ℝ} (hm : 0 < m) (h4 : 4 * a ≤ m) :
    9 * m / 64 ≤ (m - a) ^ 2 / (4 * m) := by
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

lemma num_upper2 {m a : ℝ} (hm : 0 < m) (ha : a = 2 * m) :
    3 * m / 16 ≤ (a - m) ^ 2 / (4 * (m + (a - m) / 3)) := by
  rw [ha, div_le_div_iff₀ (by norm_num) (by nlinarith)]
  nlinarith

lemma num_lower0 {m : ℝ} (hm : 0 < m) : m / 4 ≤ (m - 0) ^ 2 / (4 * m) := by
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

lemma num_lower255 {m : ℝ} (hm : 510 ≤ m) : m / 16 ≤ (m - 255) ^ 2 / (4 * m) := by
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

lemma num_test {m τ : ℝ} (hm0 : 0 ≤ m) (hm : 2 * m ≤ τ) (hτ : 0 < τ) :
    3 / 40 * τ ≤ (τ - m) ^ 2 / (4 * (m + (τ - m) / 3)) := by
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hm) (by linarith : (0 : ℝ) ≤ 9 * τ - 4 * m), sq_nonneg m]

lemma num_final : 6 * (Real.exp (-4) / (1 - Real.exp (-4))) + Real.exp (-2) < 1 := by
  have hA : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; simp
  have hB : 5 ≤ Real.exp 2 := by
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at this ⊢
    linarith
  have hpos := Real.exp_pos (-2)
  have h2 : Real.exp (-2) ≤ 1 / 5 := by nlinarith
  have h4 : Real.exp (-4) = Real.exp (-2) ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h4]
  have h5 : Real.exp (-2) ^ 2 / (1 - Real.exp (-2) ^ 2) ≤ 1 / 24 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  linarith

/-- **Summing over state cuts** (cut counting): if at most `N^{16(j+1)}` sets have `s < (j+1)µ`
and `32 log N + 4 ≤ cµ`, then `∑_{s(J) ≥ µ} e^{-c s(J)} ≤ e^{-4}/(1 - e^{-4})`. -/
lemma cut_sum_le {β : Type*} [Fintype β] (s : β → ℕ) (μ c : ℝ) (N : ℕ) (hμ : 1 ≤ μ)
    (hcμ : 32 * Real.log N + 4 ≤ c * μ)
    (hcount : ∀ j : ℕ, (((univ : Finset β).filter fun J => (s J : ℝ) < (j + 1) * μ).card : ℝ) ≤
      (N : ℝ) ^ (16 * (j + 1))) :
    ∑ J ∈ (univ : Finset β).filter (fun J => μ ≤ s J), Real.exp (-(c * s J)) ≤
      Real.exp (-4) / (1 - Real.exp (-4)) := by
  set M := ∑ J, s J with hM
  have hμpos : 0 < μ := by linarith
  have hite : ∀ (J : β) (j : ℕ),
      0 ≤ (if (s J : ℝ) < (j + 1) * μ then Real.exp (-(c * (j * μ))) else 0) := by
    intro J j
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hpt : ∀ J ∈ (univ : Finset β).filter (fun J => μ ≤ s J), Real.exp (-(c * s J)) ≤
      ∑ j ∈ Ico 1 (M + 1),
        (if (s J : ℝ) < (j + 1) * μ then Real.exp (-(c * (j * μ))) else 0) := by
    intro J hJ
    have hJ' : μ ≤ s J := (mem_filter.1 hJ).2
    set j₀ := ⌊(s J : ℝ) / μ⌋₊ with hj₀
    have h1 : 1 ≤ j₀ := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hμpos]; linarith)
    have h2 : (j₀ : ℝ) ≤ s J / μ := Nat.floor_le (by positivity)
    have h3 : (s J : ℝ) / μ < j₀ + 1 := Nat.lt_floor_add_one _
    have h2' : (j₀ : ℝ) * μ ≤ s J := (le_div_iff₀ hμpos).1 h2
    have h3' : (s J : ℝ) < (j₀ + 1) * μ := (div_lt_iff₀ hμpos).1 h3
    have hj₀M : j₀ ≤ M := by
      have : (j₀ : ℝ) ≤ s J := by
        have : (s J : ℝ) / μ ≤ s J := div_le_self (Nat.cast_nonneg _) hμ
        linarith
      have h' : j₀ ≤ s J := by exact_mod_cast this
      exact h'.trans (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ J))
    have hmem : j₀ ∈ Ico 1 (M + 1) := mem_Ico.2 ⟨h1, Nat.lt_succ_of_le hj₀M⟩
    have hc0 : 0 ≤ c := by
      have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
      have : 0 ≤ c * μ := by linarith
      exact nonneg_of_mul_nonneg_left this hμpos
    calc Real.exp (-(c * s J)) ≤ Real.exp (-(c * (j₀ * μ))) :=
          Real.exp_le_exp.2 (by nlinarith)
      _ = (if (s J : ℝ) < (j₀ + 1) * μ then Real.exp (-(c * (j₀ * μ))) else 0) := by
          rw [ite_eq_left h3']
      _ ≤ _ := single_le_sum (f := fun j : ℕ =>
          if (s J : ℝ) < (j + 1) * μ then Real.exp (-(c * (j * μ))) else 0)
          (fun j _ => hite J j) hmem
  have hterm : ∀ j ∈ Ico 1 (M + 1),
      Real.exp (-(c * (j * μ))) * (N : ℝ) ^ (16 * (j + 1)) ≤ Real.exp (-4) ^ j := by
    intro j hj
    have hj1 : 1 ≤ j := (mem_Ico.1 hj).1
    rcases Nat.eq_zero_or_pos N with hN | hN
    · rw [hN, Nat.cast_zero, zero_pow (by omega), mul_zero]
      positivity
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hpow : (N : ℝ) ^ (16 * (j + 1)) ≤ (N : ℝ) ^ (32 * j) :=
        pow_le_pow_right₀ hN1 (by omega)
      have hexp : (N : ℝ) ^ (32 * j) = Real.exp ((32 * j : ℕ) * Real.log N) := by
        rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
      have hexp4 : Real.exp (-4) ^ j = Real.exp (j * (-4)) := (Real.exp_nat_mul _ _).symm
      have hj' : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hmul := mul_le_mul_of_nonneg_left hcμ hj'
      calc Real.exp (-(c * (j * μ))) * (N : ℝ) ^ (16 * (j + 1))
          ≤ Real.exp (-(c * (j * μ))) * Real.exp ((32 * j : ℕ) * Real.log N) := by
            rw [← hexp]; exact mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
        _ = Real.exp (-(c * (j * μ)) + (32 * j : ℕ) * Real.log N) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (j * (-4)) := by
            apply Real.exp_le_exp.2
            push_cast
            linarith
        _ = _ := hexp4.symm
  calc ∑ J ∈ (univ : Finset β).filter (fun J => μ ≤ s J), Real.exp (-(c * s J))
      ≤ ∑ J ∈ (univ : Finset β).filter (fun J => μ ≤ s J), ∑ j ∈ Ico 1 (M + 1),
          (if (s J : ℝ) < (j + 1) * μ then Real.exp (-(c * (j * μ))) else 0) := sum_le_sum hpt
    _ ≤ ∑ J, ∑ j ∈ Ico 1 (M + 1),
          (if (s J : ℝ) < (j + 1) * μ then Real.exp (-(c * (j * μ))) else 0) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun J _ _ => sum_nonneg fun j _ => hite J j)
    _ = ∑ j ∈ Ico 1 (M + 1), ∑ J,
          (if (s J : ℝ) < (j + 1) * μ then Real.exp (-(c * (j * μ))) else 0) := sum_comm
    _ = ∑ j ∈ Ico 1 (M + 1), Real.exp (-(c * (j * μ))) *
          (((univ : Finset β).filter fun J => (s J : ℝ) < (j + 1) * μ).card : ℝ) := by
        refine sum_congr rfl fun j _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ j ∈ Ico 1 (M + 1), Real.exp (-(c * (j * μ))) * (N : ℝ) ^ (16 * (j + 1)) :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcount j) (Real.exp_pos _).le
    _ ≤ ∑ j ∈ Ico 1 (M + 1), Real.exp (-4) ^ j := sum_le_sum hterm
    _ ≤ Real.exp (-4) ^ 1 / (1 - Real.exp (-4)) :=
        geom_sum_Ico_le_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.2 (by norm_num))
    _ = _ := by rw [pow_one]

end Numerics

/-! ### Step E6.13: the random matching -/

section Matching

variable {G : Type u} [Fintype G] [DecidableEq G]

/-- The conclusion of Lemma 6.4 (`mutual_nominations`) for the law `ν` of `(R, Z)`. -/
def IsNom (Y : SimpleGraph G) (p : ℝ) (ν : FinDist (Finset (Sym2 G) × Finset (Sym2 G))) :
    Prop :=
  (∀ RZ ∈ ν.support, RZ.2 ⊆ RZ.1 ∧ RZ.1 ⊆ Y.edgeFinset ∧
      ∀ e ∈ RZ.1, ∀ f ∈ RZ.1, e ≠ f → ∀ v, v ∈ e → v ∉ f) ∧
    (∀ e ∈ Y.edgeFinset, ν.P (fun RZ => e ∈ RZ.1) = p ∧ ν.P (fun RZ => e ∈ RZ.2) = p / 128) ∧
    ∀ (c : Sym2 G → ℝ), (∀ e, 0 ≤ c e ∧ c e ≤ 2) → ∀ t : ℝ, 0 ≤ t →
      ∀ sel : Finset (Sym2 G) × Finset (Sym2 G) → Finset (Sym2 G),
        (sel = Prod.fst ∨ sel = Prod.snd ∨ sel = fun RZ => RZ.1 \ RZ.2) →
        (ν.P (fun RZ => ν.expect (fun RZ' => ∑ e ∈ sel RZ', c e) + t ≤ ∑ e ∈ sel RZ, c e) ≤
            Real.exp (-(t ^ 2) / (4 * (ν.expect (fun RZ' => ∑ e ∈ sel RZ', c e) + t / 3)))) ∧
        (ν.P (fun RZ => ∑ e ∈ sel RZ, c e ≤ ν.expect (fun RZ' => ∑ e ∈ sel RZ', c e) - t) ≤
            Real.exp (-(t ^ 2) / (4 * ν.expect (fun RZ' => ∑ e ∈ sel RZ', c e))))

omit [Fintype G] in
lemma expect_sel (ν : FinDist (Finset (Sym2 G) × Finset (Sym2 G))) (E : Finset (Sym2 G))
    (sel : Finset (Sym2 G) × Finset (Sym2 G) → Finset (Sym2 G))
    (hsub : ∀ RZ ∈ ν.support, sel RZ ⊆ E) (c : Sym2 G → ℝ) :
    ν.expect (fun RZ => ∑ e ∈ sel RZ, c e) =
      ∑ e ∈ E, c e * ν.P (fun RZ => e ∈ sel RZ) := by
  have h1 : ∀ RZ ∈ ν.support, ∑ e ∈ sel RZ, c e =
      ∑ e ∈ E, c e * MutualNom.ind (e ∈ sel RZ) := by
    intro RZ hRZ
    simp only [MutualNom.ind, mul_ite, mul_one, mul_zero]
    rw [sum_ite_mem, inter_eq_right.2 (hsub RZ hRZ)]
  rw [MutualNom.expect_congr ν h1, MutualNom.expect_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [MutualNom.expect_const_mul, MutualNom.P_eq_expect]

variable {Y : SimpleGraph G} {p : ℝ} {ν : FinDist (Finset (Sym2 G) × Finset (Sym2 G))}

lemma IsNom.mean_fst (h : IsNom Y p ν) (c : Sym2 G → ℝ) :
    ν.expect (fun RZ => ∑ e ∈ RZ.1, c e) = p * ∑ e ∈ Y.edgeFinset, c e := by
  rw [expect_sel ν Y.edgeFinset Prod.fst (fun RZ hRZ => (h.1 RZ hRZ).2.1) c, mul_sum]
  refine sum_congr rfl fun e he => ?_
  rw [(h.2.1 e he).1, mul_comm]

lemma IsNom.mean_snd (h : IsNom Y p ν) (c : Sym2 G → ℝ) :
    ν.expect (fun RZ => ∑ e ∈ RZ.2, c e) = p / 128 * ∑ e ∈ Y.edgeFinset, c e := by
  rw [expect_sel ν Y.edgeFinset Prod.snd
    (fun RZ hRZ => (h.1 RZ hRZ).1.trans (h.1 RZ hRZ).2.1) c, mul_sum]
  refine sum_congr rfl fun e he => ?_
  rw [(h.2.1 e he).2, mul_comm]

lemma IsNom.mean_sdiff (h : IsNom Y p ν) (c : Sym2 G → ℝ) :
    ν.expect (fun RZ => ∑ e ∈ RZ.1 \ RZ.2, c e) = 127 * p / 128 * ∑ e ∈ Y.edgeFinset, c e := by
  rw [expect_sel ν Y.edgeFinset (fun RZ => RZ.1 \ RZ.2)
    (fun RZ hRZ => sdiff_subset.trans (h.1 RZ hRZ).2.1) c, mul_sum]
  refine sum_congr rfl fun e he => ?_
  have hsplit : ν.P (fun RZ => e ∈ RZ.1) =
      ν.P (fun RZ => e ∈ RZ.1 \ RZ.2) + ν.P (fun RZ => e ∈ RZ.2) := by
    unfold FinDist.P
    rw [← sum_add_distrib]
    refine sum_congr rfl fun RZ hRZ => ?_
    have hZR := (h.1 RZ hRZ).1
    by_cases h2 : e ∈ RZ.2
    · have h1 : e ∈ RZ.1 := hZR h2
      simp [h1, h2]
    · by_cases h1 : e ∈ RZ.1 <;> simp [h1, h2]
  have h1 := (h.2.1 e he).1
  have h2 := (h.2.1 e he).2
  have : ν.P (fun RZ => e ∈ RZ.1 \ RZ.2) = 127 * p / 128 := by linarith
  rw [this, mul_comm]

lemma IsNom.lower_use (h : IsNom Y p ν)
    (sel : Finset (Sym2 G) × Finset (Sym2 G) → Finset (Sym2 G))
    (hsel : sel = Prod.fst ∨ sel = Prod.snd ∨ sel = fun RZ => RZ.1 \ RZ.2)
    (c : Sym2 G → ℝ) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 2)
    (E : Finset (Sym2 G) × Finset (Sym2 G) → Prop) (a x : ℝ)
    (hE : ∀ RZ ∈ ν.support, E RZ → ∑ e ∈ sel RZ, c e ≤ a)
    (ha : a ≤ ν.expect (fun RZ => ∑ e ∈ sel RZ, c e))
    (hx : x ≤ (ν.expect (fun RZ => ∑ e ∈ sel RZ, c e) - a) ^ 2 /
      (4 * ν.expect (fun RZ => ∑ e ∈ sel RZ, c e))) :
    ν.P E ≤ Real.exp (-x) := by
  set m := ν.expect (fun RZ => ∑ e ∈ sel RZ, c e) with hm
  have htail := (h.2.2 c hc (m - a) (by linarith) sel hsel).2
  refine (mt_P_mono ν fun RZ hRZ hE' => ?_).trans (htail.trans ?_)
  · show ∑ e ∈ sel RZ, c e ≤ m - (m - a)
    linarith [hE RZ hRZ hE']
  · rw [Real.exp_le_exp, neg_div]
    linarith

lemma IsNom.upper_use (h : IsNom Y p ν)
    (sel : Finset (Sym2 G) × Finset (Sym2 G) → Finset (Sym2 G))
    (hsel : sel = Prod.fst ∨ sel = Prod.snd ∨ sel = fun RZ => RZ.1 \ RZ.2)
    (c : Sym2 G → ℝ) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 2)
    (E : Finset (Sym2 G) × Finset (Sym2 G) → Prop) (a x : ℝ)
    (hE : ∀ RZ ∈ ν.support, E RZ → a ≤ ∑ e ∈ sel RZ, c e)
    (ha : ν.expect (fun RZ => ∑ e ∈ sel RZ, c e) ≤ a)
    (hx : x ≤ (a - ν.expect (fun RZ => ∑ e ∈ sel RZ, c e)) ^ 2 /
      (4 * (ν.expect (fun RZ => ∑ e ∈ sel RZ, c e) +
        (a - ν.expect (fun RZ => ∑ e ∈ sel RZ, c e)) / 3))) :
    ν.P E ≤ Real.exp (-x) := by
  set m := ν.expect (fun RZ => ∑ e ∈ sel RZ, c e) with hm
  have htail := (h.2.2 c hc (a - m) (by linarith) sel hsel).1
  refine (mt_P_mono ν fun RZ hRZ hE' => ?_).trans (htail.trans ?_)
  · show m + (a - m) ≤ ∑ e ∈ sel RZ, c e
    linarith [hE RZ hRZ hE']
  · rw [Real.exp_le_exp, neg_div]
    linarith

end Matching

section Arcs

variable {G : Type u} {t : ℕ}

lemma outArcs_le_two (π : G → Fin t) (sg : G → Bool) (J : Finset (Fin t × Bool)) (e : Sym2 G) :
    outArcs π sg J e ≤ 2 :=
  (card_filter_le _ _).trans (by simp)

lemma inArcs_le_two (π : G → Fin t) (sg : G → Bool) (J : Finset (Fin t × Bool)) (e : Sym2 G) :
    inArcs π sg J e ≤ 2 :=
  (card_filter_le _ _).trans (by simp)

lemma arcs_le_two (π : G → Fin t) (sg : G → Bool) (J : Finset (Fin t × Bool)) (e : Sym2 G) :
    outArcs π sg J e + inArcs π sg J e ≤ 2 := by
  simp only [outArcs, inArcs, card_filter, Fintype.sum_bool]
  split_ifs <;> first | omega | (exfalso; tauto)

lemma outCnt_cast (π : G → Fin t) (sg : G → Bool) (J : Finset (Fin t × Bool))
    (F : Finset (Sym2 G)) : (outCnt π sg J F : ℝ) = ∑ e ∈ F, (outArcs π sg J e : ℝ) := by
  unfold outCnt
  push_cast
  rfl

lemma inCnt_cast (π : G → Fin t) (sg : G → Bool) (J : Finset (Fin t × Bool))
    (F : Finset (Sym2 G)) : (inCnt π sg J F : ℝ) = ∑ e ∈ F, (inArcs π sg J e : ℝ) := by
  unfold inCnt
  push_cast
  rfl

lemma cutCnt_cast (π : G → Fin t) (sg : G → Bool) (J : Finset (Fin t × Bool))
    (F : Finset (Sym2 G)) :
    (cutCnt π sg J F : ℝ) = ∑ e ∈ F, ((outArcs π sg J e + inArcs π sg J e : ℕ) : ℝ) := by
  unfold cutCnt outCnt inCnt
  push_cast
  rw [sum_add_distrib]

lemma cutCnt_mono (π : G → Fin t) (sg : G → Bool) (J : Finset (Fin t × Bool))
    {F F' : Finset (Sym2 G)} (h : F ⊆ F') : cutCnt π sg J F ≤ cutCnt π sg J F' := by
  unfold cutCnt outCnt inCnt
  exact add_le_add (sum_le_sum_of_subset h) (sum_le_sum_of_subset h)

lemma sum_partCross (π : G → Fin t) (I : Finset (Fin t)) (F : Finset (Sym2 G)) :
    ∑ e ∈ F, (if PartCross π I e then (1 : ℝ) else 0) = ((F.filter (PartCross π I)).card : ℝ) := by
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]

end Arcs

section Matching

variable {G : Type u} [Fintype G] [DecidableEq G]
variable {Y : SimpleGraph G} {p : ℝ} {ν : FinDist (Finset (Sym2 G) × Finset (Sym2 G))}

lemma bad_out (h : IsNom Y p ν) (hp : 0 < p) {t : ℕ} (π : G → Fin t) (sg : G → Bool)
    (J : Finset (Fin t × Bool)) (hs : 0 < (cutCnt π sg J Y.edgeFinset : ℝ))
    (hbal : (cutCnt π sg J Y.edgeFinset : ℝ) ≤ 3 * outCnt π sg J Y.edgeFinset) :
    ν.P (fun RZ => (outCnt π sg J RZ.1 : ℝ) < p * cutCnt π sg J Y.edgeFinset / 12) ≤
      Real.exp (-(p / 2048 * cutCnt π sg J Y.edgeFinset)) := by
  set s := (cutCnt π sg J Y.edgeFinset : ℝ) with hs_def
  have hc : ∀ e, 0 ≤ (outArcs π sg J e : ℝ) ∧ (outArcs π sg J e : ℝ) ≤ 2 := fun e =>
    ⟨Nat.cast_nonneg _, by exact_mod_cast outArcs_le_two π sg J e⟩
  have hm : ν.expect (fun RZ => ∑ e ∈ RZ.1, (outArcs π sg J e : ℝ)) =
      p * outCnt π sg J Y.edgeFinset := by
    rw [h.mean_fst, outCnt_cast]
  have hm' : p * s / 3 ≤ p * outCnt π sg J Y.edgeFinset := by nlinarith
  refine h.lower_use Prod.fst (Or.inl rfl) _ hc _ (p * s / 12) _ ?_ ?_ ?_
  · intro RZ _ hlt
    rw [outCnt_cast] at hlt
    exact hlt.le
  · rw [hm]; nlinarith
  · rw [hm]
    refine le_trans ?_ (num_lower4 (by nlinarith) (by nlinarith))
    nlinarith

lemma bad_in (h : IsNom Y p ν) (hp : 0 < p) {t : ℕ} (π : G → Fin t) (sg : G → Bool)
    (J : Finset (Fin t × Bool)) (hs : 0 < (cutCnt π sg J Y.edgeFinset : ℝ))
    (hbal : (cutCnt π sg J Y.edgeFinset : ℝ) ≤ 3 * inCnt π sg J Y.edgeFinset) :
    ν.P (fun RZ => (inCnt π sg J RZ.1 : ℝ) < p * cutCnt π sg J Y.edgeFinset / 12) ≤
      Real.exp (-(p / 2048 * cutCnt π sg J Y.edgeFinset)) := by
  set s := (cutCnt π sg J Y.edgeFinset : ℝ) with hs_def
  have hc : ∀ e, 0 ≤ (inArcs π sg J e : ℝ) ∧ (inArcs π sg J e : ℝ) ≤ 2 := fun e =>
    ⟨Nat.cast_nonneg _, by exact_mod_cast inArcs_le_two π sg J e⟩
  have hm : ν.expect (fun RZ => ∑ e ∈ RZ.1, (inArcs π sg J e : ℝ)) =
      p * inCnt π sg J Y.edgeFinset := by
    rw [h.mean_fst, inCnt_cast]
  have hm' : p * s / 3 ≤ p * inCnt π sg J Y.edgeFinset := by nlinarith
  refine h.lower_use Prod.fst (Or.inl rfl) _ hc _ (p * s / 12) _ ?_ ?_ ?_
  · intro RZ _ hlt
    rw [inCnt_cast] at hlt
    exact hlt.le
  · rw [hm]; nlinarith
  · rw [hm]
    refine le_trans ?_ (num_lower4 (by nlinarith) (by nlinarith))
    nlinarith

lemma bad_cutR (h : IsNom Y p ν) (hp : 0 < p) {t : ℕ} (π : G → Fin t) (sg : G → Bool)
    (J : Finset (Fin t × Bool)) (hs : 0 < (cutCnt π sg J Y.edgeFinset : ℝ)) :
    ν.P (fun RZ => 2 * p * cutCnt π sg J Y.edgeFinset < (cutCnt π sg J RZ.1 : ℝ)) ≤
      Real.exp (-(p / 2048 * cutCnt π sg J Y.edgeFinset)) := by
  set s := (cutCnt π sg J Y.edgeFinset : ℝ) with hs_def
  have hc : ∀ e, 0 ≤ ((outArcs π sg J e + inArcs π sg J e : ℕ) : ℝ) ∧
      ((outArcs π sg J e + inArcs π sg J e : ℕ) : ℝ) ≤ 2 := fun e =>
    ⟨Nat.cast_nonneg _, by exact_mod_cast arcs_le_two π sg J e⟩
  have hm : ν.expect (fun RZ => ∑ e ∈ RZ.1,
      ((outArcs π sg J e + inArcs π sg J e : ℕ) : ℝ)) = p * s := by
    rw [h.mean_fst, hs_def, cutCnt_cast]
  refine h.upper_use Prod.fst (Or.inl rfl) _ hc _ (2 * p * s) _ ?_ ?_ ?_
  · intro RZ _ hlt
    rw [cutCnt_cast] at hlt
    exact hlt.le
  · rw [hm]; nlinarith
  · rw [hm]
    refine le_trans ?_ (num_upper2 (by positivity) (by ring))
    nlinarith

lemma bad_cutZ (h : IsNom Y p ν) (hp : 0 < p) {t : ℕ} (π : G → Fin t) (sg : G → Bool)
    (J : Finset (Fin t × Bool)) (hs : 0 < (cutCnt π sg J Y.edgeFinset : ℝ)) :
    ν.P (fun RZ => p * cutCnt π sg J Y.edgeFinset / 64 < (cutCnt π sg J RZ.2 : ℝ)) ≤
      Real.exp (-(p / 2048 * cutCnt π sg J Y.edgeFinset)) := by
  set s := (cutCnt π sg J Y.edgeFinset : ℝ) with hs_def
  have hc : ∀ e, 0 ≤ ((outArcs π sg J e + inArcs π sg J e : ℕ) : ℝ) ∧
      ((outArcs π sg J e + inArcs π sg J e : ℕ) : ℝ) ≤ 2 := fun e =>
    ⟨Nat.cast_nonneg _, by exact_mod_cast arcs_le_two π sg J e⟩
  have hm : ν.expect (fun RZ => ∑ e ∈ RZ.2,
      ((outArcs π sg J e + inArcs π sg J e : ℕ) : ℝ)) = p / 128 * s := by
    rw [h.mean_snd, hs_def, cutCnt_cast]
  refine h.upper_use Prod.snd (Or.inr (Or.inl rfl)) _ hc _ (p * s / 64) _ ?_ ?_ ?_
  · intro RZ _ hlt
    rw [cutCnt_cast] at hlt
    exact hlt.le
  · rw [hm]; nlinarith
  · rw [hm]
    refine le_trans ?_ (num_upper2 (by positivity) (by ring))
    nlinarith

lemma bad_marked (h : IsNom Y p ν) (hp : 0 < p) {t : ℕ} (π : G → Fin t) (sg : G → Bool)
    (I : Finset (Fin t)) (hs : 0 < (cutCnt π sg (I ×ˢ univ) Y.edgeFinset : ℝ)) :
    ν.P (fun RZ => ¬ ∃ e ∈ RZ.2, PartCross π I e) ≤
      Real.exp (-(p / 2048 * cutCnt π sg (I ×ˢ univ) Y.edgeFinset)) := by
  have hs2 : (cutCnt π sg (I ×ˢ univ) Y.edgeFinset : ℝ) =
      2 * ((Y.edgeFinset.filter (PartCross π I)).card : ℝ) := by
    rw [cutCnt_prod_univ]; push_cast; ring
  rw [hs2] at hs ⊢
  set n := ((Y.edgeFinset.filter (PartCross π I)).card : ℝ) with hn
  have hc : ∀ e, 0 ≤ (if PartCross π I e then (1 : ℝ) else 0) ∧
      (if PartCross π I e then (1 : ℝ) else 0) ≤ 2 := fun e => by
    split_ifs <;> norm_num
  have hm : ν.expect (fun RZ => ∑ e ∈ RZ.2, (if PartCross π I e then (1 : ℝ) else 0)) =
      p / 128 * n := by
    rw [h.mean_snd, sum_partCross]
  refine h.lower_use Prod.snd (Or.inr (Or.inl rfl)) _ hc _ 0 _ ?_ ?_ ?_
  · intro RZ _ hno
    rw [sum_partCross]
    have : RZ.2.filter (PartCross π I) = ∅ := by
      rw [filter_eq_empty_iff]
      intro e he hce
      exact hno ⟨e, he, hce⟩
    rw [this, card_empty, Nat.cast_zero]
  · rw [hm]; positivity
  · rw [hm]
    refine le_trans ?_ (num_lower0 (mul_pos (by positivity) (by linarith)))
    nlinarith

lemma bad_unmarked (h : IsNom Y p ν) {t : ℕ} (π : G → Fin t) (sg : G → Bool)
    (I : Finset (Fin t)) (hs : 1100 ≤ p * cutCnt π sg (I ×ˢ univ) Y.edgeFinset) :
    ν.P (fun RZ => ((RZ.1 \ RZ.2).filter (PartCross π I)).card < 256) ≤
      Real.exp (-(p / 2048 * cutCnt π sg (I ×ˢ univ) Y.edgeFinset)) := by
  have hs2 : (cutCnt π sg (I ×ˢ univ) Y.edgeFinset : ℝ) =
      2 * ((Y.edgeFinset.filter (PartCross π I)).card : ℝ) := by
    rw [cutCnt_prod_univ]; push_cast; ring
  rw [hs2] at hs ⊢
  set n := ((Y.edgeFinset.filter (PartCross π I)).card : ℝ) with hn
  have hc : ∀ e, 0 ≤ (if PartCross π I e then (1 : ℝ) else 0) ∧
      (if PartCross π I e then (1 : ℝ) else 0) ≤ 2 := fun e => by
    split_ifs <;> norm_num
  have hm : ν.expect (fun RZ => ∑ e ∈ RZ.1 \ RZ.2, (if PartCross π I e then (1 : ℝ) else 0)) =
      127 * p / 128 * n := by
    rw [h.mean_sdiff, sum_partCross]
  refine h.lower_use (fun RZ => RZ.1 \ RZ.2) (Or.inr (Or.inr rfl)) _ hc _ 255 _ ?_ ?_ ?_
  · intro RZ _ hlt
    show ∑ e ∈ RZ.1 \ RZ.2, (if PartCross π I e then (1 : ℝ) else 0) ≤ 255
    rw [sum_partCross]
    have : ((RZ.1 \ RZ.2).filter (PartCross π I)).card ≤ 255 := by omega
    exact_mod_cast this
  · rw [hm]; nlinarith
  · rw [hm]
    refine le_trans ?_ (num_lower255 (by nlinarith))
    nlinarith

omit [Fintype G] in
lemma card_filter_mem_sym2_le (A : Finset G) (e : Sym2 G) : (A.filter (· ∈ e)).card ≤ 2 := by
  refine (card_le_card (s := A.filter (· ∈ e)) (t := {e.out.1, e.out.2}) ?_).trans card_le_two
  intro v hv
  have hv' : v ∈ e := (mem_filter.1 hv).2
  rw [← mk_out e, Sym2.mem_iff] at hv'
  rcases hv' with rfl | rfl <;> simp

lemma bad_test (h : IsNom Y p ν) (hp : 0 < p) (k : ℕ) (hk : ∀ v, Y.degree v ≤ k)
    (A : Finset G) (τ : ℝ) (hτ : 0 < τ) (hA : p * k * A.card ≤ τ / 2) :
    ν.P (fun RZ => τ < ((A.filter (· ∈ vtx RZ.1)).card : ℝ)) ≤ Real.exp (-(3 / 40 * τ)) := by
  have hc : ∀ e : Sym2 G,
      0 ≤ ((A.filter (· ∈ e)).card : ℝ) ∧ ((A.filter (· ∈ e)).card : ℝ) ≤ 2 := fun e =>
    ⟨Nat.cast_nonneg _, by exact_mod_cast card_filter_mem_sym2_le A e⟩
  have hdeg : ∑ e ∈ Y.edgeFinset, (A.filter (· ∈ e)).card ≤ A.card * k := by
    have h1 : ∑ e ∈ Y.edgeFinset, (A.filter (· ∈ e)).card =
        ∑ v ∈ A, (Y.edgeFinset.filter (v ∈ ·)).card := by
      simp only [card_filter]
      exact sum_comm
    rw [h1]
    calc ∑ v ∈ A, (Y.edgeFinset.filter (v ∈ ·)).card ≤ ∑ _v ∈ A, k := by
          refine sum_le_sum fun v _ => ?_
          rw [← SimpleGraph.incidenceFinset_eq_filter, SimpleGraph.card_incidenceFinset_eq_degree]
          exact hk v
      _ = A.card * k := by rw [sum_const, smul_eq_mul]
  have hdeg' : (∑ e ∈ Y.edgeFinset, ((A.filter (· ∈ e)).card : ℝ)) ≤ A.card * k := by
    exact_mod_cast hdeg
  have hm0 : 0 ≤ ν.expect (fun RZ => ∑ e ∈ RZ.1, ((A.filter (· ∈ e)).card : ℝ)) := by
    rw [h.mean_fst]
    exact mul_nonneg hp.le (sum_nonneg fun e _ => Nat.cast_nonneg _)
  have hm : ν.expect (fun RZ => ∑ e ∈ RZ.1, ((A.filter (· ∈ e)).card : ℝ)) ≤ τ / 2 := by
    rw [h.mean_fst]
    calc p * ∑ e ∈ Y.edgeFinset, ((A.filter (· ∈ e)).card : ℝ) ≤ p * (A.card * k) :=
          mul_le_mul_of_nonneg_left hdeg' hp.le
      _ = p * k * A.card := by ring
      _ ≤ τ / 2 := hA
  refine h.upper_use Prod.fst (Or.inl rfl) _ hc _ τ _ ?_ ?_ ?_
  · intro RZ _ hlt
    refine hlt.le.trans ?_
    have hsub : A.filter (· ∈ vtx RZ.1) ⊆ RZ.1.biUnion fun e => A.filter (· ∈ e) := by
      intro v hv
      rw [mem_filter, mem_vtx] at hv
      obtain ⟨e, he, hve⟩ := hv.2
      exact mem_biUnion.2 ⟨e, he, mem_filter.2 ⟨hv.1, hve⟩⟩
    have := (card_le_card hsub).trans card_biUnion_le
    show ((A.filter (· ∈ vtx RZ.1)).card : ℝ) ≤ ∑ e ∈ RZ.1, ((A.filter (· ∈ e)).card : ℝ)
    exact_mod_cast this
  · linarith
  · exact num_test hm0 (by linarith) hτ

/-- **The matching `R` and the marks `Z₀` (§6.4, (6.13)–(6.17)).** Apply Lemma 6.4 to `Y` with
edge probability `p` and marking probability `1/128`. Given directional balance, the gap
`s(J) ∈ {0} ∪ [µ, ∞)`, the part-cut bound and cut counting for the state cuts, and endpoint tests
`(A, τ)` with mean `≤ pk|A| ≤ τ/2`, a union bound gives an outcome with
`|δ^±_{D(R)}(J)| ≥ ps/12`, `|δ_{D(R)}(J)| ≤ 2ps`, `|δ_{D(Z₀)}(J)| ≤ ps/64` for every state set
`J` (`s = s(J)`), a marked edge across every nontrivial part cut, at least `256` unmarked
matching edges across every nontrivial part cut (6.15), and `|A ∩ V(R)| ≤ τ` for every test
(6.17).

Proof sketch (constants checked): for a state set `J` with `s = s(J) ≥ µ`, the tails of Lemma 6.4
give failure probabilities at most `e^{-3ps/64}` (each direction, mean `≥ ps/3`), `e^{-3ps/16}`
(`|δ_{D(R)}| > 2ps`, mean `ps`), `e^{-3ps/2048}` (`|δ_{D(Z₀)}| > ps/64`, mean `ps/128`); for a part
cut `I` with `s = s(I × Bool) ≥ µ`, at most `e^{-ps/1024}` (no marked crossing edge, mean `ps/256`)
and `e^{-127ps/4096}` (fewer than `256` unmarked crossing edges, mean `127ps/256 ≥ 512`). All are
`≤ e^{-ps/2048}`, so the cut events cost `≤ ∑_{j ≥ 1} 6 N^{16(j+1)} e^{-jpµ/2048} ≤ 6∑_j e^{-4j}`
by `hcount` and `hpµ₂`; state sets with `s(J) = 0` impose nothing. A test `(A, τ)` fails with
probability `≤ e^{-3τ/40}` (mean `≤ τ/2`), and these sum to `≤ e^{-2}`. The total is `< 1`. -/
theorem exists_matching {t : ℕ} (Y : SimpleGraph G) (π : G → Fin t) (sg : G → Bool) (k : ℕ)
    (hk : ∀ v, Y.degree v ≤ k) (p μ : ℝ) (hp : 0 < p) (hpk : p * k ^ 2 ≤ 1) (hμ : 6 ≤ μ)
    (hpμ₁ : 1100 ≤ p * μ)
    (hpμ₂ : 32 * Real.log (4 * (t + Y.edgeFinset.card)) + 4 ≤ p * μ / 2048)
    (hbal : ∀ J : Finset (Fin t × Bool),
      (cutCnt π sg J Y.edgeFinset : ℝ) ≤ 3 * outCnt π sg J Y.edgeFinset ∧
        (cutCnt π sg J Y.edgeFinset : ℝ) ≤ 3 * inCnt π sg J Y.edgeFinset)
    (hgap : ∀ J : Finset (Fin t × Bool),
      cutCnt π sg J Y.edgeFinset = 0 ∨ μ ≤ cutCnt π sg J Y.edgeFinset)
    (hpart : ∀ I : Finset (Fin t), I.Nonempty → I ≠ univ →
      μ ≤ cutCnt π sg (I ×ˢ univ) Y.edgeFinset)
    (hcount : ∀ j : ℕ, (((univ : Finset (Finset (Fin t × Bool))).filter fun J =>
      (cutCnt π sg J Y.edgeFinset : ℝ) < (j + 1) * μ).card : ℝ) ≤
        (4 * (t + Y.edgeFinset.card)) ^ (16 * (j + 1)))
    (tests : Finset (Finset G × ℝ))
    (htests : ∀ q ∈ tests, p * k * q.1.card ≤ q.2 / 2 ∧
      Real.log tests.card + 2 ≤ 3 / 40 * q.2) :
    ∃ R Z₀ : Finset (Sym2 G), Z₀ ⊆ R ∧ R ⊆ Y.edgeFinset ∧
      (∀ e ∈ R, ∀ f ∈ R, e ≠ f → ∀ v ∈ e, v ∉ f) ∧
      (∀ J : Finset (Fin t × Bool),
        p * cutCnt π sg J Y.edgeFinset / 12 ≤ outCnt π sg J R ∧
        p * cutCnt π sg J Y.edgeFinset / 12 ≤ inCnt π sg J R ∧
        (cutCnt π sg J R : ℝ) ≤ 2 * p * cutCnt π sg J Y.edgeFinset ∧
        (cutCnt π sg J Z₀ : ℝ) ≤ p * cutCnt π sg J Y.edgeFinset / 64) ∧
      (∀ I : Finset (Fin t), I.Nonempty → I ≠ univ → ∃ e ∈ Z₀, PartCross π I e) ∧
      (∀ I : Finset (Fin t), I.Nonempty → I ≠ univ →
        256 ≤ ((R \ Z₀).filter (PartCross π I)).card) ∧
      ∀ q ∈ tests, ((q.1.filter (· ∈ vtx R)).card : ℝ) ≤ q.2 := by
  obtain ⟨ν, hν⟩ := mutual_nominations Y k hk p hp.le hpk
  have hN : IsNom Y p ν := hν
  let Jset := (univ : Finset (Finset (Fin t × Bool))).filter
    fun J => μ ≤ (cutCnt π sg J Y.edgeFinset : ℝ)
  let Iset := (univ : Finset (Finset (Fin t))).filter fun I => I.Nonempty ∧ I ≠ univ
  let BJ : Finset (Fin t × Bool) → Finset (Sym2 G) × Finset (Sym2 G) → Prop := fun J RZ =>
    ((outCnt π sg J RZ.1 : ℝ) < p * cutCnt π sg J Y.edgeFinset / 12 ∨
      (inCnt π sg J RZ.1 : ℝ) < p * cutCnt π sg J Y.edgeFinset / 12) ∨
    (2 * p * cutCnt π sg J Y.edgeFinset < (cutCnt π sg J RZ.1 : ℝ) ∨
      p * cutCnt π sg J Y.edgeFinset / 64 < (cutCnt π sg J RZ.2 : ℝ))
  let BI : Finset (Fin t) → Finset (Sym2 G) × Finset (Sym2 G) → Prop := fun I RZ =>
    (¬ ∃ e ∈ RZ.2, PartCross π I e) ∨ ((RZ.1 \ RZ.2).filter (PartCross π I)).card < 256
  let BT : Finset G × ℝ → Finset (Sym2 G) × Finset (Sym2 G) → Prop := fun q RZ =>
    q.2 < ((q.1.filter (· ∈ vtx RZ.1)).card : ℝ)
  have hJ : ∀ J ∈ Jset, ν.P (BJ J) ≤
      4 * Real.exp (-(p / 2048 * cutCnt π sg J Y.edgeFinset)) := by
    intro J hJ
    have hJ' : μ ≤ (cutCnt π sg J Y.edgeFinset : ℝ) := (mem_filter.1 hJ).2
    have hs : 0 < (cutCnt π sg J Y.edgeFinset : ℝ) := by linarith
    have h1 := bad_out hN hp π sg J hs (hbal J).1
    have h2 := bad_in hN hp π sg J hs (hbal J).2
    have h3 := bad_cutR hN hp π sg J hs
    have h4 := bad_cutZ hN hp π sg J hs
    calc ν.P (BJ J) ≤ _ := mt_P_or_le ν _ _
      _ ≤ _ := add_le_add ((mt_P_or_le ν _ _).trans (add_le_add h1 h2))
          ((mt_P_or_le ν _ _).trans (add_le_add h3 h4))
      _ = 4 * Real.exp (-(p / 2048 * cutCnt π sg J Y.edgeFinset)) := by ring
  have hI : ∀ I ∈ Iset, ν.P (BI I) ≤
      2 * Real.exp (-(p / 2048 * cutCnt π sg (I ×ˢ univ) Y.edgeFinset)) := by
    intro I hI
    have hI' := (mem_filter.1 hI).2
    have hμI := hpart I hI'.1 hI'.2
    have hs : 0 < (cutCnt π sg (I ×ˢ univ) Y.edgeFinset : ℝ) := by linarith
    have hps : 1100 ≤ p * cutCnt π sg (I ×ˢ univ) Y.edgeFinset := by nlinarith
    have h5 := bad_marked hN hp π sg I hs
    have h6 := bad_unmarked hN π sg I hps
    calc ν.P (BI I) ≤ _ := mt_P_or_le ν _ _
      _ ≤ _ := add_le_add h5 h6
      _ = 2 * Real.exp (-(p / 2048 * cutCnt π sg (I ×ˢ univ) Y.edgeFinset)) := by ring
  have hT : ∀ q ∈ tests, ν.P (BT q) ≤ Real.exp (-(3 / 40 * q.2)) := by
    intro q hq
    have hcard : (1 : ℝ) ≤ tests.card := by exact_mod_cast card_pos.2 ⟨q, hq⟩
    have hlog := Real.log_nonneg hcard
    have hτ : 0 < q.2 := by linarith [(htests q hq).2]
    exact bad_test hN hp k hk q.1 q.2 hτ (htests q hq).1
  have hsumT : ∑ q ∈ tests, Real.exp (-(3 / 40 * q.2)) ≤ Real.exp (-2) := by
    rcases tests.eq_empty_or_nonempty with he | hne
    · rw [he, sum_empty]; positivity
    · have hcard : (0 : ℝ) < tests.card := by exact_mod_cast card_pos.2 hne
      have hex : Real.exp (-(Real.log tests.card + 2)) = Real.exp (-2) / tests.card := by
        rw [show -(Real.log tests.card + 2) = -2 - Real.log tests.card by ring, Real.exp_sub,
          Real.exp_log hcard]
      calc ∑ q ∈ tests, Real.exp (-(3 / 40 * q.2))
          ≤ ∑ _q ∈ tests, Real.exp (-(Real.log tests.card + 2)) :=
            sum_le_sum fun q hq => Real.exp_le_exp.2 (by linarith [(htests q hq).2])
        _ = Real.exp (-2) := by
            rw [sum_const, nsmul_eq_mul, hex]
            field_simp
  have hsumI : ∑ I ∈ Iset, 2 * Real.exp (-(p / 2048 * cutCnt π sg (I ×ˢ univ) Y.edgeFinset)) ≤
      ∑ J ∈ Jset, 2 * Real.exp (-(p / 2048 * cutCnt π sg J Y.edgeFinset)) := by
    have hinj : Set.InjOn (fun I : Finset (Fin t) => I ×ˢ (univ : Finset Bool)) Iset := by
      intro I _ I' _ hII
      ext i
      have := congrArg (fun J => (i, true) ∈ J) hII
      simpa using this
    have hsub : Iset.image (fun I => I ×ˢ (univ : Finset Bool)) ⊆ Jset := by
      intro J hJ
      obtain ⟨I, hI, rfl⟩ := mem_image.1 hJ
      have hI' := (mem_filter.1 hI).2
      exact mem_filter.2 ⟨mem_univ _, hpart I hI'.1 hI'.2⟩
    rw [← sum_image (f := fun J => 2 * Real.exp (-(p / 2048 * cutCnt π sg J Y.edgeFinset))) hinj]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hsumJ : ∑ J ∈ Jset, Real.exp (-(p / 2048 * cutCnt π sg J Y.edgeFinset)) ≤
      Real.exp (-4) / (1 - Real.exp (-4)) := by
    have hNcast : ((4 * (t + Y.edgeFinset.card) : ℕ) : ℝ) = 4 * (t + Y.edgeFinset.card) := by
      push_cast; ring
    refine cut_sum_le (fun J => cutCnt π sg J Y.edgeFinset) μ (p / 2048)
      (4 * (t + Y.edgeFinset.card)) (by linarith) ?_ ?_
    · rw [hNcast]
      have : p / 2048 * μ = p * μ / 2048 := by ring
      linarith
    · intro j
      rw [hNcast]
      exact hcount j
  let Bad : Finset (Sym2 G) × Finset (Sym2 G) → Prop := fun RZ =>
    (∃ J ∈ Jset, BJ J RZ) ∨ ((∃ I ∈ Iset, BI I RZ) ∨ (∃ q ∈ tests, BT q RZ))
  have hP : ν.P Bad < 1 := by
    have e1 : ν.P Bad ≤ ∑ J ∈ Jset, ν.P (BJ J) +
        (∑ I ∈ Iset, ν.P (BI I) + ∑ q ∈ tests, ν.P (BT q)) :=
      (mt_P_or_le ν _ _).trans (add_le_add (mt_P_exists_le ν _ _)
        ((mt_P_or_le ν _ _).trans (add_le_add (mt_P_exists_le ν _ _) (mt_P_exists_le ν _ _))))
    have e2 := sum_le_sum hJ
    have e3 := sum_le_sum hI
    have e4 := sum_le_sum hT
    rw [← mul_sum] at e2
    have e5 : ∑ J ∈ Jset, 2 * Real.exp (-(p / 2048 * cutCnt π sg J Y.edgeFinset)) =
        2 * ∑ J ∈ Jset, Real.exp (-(p / 2048 * cutCnt π sg J Y.edgeFinset)) := by
      rw [mul_sum]
    have := num_final
    linarith
  obtain ⟨RZ, hRZ, hgood⟩ := mt_exists_not ν Bad hP
  have hgJ : ∀ J ∈ Jset, ¬ BJ J RZ := fun J hJ hb => hgood (Or.inl ⟨J, hJ, hb⟩)
  have hgI : ∀ I ∈ Iset, ¬ BI I RZ := fun I hI hb => hgood (Or.inr (Or.inl ⟨I, hI, hb⟩))
  have hgT : ∀ q ∈ tests, ¬ BT q RZ := fun q hq hb => hgood (Or.inr (Or.inr ⟨q, hq, hb⟩))
  obtain ⟨hZR, hRE, hmatch⟩ := hN.1 RZ hRZ
  refine ⟨RZ.1, RZ.2, hZR, hRE, fun e he f hf hef v hv => hmatch e he f hf hef v hv,
    ?_, ?_, ?_, ?_⟩
  · intro J
    by_cases hJ : J ∈ Jset
    · have := hgJ J hJ
      simp only [BJ, not_or, not_lt] at this
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := this
      exact ⟨h1, h2, h3, h4⟩
    · have h0 : cutCnt π sg J Y.edgeFinset = 0 := by
        rcases hgap J with h | h
        · exact h
        · exact (hJ (mem_filter.2 ⟨mem_univ _, h⟩)).elim
      have hR0 : cutCnt π sg J RZ.1 = 0 :=
        Nat.eq_zero_of_le_zero ((cutCnt_mono π sg J hRE).trans h0.le)
      have hZ0 : cutCnt π sg J RZ.2 = 0 :=
        Nat.eq_zero_of_le_zero ((cutCnt_mono π sg J (hZR.trans hRE)).trans h0.le)
      rw [h0, hR0, hZ0]
      simp
  · intro I hI hIu
    have := hgI I (mem_filter.2 ⟨mem_univ _, hI, hIu⟩)
    simp only [BI, not_or, not_not] at this
    exact this.1
  · intro I hI hIu
    have := hgI I (mem_filter.2 ⟨mem_univ _, hI, hIu⟩)
    simp only [BI, not_or, not_lt] at this
    exact this.2
  · intro q hq
    have := hgT q hq
    simp only [BT, not_lt] at this
    exact this

end Matching

end Connector

end Lovasz
