/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.TraceConcentration
import Lovasz.SwapRounding

/-!
# Lemma 2.2: column sampling

DAG node `L2.2` of `docs/BLUEPRINT.md`. The paper derives it from the one-sided matrix
Bernstein inequality (2.5); in this DAG the retention step is instead the special case of
Lemma 4.3 in which every move changes one coordinate (independent Bernoulli retention), which
changes the constant in front of `c √t` by a universal factor.

Proof outline (with `C = 6`, `q = k/s`, `T = (√q a + 6 c √t)²`):
* independent Bernoulli(`q`) retention of the columns is a line process whose `j`-th move sends
  coordinate `j` to `1` or `0` (`bernoulli_process`), with product-Bernoulli terminal law;
* Lemma 4.3 with `A_j = f_j f_jᵀ`, `b = c²`, `ν = q a²` and deviation `T - q a²` bounds the
  probability of `λ_max(F_I F_Iᵀ) ≥ T` by `r e^{-t}` (`const_bound`), and
  `λ_max(F_Iᵀ F_I) = λ_max(F_I F_Iᵀ)` (`transpose_witness`);
* each `k`-subset has Bernoulli weight `q^k (1-q)^(s-k) ≥ 1/((s+1) C(s,k))` since `k` is a mode
  of `Bin(s, q)` (`mode_bound`).
-/

namespace Lovasz

open Finset Matrix

namespace ColumnSampling

open Classical in
lemma P_dirac {α : Type*} (a : α) (E : α → Prop) :
    (FinDist.dirac a).P E = if E a then 1 else 0 := by
  simp [FinDist.P, FinDist.dirac]

lemma isExact_dirac {α : Type*} (a : α) : (FinDist.dirac a).IsExact := by
  intro b hb
  simp only [FinDist.dirac, Finset.mem_singleton] at hb ⊢
  simp [hb]

open Classical in
lemma P_mix {α : Type*} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (μ₁ μ₂ : FinDist α)
    (h₁ : μ₁.IsExact) (h₂ : μ₂.IsExact)
    (E : α → Prop) :
    (FinDist.mix p hp μ₁ μ₂ h₁ h₂).P E = p * μ₁.P E + (1 - p) * μ₂.P E := by
  simp only [FinDist.P, FinDist.mix]
  have e₁ : ∑ a ∈ μ₁.support ∪ μ₂.support, (if E a then μ₁.prob a else 0) =
      ∑ a ∈ μ₁.support, (if E a then μ₁.prob a else 0) := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro a _ ha
    simp [h₁ a ha]
  have e₂ : ∑ a ∈ μ₁.support ∪ μ₂.support, (if E a then μ₂.prob a else 0) =
      ∑ a ∈ μ₂.support, (if E a then μ₂.prob a else 0) := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro a _ ha
    simp [h₂ a ha]
  rw [← e₁, ← e₂, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> ring

lemma isExact_mix {α : Type*} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (μ₁ μ₂ : FinDist α)
    (h₁ : μ₁.IsExact) (h₂ : μ₂.IsExact) :
    (FinDist.mix p hp μ₁ μ₂ h₁ h₂).IsExact := by
  intro a ha
  simp only [FinDist.mix, Finset.mem_union, not_or] at ha ⊢
  rw [h₁ a ha.1, h₂ a ha.2]
  ring

/-- Round the coordinates in `U` to the indicator of `I`, keeping the others. -/
def roundOn {ι : Type*} [DecidableEq ι] (y : ι → ℝ) (U I : Finset ι) : ι → ℝ :=
  fun j => if j ∈ U then (if j ∈ I then 1 else 0) else y j

/-- The product Bernoulli(`q`) weight of the rounding pattern `I` on `U`. -/
def weight {ι : Type*} [DecidableEq ι] (q : ℝ) (U I : Finset ι) : ℝ :=
  ∏ i ∈ U, if i ∈ I then q else 1 - q

open Classical in
/-- Independent Bernoulli(`q`) rounding of the coordinates in `U` (each equal to `q`) is a line
process whose moves change one coordinate each. -/
theorem bernoulli_process {ι : Type*} [DecidableEq ι] (ok : (ι → ℝ) → Prop)
    (hok : ∀ j, ok (Pi.single j 1)) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (U : Finset ι) :
    ∀ y : ι → ℝ, (∀ j ∈ U, y j = q) → (∀ j, 0 ≤ y j ∧ y j ≤ 1) →
    ∃ μ : FinDist (ι → ℝ), LineProcess ok y μ ∧ μ.IsExact ∧ ∀ E : (ι → ℝ) → Prop,
      μ.P E = ∑ I ∈ U.powerset, if E (roundOn y U I) then weight q U I else 0 := by
  induction U using Finset.induction_on with
  | empty =>
    intro y _ hy
    refine ⟨FinDist.dirac y, LineProcess.stop y hy, isExact_dirac y, fun E => ?_⟩
    rw [P_dirac]
    have : roundOn y ∅ ∅ = y := by funext j; simp [roundOn]
    rw [Finset.powerset_empty, Finset.sum_singleton, this]
    simp [weight]
  | insert j U hj ih =>
    intro y hyU hy
    have hyj : y j = q := hyU j (mem_insert_self j U)
    have hyU' : ∀ i ∈ U, y i = q := fun i hi => hyU i (mem_insert_of_mem hi)
    have hne : ∀ i ∈ U, i ≠ j := fun i hi h => hj (h ▸ hi)
    have e1 : ∀ i, ((y + (1 - q) • Pi.single j (1 : ℝ) : ι → ℝ)) i = if i = j then 1 else y i := by
      intro i
      by_cases h : i = j
      · subst h; simp [hyj]
      · simp [h]
    have e0 : ∀ i, ((y - q • Pi.single j (1 : ℝ) : ι → ℝ)) i = if i = j then 0 else y i := by
      intro i
      by_cases h : i = j
      · subst h; simp [hyj]
      · simp [h]
    have b1 : ∀ i, 0 ≤ ((y + (1 - q) • Pi.single j (1 : ℝ) : ι → ℝ)) i ∧
        ((y + (1 - q) • Pi.single j (1 : ℝ) : ι → ℝ)) i ≤ 1 := by
      intro i
      rw [e1]
      split_ifs
      · norm_num
      · exact hy i
    have b0 : ∀ i, 0 ≤ ((y - q • Pi.single j (1 : ℝ) : ι → ℝ)) i ∧
        ((y - q • Pi.single j (1 : ℝ) : ι → ℝ)) i ≤ 1 := by
      intro i
      rw [e0]
      split_ifs
      · norm_num
      · exact hy i
    obtain ⟨μ₁, lp₁, ex₁, P₁⟩ := ih (y + (1 - q) • Pi.single j 1)
      (fun i hi => by simp only [e1, hne i hi, ite_false, hyU' i hi]) b1
    obtain ⟨μ₂, lp₂, ex₂, P₂⟩ := ih (y - q • Pi.single j 1)
      (fun i hi => by simp only [e0, hne i hi, ite_false, hyU' i hi]) b0
    refine ⟨_, LineProcess.move y (Pi.single j 1) (1 - q) q μ₁ μ₂ (by linarith) hq0 ex₁ ex₂ hy
      (hok j) lp₁ lp₂, isExact_mix _ _ _ _ _ _, fun E => ?_⟩
    rw [P_mix, P₁, P₂, Finset.sum_powerset_insert hj, Finset.mul_sum, Finset.mul_sum, add_comm]
    have hp : q / (1 - q + q) = q := by simp
    rw [hp]
    congr 1
    · refine Finset.sum_congr rfl fun I hI => ?_
      have hIU : I ⊆ U := Finset.mem_powerset.1 hI
      have hjI : j ∉ I := fun h => hj (hIU h)
      have hr : roundOn (y - q • Pi.single j 1) U I = roundOn y (insert j U) I := by
        funext i
        by_cases h : i = j
        · subst h; simp [roundOn, e0, hj, hjI]
        · simp [roundOn, e0, h]
      have hw : weight q (insert j U) I = (1 - q) * weight q U I := by
        rw [weight, Finset.prod_insert hj, ite_eq_right hjI]
        rfl
      rw [hr, hw]
      split_ifs <;> ring
    · refine Finset.sum_congr rfl fun I hI => ?_
      have hIU : I ⊆ U := Finset.mem_powerset.1 hI
      have hr : roundOn (y + (1 - q) • Pi.single j 1) U I = roundOn y (insert j U) (insert j I) := by
        funext i
        by_cases h : i = j
        · subst h; simp [roundOn, e1, hj]
        · simp [roundOn, e1, h]
      have hw : weight q (insert j U) (insert j I) = q * weight q U I := by
        rw [weight, Finset.prod_insert hj, ite_eq_left (mem_insert_self j I)]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        simp [hne i hi]
      rw [hr, hw]
      split_ifs <;> ring



/-- Ratio of consecutive terms of `m ↦ C(s,m) k^m (s-k)^(s-m)`. -/
lemma binom_step (s k m : ℕ) (hm : m < s) :
    s.choose (m + 1) * k ^ (m + 1) * (s - k) ^ (s - (m + 1)) * ((m + 1) * (s - k)) =
      s.choose m * k ^ m * (s - k) ^ (s - m) * ((s - m) * k) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt hm
  have h1 : m + l + 1 - (m + 1) = l := by omega
  have h2 : m + l + 1 - m = l + 1 := by omega
  have hc := Nat.choose_succ_right_eq (m + l + 1) m
  rw [h2] at hc
  rw [h1, h2]
  generalize m + l + 1 - k = d
  calc (m + l + 1).choose (m + 1) * k ^ (m + 1) * d ^ l * ((m + 1) * d)
      = ((m + l + 1).choose (m + 1) * (m + 1)) * k ^ (m + 1) * d ^ (l + 1) := by ring
    _ = ((m + l + 1).choose m * (l + 1)) * k ^ (m + 1) * d ^ (l + 1) := by rw [hc]
    _ = _ := by ring

/-- `k` is a mode of `m ↦ C(s,m) k^m (s-k)^(s-m)`. -/
lemma binom_mode (s k : ℕ) (hks : k < s) (m : ℕ) (hm : m ≤ s) :
    s.choose m * k ^ m * (s - k) ^ (s - m) ≤ s.choose k * k ^ k * (s - k) ^ (s - k) := by
  set b : ℕ → ℕ := fun m => s.choose m * k ^ m * (s - k) ^ (s - m) with hb
  change b m ≤ b k
  have hP : ∀ m, 0 < (m + 1) * (s - k) := fun m => Nat.mul_pos (Nat.succ_pos m) (by omega)
  have up : ∀ d, k + d ≤ s → b (k + d) ≤ b k := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      have hstep := binom_step s k (k + d) (by omega)
      have hQ : (s - (k + d)) * k ≤ (k + d + 1) * (s - k) := by
        rw [mul_comm]
        exact Nat.mul_le_mul (by omega) (by omega)
      have : b (k + d + 1) * ((k + d + 1) * (s - k)) ≤ b (k + d) * ((k + d + 1) * (s - k)) := by
        calc b (k + d + 1) * ((k + d + 1) * (s - k))
            = b (k + d) * ((s - (k + d)) * k) := hstep
          _ ≤ _ := Nat.mul_le_mul_left _ hQ
      exact (Nat.le_of_mul_le_mul_right this (hP _)).trans (ih (by omega))
  have down : ∀ d, d ≤ k → b (k - d) ≤ b k := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      have hstep := binom_step s k (k - (d + 1)) (by omega)
      have e : k - (d + 1) + 1 = k - d := by omega
      rw [e] at hstep
      have hQ : (k - d) * (s - k) ≤ (s - (k - (d + 1))) * k := by
        rw [mul_comm (s - _)]
        exact Nat.mul_le_mul (by omega) (by omega)
      have : b (k - (d + 1)) * ((k - d) * (s - k)) ≤ b (k - d) * ((k - d) * (s - k)) := by
        calc b (k - (d + 1)) * ((k - d) * (s - k))
            ≤ b (k - (d + 1)) * ((s - (k - (d + 1))) * k) := Nat.mul_le_mul_left _ hQ
          _ = _ := hstep.symm
      exact (Nat.le_of_mul_le_mul_right this (by have := hP (k - (d + 1)); rwa [e] at this)).trans
        (ih (by omega))
  rcases le_total k m with h | h
  · have := up (m - k) (by omega)
    rwa [Nat.add_sub_cancel' h] at this
  · have := down (k - m) (by omega)
    rwa [Nat.sub_sub_self h] at this

/-- `s^s ≤ (s+1) C(s,k) k^k (s-k)^(s-k)`. -/
lemma pow_le_mode (s k : ℕ) (hks : k < s) :
    s ^ s ≤ (s + 1) * (s.choose k * k ^ k * (s - k) ^ (s - k)) := by
  have h := add_pow k (s - k) s
  rw [Nat.add_sub_cancel' hks.le] at h
  rw [h]
  calc ∑ m ∈ range (s + 1), k ^ m * (s - k) ^ (s - m) * s.choose m
      ≤ ∑ _m ∈ range (s + 1), s.choose k * k ^ k * (s - k) ^ (s - k) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have := binom_mode s k hks m (by simp at hm; omega)
        calc k ^ m * (s - k) ^ (s - m) * s.choose m = s.choose m * k ^ m * (s - k) ^ (s - m) := by
              ring
          _ ≤ _ := this
    _ = _ := by simp

/-- The value `k` is a mode of `Bin(s, k/s)`: `C(s,k) q^k (1-q)^(s-k) ≥ 1/(s+1)`. -/
lemma mode_bound (s k : ℕ) (hk : 0 < k) (hks : k < s) :
    1 ≤ ((s : ℝ) + 1) * s.choose k * (((k : ℝ) / s) ^ k * (1 - (k : ℝ) / s) ^ (s - k)) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast (hk.trans hks)
  have h := pow_le_mode s k hks
  have hR : ((s : ℝ)) ^ s ≤ ((s : ℝ) + 1) * (s.choose k * (k : ℝ) ^ k * ((s - k : ℕ) : ℝ) ^ (s - k)) := by
    exact_mod_cast h
  have e1 : 1 - (k : ℝ) / s = ((s - k : ℕ) : ℝ) / s := by
    rw [Nat.cast_sub hks.le]; field_simp
  have e2 : ((k : ℝ) / s) ^ k * (((s - k : ℕ) : ℝ) / s) ^ (s - k) =
      (k : ℝ) ^ k * ((s - k : ℕ) : ℝ) ^ (s - k) / (s : ℝ) ^ s := by
    rw [div_pow, div_pow, div_mul_div_comm, ← pow_add, Nat.add_sub_cancel' hks.le]
  rw [e1, e2, ← mul_div_assoc, le_div_iff₀ (pow_pos hs s), one_mul]
  calc (s : ℝ) ^ s ≤ _ := hR
    _ = _ := by ring

/-- The rank-one matrix `f_j f_jᵀ` of the `j`-th column. -/
def colOuter {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (j : Fin s) : Matrix (Fin r) (Fin r) ℝ :=
  vecMulVec (fun i => F i j) (fun i => F i j)

lemma quad_colOuter {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (z : Fin s → ℝ) (w : Fin r → ℝ) :
    w ⬝ᵥ ((∑ j, z j • colOuter F j) *ᵥ w) = ∑ j, z j * (∑ i, F i j * w i) ^ 2 := by
  rw [sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mulVec, dotProduct_smul, colOuter, vecMulVec_mulVec]
  simp only [smul_eq_mul]
  congr 1
  simp [dotProduct, sq, Finset.mul_sum, mul_comm, mul_left_comm]

lemma colOuter_psd {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (j : Fin s) :
    (colOuter F j).PosSemidef := by
  have := posSemidef_vecMulVec_self_star (fun i => F i j)
  simpa [colOuter] using this



/-- `‖Fᵀ‖ ≤ ‖F‖`, in quadratic-form language. -/
lemma transpose_bound {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (a : ℝ)
    (hF : ∀ v : Fin s → ℝ, ∑ i, (∑ j, F i j * v j) ^ 2 ≤ a ^ 2 * ∑ j, v j ^ 2) (w : Fin r → ℝ) :
    ∑ j, (∑ i, F i j * w i) ^ 2 ≤ a ^ 2 * ∑ i, w i ^ 2 := by
  set g : Fin s → ℝ := fun j => ∑ i, F i j * w i with hg
  have key : ∑ j, g j ^ 2 = ∑ i, w i * ∑ j, F i j * g j := by
    have : ∀ j, g j ^ 2 = ∑ i, w i * (F i j * g j) := by
      intro j
      rw [sq]
      conv_lhs => arg 1; rw [hg]
      simp only [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    simp_rw [this, Finset.mul_sum]
    exact Finset.sum_comm
  have hG0 : 0 ≤ ∑ j, g j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hW0 : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ w (fun i => ∑ j, F i j * g j)
  rw [← key] at hcs
  have h2 := hF g
  change ∑ j, g j ^ 2 ≤ a ^ 2 * ∑ i, w i ^ 2
  rcases hG0.eq_or_lt with h | h
  · rw [← h]; positivity
  · nlinarith

/-- If `F[:, I]` has a vector `v` with `|F_I v|² > T |v_I|²`, then `F_Iᵀ` has one too. -/
lemma transpose_witness {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (I : Finset (Fin s)) (T : ℝ)
    (hT : 0 ≤ T) (v : Fin s → ℝ)
    (hv : T * ∑ j ∈ I, v j ^ 2 < ∑ i, (∑ j ∈ I, F i j * v j) ^ 2) :
    ∃ u : Fin r → ℝ, 0 < ∑ i, u i ^ 2 ∧
      T * ∑ i, u i ^ 2 ≤ ∑ j ∈ I, (∑ i, F i j * u i) ^ 2 := by
  set u : Fin r → ℝ := fun i => ∑ j ∈ I, F i j * v j with hu
  refine ⟨u, ?_, ?_⟩
  · have : 0 ≤ T * ∑ j ∈ I, v j ^ 2 := mul_nonneg hT (Finset.sum_nonneg fun j _ => sq_nonneg _)
    linarith
  set N := ∑ i, u i ^ 2
  set V := ∑ j ∈ I, v j ^ 2
  set G := ∑ j ∈ I, (∑ i, F i j * u i) ^ 2
  have key : N = ∑ j ∈ I, v j * ∑ i, F i j * u i := by
    have : ∀ i, u i ^ 2 = ∑ j ∈ I, v j * (F i j * u i) := by
      intro i
      rw [sq]
      conv_lhs => arg 1; rw [hu]
      simp only [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => by ring
    simp only [N]
    simp_rw [this, Finset.mul_sum]
    exact Finset.sum_comm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I v (fun j => ∑ i, F i j * u i)
  rw [← key] at hcs
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hN : 0 < N := by have := mul_nonneg hT hV0; linarith
  change T * V < N at hv
  change N ^ 2 ≤ V * G at hcs
  nlinarith [mul_nonneg hT hV0]

/-- A vector with large Rayleigh quotient witnesses `LamMaxGe`. -/
lemma lamMaxGe_of_quad {q : ℕ} (B : Matrix (Fin q) (Fin q) ℝ) (t : ℝ) (u : Fin q → ℝ)
    (hu : 0 < u ⬝ᵥ u) (h : t * (u ⬝ᵥ u) ≤ u ⬝ᵥ (B *ᵥ u)) : LamMaxGe B t := by
  set c := (Real.sqrt (u ⬝ᵥ u))⁻¹
  have hc2 : c * c * (u ⬝ᵥ u) = 1 := by
    have hs := Real.mul_self_sqrt hu.le
    have hs0 : 0 < Real.sqrt (u ⬝ᵥ u) := Real.sqrt_pos.2 hu
    simp only [c]
    field_simp
    linarith
  refine ⟨c • u, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, hc2]
  · rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    have hcc : 0 ≤ c * c := mul_self_nonneg c
    calc t = c * c * (t * (u ⬝ᵥ u)) := by rw [mul_comm t, ← mul_assoc, hc2, one_mul]
      _ ≤ c * c * (u ⬝ᵥ (B *ᵥ u)) := mul_le_mul_of_nonneg_left h hcc

lemma dot_self_eq {q : ℕ} (u : Fin q → ℝ) : u ⬝ᵥ u = ∑ i, u i ^ 2 := by
  simp [dotProduct, sq]

/-- The constant: with `T = (√q a + 6 c √t)²` and `t' = T - q a²`, the tail bound of Lemma 4.3
is at most `e^{-t}`. -/
lemma const_bound (q a c t : ℝ) (hq : 0 ≤ q) (ha : 0 ≤ a) (hc : 0 < c) (ht : 0 < t) :
    0 < (Real.sqrt q * a + 6 * c * Real.sqrt t) ^ 2 - q * a ^ 2 ∧
    Real.exp (-(((Real.sqrt q * a + 6 * c * Real.sqrt t) ^ 2 - q * a ^ 2) ^ 2) /
        (32 * c ^ 2 * (q * a ^ 2 + ((Real.sqrt q * a + 6 * c * Real.sqrt t) ^ 2 - q * a ^ 2))))
      ≤ Real.exp (-t) := by
  set p := Real.sqrt q * a with hp
  set u := 6 * c * Real.sqrt t with hu
  have hp0 : 0 ≤ p := mul_nonneg (Real.sqrt_nonneg q) ha
  have hu0 : 0 < u := by positivity
  have hpq : q * a ^ 2 = p ^ 2 := by rw [hp, mul_pow, Real.sq_sqrt hq]
  have hu2 : u ^ 2 = 36 * c ^ 2 * t := by rw [hu, mul_pow, Real.sq_sqrt ht.le]; ring
  rw [hpq]
  have e1 : (p + u) ^ 2 - p ^ 2 = u * (2 * p + u) := by ring
  have e2 : p ^ 2 + (p + u) ^ 2 - p ^ 2 = (p + u) ^ 2 := by ring
  rw [add_sub_assoc'] at *
  refine ⟨by rw [e1]; positivity, ?_⟩
  rw [e2, e1, Real.exp_le_exp, neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
  have h1 : (p + u) ^ 2 ≤ (2 * p + u) ^ 2 := by nlinarith
  have h2 : t * (32 * c ^ 2 * (p + u) ^ 2) ≤ u ^ 2 * (p + u) ^ 2 := by
    have : t * (32 * c ^ 2) ≤ u ^ 2 := by rw [hu2]; nlinarith [sq_nonneg c]
    calc t * (32 * c ^ 2 * (p + u) ^ 2) = t * (32 * c ^ 2) * (p + u) ^ 2 := by ring
      _ ≤ u ^ 2 * (p + u) ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg _)
  calc t * (32 * c ^ 2 * (p + u) ^ 2) ≤ u ^ 2 * (p + u) ^ 2 := h2
    _ ≤ u ^ 2 * (2 * p + u) ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = (u * (2 * p + u)) ^ 2 := by ring


lemma quad_single {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (j : Fin s) (w : Fin r → ℝ) :
    w ⬝ᵥ (colOuter F j *ᵥ w) = (∑ i, F i j * w i) ^ 2 := by
  rw [colOuter, vecMulVec_mulVec]
  simp [dotProduct, sq, Finset.mul_sum, mul_comm, mul_left_comm]

lemma weight_nonneg {ι : Type*} [DecidableEq ι] (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (U I : Finset ι) : 0 ≤ weight q U I :=
  Finset.prod_nonneg fun i _ => by split_ifs <;> linarith

lemma weight_univ {s : ℕ} (q : ℝ) (I : Finset (Fin s)) :
    weight q univ I = q ^ I.card * (1 - q) ^ (s - I.card) := by
  rw [weight, Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff,
    prod_const, prod_const, univ_inter, card_univ_sdiff, Fintype.card_fin]

open Classical in
/-- The main case `c > 0`, `0 < k < s` of Lemma 2.2, with `C = 6`. -/
lemma main_case {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (a c : ℝ)
    (hF : ∀ v : Fin s → ℝ, ∑ i, (∑ j, F i j * v j) ^ 2 ≤ a ^ 2 * ∑ j, v j ^ 2)
    (hcol : ∀ j, ∑ i, F i j ^ 2 ≤ c ^ 2) (ha : 0 ≤ a) (hc : 0 < c)
    (k : ℕ) (hk0 : 0 < k) (hks : k < s) (t : ℝ) (ht : 0 < t) :
    ((((univ : Finset (Fin s)).powersetCard k).filter fun I => ∃ v : Fin s → ℝ,
        (Real.sqrt ((k : ℝ) / s) * a + 6 * c * Real.sqrt t) ^ 2 * ∑ j ∈ I, v j ^ 2 <
          ∑ i, (∑ j ∈ I, F i j * v j) ^ 2).card : ℝ) ≤
      r * (s + 1) * Real.exp (-t) * s.choose k := by
  set q : ℝ := (k : ℝ) / s with hq
  set T := (Real.sqrt q * a + 6 * c * Real.sqrt t) ^ 2 with hT
  set bad := ((univ : Finset (Fin s)).powersetCard k).filter fun I => ∃ v : Fin s → ℝ,
    T * ∑ j ∈ I, v j ^ 2 < ∑ i, (∑ j ∈ I, F i j * v j) ^ 2 with hbad
  have hs : (0 : ℝ) < s := by exact_mod_cast hk0.trans hks
  have hq0 : 0 < q := div_pos (by exact_mod_cast hk0) hs
  have hq1 : q < 1 := (div_lt_one hs).2 (by exact_mod_cast hks)
  have hT0 : 0 ≤ T := sq_nonneg _
  obtain ⟨ht'0, hexp⟩ := const_bound q a c t hq0.le ha hc ht
  set t' := T - q * a ^ 2 with ht'
  -- independent Bernoulli(`q`) retention as a line process
  let ok : (Fin s → ℝ) → Prop := fun h =>
    ((univ : Finset (Fin s)).filter fun i => h i ≠ 0).card ≤ 4
  have hok : ∀ j : Fin s, ok (Pi.single j 1) := by
    intro j
    show ((univ : Finset (Fin s)).filter fun i => (Pi.single j (1 : ℝ) : Fin s → ℝ) i ≠ 0).card
      ≤ 4
    calc _ ≤ ({j} : Finset (Fin s)).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter] at hi
          by_contra h
          simp only [Finset.mem_singleton] at h
          exact hi.2 (Pi.single_eq_of_ne h 1)
      _ ≤ 4 := by simp
  set x : Fin s → ℝ := fun _ => q with hx
  obtain ⟨μ, lp, -, hP⟩ := bernoulli_process ok hok q hq0 hq1 univ x (fun _ _ => rfl)
    (fun _ => ⟨hq0.le, hq1.le⟩)
  -- the matrices `A_j = f_j f_jᵀ`
  have hAb : ∀ j, QuadLe (colOuter F j) (c ^ 2) := by
    intro j w
    rw [quad_single, dot_self_eq]
    calc (∑ i, F i j * w i) ^ 2 ≤ (∑ i, F i j ^ 2) * ∑ i, w i ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ c ^ 2 * ∑ i, w i ^ 2 :=
          mul_le_mul_of_nonneg_right (hcol j) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hM : QuadLe (∑ i, x i • colOuter F i) (q * a ^ 2) := by
    intro w
    rw [quad_colOuter, dot_self_eq]
    simp only [x]
    rw [← Finset.mul_sum, mul_assoc]
    exact mul_le_mul_of_nonneg_left (transpose_bound F a hF w) hq0.le
  have hconc := (bounded_support_concentration (q := r) univ ok (fun h hh => hh) x μ lp
    (colOuter F) (colOuter_psd F) (c ^ 2) (q * a ^ 2) t' (by positivity) hAb
    (fun i hi => absurd (mem_univ i) hi) hM ht'0).1
  set E : (Fin s → ℝ) → Prop := fun z =>
    LamMaxGe (∑ i, z i • colOuter F i - ∑ i, x i • colOuter F i) t' with hE
  have hPE : μ.P E ≤ r * Real.exp (-t) :=
    hconc.trans (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg r))
  -- every bad `k`-subset is a bad outcome of the Bernoulli process
  have hbadE : ∀ I ∈ bad, E (roundOn x univ I) := by
    intro I hI
    obtain ⟨v, hv⟩ := (Finset.mem_filter.1 hI).2
    obtain ⟨u, hu0, huT⟩ := transpose_witness F I T hT0 v hv
    apply lamMaxGe_of_quad _ _ u (by rw [dot_self_eq]; exact hu0)
    rw [sub_mulVec, dotProduct_sub, quad_colOuter, quad_colOuter, dot_self_eq]
    have hr : ∀ j, roundOn x univ I j = if j ∈ I then 1 else 0 := fun j => by simp [roundOn]
    simp only [hr, x, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, univ_inter, ← Finset.mul_sum]
    have := transpose_bound F a hF u
    have hqa : q * ∑ j, (∑ i, F i j * u i) ^ 2 ≤ q * (a ^ 2 * ∑ i, u i ^ 2) :=
      mul_le_mul_of_nonneg_left this hq0.le
    rw [ht']
    nlinarith
  set π := q ^ k * (1 - q) ^ (s - k) with hπ
  have hweight : ∀ I ∈ bad, weight q univ I = π := by
    intro I hI
    rw [weight_univ, (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hI).1).2]
  have hlow : (bad.card : ℝ) * π ≤ μ.P E := by
    rw [hP E]
    calc (bad.card : ℝ) * π
        = ∑ I ∈ bad, (if E (roundOn x univ I) then weight q univ I else 0) := by
          rw [Finset.sum_congr rfl fun I hI => by rw [ite_eq_left (hbadE I hI), hweight I hI]]
          simp
      _ ≤ ∑ I ∈ (univ : Finset (Fin s)).powerset,
            (if E (roundOn x univ I) then weight q univ I else 0) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro I _
            simp
          · intro I _ _
            split_ifs
            · exact weight_nonneg q hq0.le hq1.le _ _
            · exact le_rfl
  have hmode : 1 ≤ ((s : ℝ) + 1) * s.choose k * π := mode_bound s k hk0 hks
  have h1 : (bad.card : ℝ) ≤ bad.card * (((s : ℝ) + 1) * s.choose k * π) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hmode
  have h3 : (((s : ℝ) + 1) * s.choose k) * (bad.card * π) ≤
      (((s : ℝ) + 1) * s.choose k) * (r * Real.exp (-t)) :=
    mul_le_mul_of_nonneg_left (hlow.trans hPE) (by positivity)
  calc (bad.card : ℝ) ≤ bad.card * (((s : ℝ) + 1) * s.choose k * π) := h1
    _ = (((s : ℝ) + 1) * s.choose k) * (bad.card * π) := by ring
    _ ≤ (((s : ℝ) + 1) * s.choose k) * (r * Real.exp (-t)) := h3
    _ = r * (s + 1) * Real.exp (-t) * s.choose k := by ring

open Classical in
/-- In the degenerate cases `c = 0`, `k = 0`, `k = s` there are no bad `k`-subsets. -/
lemma degenerate {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (a c : ℝ)
    (hF : ∀ v : Fin s → ℝ, ∑ i, (∑ j, F i j * v j) ^ 2 ≤ a ^ 2 * ∑ j, v j ^ 2)
    (hcol : ∀ j, ∑ i, F i j ^ 2 ≤ c ^ 2) (ha : 0 ≤ a) (hc : 0 ≤ c) (C : ℝ) (hC : 0 ≤ C)
    (k : ℕ) (t : ℝ) (ht : 0 < t) (hdeg : c = 0 ∨ k = 0 ∨ k = s) :
    (((univ : Finset (Fin s)).powersetCard k).filter fun I => ∃ v : Fin s → ℝ,
        (Real.sqrt ((k : ℝ) / s) * a + C * c * Real.sqrt t) ^ 2 * ∑ j ∈ I, v j ^ 2 <
          ∑ i, (∑ j ∈ I, F i j * v j) ^ 2) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  rintro I hI ⟨v, hv⟩
  rw [Finset.mem_powersetCard] at hI
  have hV0 : 0 ≤ ∑ j ∈ I, v j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hT0 : 0 ≤ (Real.sqrt ((k : ℝ) / s) * a + C * c * Real.sqrt t) ^ 2 *
      ∑ j ∈ I, v j ^ 2 := mul_nonneg (sq_nonneg _) hV0
  rcases hdeg with h | h | h
  · have hF0 : ∀ i j, F i j = 0 := by
      intro i j
      have h1 := hcol j
      rw [h] at h1
      have h2 : ∑ i, F i j ^ 2 = 0 :=
        le_antisymm (by simpa using h1) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)] at h2
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (h2 i (mem_univ i))
    have h0 : ∑ i, (∑ j ∈ I, F i j * v j) ^ 2 = 0 := by simp [hF0]
    rw [h0] at hv
    linarith
  · have hI0 : I = ∅ := Finset.card_eq_zero.1 (hI.2.trans h)
    subst hI0
    simp at hv
  · have hIu : I = univ := Finset.eq_univ_of_card I (by rw [hI.2, h, Fintype.card_fin])
    subst hIu
    have h2 := hF v
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      simp at hv
    · have hq : (k : ℝ) / s = 1 := by
        rw [h]; exact div_self (by positivity)
      rw [hq, Real.sqrt_one, one_mul] at hv
      have hle : a ^ 2 ≤ (a + C * c * Real.sqrt t) ^ 2 := by
        have : 0 ≤ C * c * Real.sqrt t := by positivity
        nlinarith
      have : a ^ 2 * ∑ j, v j ^ 2 ≤ (a + C * c * Real.sqrt t) ^ 2 * ∑ j, v j ^ 2 :=
        mul_le_mul_of_nonneg_right hle hV0
      linarith

end ColumnSampling

open Classical in
/-- **Lemma 2.2 (Column sampling).** Let `F` be an `r × s` real matrix with `‖F‖ ≤ a` and all
columns of Euclidean norm at most `c`, and let `I` be a uniform `k`-subset of the columns,
`q = k/s`. For `t > 0`, `P(‖F[:, I]‖ > √q a + C c √t) ≤ r (s+1) e^{-t}` for a universal
constant `C` (stated by counting `k`-subsets; the operator norm is expressed through the
quadratic form). -/
theorem column_sampling :
    ∃ C : ℝ, 0 < C ∧ ∀ {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (a c : ℝ),
      (∀ v : Fin s → ℝ, ∑ i, (∑ j, F i j * v j) ^ 2 ≤ a ^ 2 * ∑ j, v j ^ 2) →
      (∀ j, ∑ i, F i j ^ 2 ≤ c ^ 2) → 0 ≤ a → 0 ≤ c →
      ∀ k : ℕ, k ≤ s → ∀ t : ℝ, 0 < t →
        ((((univ : Finset (Fin s)).powersetCard k).filter fun I => ∃ v : Fin s → ℝ,
            (Real.sqrt ((k : ℝ) / s) * a + C * c * Real.sqrt t) ^ 2 * ∑ j ∈ I, v j ^ 2 <
              ∑ i, (∑ j ∈ I, F i j * v j) ^ 2).card : ℝ) ≤
          r * (s + 1) * Real.exp (-t) * s.choose k := by
  refine ⟨6, by norm_num, ?_⟩
  intro r s F a c hF hcol ha hc k hk t ht
  by_cases hdeg : c = 0 ∨ k = 0 ∨ k = s
  · rw [ColumnSampling.degenerate F a c hF hcol ha hc 6 (by norm_num) k t ht hdeg]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · simp only [not_or] at hdeg
    obtain ⟨hc0, hk0, hks⟩ := hdeg
    exact ColumnSampling.main_case F a c hF hcol ha (lt_of_le_of_ne hc (Ne.symm hc0)) k
      (Nat.pos_of_ne_zero hk0) (lt_of_le_of_ne hk hks) t ht

end Lovasz
