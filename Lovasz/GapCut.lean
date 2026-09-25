/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Equation (2.2): the gap bounds edge boundaries; cut density

DAG nodes `E2.2` and `E2.2c` of `docs/BLUEPRINT.md`.
-/

namespace Lovasz

open Finset

namespace WGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
private lemma deg_nonneg (H : WGraph V) (x : V) : 0 ≤ H.deg x :=
  sum_nonneg fun y _ => H.nonneg x y

omit [DecidableEq V] in
private lemma vol_nonneg (H : WGraph V) (A : Finset V) : 0 ≤ H.vol A :=
  sum_nonneg fun x _ => H.deg_nonneg x

omit [Fintype V] [DecidableEq V] in
private lemma edgeWeight_nonneg (H : WGraph V) (A B : Finset V) : 0 ≤ H.edgeWeight A B :=
  sum_nonneg fun x _ => sum_nonneg fun y _ => H.nonneg x y

lemma vol_univ_eq (H : WGraph V) (U : Finset V) : H.vol univ = H.vol U + H.vol (univ \ U) := by
  unfold vol
  rw [← compl_eq_univ_sdiff, sum_add_sum_compl]

/-- The Dirichlet form of the indicator of `U` is `e_H(U, Uᶜ)`. -/
lemma dirichlet_indicator (H : WGraph V) (U : Finset V) :
    H.dirichlet (fun x => if x ∈ U then 1 else 0) = H.edgeWeight U (univ \ U) := by
  unfold dirichlet edgeWeight
  have hsym : ∑ x ∈ Uᶜ, ∑ y ∈ U, H.w x y = ∑ x ∈ U, ∑ y ∈ Uᶜ, H.w x y := by
    rw [sum_comm]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => H.symm y x
  have hsplit : ∀ x, ∑ y, H.w x y * ((if x ∈ U then (1 : ℝ) else 0) -
      (if y ∈ U then 1 else 0)) ^ 2 =
      (if x ∈ U then ∑ y ∈ Uᶜ, H.w x y else ∑ y ∈ U, H.w x y) := by
    intro x
    rw [← sum_add_sum_compl U]
    split_ifs with hx
    · rw [sum_eq_zero (fun y hy => by simp), zero_add]
      exact sum_congr rfl fun y hy => by simp [(mem_compl.mp hy)]
    · rw [sum_eq_zero (s := Uᶜ) (fun y hy => by simp [(mem_compl.mp hy)]), add_zero]
      exact sum_congr rfl fun y hy => by simp
  simp_rw [hsplit]
  rw [← sum_add_sum_compl U]
  rw [sum_ite_of_true (fun x hx => hx), sum_ite_of_false (fun x hx => mem_compl.mp hx), hsym,
    ← compl_eq_univ_sdiff]
  ring

/-- **Equation (2.2).** A normalized gap of at least `σ` implies
`e_H(U, Uᶜ) ≥ σ vol_H(U) vol_H(Uᶜ) / vol_H(V)` (stated without division). -/
theorem edgeWeight_compl_ge_of_hasGap (H : WGraph V) {σ : ℝ} (hσ : H.HasGap σ) (hσ0 : 0 ≤ σ)
    (U : Finset V) :
    σ * H.vol U * H.vol (univ \ U) ≤ H.edgeWeight U (univ \ U) * H.vol univ := by
  obtain ⟨z, hz⟩ := hσ (fun x => if x ∈ U then 1 else 0)
  rw [dirichlet_indicator] at hz
  have hQ : ∑ x, H.deg x * ((if x ∈ U then (1 : ℝ) else 0) - z) ^ 2 =
      H.vol U * (1 - z) ^ 2 + H.vol (univ \ U) * z ^ 2 := by
    rw [← sum_add_sum_compl U, vol, vol, sum_mul, sum_mul, ← compl_eq_univ_sdiff]
    congr 1
    · exact sum_congr rfl fun x hx => by simp [hx]
    · exact sum_congr rfl fun x hx => by simp [mem_compl.mp hx]
  rw [hQ] at hz
  rw [vol_univ_eq H U]
  have hA := H.vol_nonneg U
  have hB := H.vol_nonneg (univ \ U)
  set A := H.vol U
  set B := H.vol (univ \ U)
  set e := H.edgeWeight U (univ \ U)
  have key : A * B ≤ (A + B) * (A * (1 - z) ^ 2 + B * z ^ 2) := by
    nlinarith [sq_nonneg (A * (1 - z) - B * z)]
  calc σ * A * B = σ * (A * B) := by ring
    _ ≤ σ * ((A + B) * (A * (1 - z) ^ 2 + B * z ^ 2)) := mul_le_mul_of_nonneg_left key hσ0
    _ = (A + B) * (σ * (A * (1 - z) ^ 2 + B * z ^ 2)) := by ring
    _ ≤ (A + B) * e := mul_le_mul_of_nonneg_left hz (by linarith)
    _ = e * (A + B) := by ring

/-- **Section 2.3.** Degrees in `[aD, bD]` and gap `σ` imply `(σ a² D / (b h))`-cut-density,
where `h = |V(H)|`. -/
theorem isCutDense_of_hasGap (H : WGraph V) {σ a b D : ℝ} (hσ : H.HasGap σ) (hσ0 : 0 ≤ σ)
    (ha : 0 < a) (hD : 0 < D) (hdeg : H.DegBetween (a * D) (b * D)) :
    H.IsCutDense (σ * a ^ 2 * D / (b * Fintype.card V)) := by
  intro A
  have he := H.edgeWeight_nonneg A (univ \ A)
  rcases isEmpty_or_nonempty V with hV | ⟨⟨x0⟩⟩
  · simpa [Fintype.card_eq_zero] using he
  have hab : a ≤ b := le_of_mul_le_mul_right ((hdeg x0).1.trans (hdeg x0).2) hD
  have hb : 0 < b := ha.trans_le hab
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨x0⟩
  have h1 := H.edgeWeight_compl_ge_of_hasGap hσ hσ0 A
  have hvA : a * D * A.card ≤ H.vol A := by
    have := card_nsmul_le_sum A H.deg (a * D) (fun x _ => (hdeg x).1)
    rw [nsmul_eq_mul] at this
    unfold vol; linarith
  have hvB : a * D * (univ \ A).card ≤ H.vol (univ \ A) := by
    have := card_nsmul_le_sum (univ \ A) H.deg (a * D) (fun x _ => (hdeg x).1)
    rw [nsmul_eq_mul] at this
    unfold vol; linarith
  have hvV : H.vol univ ≤ b * D * Fintype.card V := by
    have := sum_le_card_nsmul univ H.deg (b * D) (fun x _ => (hdeg x).2)
    rw [nsmul_eq_mul, card_univ] at this
    unfold vol; linarith
  have hA0 : (0 : ℝ) ≤ a * D * A.card := by positivity
  have hB0 : (0 : ℝ) ≤ a * D * (univ \ A).card := by positivity
  have key : σ * a ^ 2 * D * A.card * (univ \ A).card * D ≤
      H.edgeWeight A (univ \ A) * (b * Fintype.card V) * D := by
    calc σ * a ^ 2 * D * A.card * (univ \ A).card * D
        = σ * (a * D * A.card) * (a * D * (univ \ A).card) := by ring
      _ ≤ σ * H.vol A * H.vol (univ \ A) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hvA hσ0) hvB hB0
          exact mul_nonneg hσ0 (H.vol_nonneg A)
      _ ≤ H.edgeWeight A (univ \ A) * H.vol univ := h1
      _ ≤ H.edgeWeight A (univ \ A) * (b * D * Fintype.card V) :=
          mul_le_mul_of_nonneg_left hvV he
      _ = H.edgeWeight A (univ \ A) * (b * Fintype.card V) * D := by ring
  have key' := le_of_mul_le_mul_right key hD
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  exact key'

end WGraph

end Lovasz
