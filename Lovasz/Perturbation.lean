/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent)
-/
import Lovasz.Defs

/-!
# Lemma 2.1: deleting vertices and edges

DAG node `L2.1` of `docs/BLUEPRINT.md`.

With the variational definition of `HasGap`, the lemma has a direct proof: extend a test
function on `A` by its degree-weighted mean `z`, apply the gap of `H`, and bound the Dirichlet
energy lost by deleting vertices and decreasing weights by `2β ∑_A (f_x - z)^2`.
-/

universe u

namespace Lovasz

open Finset

/-- A sum over the subtype `A` of a function vanishing off `A` equals the sum over `V`. -/
private lemma sum_subtype_eq_sum_univ_of_vanish {V : Type u} [Fintype V] (A : Finset V) (g : V → ℝ)
    (hg : ∀ x, x ∉ A → g x = 0) : ∑ x : A, g x = ∑ x, g x := by
  rw [Finset.sum_coe_sort]
  exact Finset.sum_subset (subset_univ _) (fun x _ hx => hg x hx)

/-- The weighted mean minimizes the weighted squared deviation. -/
private lemma weighted_mean_min {ι : Type*} [Fintype ι] (d f : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (c : ℝ) :
    ∑ i, d i * (f i - (∑ j, d j * f j) / (∑ j, d j)) ^ 2 ≤ ∑ i, d i * (f i - c) ^ 2 := by
  by_cases h0 : ∑ j, d j = 0
  · have hz : ∀ i, d i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hd j)).1 h0 i (mem_univ i)
    simp [hz]
  · obtain ⟨m, hm⟩ : ∃ m, m = (∑ j, d j * f j) / (∑ j, d j) := ⟨_, rfl⟩
    rw [← hm]
    have hsum : ∑ j, d j * f j = m * ∑ j, d j := by rw [hm]; field_simp
    have hpt : ∀ i, d i * (f i - c) ^ 2 = d i * (f i - m) ^ 2 + (m - c) ^ 2 * d i
        + 2 * (m - c) * (d i * f i) - 2 * (m - c) * m * d i := fun i => by ring
    have key : ∑ i, d i * (f i - c) ^ 2
        = ∑ i, d i * (f i - m) ^ 2 + (m - c) ^ 2 * ∑ j, d j := by
      simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
      ring
    rw [key]
    have : 0 ≤ (m - c) ^ 2 * ∑ j, d j :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun j _ => hd j))
    linarith

/-- Core of Lemma 2.1 with the explicit constant `C' = 2 / a`. -/
lemma hasGap_of_deletion_core {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V)
    (A : Finset V) (H' : WGraph A) (a D σ β : ℝ) (ha : 0 < a) (hD : 0 < D)
    (hdeg : ∀ x, a * D ≤ H.deg x) (hgap : H.HasGap σ)
    (hw : ∀ x y : A, H'.w x y ≤ H.w x y) (hloss : ∀ x : A, H.deg x - H'.deg x ≤ β)
    (hβ : 0 ≤ β) (f : A → ℝ) :
    ∃ z : ℝ, (σ - 2 * β / (a * D)) * ∑ x : A, H'.deg x * (f x - z) ^ 2 ≤ H'.dirichlet f := by
  classical
  have haD : 0 < a * D := mul_pos ha hD
  have hdpos : ∀ x, 0 < H.deg x := fun x => lt_of_lt_of_le haD (hdeg x)
  have hdeg'_nonneg : ∀ x, 0 ≤ H'.deg x := fun x => Finset.sum_nonneg fun y _ => H'.nonneg x y
  have hdir'_nonneg : 0 ≤ H'.dirichlet f := by
    unfold WGraph.dirichlet
    refine div_nonneg ?_ (by norm_num)
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (H'.nonneg x y) (sq_nonneg _)
  by_cases hsneg : σ - 2 * β / (a * D) < 0
  · refine ⟨0, ?_⟩
    have : 0 ≤ ∑ x : A, H'.deg x * (f x - 0) ^ 2 :=
      Finset.sum_nonneg fun x _ => mul_nonneg (hdeg'_nonneg x) (sq_nonneg _)
    nlinarith
  replace hsneg := not_lt.1 hsneg
  have hσ : 0 ≤ σ := by
    have : 0 ≤ 2 * β / (a * D) := by positivity
    linarith
  -- the degree-weighted mean of `f`
  obtain ⟨z, hz⟩ : ∃ z, z = (∑ x : A, H.deg x * f x) / ∑ x : A, H.deg (x : V) := ⟨_, rfl⟩
  refine ⟨z, ?_⟩
  -- extension of `f` by `z`
  obtain ⟨F, hFA, hFn⟩ : ∃ F : V → ℝ, (∀ x : A, F x = f x) ∧ (∀ v, v ∉ A → F v = z) :=
    ⟨fun v => if h : v ∈ A then f ⟨v, h⟩ else z, fun x => by simp [x.2],
      fun v hv => by simp [hv]⟩
  -- extension of the weights of `H'` by `0`
  obtain ⟨w', hw'A, hw'n⟩ : ∃ w' : V → V → ℝ, (∀ x y : A, w' x y = H'.w x y) ∧
      (∀ x y, ¬(x ∈ A ∧ y ∈ A) → w' x y = 0) :=
    ⟨fun x y => if h : x ∈ A ∧ y ∈ A then H'.w ⟨x, h.1⟩ ⟨y, h.2⟩ else 0,
      fun x y => by simp [x.2, y.2], fun x y h => by simp [h]⟩
  have hw'le : ∀ x y, w' x y ≤ H.w x y := by
    intro x y
    by_cases h : x ∈ A ∧ y ∈ A
    · exact (hw'A ⟨x, h.1⟩ ⟨y, h.2⟩).trans_le (hw ⟨x, h.1⟩ ⟨y, h.2⟩)
    · rw [hw'n x y h]; exact H.nonneg x y
  have hw'symm : ∀ x y, w' x y = w' y x := by
    intro x y
    by_cases h : x ∈ A ∧ y ∈ A
    · rw [hw'A ⟨x, h.1⟩ ⟨y, h.2⟩, hw'A ⟨y, h.2⟩ ⟨x, h.1⟩]; exact H'.symm _ _
    · rw [hw'n x y h, hw'n y x (fun h' => h ⟨h'.2, h'.1⟩)]
  -- `H'`-degrees and the `H'`-Dirichlet form as sums over `V`
  have hdeg' : ∀ x : A, H'.deg x = ∑ y, w' x y := by
    intro x
    rw [← sum_subtype_eq_sum_univ_of_vanish A (fun y => w' x y)
      (fun y hy => hw'n _ _ (fun h => hy h.2))]
    exact Finset.sum_congr rfl fun y _ => (hw'A x y).symm
  have hdir' : H'.dirichlet f = (∑ x, ∑ y, w' x y * (F x - F y) ^ 2) / 2 := by
    unfold WGraph.dirichlet
    congr 1
    rw [← sum_subtype_eq_sum_univ_of_vanish A (fun x => ∑ y, w' x y * (F x - F y) ^ 2)
      (fun x hx => Finset.sum_eq_zero fun y _ => by rw [hw'n x y (fun h => hx h.1), zero_mul])]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← sum_subtype_eq_sum_univ_of_vanish A (fun y => w' x y * (F x - F y) ^ 2)
      (fun y hy => by rw [hw'n x y (fun h => hy h.2), zero_mul])]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hw'A, hFA, hFA]
  -- the degree loss at each vertex
  have hlossV : ∀ x, (F x - z) ^ 2 * ∑ y, (H.w x y - w' x y) ≤ β * (F x - z) ^ 2 := by
    intro x
    by_cases hx : x ∈ A
    · have h1 := hloss ⟨x, hx⟩
      rw [hdeg'] at h1
      have h2 : ∑ y, (H.w x y - w' x y) ≤ β := by
        rw [Finset.sum_sub_distrib]; exact h1
      nlinarith [sq_nonneg (F x - z)]
    · simp [hFn x hx]
  -- energy comparison
  have hpt : ∀ x y, H.w x y * (F x - F y) ^ 2 ≤ w' x y * (F x - F y) ^ 2
      + 2 * ((H.w x y - w' x y) * (F x - z) ^ 2) + 2 * ((H.w x y - w' x y) * (F y - z) ^ 2) := by
    intro x y
    have h1 : (F x - F y) ^ 2 ≤ 2 * (F x - z) ^ 2 + 2 * (F y - z) ^ 2 := by
      nlinarith [sq_nonneg (F x + F y - 2 * z)]
    have h2 : 0 ≤ H.w x y - w' x y := sub_nonneg.2 (hw'le x y)
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have hsum1 : ∑ x, ∑ y, H.w x y * (F x - F y) ^ 2 ≤ ∑ x, ∑ y, w' x y * (F x - F y) ^ 2
      + 2 * ∑ x, ∑ y, (H.w x y - w' x y) * (F x - z) ^ 2
      + 2 * ∑ x, ∑ y, (H.w x y - w' x y) * (F y - z) ^ 2 := by
    calc _ ≤ ∑ x, ∑ y, (w' x y * (F x - F y) ^ 2
            + 2 * ((H.w x y - w' x y) * (F x - z) ^ 2)
            + 2 * ((H.w x y - w' x y) * (F y - z) ^ 2)) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpt x y
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hswap : ∑ x, ∑ y, (H.w x y - w' x y) * (F y - z) ^ 2
      = ∑ x, ∑ y, (H.w x y - w' x y) * (F x - z) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [H.symm y x, hw'symm y x]
  have hrow : ∑ x, ∑ y, (H.w x y - w' x y) * (F x - z) ^ 2 ≤ β * ∑ x, (F x - z) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← Finset.sum_mul, mul_comm]
    exact hlossV x
  have hdirF : H.dirichlet F ≤ H'.dirichlet f + 2 * (β * ∑ x, (F x - z) ^ 2) := by
    have e : H.dirichlet F = (∑ x, ∑ y, H.w x y * (F x - F y) ^ 2) / 2 := rfl
    rw [e, hdir']
    linarith
  have hweight : β * ∑ x, (F x - z) ^ 2
      ≤ β / (a * D) * ∑ x, H.deg x * (F x - z) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have h1 : β ≤ β / (a * D) * H.deg x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ haD]
      exact mul_le_mul_of_nonneg_left (hdeg x) hβ
    nlinarith [sq_nonneg (F x - z)]
  have hVA : ∑ x, H.deg x * (F x - z) ^ 2 = ∑ x : A, H.deg x * (f x - z) ^ 2 := by
    rw [← sum_subtype_eq_sum_univ_of_vanish A (fun x => H.deg x * (F x - z) ^ 2)
      (fun x hx => by simp [hFn x hx])]
    exact Finset.sum_congr rfl fun x _ => by rw [hFA]
  -- the gap of `H` applied to `F`
  obtain ⟨z₁, hz₁⟩ := hgap F
  have hmin : ∑ x : A, H.deg x * (f x - z) ^ 2 ≤ ∑ x : A, H.deg x * (f x - z₁) ^ 2 := by
    rw [hz]
    exact weighted_mean_min (fun x : A => H.deg x) f (fun x => (hdpos x).le) z₁
  have hsub : ∑ x : A, H.deg x * (f x - z₁) ^ 2 ≤ ∑ x, H.deg x * (F x - z₁) ^ 2 := by
    calc ∑ x : A, H.deg x * (f x - z₁) ^ 2 = ∑ x : A, H.deg (x : V) * (F x - z₁) ^ 2 :=
          Finset.sum_congr rfl fun x _ => by rw [hFA]
      _ = ∑ x ∈ A, H.deg x * (F x - z₁) ^ 2 :=
          Finset.sum_coe_sort A (fun x => H.deg x * (F x - z₁) ^ 2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ A)
          (fun x _ _ => mul_nonneg (hdpos x).le (sq_nonneg _))
  have hmain : σ * ∑ x : A, H.deg x * (f x - z) ^ 2
      ≤ H'.dirichlet f + 2 * β / (a * D) * ∑ x : A, H.deg x * (f x - z) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (hmin.trans hsub) hσ
    have h2 : 2 * β / (a * D) * ∑ x : A, H.deg x * (f x - z) ^ 2
        = 2 * (β / (a * D) * ∑ x, H.deg x * (F x - z) ^ 2) := by
      rw [hVA]; ring
    rw [h2]
    linarith
  have hdeg_le : ∑ x : A, H'.deg x * (f x - z) ^ 2 ≤ ∑ x : A, H.deg x * (f x - z) ^ 2 := by
    refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [hdeg']
    exact Finset.sum_le_sum fun y _ => hw'le x y
  calc (σ - 2 * β / (a * D)) * ∑ x : A, H'.deg x * (f x - z) ^ 2
      ≤ (σ - 2 * β / (a * D)) * ∑ x : A, H.deg x * (f x - z) ^ 2 :=
        mul_le_mul_of_nonneg_left hdeg_le hsneg
    _ = σ * ∑ x : A, H.deg x * (f x - z) ^ 2
        - 2 * β / (a * D) * ∑ x : A, H.deg x * (f x - z) ^ 2 := by ring
    _ ≤ H'.dirichlet f := by linarith

/-- **Lemma 2.1.** Suppose `H` has degrees in `[aD, bD]` and normalized upper gap `σ`. Delete
vertices (keep the set `A`) and delete or decrease edge weights (`H' ≤ H` on `A`) so that every
remaining vertex loses at most `β ≤ c' D` weighted degree. The remaining graph has normalized
upper gap at least `σ - C' β / D`. -/
theorem hasGap_of_deletion (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (A : Finset V) (H' : WGraph A)
        (D σ β : ℝ),
        0 < D → H.DegBetween (a * D) (b * D) → H.HasGap σ →
        (∀ x y : A, H'.w x y ≤ H.w x y) → (∀ x : A, H.deg x - H'.deg x ≤ β) →
        0 ≤ β → β ≤ c' * D →
        H'.HasGap (σ - C' * β / D) := by
  refine ⟨1, 2 / a, one_pos, by positivity, ?_⟩
  intro V _ _ H A H' D σ β hD hdeg hgap hw hloss hβ _ f
  have e : 2 / a * β / D = 2 * β / (a * D) := by rw [div_mul_eq_mul_div, div_div]
  rw [e]
  exact hasGap_of_deletion_core H A H' a D σ β ha hD (fun x => (hdeg x).1) hgap hw hloss hβ f

end Lovasz
