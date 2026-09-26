/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent)
-/
import Lovasz.Defs

/-!
# The normalized Cheeger inequality (classical input)

DAG node `K.cheeger` of `docs/BLUEPRINT.md`; cited in Section 2.1 of the paper (Chung,
*Spectral Graph Theory*). Only the hard direction `1 - λ₂(N_H) ≥ Φ(H)² / 2` is used.

The proof: split `f - z` (with `z` a degree-weighted median) into positive and negative parts;
for a nonnegative `h` supported on at most half the volume, a discrete co-area inequality
(proved by peeling off the minimum positive level) gives
`∑_{x,y} a_{xy} |h_x² - h_y²| ≥ 2 φ ∑_x d_x h_x²`, and Cauchy–Schwarz finishes.
-/

namespace Lovasz

open Finset

namespace WGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

section CheegerAux

variable (H : WGraph V)

omit [DecidableEq V] in
lemma deg_nonneg_aux (x : V) : 0 ≤ H.deg x := Finset.sum_nonneg fun y _ => H.nonneg x y

omit [DecidableEq V] in
lemma vol_nonneg_aux (U : Finset V) : 0 ≤ H.vol U :=
  Finset.sum_nonneg fun x _ => H.deg_nonneg_aux x

omit [Fintype V] [DecidableEq V] in
/-- `t ↦ min t m` and `t ↦ max (t - m) 0` are comonotone and sum to `t`. -/
lemma abs_sub_eq_min_add_max (a b m : ℝ) :
    |a - b| = |min a m - min b m| + |max (a - m) 0 - max (b - m) 0| := by
  rw [abs_eq_max_neg, abs_eq_max_neg, abs_eq_max_neg]
  simp only [max_def, min_def]
  split_ifs <;> linarith

omit [Fintype V] [DecidableEq V] in
lemma sq_eq_pos_part_sq_add_neg_part_sq (a : ℝ) : a ^ 2 = max a 0 ^ 2 + max (-a) 0 ^ 2 := by
  simp only [max_def]
  split_ifs <;> nlinarith

omit [Fintype V] [DecidableEq V] in
lemma pos_neg_part_sq_le (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 + (max (-a) 0 - max (-b) 0) ^ 2 ≤ (a - b) ^ 2 := by
  simp only [max_def]
  split_ifs <;> nlinarith

lemma sum_eq_sum_add_sum_sdiff (S : Finset V) (F : V → ℝ) :
    ∑ x, F x = ∑ x ∈ S, F x + ∑ x ∈ univ \ S, F x := by
  rw [add_comm, Finset.sum_sdiff (subset_univ S)]

/-- The double sum of `a_{xy} |m 1_S(x) - m 1_S(y)|` is `2 m e(S, Sᶜ)`. -/
lemma sum_w_abs_ind (S : Finset V) {m : ℝ} (hm : 0 ≤ m) :
    ∑ x, ∑ y, H.w x y * |(if x ∈ S then m else 0) - (if y ∈ S then m else 0)| =
      2 * m * H.edgeWeight S (univ \ S) := by
  have h1 : ∀ x ∈ S, ∑ y, H.w x y * |(if x ∈ S then m else 0) - (if y ∈ S then m else 0)| =
      m * ∑ y ∈ univ \ S, H.w x y := by
    intro x hx
    rw [sum_eq_sum_add_sum_sdiff S, mul_sum]
    have h0 : ∑ y ∈ S, H.w x y * |(if x ∈ S then m else 0) - (if y ∈ S then m else 0)| = 0 :=
      sum_eq_zero fun y hy => by simp [hx, hy]
    rw [h0, zero_add]
    refine sum_congr rfl fun y hy => ?_
    have hy' : y ∉ S := (mem_sdiff.1 hy).2
    simp [hx, hy', abs_of_nonneg hm]
    ring
  have h2 : ∀ x ∈ univ \ S,
      ∑ y, H.w x y * |(if x ∈ S then m else 0) - (if y ∈ S then m else 0)| =
      m * ∑ y ∈ S, H.w x y := by
    intro x hx
    have hx' : x ∉ S := (mem_sdiff.1 hx).2
    rw [sum_eq_sum_add_sum_sdiff S, mul_sum]
    have h0 : ∑ y ∈ univ \ S,
        H.w x y * |(if x ∈ S then m else 0) - (if y ∈ S then m else 0)| = 0 :=
      sum_eq_zero fun y hy => by simp [hx', (mem_sdiff.1 hy).2]
    rw [h0, add_zero]
    refine sum_congr rfl fun y hy => ?_
    simp [hx', hy, abs_of_nonneg hm]
    ring
  have hsym : ∑ x ∈ univ \ S, ∑ y ∈ S, H.w x y = H.edgeWeight S (univ \ S) := by
    unfold edgeWeight
    rw [sum_comm]
    exact sum_congr rfl fun y _ => sum_congr rfl fun x _ => H.symm _ _
  rw [sum_eq_sum_add_sum_sdiff S, sum_congr rfl h1, sum_congr rfl h2, ← mul_sum, ← mul_sum,
    hsym]
  unfold edgeWeight
  ring

/-- **Discrete co-area inequality.** For `u ≥ 0` such that every set of vertices where `u` is
positive has conductance at least `φ`, `∑_{x,y} a_{xy} |u_x - u_y| ≥ 2 φ ∑_x d_x u_x`. -/
lemma coarea_aux (φ : ℝ) :
    ∀ (n : ℕ) (u : V → ℝ), (univ.filter (fun x => 0 < u x)).card ≤ n → (∀ x, 0 ≤ u x) →
      (∀ U : Finset V, (∀ x ∈ U, 0 < u x) → φ * H.vol U ≤ H.edgeWeight U (univ \ U)) →
      2 * φ * ∑ x, H.deg x * u x ≤ ∑ x, ∑ y, H.w x y * |u x - u y| := by
  have triv : ∀ u : V → ℝ, univ.filter (fun x => 0 < u x) = ∅ → (∀ x, 0 ≤ u x) →
      2 * φ * ∑ x, H.deg x * u x ≤ ∑ x, ∑ y, H.w x y * |u x - u y| := by
    intro u hS hu
    have h0 : ∀ x, u x = 0 := by
      intro x
      refine le_antisymm ?_ (hu x)
      by_contra hne
      have : x ∈ univ.filter (fun x => 0 < u x) := mem_filter.2 ⟨mem_univ _, not_le.1 hne⟩
      rw [hS] at this
      exact absurd this (notMem_empty x)
    simp [h0]
  intro n
  induction n with
  | zero =>
    intro u hcard hu _
    exact triv u (card_eq_zero.1 (Nat.le_zero.1 hcard)) hu
  | succ n ih =>
    intro u hcard hu hP
    rcases (univ.filter (fun x => 0 < u x)).eq_empty_or_nonempty with hSe | hSne
    · exact triv u hSe hu
    set S := univ.filter (fun x => 0 < u x) with hS
    obtain ⟨x0, hx0S, hx0min⟩ := S.exists_min_image u hSne
    have hm : 0 < u x0 := (mem_filter.1 hx0S).2
    set m := u x0 with hmdef
    set u' : V → ℝ := fun x => max (u x - m) 0 with hu'
    have hu'nn : ∀ x, 0 ≤ u' x := fun x => le_max_right _ _
    have hpos : ∀ x, 0 < u' x → m < u x := by
      intro x hx
      simp only [u', lt_max_iff, lt_irrefl, or_false] at hx
      linarith
    have hsub : univ.filter (fun x => 0 < u' x) ⊆ S.erase x0 := by
      intro x hx
      have hx' := hpos x (mem_filter.1 hx).2
      refine mem_erase.2 ⟨?_, mem_filter.2 ⟨mem_univ _, by linarith⟩⟩
      rintro rfl
      exact lt_irrefl _ hx'
    have hcard' : (univ.filter (fun x => 0 < u' x)).card ≤ n := by
      have h1 := card_le_card hsub
      rw [card_erase_of_mem hx0S] at h1
      omega
    have hP' : ∀ U : Finset V, (∀ x ∈ U, 0 < u' x) → φ * H.vol U ≤ H.edgeWeight U (univ \ U) :=
      fun U hU => hP U fun x hx => by linarith [hpos x (hU x hx)]
    have ih' := ih u' hcard' hu'nn hP'
    have hmin : ∀ x, min (u x) m = if x ∈ S then m else 0 := by
      intro x
      by_cases hx : x ∈ S
      · simp only [hx, ↓reduceIte]
        exact min_eq_right (hx0min x hx)
      · simp only [hx, ↓reduceIte]
        have hx0 : u x = 0 := le_antisymm (by simpa [S] using hx) (hu x)
        rw [hx0]
        exact min_eq_left hm.le
    have habs : ∀ x y, |u x - u y| =
        |(if x ∈ S then m else 0) - (if y ∈ S then m else 0)| + |u' x - u' y| := by
      intro x y
      rw [← hmin, ← hmin]
      exact abs_sub_eq_min_add_max _ _ _
    have hval : ∀ x, u x = (if x ∈ S then m else 0) + u' x := by
      intro x
      rw [← hmin]
      simp only [u']
      rcases le_total (u x) m with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]
        ring
      · rw [min_eq_right h, max_eq_left (by linarith)]
        ring
    have hRHS : ∑ x, ∑ y, H.w x y * |u x - u y| =
        2 * m * H.edgeWeight S (univ \ S) + ∑ x, ∑ y, H.w x y * |u' x - u' y| := by
      rw [← H.sum_w_abs_ind S hm.le, ← sum_add_distrib]
      refine sum_congr rfl fun x _ => ?_
      rw [← sum_add_distrib]
      refine sum_congr rfl fun y _ => ?_
      rw [habs]
      ring
    have hLHS : ∑ x, H.deg x * u x = m * H.vol S + ∑ x, H.deg x * u' x := by
      have e : ∑ x, H.deg x * (if x ∈ S then m else 0) = m * H.vol S := by
        simp only [mul_ite, mul_zero]
        rw [sum_ite_mem, univ_inter, ← sum_mul, vol]
        ring
      rw [← e, ← sum_add_distrib]
      refine sum_congr rfl fun x _ => ?_
      rw [hval x]
      ring
    have hcut := hP S fun x hx => (mem_filter.1 hx).2
    rw [hRHS, hLHS]
    have := mul_le_mul_of_nonneg_left hcut hm.le
    nlinarith

/-- Cheeger bound for a nonnegative function supported on at most half the volume. -/
lemma gap_of_nonneg_aux (φ : ℝ) (hφ : 0 ≤ φ)
    (hcond : ∀ U : Finset V, 2 * H.vol U ≤ H.vol univ →
      φ * H.vol U ≤ H.edgeWeight U (univ \ U))
    (h : V → ℝ) (hh : ∀ x, 0 ≤ h x)
    (hsupp : 2 * H.vol (univ.filter (fun x => 0 < h x)) ≤ H.vol univ) :
    φ ^ 2 / 2 * ∑ x, H.deg x * h x ^ 2 ≤ H.dirichlet h := by
  have hA : 2 * φ * ∑ x, H.deg x * h x ^ 2 ≤ ∑ x, ∑ y, H.w x y * |h x ^ 2 - h y ^ 2| := by
    refine H.coarea_aux φ _ (fun x => h x ^ 2) le_rfl (fun x => sq_nonneg _) ?_
    intro U hU
    apply hcond
    refine le_trans ?_ hsupp
    have : H.vol U ≤ H.vol (univ.filter (fun x => 0 < h x)) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        refine mem_filter.2 ⟨mem_univ _, ?_⟩
        have hx2 : 0 < h x ^ 2 := hU x hx
        rcases (hh x).lt_or_eq with h1 | h1
        · exact h1
        · rw [← h1] at hx2
          norm_num at hx2
      · intro x _ _
        exact H.deg_nonneg_aux x
    linarith
  have hCS : (∑ x, ∑ y, H.w x y * |h x ^ 2 - h y ^ 2|) ^ 2 ≤
      (∑ x, ∑ y, H.w x y * (h x - h y) ^ 2) * ∑ x, ∑ y, H.w x y * (h x + h y) ^ 2 := by
    have key := sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset (V × V))
      (r := fun p => H.w p.1 p.2 * |h p.1 ^ 2 - h p.2 ^ 2|)
      (f := fun p => H.w p.1 p.2 * (h p.1 - h p.2) ^ 2)
      (g := fun p => H.w p.1 p.2 * (h p.1 + h p.2) ^ 2)
      (fun p _ => mul_nonneg (H.nonneg _ _) (sq_nonneg _))
      (fun p _ => mul_nonneg (H.nonneg _ _) (sq_nonneg _))
      (fun p _ => le_of_eq (by rw [mul_pow, sq_abs]; ring))
    simpa only [Fintype.sum_prod_type] using key
  have ea : ∑ x, ∑ y, H.w x y * h x ^ 2 = ∑ x, H.deg x * h x ^ 2 := by
    refine sum_congr rfl fun x _ => ?_
    rw [deg, sum_mul]
  have eb : ∑ x, ∑ y, H.w x y * h y ^ 2 = ∑ x, H.deg x * h x ^ 2 := by
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [deg, sum_mul]
    exact sum_congr rfl fun x _ => by rw [H.symm]
  have hB : ∑ x, ∑ y, H.w x y * (h x + h y) ^ 2 ≤ 4 * ∑ x, H.deg x * h x ^ 2 := by
    calc ∑ x, ∑ y, H.w x y * (h x + h y) ^ 2
        ≤ ∑ x, ∑ y, (2 * (H.w x y * h x ^ 2) + 2 * (H.w x y * h y ^ 2)) :=
          sum_le_sum fun x _ => sum_le_sum fun y _ => by
            have := H.nonneg x y
            nlinarith [mul_nonneg this (sq_nonneg (h x - h y))]
      _ = 4 * ∑ x, H.deg x * h x ^ 2 := by
          simp only [sum_add_distrib, ← mul_sum, ea, eb]
          ring
  have hS : 0 ≤ ∑ x, H.deg x * h x ^ 2 :=
    sum_nonneg fun x _ => mul_nonneg (H.deg_nonneg_aux x) (sq_nonneg _)
  have hD : 0 ≤ ∑ x, ∑ y, H.w x y * (h x - h y) ^ 2 :=
    sum_nonneg fun x _ => sum_nonneg fun y _ => mul_nonneg (H.nonneg x y) (sq_nonneg _)
  unfold dirichlet
  generalize ∑ x, H.deg x * h x ^ 2 = S at hA hB hS ⊢
  generalize ∑ x, ∑ y, H.w x y * |h x ^ 2 - h y ^ 2| = A at hA hCS
  generalize ∑ x, ∑ y, H.w x y * (h x - h y) ^ 2 = D at hCS hD ⊢
  generalize ∑ x, ∑ y, H.w x y * (h x + h y) ^ 2 = B at hCS hB
  have h1 : (2 * φ * S) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (by positivity) hA 2
  have h2 : (2 * φ * S) ^ 2 ≤ D * (4 * S) :=
    h1.trans (hCS.trans (mul_le_mul_of_nonneg_left hB hD))
  rcases hS.lt_or_eq with hSpos | hS0
  · have h3 : S * (φ ^ 2 * S) ≤ S * D := by nlinarith
    have h4 : φ ^ 2 * S ≤ D := le_of_mul_le_mul_left h3 hSpos
    linarith
  · rw [← hS0]
    linarith

omit [DecidableEq V] in
/-- A degree-weighted median of `f`. -/
lemma exists_median (f : V → ℝ) :
    ∃ z : ℝ, 2 * H.vol (univ.filter (fun x => f x < z)) ≤ H.vol univ ∧
      2 * H.vol (univ.filter (fun x => z < f x)) ≤ H.vol univ := by
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨0, by simp [vol, univ_eq_empty], by simp [vol, univ_eq_empty]⟩
  set C := univ.filter (fun x => H.vol univ ≤ 2 * H.vol (univ.filter (fun y => f y ≤ f x)))
    with hC
  have hCne : C.Nonempty := by
    obtain ⟨x1, -, hx1⟩ := (univ : Finset V).exists_max_image f univ_nonempty
    refine ⟨x1, mem_filter.2 ⟨mem_univ _, ?_⟩⟩
    have e : univ.filter (fun y => f y ≤ f x1) = univ :=
      filter_true_of_mem fun y _ => hx1 y (mem_univ _)
    rw [e]
    linarith [H.vol_nonneg_aux univ]
  obtain ⟨x0, hx0C, hx0min⟩ := C.exists_min_image f hCne
  refine ⟨f x0, ?_, ?_⟩
  · by_contra hlt
    replace hlt := not_le.1 hlt
    rcases (univ.filter (fun x => f x < f x0)).eq_empty_or_nonempty with hLe | hLne
    · have h0 : H.vol ∅ = 0 := sum_empty
      rw [hLe, h0] at hlt
      linarith [H.vol_nonneg_aux univ]
    obtain ⟨x1, hx1L, hx1max⟩ := (univ.filter (fun x => f x < f x0)).exists_max_image f hLne
    have hx1lt : f x1 < f x0 := (mem_filter.1 hx1L).2
    have heq : univ.filter (fun y => f y ≤ f x1) = univ.filter (fun x => f x < f x0) := by
      ext y
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro hy
        exact lt_of_le_of_lt hy hx1lt
      · intro hy
        exact hx1max y (mem_filter.2 ⟨mem_univ _, hy⟩)
    have hx1C : x1 ∈ C := mem_filter.2 ⟨mem_univ _, by rw [heq]; linarith⟩
    have := hx0min x1 hx1C
    linarith
  · have hC0 := (mem_filter.1 hx0C).2
    have hsplit := sum_filter_add_sum_filter_not univ (fun y => f y ≤ f x0) H.deg
    simp only [not_le] at hsplit
    unfold vol at hC0 ⊢
    linarith

end CheegerAux

/-- **Normalized Cheeger inequality.** If every vertex set `U` with
`vol(U) ≤ vol(V) / 2` has `e_H(U, Uᶜ) ≥ φ vol(U)` (conductance `Φ(H) ≥ φ`) and all degrees are
positive, then the normalized upper gap is at least `φ² / 2`. -/
theorem hasGap_of_conductance (H : WGraph V) (φ : ℝ) (hφ : 0 ≤ φ) (hdeg : ∀ x, 0 < H.deg x)
    (hcond : ∀ U : Finset V, 2 * H.vol U ≤ H.vol univ →
      φ * H.vol U ≤ H.edgeWeight U (univ \ U)) :
    H.HasGap (φ ^ 2 / 2) := by
  intro f
  obtain ⟨z, hz1, hz2⟩ := H.exists_median f
  refine ⟨z, ?_⟩
  have hp := H.gap_of_nonneg_aux φ hφ hcond (fun x => max (f x - z) 0)
    (fun x => le_max_right _ _) (by
      have e : univ.filter (fun x => 0 < max (f x - z) 0) = univ.filter (fun x => z < f x) := by
        ext x
        simp only [mem_filter, mem_univ, true_and, lt_max_iff, lt_irrefl, or_false, sub_pos]
      rw [e]
      exact hz2)
  have hq := H.gap_of_nonneg_aux φ hφ hcond (fun x => max (-(f x - z)) 0)
    (fun x => le_max_right _ _) (by
      have e : univ.filter (fun x => 0 < max (-(f x - z)) 0) =
          univ.filter (fun x => f x < z) := by
        ext x
        simp only [mem_filter, mem_univ, true_and, lt_max_iff, lt_irrefl, or_false, neg_sub,
          sub_pos]
      rw [e]
      exact hz1)
  have hdir : H.dirichlet (fun x => max (f x - z) 0) + H.dirichlet (fun x => max (-(f x - z)) 0)
      ≤ H.dirichlet f := by
    unfold dirichlet
    rw [← add_div, ← sum_add_distrib]
    refine div_le_div_of_nonneg_right (sum_le_sum fun x _ => ?_) (by norm_num)
    rw [← sum_add_distrib]
    refine sum_le_sum fun y _ => ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (H.nonneg x y)
    have := pos_neg_part_sq_le (f x - z) (f y - z)
    have e : f x - z - (f y - z) = f x - f y := by ring
    rw [e] at this
    exact this
  calc φ ^ 2 / 2 * ∑ x, H.deg x * (f x - z) ^ 2
      = φ ^ 2 / 2 * ∑ x, H.deg x * max (f x - z) 0 ^ 2 +
          φ ^ 2 / 2 * ∑ x, H.deg x * max (-(f x - z)) 0 ^ 2 := by
        rw [← mul_add, ← sum_add_distrib]
        congr 1
        exact sum_congr rfl fun x _ => by rw [sq_eq_pos_part_sq_add_neg_part_sq (f x - z), mul_add]
    _ ≤ _ := add_le_add hp hq
    _ ≤ H.dirichlet f := hdir

end WGraph

end Lovasz
