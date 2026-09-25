/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 2.5: robust Hall

DAG node `L2.5` of `docs/BLUEPRINT.md`. Uses Hall's theorem (Mathlib:
`Finset.all_card_le_biUnion_card_iff_exists_injective`).
-/

namespace Lovasz

open Finset

namespace RobustHall

variable {V : Type*} (H : WGraph V)

lemma eW_union_left [DecidableEq V] {A B : Finset V} (C : Finset V) (h : Disjoint A B) :
    H.edgeWeight (A ∪ B) C = H.edgeWeight A C + H.edgeWeight B C := by
  unfold WGraph.edgeWeight; exact sum_union h

lemma eW_union_right [DecidableEq V] (A : Finset V) {B C : Finset V} (h : Disjoint B C) :
    H.edgeWeight A (B ∪ C) = H.edgeWeight A B + H.edgeWeight A C := by
  unfold WGraph.edgeWeight
  rw [← sum_add_distrib]
  exact sum_congr rfl fun _ _ => sum_union h

lemma eW_comm (A B : Finset V) : H.edgeWeight A B = H.edgeWeight B A := by
  unfold WGraph.edgeWeight
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => H.symm _ _

lemma eW_zero {A B : Finset V} (h : ∀ a ∈ A, ∀ b ∈ B, H.w a b = 0) :
    H.edgeWeight A B = 0 := by
  unfold WGraph.edgeWeight
  exact sum_eq_zero fun a ha => sum_eq_zero fun b hb => h a ha b hb

lemma eW_mono_right (A : Finset V) {B C : Finset V} (h : B ⊆ C) :
    H.edgeWeight A B ≤ H.edgeWeight A C := by
  unfold WGraph.edgeWeight
  exact sum_le_sum fun _ _ => sum_le_sum_of_subset_of_nonneg h fun _ _ _ => H.nonneg _ _

lemma eW_le_of_deg_le {A B : Finset V} {c : ℝ} (h : ∀ a ∈ A, H.degOn a B ≤ c) :
    H.edgeWeight A B ≤ A.card * c := by
  calc H.edgeWeight A B = ∑ a ∈ A, H.degOn a B := rfl
    _ ≤ ∑ _a ∈ A, c := sum_le_sum h
    _ = A.card * c := by rw [sum_const, nsmul_eq_mul]

lemma le_eW_of_le_deg {A B : Finset V} {c : ℝ} (h : ∀ a ∈ A, c ≤ H.degOn a B) :
    A.card * c ≤ H.edgeWeight A B := by
  calc (A.card : ℝ) * c = ∑ _a ∈ A, c := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ A, H.degOn a B := sum_le_sum h
    _ = H.edgeWeight A B := rfl

/-- The numerical heart of Lemma 2.5: with `h = r - s`, the inequality
`α (2s + h) ≤ (1 + η) h + 2 η s` gives `h ≥ α s ≥ 0`, and then `x ≤ (α / 10)(h + s) ≤ h`. -/
lemma arith (s r x α η : ℝ) (hs0 : 0 ≤ s) (hα : 0 < α) (hα' : α ≤ 1 / 2) (hη0 : 0 ≤ η)
    (hη : η ≤ α / 10) (hK : (s + r) * α ≤ r * (1 + η) - s * (1 - η))
    (hXb : x ≤ r * α / 10) : x ≤ r - s := by
  have hαη : 0 ≤ α - η := by linarith
  have hh : 0 ≤ r - s := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_nonneg hs0 hαη, mul_pos (show 0 < s - r by linarith)
      (show 0 < 1 + η - α by linarith)]
  have h18 : 18 / 10 * α * s ≤ r - s := by
    nlinarith [mul_nonneg hs0 (show 0 ≤ α / 10 - η by linarith), mul_nonneg hh hαη]
  nlinarith [mul_nonneg hh (show 0 ≤ 1 / 2 - α by linarith)]

/-- The one-sided core of Lemma 2.5: if `S ⊆ L₀`, `T ⊆ R₀` with `|S| ≤ |T|` and `Sx ⊆ X`, and
neither `S` nor `Sx` sends support edges into `T`, then `|Sx| + |S| + |T| ≤ m`. This combines
(2.10) (for `s ≤ t`) with the edge count from `Sx` into `R₀ \ T`. -/
lemma core [DecidableEq V] (L₀ R₀ X : Finset V) (m : ℕ) (D₀ η ξ : ℝ)
    (hLR : Disjoint L₀ R₀) (hL : L₀.card = m) (hR : R₀.card = m)
    (hbipL : ∀ x ∈ L₀, ∀ y ∈ L₀, H.w x y = 0) (hbipR : ∀ x ∈ R₀, ∀ y ∈ R₀, H.w x y = 0)
    (hD₀ : 0 < D₀)
    (hdegL : ∀ v ∈ L₀, |H.degOn v R₀ - D₀| ≤ η * D₀)
    (hdegR : ∀ v ∈ R₀, |H.degOn v L₀ - D₀| ≤ η * D₀)
    (hcut : ∀ A ⊆ L₀ ∪ R₀, ξ * A.card * ((L₀ ∪ R₀) \ A).card ≤ H.edgeWeight A ((L₀ ∪ R₀) \ A))
    (hα : 0 < ξ * m / D₀) (hα' : ξ * m / D₀ ≤ 1 / 2) (hη : η ≤ ξ * m / D₀ / 10)
    (hX : ∀ x ∈ X, D₀ / 2 ≤ H.degOn x R₀)
    (hRX' : ∀ v ∈ R₀, H.degOn v X ≤ ξ * m / D₀ * D₀ / 20)
    (S T Sx : Finset V) (hS : S ⊆ L₀) (hT : T ⊆ R₀) (hSx : Sx ⊆ X)
    (hST : ∀ a ∈ S, ∀ b ∈ T, H.w a b = 0) (hSxT : ∀ a ∈ Sx, ∀ b ∈ T, H.w a b = 0)
    (hst : S.card ≤ T.card) : Sx.card + S.card + T.card ≤ m := by
  set α := ξ * m / D₀ with hαdef
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [hαdef, h] at hα
    · exact h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hαD : α * D₀ = ξ * m := div_mul_cancel₀ _ hD₀.ne'
  have hξ : 0 < ξ := by
    have h1 : 0 < ξ * m := by rw [← hαD]; exact mul_pos hα hD₀
    exact pos_of_mul_pos_left h1 hmR.le
  have hη0 : 0 ≤ η := by
    obtain ⟨v, hv⟩ : L₀.Nonempty := by rw [← card_pos, hL]; exact hm
    have h1 := (abs_nonneg _).trans (hdegL v hv)
    exact nonneg_of_mul_nonneg_left h1 hD₀
  -- cardinalities
  have hTR : (R₀ \ T).card + T.card = m := by rw [card_sdiff_add_card_eq_card hT, hR]
  have hSL : (L₀ \ S).card + S.card = m := by rw [card_sdiff_add_card_eq_card hS, hL]
  -- the set `Z = S ∪ (R₀ \ T)` and its complement in `L₀ ∪ R₀`
  have hZsub : S ∪ (R₀ \ T) ⊆ L₀ ∪ R₀ := union_subset_union hS sdiff_subset
  have hZc : (L₀ ∪ R₀) \ (S ∪ (R₀ \ T)) = (L₀ \ S) ∪ T := by
    ext v
    have h1 := @hS v
    have h2 := @hT v
    have h3 : v ∈ L₀ → v ∉ R₀ := fun h => disjoint_left.mp hLR h
    simp only [mem_sdiff, mem_union]
    tauto
  have hdisjZ : Disjoint S (R₀ \ T) :=
    disjoint_of_subset_left hS (disjoint_of_subset_right sdiff_subset hLR)
  have hdisjZc : Disjoint (L₀ \ S) T :=
    disjoint_of_subset_left sdiff_subset (disjoint_of_subset_right hT hLR)
  have hcardZ : (S ∪ (R₀ \ T)).card = S.card + (R₀ \ T).card := card_union_of_disjoint hdisjZ
  have hcardZc : ((L₀ ∪ R₀) \ (S ∪ (R₀ \ T))).card = (L₀ \ S).card + T.card := by
    rw [hZc]; exact card_union_of_disjoint hdisjZc
  -- edge-weight bookkeeping
  have hE : H.edgeWeight (S ∪ (R₀ \ T)) ((L₀ ∪ R₀) \ (S ∪ (R₀ \ T))) =
      H.edgeWeight (R₀ \ T) (L₀ \ S) := by
    rw [hZc, eW_union_left H _ hdisjZ, eW_union_right H _ hdisjZc, eW_union_right H _ hdisjZc,
      eW_zero H (A := S) (B := L₀ \ S) (fun a ha b hb => hbipL a (hS ha) b (sdiff_subset hb)),
      eW_zero H (A := S) (B := T) hST,
      eW_zero H (A := R₀ \ T) (B := T) (fun a ha b hb => hbipR a (sdiff_subset ha) b (hT hb))]
    ring
  have hE2 : H.edgeWeight (R₀ \ T) L₀ =
      H.edgeWeight (R₀ \ T) (L₀ \ S) + H.edgeWeight (R₀ \ T) S := by
    rw [← eW_union_right H _ sdiff_disjoint, sdiff_union_of_subset hS]
  have hE3 : H.edgeWeight S R₀ = H.edgeWeight S (R₀ \ T) + H.edgeWeight S T := by
    rw [← eW_union_right H _ sdiff_disjoint, sdiff_union_of_subset hT]
  have hE4 : H.edgeWeight Sx R₀ = H.edgeWeight Sx (R₀ \ T) + H.edgeWeight Sx T := by
    rw [← eW_union_right H _ sdiff_disjoint, sdiff_union_of_subset hT]
  have hST0 : H.edgeWeight S T = 0 := eW_zero H hST
  have hSxT0 : H.edgeWeight Sx T = 0 := eW_zero H hSxT
  have hcommS : H.edgeWeight (R₀ \ T) S = H.edgeWeight S (R₀ \ T) := eW_comm H _ _
  have hcommSx : H.edgeWeight Sx (R₀ \ T) = H.edgeWeight (R₀ \ T) Sx := eW_comm H _ _
  have hup : H.edgeWeight (R₀ \ T) L₀ ≤ (R₀ \ T).card * ((1 + η) * D₀) :=
    eW_le_of_deg_le H fun a ha => by
      have := (abs_le.mp (hdegR a (sdiff_subset ha))).2; linarith
  have hlow : S.card * ((1 - η) * D₀) ≤ H.edgeWeight S R₀ :=
    le_eW_of_le_deg H fun a ha => by
      have := (abs_le.mp (hdegL a (hS ha))).1; linarith
  have hxlow : Sx.card * (D₀ / 2) ≤ H.edgeWeight Sx R₀ :=
    le_eW_of_le_deg H fun a ha => hX a (hSx ha)
  have hxup : H.edgeWeight (R₀ \ T) Sx ≤ (R₀ \ T).card * (α * D₀ / 20) :=
    (eW_mono_right H _ hSx).trans (eW_le_of_deg_le H fun a ha => hRX' a (sdiff_subset ha))
  have hcutZ := hcut _ hZsub
  rw [hE, hcardZ, hcardZc] at hcutZ
  -- pass to real arithmetic
  set s : ℝ := (S.card : ℝ) with hs
  set t : ℝ := (T.card : ℝ) with ht
  set r : ℝ := ((R₀ \ T).card : ℝ) with hr
  set l : ℝ := ((L₀ \ S).card : ℝ) with hl
  set x : ℝ := (Sx.card : ℝ) with hx
  have hTR' : r + t = m := by rw [hr, ht]; exact_mod_cast hTR
  have hSL' : l + s = m := by rw [hl, hs]; exact_mod_cast hSL
  have hst' : s ≤ t := by rw [hs, ht]; exact_mod_cast hst
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  push_cast at hcutZ
  -- (2.10)-type inequality, before dividing by `D₀`
  have hK0 : (s + r) * α * D₀ ≤ (r * (1 + η) - s * (1 - η)) * D₀ := by
    have h1 : ξ * (s + r) * m ≤ ξ * (s + r) * (l + t) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hξ.le (by linarith))
    have h2 : (s + r) * α * D₀ = ξ * (s + r) * m := by rw [mul_assoc, hαD]; ring
    linarith
  have hK : (s + r) * α ≤ r * (1 + η) - s * (1 - η) := le_of_mul_le_mul_right hK0 hD₀
  have hX0 : x * D₀ ≤ (r * α / 10) * D₀ := by linarith
  have hXb : x ≤ r * α / 10 := le_of_mul_le_mul_right hX0 hD₀
  have hfin : x ≤ r - s := arith s r x α η hs0 hα hα' hη0 hη hK hXb
  have : (Sx.card : ℝ) + S.card + T.card ≤ m := by linarith
  exact_mod_cast this

end RobustHall

/-- **Lemma 2.5 (Robust Hall).** Let `H₀` be the bipartite weighted graph between `L₀, R₀`
(each of size `m`) with degrees `(1 ± η) D₀` and cut-density `ξ`; put `α = ξ m / D₀` with
`0 < α ≤ 1/2` and `η ≤ α / 10`. Add sets `X, Y` of equal size to the two classes, each added
vertex having at least `D₀ / 2` weighted neighbours in the opposite old class and each old
vertex at most `α D₀ / 20` weighted neighbours in the opposite added class. Then the support of
the enlarged bipartite graph between `L₀ ∪ X` and `R₀ ∪ Y` has a perfect matching. -/
theorem robust_hall {V : Type*} [DecidableEq V] (H : WGraph V)
    (L₀ R₀ X Y : Finset V) (m : ℕ) (D₀ η ξ : ℝ)
    (hLR : Disjoint L₀ R₀) (hLX : Disjoint L₀ X) (hLY : Disjoint L₀ Y) (hRX : Disjoint R₀ X)
    (hRY : Disjoint R₀ Y) (hXY : Disjoint X Y)
    (hL : L₀.card = m) (hR : R₀.card = m) (hcardXY : X.card = Y.card)
    (hbipL : ∀ x ∈ L₀, ∀ y ∈ L₀, H.w x y = 0) (hbipR : ∀ x ∈ R₀, ∀ y ∈ R₀, H.w x y = 0)
    (hD₀ : 0 < D₀)
    (hdegL : ∀ v ∈ L₀, |H.degOn v R₀ - D₀| ≤ η * D₀)
    (hdegR : ∀ v ∈ R₀, |H.degOn v L₀ - D₀| ≤ η * D₀)
    (hcut : ∀ A ⊆ L₀ ∪ R₀, ξ * A.card * ((L₀ ∪ R₀) \ A).card ≤ H.edgeWeight A ((L₀ ∪ R₀) \ A))
    (hα : 0 < ξ * m / D₀) (hα' : ξ * m / D₀ ≤ 1 / 2) (hη : η ≤ ξ * m / D₀ / 10)
    (hX : ∀ x ∈ X, D₀ / 2 ≤ H.degOn x R₀) (hY : ∀ y ∈ Y, D₀ / 2 ≤ H.degOn y L₀)
    (hLY' : ∀ v ∈ L₀, H.degOn v Y ≤ ξ * m / D₀ * D₀ / 20)
    (hRX' : ∀ v ∈ R₀, H.degOn v X ≤ ξ * m / D₀ * D₀ / 20) :
    ∃ f : (L₀ ∪ X : Finset V) → V, Function.Injective f ∧ (∀ x, f x ∈ R₀ ∪ Y) ∧
      ∀ x : (L₀ ∪ X : Finset V), 0 < H.w x (f x) := by
  -- support neighbourhoods in `R₀ ∪ Y`
  let nb : (L₀ ∪ X : Finset V) → Finset V := fun a => (R₀ ∪ Y).filter (fun b => 0 < H.w a b)
  suffices hall : ∀ s : Finset (L₀ ∪ X : Finset V), s.card ≤ (s.biUnion nb).card by
    obtain ⟨f, hf, hfnb⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' nb).mp hall
    exact ⟨f, hf, fun a => (mem_filter.mp (hfnb a)).1, fun a => (mem_filter.mp (hfnb a)).2⟩
  intro s
  by_contra hlt
  push Not at hlt
  -- a Hall violator `S'` and the set `T'` of its non-neighbours
  set S' : Finset V := s.map (Function.Embedding.subtype _) with hS'
  set N : Finset V := s.biUnion nb with hN
  set T' : Finset V := (R₀ ∪ Y) \ N with hT'
  have hS'sub : S' ⊆ L₀ ∪ X := by
    intro a ha
    obtain ⟨a', -, rfl⟩ := mem_map.mp ha
    exact a'.2
  have hS'card : S'.card = s.card := card_map _
  have hNsub : N ⊆ R₀ ∪ Y := biUnion_subset.mpr fun a _ => filter_subset _ _
  have hT'card : T'.card + N.card = m + Y.card := by
    rw [card_sdiff_add_card_eq_card hNsub, card_union_of_disjoint hRY, hR]
  have hT'sub : T' ⊆ R₀ ∪ Y := sdiff_subset
  have hedge : ∀ a ∈ S', ∀ b ∈ T', H.w a b = 0 := by
    intro a ha b hb
    obtain ⟨a', ha's, rfl⟩ := mem_map.mp ha
    have hb1 := mem_sdiff.mp hb
    have hnb : b ∉ nb a' := fun hbt => hb1.2 (mem_biUnion.mpr ⟨a', ha's, hbt⟩)
    simp only [nb, mem_filter, not_and, not_lt] at hnb
    exact le_antisymm (hnb hb1.1) (H.nonneg _ _)
  -- split `S'` and `T'` into old and added parts
  have hS'split : (S' ∩ L₀).card + (S' ∩ X).card = S'.card := by
    rw [← card_union_of_disjoint (disjoint_of_subset_left inter_subset_right
      (disjoint_of_subset_right inter_subset_right hLX)), ← inter_union_distrib_left,
      inter_eq_left.mpr hS'sub]
  have hT'split : (T' ∩ R₀).card + (T' ∩ Y).card = T'.card := by
    rw [← card_union_of_disjoint (disjoint_of_subset_left inter_subset_right
      (disjoint_of_subset_right inter_subset_right hRY)), ← inter_union_distrib_left,
      inter_eq_left.mpr hT'sub]
  have hSx : (S' ∩ X).card ≤ X.card := card_le_card inter_subset_right
  have hTy : (T' ∩ Y).card ≤ Y.card := card_le_card inter_subset_right
  rcases le_total (S' ∩ L₀).card (T' ∩ R₀).card with hst | hts
  · have := RobustHall.core H L₀ R₀ X m D₀ η ξ hLR hL hR hbipL hbipR hD₀ hdegL hdegR hcut
      hα hα' hη hX hRX' (S' ∩ L₀) (T' ∩ R₀) (S' ∩ X) inter_subset_right inter_subset_right
      inter_subset_right
      (fun a ha b hb => hedge a (inter_subset_left ha) b (inter_subset_left hb))
      (fun a ha b hb => hedge a (inter_subset_left ha) b (inter_subset_left hb)) hst
    omega
  · have hcut' : ∀ A ⊆ R₀ ∪ L₀,
        ξ * A.card * ((R₀ ∪ L₀) \ A).card ≤ H.edgeWeight A ((R₀ ∪ L₀) \ A) := by
      intro A hA
      rw [union_comm R₀ L₀] at hA ⊢
      exact hcut A hA
    have := RobustHall.core H R₀ L₀ Y m D₀ η ξ hLR.symm hR hL hbipR hbipL hD₀ hdegR hdegL hcut'
      hα hα' hη hY hLY' (T' ∩ R₀) (S' ∩ L₀) (T' ∩ Y) inter_subset_right inter_subset_right
      inter_subset_right
      (fun a ha b hb => by
        rw [H.symm]; exact hedge b (inter_subset_left hb) a (inter_subset_left ha))
      (fun a ha b hb => by
        rw [H.symm]; exact hedge b (inter_subset_left hb) a (inter_subset_left ha))
      hts
    omega

end Lovasz
