/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.ColumnSampling
import Lovasz.Chernoff
import Lovasz.Perturbation

/-!
# Lemma 2.3: bipartite sampling

DAG node `L2.3` of `docs/BLUEPRINT.md`.

With `F = K - d_A d_Bᵀ / e` (`K` the biadjacency matrix, `e` the total weight), the variational
gap gives `‖F‖ ≤ (1 - σ)(1 + η) D` (`spectral_bound`). Two applications of Lemma 2.2 (rows, then
columns) and scalar Chernoff bounds control `‖F[U, W]‖` and all sampled degrees outside five bad
events (`bad1`–`bad5`). The gap of the sample then follows from `gap_suff`: if the weights between
`U` and `W` are `Fm + λ p qᵀ` with `λ ≥ 0` and `‖Fm‖ ≤ β`, shifting a test function so that
`pᵀx + qᵀy = 0` makes the rank-one term nonpositive in the energy, so the gap is at least
`(δ₁ - β) / δ₂` for degrees in `[δ₁, δ₂]`. The lower weight bound `ω` is not needed.
-/

universe u

namespace Lovasz

open Finset

namespace BipSampling

variable {V : Type u}

/-! ### Transferring the sampling lemmas from `Fin` to finsets -/

/-- The embedding `Fin #S ↪ V` enumerating `S`. -/
noncomputable def enum (S : Finset V) : Fin S.card ↪ V :=
  S.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)

lemma enum_mem (S : Finset V) (j : Fin S.card) : enum S j ∈ S := (S.equivFin.symm j).2

lemma univ_map_enum (S : Finset V) : (univ : Finset (Fin S.card)).map (enum S) = S := by
  ext x
  simp only [mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact enum_mem S j
  · intro hx
    exact ⟨S.equivFin ⟨x, hx⟩, by simp [enum]⟩

lemma sum_enum (S : Finset V) (g : V → ℝ) :
    ∑ j : Fin S.card, g (enum S j) = ∑ j ∈ S, g j := by
  have h := sum_map (univ : Finset (Fin S.card)) (enum S) g
  rw [univ_map_enum] at h
  exact h.symm

lemma card_filter_powersetCard_le (S : Finset V) (k : ℕ) (P : Finset V → Prop)
    [DecidablePred P] (Q : Finset (Fin S.card) → Prop) [DecidablePred Q]
    (hPQ : ∀ I, P (I.map (enum S)) → Q I) :
    ((S.powersetCard k).filter P).card ≤
      (((univ : Finset (Fin S.card)).powersetCard k).filter Q).card := by
  have h := powersetCard_map (enum S) k univ
  rw [univ_map_enum] at h
  rw [h, filter_map, card_map]
  refine card_le_card fun I => ?_
  simp only [mem_filter, Function.comp_apply]
  exact fun hI => ⟨hI.1, hPQ I hI.2⟩

open Classical in
/-- The universal statement of Lemma 2.2 for a given constant. -/
def ColSampProp (C : ℝ) : Prop :=
  ∀ {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (a c : ℝ),
      (∀ v : Fin s → ℝ, ∑ i, (∑ j, F i j * v j) ^ 2 ≤ a ^ 2 * ∑ j, v j ^ 2) →
      (∀ j, ∑ i, F i j ^ 2 ≤ c ^ 2) → 0 ≤ a → 0 ≤ c →
      ∀ k : ℕ, k ≤ s → ∀ t : ℝ, 0 < t →
        ((((univ : Finset (Fin s)).powersetCard k).filter fun I => ∃ v : Fin s → ℝ,
            (Real.sqrt ((k : ℝ) / s) * a + C * c * Real.sqrt t) ^ 2 * ∑ j ∈ I, v j ^ 2 <
              ∑ i, (∑ j ∈ I, F i j * v j) ^ 2).card : ℝ) ≤
          r * (s + 1) * Real.exp (-t) * s.choose k

lemma exists_colSampProp : ∃ C : ℝ, 0 < C ∧ ColSampProp C := column_sampling

open Classical in
/-- Lemma 2.2 for a matrix with rows `R` and columns `S` indexed by finsets of `V`. -/
lemma column_sampling_finset {C : ℝ} (hC : ColSampProp C) (R S : Finset V) (G : V → V → ℝ)
    (a c : ℝ)
    (ha : ∀ v : V → ℝ, ∑ i ∈ R, (∑ j ∈ S, G i j * v j) ^ 2 ≤ a ^ 2 * ∑ j ∈ S, v j ^ 2)
    (hc : ∀ j ∈ S, ∑ i ∈ R, G i j ^ 2 ≤ c ^ 2) (ha0 : 0 ≤ a) (hc0 : 0 ≤ c)
    (k : ℕ) (hk : k ≤ S.card) (t : ℝ) (ht : 0 < t) :
    (((S.powersetCard k).filter fun W => ∃ v : V → ℝ,
        (Real.sqrt ((k : ℝ) / S.card) * a + C * c * Real.sqrt t) ^ 2 * ∑ j ∈ W, v j ^ 2 <
          ∑ i ∈ R, (∑ j ∈ W, G i j * v j) ^ 2).card : ℝ) ≤
      R.card * (S.card + 1) * Real.exp (-t) * S.card.choose k := by
  unfold ColSampProp at hC
  set F : Matrix (Fin R.card) (Fin S.card) ℝ := fun i j => G (enum R i) (enum S j) with hF
  have hext : ∀ v' : Fin S.card → ℝ, ∃ v : V → ℝ, ∀ j, v (enum S j) = v' j := by
    intro v'
    refine ⟨fun x => if h : x ∈ S then v' (S.equivFin ⟨x, h⟩) else 0, fun j => ?_⟩
    simp [enum]
  have haF : ∀ v' : Fin S.card → ℝ,
      ∑ i, (∑ j, F i j * v' j) ^ 2 ≤ a ^ 2 * ∑ j, v' j ^ 2 := by
    intro v'
    obtain ⟨v, hv⟩ := hext v'
    have h1 : ∀ i, ∑ j, F i j * v' j = ∑ j ∈ S, G (enum R i) j * v j := by
      intro i
      rw [← sum_enum S]
      exact sum_congr rfl fun j _ => by rw [hv]
    have h2 : ∑ j, v' j ^ 2 = ∑ j ∈ S, v j ^ 2 := by
      rw [← sum_enum S]
      exact sum_congr rfl fun j _ => by rw [hv]
    simp_rw [h1, h2]
    rw [sum_enum R (fun i => (∑ j ∈ S, G i j * v j) ^ 2)]
    exact ha v
  have hcF : ∀ j, ∑ i, F i j ^ 2 ≤ c ^ 2 := by
    intro j
    rw [sum_enum R (fun i => G i (enum S j) ^ 2)]
    exact hc _ (enum_mem S j)
  refine le_trans (Nat.cast_le.2 (card_filter_powersetCard_le S k _ _ ?_))
    (hC F a c haF hcF ha0 hc0 k hk t ht)
  rintro I ⟨v, hv⟩
  refine ⟨fun j => v (enum S j), ?_⟩
  rw [sum_map] at hv
  simp_rw [sum_map] at hv
  rw [← sum_enum R (fun i => (∑ j ∈ I, G i (enum S j) * v (enum S j)) ^ 2)] at hv
  exact hv

open Classical in
/-- Sampling without replacement (upper tail) for a uniform `k`-subset of a finset. -/
lemma hyp_upper_finset (S : Finset V) (g : V → ℝ) (hg : ∀ j ∈ S, 0 ≤ g j ∧ g j ≤ 1) (k : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    (((S.powersetCard k).filter fun W =>
        (k : ℝ) / S.card * ∑ j ∈ S, g j + t ≤ ∑ j ∈ W, g j).card : ℝ) ≤
      Real.exp (-(t ^ 2) / (2 * ((k : ℝ) / S.card * ∑ j ∈ S, g j + t / 3))) *
        S.card.choose k := by
  have h := hypergeometric_upper (fun j : Fin S.card => g (enum S j))
    (fun j => hg _ (enum_mem S j)) k t ht
  rw [Fintype.card_fin, sum_enum S g] at h
  refine le_trans (Nat.cast_le.2 (card_filter_powersetCard_le S k _ _ ?_)) h
  intro I hI
  rwa [sum_map] at hI

open Classical in
/-- Sampling without replacement (lower tail) for a uniform `k`-subset of a finset. -/
lemma hyp_lower_finset (S : Finset V) (g : V → ℝ) (hg : ∀ j ∈ S, 0 ≤ g j ∧ g j ≤ 1) (k : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    (((S.powersetCard k).filter fun W =>
        ∑ j ∈ W, g j ≤ (k : ℝ) / S.card * ∑ j ∈ S, g j - t).card : ℝ) ≤
      Real.exp (-(t ^ 2) / (2 * ((k : ℝ) / S.card * ∑ j ∈ S, g j))) * S.card.choose k := by
  have h := hypergeometric_lower (fun j : Fin S.card => g (enum S j))
    (fun j => hg _ (enum_mem S j)) k t ht
  rw [Fintype.card_fin, sum_enum S g] at h
  refine le_trans (Nat.cast_le.2 (card_filter_powersetCard_le S k _ _ ?_)) h
  intro I hI
  rwa [sum_map] at hI

/-! ### Bilinear and operator bounds -/

lemma two_mul_le_of_sq_le {s β X Y : ℝ} (h : s ^ 2 ≤ β ^ 2 * (X * Y)) (hβ : 0 ≤ β)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) : 2 * s ≤ β * (X + Y) := by
  have h1 : (2 * s) ^ 2 ≤ (β * (X + Y)) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg β) (sq_nonneg (X - Y))]
  exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq h1 (mul_nonneg hβ (add_nonneg hX hY)))

/-- An operator bound gives a bilinear bound. -/
lemma bil_of_op (R S : Finset V) (G : V → V → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (h : ∀ y : V → ℝ, ∑ i ∈ R, (∑ j ∈ S, G i j * y j) ^ 2 ≤ β ^ 2 * ∑ j ∈ S, y j ^ 2)
    (x y : V → ℝ) :
    2 * ∑ i ∈ R, ∑ j ∈ S, x i * G i j * y j ≤ β * (∑ i ∈ R, x i ^ 2 + ∑ j ∈ S, y j ^ 2) := by
  have e : ∑ i ∈ R, ∑ j ∈ S, x i * G i j * y j = ∑ i ∈ R, x i * (∑ j ∈ S, G i j * y j) := by
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [e]
  have cs := sum_mul_sq_le_sq_mul_sq R x (fun i => ∑ j ∈ S, G i j * y j)
  refine two_mul_le_of_sq_le ?_ hβ (sum_nonneg fun i _ => sq_nonneg _)
    (sum_nonneg fun j _ => sq_nonneg _)
  calc _ ≤ _ := cs
    _ ≤ (∑ i ∈ R, x i ^ 2) * (β ^ 2 * ∑ j ∈ S, y j ^ 2) :=
        mul_le_mul_of_nonneg_left (h y) (sum_nonneg fun i _ => sq_nonneg _)
    _ = _ := by ring

/-- A bilinear bound gives an operator bound. -/
lemma op_of_bil (R S : Finset V) (G : V → V → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ x y : V → ℝ, 2 * ∑ i ∈ R, ∑ j ∈ S, x i * G i j * y j ≤
      M * (∑ i ∈ R, x i ^ 2 + ∑ j ∈ S, y j ^ 2)) (y : V → ℝ) :
    ∑ i ∈ R, (∑ j ∈ S, G i j * y j) ^ 2 ≤ M ^ 2 * ∑ j ∈ S, y j ^ 2 := by
  obtain ⟨z, hz⟩ : ∃ z : V → ℝ, ∀ i, z i = ∑ j ∈ S, G i j * y j := ⟨_, fun i => rfl⟩
  have hgoal : ∑ i ∈ R, (∑ j ∈ S, G i j * y j) ^ 2 = ∑ i ∈ R, z i ^ 2 :=
    sum_congr rfl fun i _ => by rw [hz]
  rw [hgoal]
  have hZ : 0 ≤ ∑ i ∈ R, z i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have hY : 0 ≤ ∑ j ∈ S, y j ^ 2 := sum_nonneg fun j _ => sq_nonneg _
  have e1 : ∀ c : ℝ, ∑ i ∈ R, ∑ j ∈ S, z i * G i j * (c * y j) = c * ∑ i ∈ R, z i ^ 2 := by
    intro c
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have : ∑ j ∈ S, z i * G i j * (c * y j) = c * z i * ∑ j ∈ S, G i j * y j := by
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [this, ← hz]
    ring
  have e2 : ∀ c : ℝ, ∑ j ∈ S, (c * y j) ^ 2 = c ^ 2 * ∑ j ∈ S, y j ^ 2 := by
    intro c
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rcases hM.eq_or_lt with h0 | hpos
  · have k1 := h z (fun j => 1 * y j)
    rw [e1, e2, ← h0] at k1
    rw [← h0]
    nlinarith
  · have k2 := h z (fun j => M * y j)
    rw [e1, e2] at k2
    have : M * ∑ i ∈ R, z i ^ 2 ≤ M * (M ^ 2 * ∑ j ∈ S, y j ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this hpos

/-- A bilinear bound gives an operator bound for the transpose. -/
lemma op_of_bil' (R S : Finset V) (G : V → V → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ x y : V → ℝ, 2 * ∑ i ∈ R, ∑ j ∈ S, x i * G i j * y j ≤
      M * (∑ i ∈ R, x i ^ 2 + ∑ j ∈ S, y j ^ 2)) (x : V → ℝ) :
    ∑ j ∈ S, (∑ i ∈ R, G i j * x i) ^ 2 ≤ M ^ 2 * ∑ i ∈ R, x i ^ 2 := by
  refine op_of_bil S R (fun j i => G i j) M hM (fun y x' => ?_) x
  have h1 := h x' y
  rw [sum_comm] at h1
  calc 2 * ∑ j ∈ S, ∑ i ∈ R, y j * G i j * x' i
        = 2 * ∑ j ∈ S, ∑ i ∈ R, x' i * G i j * y j := by
          congr 1
          exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring
    _ ≤ _ := h1
    _ = _ := by ring

/-- Operator bounds pass to the transpose. -/
lemma op_transpose (R S : Finset V) (G : V → V → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (h : ∀ y : V → ℝ, ∑ i ∈ R, (∑ j ∈ S, G i j * y j) ^ 2 ≤ β ^ 2 * ∑ j ∈ S, y j ^ 2)
    (x : V → ℝ) :
    ∑ j ∈ S, (∑ i ∈ R, G i j * x i) ^ 2 ≤ β ^ 2 * ∑ i ∈ R, x i ^ 2 :=
  op_of_bil' R S G β hβ (bil_of_op R S G β hβ h) x

/-! ### Bipartite sums -/

lemma bip_sum [DecidableEq V] (P Q : Finset V) (hPQ : Disjoint P Q) (w : V → V → ℝ)
    (hsymm : ∀ x y, w x y = w y x) (hP : ∀ x ∈ P, ∀ y ∈ P, w x y = 0)
    (hQ : ∀ x ∈ Q, ∀ y ∈ Q, w x y = 0) (g : V → V → ℝ) :
    ∑ x ∈ P ∪ Q, ∑ y ∈ P ∪ Q, w x y * g x y =
      ∑ x ∈ P, ∑ y ∈ Q, w x y * (g x y + g y x) := by
  have h1 : ∑ x ∈ P, ∑ y ∈ P, w x y * g x y = 0 :=
    sum_eq_zero fun x hx => sum_eq_zero fun y hy => by rw [hP x hx y hy, zero_mul]
  have h2 : ∑ x ∈ Q, ∑ y ∈ Q, w x y * g x y = 0 :=
    sum_eq_zero fun x hx => sum_eq_zero fun y hy => by rw [hQ x hx y hy, zero_mul]
  have h3 : ∑ x ∈ Q, ∑ y ∈ P, w x y * g x y = ∑ x ∈ P, ∑ y ∈ Q, w x y * g y x := by
    rw [sum_comm]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by rw [hsymm]
  rw [sum_union hPQ]
  simp_rw [sum_union hPQ, sum_add_distrib]
  rw [h1, h2, h3]
  simp_rw [mul_add, sum_add_distrib]
  ring

lemma sum_union_left_zero [DecidableEq V] (P Q : Finset V) (hPQ : Disjoint P Q) (w : V → V → ℝ) (x : V)
    (hP : ∀ y ∈ P, w x y = 0) : ∑ y ∈ P ∪ Q, w x y = ∑ y ∈ Q, w x y := by
  rw [sum_union hPQ, sum_eq_zero hP, zero_add]

lemma sum_union_right_zero [DecidableEq V] (P Q : Finset V) (hPQ : Disjoint P Q) (w : V → V → ℝ) (x : V)
    (hQ : ∀ y ∈ Q, w x y = 0) : ∑ y ∈ P ∪ Q, w x y = ∑ y ∈ P, w x y := by
  rw [sum_union hPQ, sum_eq_zero hQ, add_zero]

/-- Expansion of a bipartite energy. -/
lemma energy_expand (P Q : Finset V) (w : V → V → ℝ) (dP dQ : V → ℝ)
    (hdP : ∀ i ∈ P, dP i = ∑ j ∈ Q, w i j) (hdQ : ∀ j ∈ Q, dQ j = ∑ i ∈ P, w i j)
    (x y : V → ℝ) :
    ∑ i ∈ P, ∑ j ∈ Q, w i j * (x i - y j) ^ 2 =
      ∑ i ∈ P, dP i * x i ^ 2 + ∑ j ∈ Q, dQ j * y j ^ 2 -
        2 * ∑ i ∈ P, ∑ j ∈ Q, x i * w i j * y j := by
  have h1 : ∑ i ∈ P, dP i * x i ^ 2 = ∑ i ∈ P, ∑ j ∈ Q, w i j * x i ^ 2 :=
    sum_congr rfl fun i hi => by rw [hdP i hi, sum_mul]
  have h2 : ∑ j ∈ Q, dQ j * y j ^ 2 = ∑ i ∈ P, ∑ j ∈ Q, w i j * y j ^ 2 := by
    rw [sum_comm]
    exact sum_congr rfl fun j hj => by rw [hdQ j hj, sum_mul]
  rw [h1, h2, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun j _ => by ring

/-- Expansion of a weighted squared deviation. -/
lemma sum_sq_shift (P : Finset V) (d u : V → ℝ) (z : ℝ) :
    ∑ i ∈ P, d i * (u i - z) ^ 2 =
      ∑ i ∈ P, d i * u i ^ 2 - 2 * z * ∑ i ∈ P, d i * u i + z ^ 2 * ∑ i ∈ P, d i := by
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

/-! ### The spectral bound for `H` and the gap criterion for the sample -/

/-- The gap of the bipartite graph `H` bounds the bilinear form of `F = K - d_A d_Bᵀ / e`. -/
lemma spectral_bound [Fintype V] [DecidableEq V] (H : WGraph V) (A B : Finset V) (hAB : Disjoint A B)
    (hAB' : A ∪ B = univ) (hA : ∀ x ∈ A, ∀ y ∈ A, H.w x y = 0)
    (hB : ∀ x ∈ B, ∀ y ∈ B, H.w x y = 0) (σ Δ : ℝ) (hgap : H.HasGap σ) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hΔ : ∀ x, H.deg x ≤ Δ)
    (hdA : ∀ i ∈ A, H.deg i = ∑ j ∈ B, H.w i j) (hdB : ∀ j ∈ B, H.deg j = ∑ i ∈ A, H.w i j)
    (hepos : 0 < ∑ i ∈ A, H.deg i) (x y : V → ℝ) :
    2 * ∑ i ∈ A, ∑ j ∈ B, x i * (H.w i j - H.deg i * H.deg j / ∑ l ∈ A, H.deg l) * y j ≤
      (1 - σ) * Δ * (∑ i ∈ A, x i ^ 2 + ∑ j ∈ B, y j ^ 2) := by
  set e := ∑ l ∈ A, H.deg l with he_def
  have heB : ∑ j ∈ B, H.deg j = e := by
    rw [he_def]
    calc ∑ j ∈ B, H.deg j = ∑ j ∈ B, ∑ i ∈ A, H.w i j := sum_congr rfl hdB
      _ = ∑ i ∈ A, ∑ j ∈ B, H.w i j := sum_comm
      _ = _ := sum_congr rfl fun i hi => (hdA i hi).symm
  set dA := ∑ i ∈ A, H.deg i * x i with hdA_def
  set dB := ∑ j ∈ B, H.deg j * y j with hdB_def
  set a := dA / e with ha_def
  set b := dB / e with hb_def
  obtain ⟨z, hz⟩ := hgap (fun v => if v ∈ A then x v - a else y v - b)
  have hBA : ∀ j ∈ B, j ∉ A := fun j hj hjA => disjoint_left.1 hAB hjA hj
  -- the Dirichlet form
  have hdir : H.dirichlet (fun v => if v ∈ A then x v - a else y v - b) =
      ∑ i ∈ A, ∑ j ∈ B, H.w i j * ((x i - a) - (y j - b)) ^ 2 := by
    unfold WGraph.dirichlet
    rw [← hAB', bip_sum A B hAB H.w H.symm hA hB]
    rw [div_eq_iff (two_ne_zero), mul_comm, two_mul, ← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    simp only [hi, hBA j hj, ↓reduceIte]
    ring
  -- the variance
  have hvar : ∑ i ∈ A, H.deg i * (x i - a) ^ 2 + ∑ j ∈ B, H.deg j * (y j - b) ^ 2 ≤
      ∑ v, H.deg v * ((fun v => if v ∈ A then x v - a else y v - b) v - z) ^ 2 := by
    rw [← hAB', sum_union hAB]
    have e1 : ∑ v ∈ A, H.deg v * ((fun v => if v ∈ A then x v - a else y v - b) v - z) ^ 2 =
        ∑ i ∈ A, H.deg i * ((x i - a) - z) ^ 2 :=
      sum_congr rfl fun i hi => by simp only [hi, ↓reduceIte]
    have e2 : ∑ v ∈ B, H.deg v * ((fun v => if v ∈ A then x v - a else y v - b) v - z) ^ 2 =
        ∑ j ∈ B, H.deg j * ((y j - b) - z) ^ 2 :=
      sum_congr rfl fun j hj => by simp only [hBA j hj, ↓reduceIte]
    rw [e1, e2, sum_sq_shift A H.deg (fun i => x i - a) z,
      sum_sq_shift B H.deg (fun j => y j - b) z]
    have hcA : ∑ i ∈ A, H.deg i * (x i - a) = 0 := by
      have : ∑ i ∈ A, H.deg i * (x i - a) = dA - a * e := by
        rw [hdA_def, he_def, mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun i _ => by ring
      rw [this, ha_def, div_mul_cancel₀ _ hepos.ne', sub_self]
    have hcB : ∑ j ∈ B, H.deg j * (y j - b) = 0 := by
      have : ∑ j ∈ B, H.deg j * (y j - b) = dB - b * e := by
        rw [hdB_def, ← heB, mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun j _ => by ring
      rw [this, hb_def, div_mul_cancel₀ _ hepos.ne', sub_self]
    rw [hcA, hcB, heB]
    nlinarith [sq_nonneg z]
  -- the energy
  have hen := energy_expand A B H.w H.deg H.deg hdA
    (fun j hj => by rw [hdB j hj]) (fun i => x i - a) (fun j => y j - b)
  have hT : ∑ i ∈ A, ∑ j ∈ B, (x i - a) * H.w i j * (y j - b) =
      ∑ i ∈ A, ∑ j ∈ B, x i * (H.w i j - H.deg i * H.deg j / e) * y j := by
    have h1 : ∑ i ∈ A, ∑ j ∈ B, H.w i j * y j = dB := by
      rw [sum_comm]
      exact sum_congr rfl fun j hj => by rw [← sum_mul, ← hdB j hj]
    have h2 : ∑ i ∈ A, ∑ j ∈ B, x i * H.w i j = dA :=
      sum_congr rfl fun i hi => by rw [← mul_sum, ← hdA i hi, mul_comm]
    have h3 : ∑ i ∈ A, ∑ j ∈ B, H.w i j = e := sum_congr rfl fun i hi => (hdA i hi).symm
    have h4 : ∑ i ∈ A, ∑ j ∈ B, H.deg i * x i * (H.deg j * y j) = dA * dB := by
      rw [sum_mul_sum]
    have L1 : ∑ i ∈ A, ∑ j ∈ B, (x i - a) * H.w i j * (y j - b) =
        ∑ i ∈ A, ∑ j ∈ B, x i * H.w i j * y j - a * dB - b * dA + a * b * e := by
      rw [← h1, ← h2, ← h3, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib,
        ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun j _ => by ring
    have L2 : ∑ i ∈ A, ∑ j ∈ B, x i * (H.w i j - H.deg i * H.deg j / e) * y j =
        ∑ i ∈ A, ∑ j ∈ B, x i * H.w i j * y j - dA * dB / e := by
      rw [← h4, sum_div, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [sum_div, ← sum_sub_distrib]
      exact sum_congr rfl fun j _ => by ring
    rw [L1, L2, ha_def, hb_def]
    field_simp
    ring
  rw [hT] at hen
  -- the deviation terms are at most the plain weighted norms
  have hXa : ∑ i ∈ A, H.deg i * (x i - a) ^ 2 ≤ Δ * ∑ i ∈ A, x i ^ 2 := by
    rw [sum_sq_shift A H.deg x a, ← hdA_def, ← he_def]
    have h1 : ∑ i ∈ A, H.deg i * x i ^ 2 ≤ Δ * ∑ i ∈ A, x i ^ 2 := by
      rw [mul_sum]
      exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hΔ i) (sq_nonneg _)
    have h2 : 2 * a * dA - a ^ 2 * e = dA ^ 2 / e := by
      rw [ha_def]; field_simp; ring
    have h3 : 0 ≤ dA ^ 2 / e := div_nonneg (sq_nonneg _) hepos.le
    linarith
  have hYb : ∑ j ∈ B, H.deg j * (y j - b) ^ 2 ≤ Δ * ∑ j ∈ B, y j ^ 2 := by
    rw [sum_sq_shift B H.deg y b, ← hdB_def, heB]
    have h1 : ∑ j ∈ B, H.deg j * y j ^ 2 ≤ Δ * ∑ j ∈ B, y j ^ 2 := by
      rw [mul_sum]
      exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hΔ j) (sq_nonneg _)
    have h2 : 2 * b * dB - b ^ 2 * e = dB ^ 2 / e := by
      rw [hb_def]; field_simp; ring
    have h3 : 0 ≤ dB ^ 2 / e := div_nonneg (sq_nonneg _) hepos.le
    linarith
  have hgap' := hz
  rw [hdir, hen] at hgap'
  have hmono := mul_le_mul_of_nonneg_left hvar hσ0
  have h1σ : 0 ≤ 1 - σ := by linarith
  have := mul_le_mul_of_nonneg_left (add_le_add hXa hYb) h1σ
  nlinarith

/-- A sufficient condition for the gap of the induced graph on `U ∪ W` (bipartite between `U`
and `W`): the weights between `U` and `W` are `Fm + λ p qᵀ` with `λ ≥ 0`, the bilinear form of
`Fm` is bounded by `β`, `∑ p + ∑ q > 0`, and the degrees lie in `[δ₁, δ₂]`. -/
lemma gap_suff [DecidableEq V] (H : WGraph V) (U W : Finset V) (hUW : Disjoint U W)
    (hU : ∀ x ∈ U, ∀ y ∈ U, H.w x y = 0) (hW : ∀ x ∈ W, ∀ y ∈ W, H.w x y = 0)
    (Fm : V → V → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) (p q : V → ℝ)
    (hK : ∀ i ∈ U, ∀ j ∈ W, H.w i j = Fm i j + lam * p i * q j)
    (hpq : 0 < ∑ i ∈ U, p i + ∑ j ∈ W, q j) (β δ₁ δ₂ s : ℝ)
    (hbil : ∀ x y : V → ℝ, 2 * ∑ i ∈ U, ∑ j ∈ W, x i * Fm i j * y j ≤
      β * (∑ i ∈ U, x i ^ 2 + ∑ j ∈ W, y j ^ 2))
    (hdeg : ∀ v ∈ U ∪ W, δ₁ ≤ ∑ y ∈ U ∪ W, H.w v y ∧ ∑ y ∈ U ∪ W, H.w v y ≤ δ₂)
    (hs : 0 ≤ s) (hsδ : s * δ₂ ≤ δ₁ - β) : (H.induce (U ∪ W)).HasGap s := by
  intro f
  obtain ⟨F, hF⟩ : ∃ F : V → ℝ, ∀ x : ↥(U ∪ W), f x = F x :=
    ⟨fun v => if h : v ∈ (U ∪ W) then f ⟨v, h⟩ else 0, fun x => by simp [x.2]⟩
  set t := (∑ i ∈ U, p i * F i + ∑ j ∈ W, q j * F j) / (∑ i ∈ U, p i + ∑ j ∈ W, q j)
    with ht
  refine ⟨t, ?_⟩
  obtain ⟨dd, hdd⟩ : ∃ dd : V → ℝ, ∀ v, dd v = ∑ y ∈ (U ∪ W), H.w v y := ⟨_, fun v => rfl⟩
  have hdegS : ∀ x : ↥(U ∪ W), (H.induce (U ∪ W)).deg x = dd x := by
    intro x
    rw [hdd]
    exact sum_coe_sort (U ∪ W) (fun y => H.w x y)
  have hLHS : ∑ x : ↥(U ∪ W), (H.induce (U ∪ W)).deg x * (f x - t) ^ 2 =
      ∑ x ∈ (U ∪ W), dd x * (F x - t) ^ 2 := by
    rw [← sum_coe_sort (U ∪ W) (fun x => dd x * (F x - t) ^ 2)]
    exact sum_congr rfl fun x _ => by rw [hdegS, hF]
  have hRHS : (H.induce (U ∪ W)).dirichlet f =
      (∑ x ∈ (U ∪ W), ∑ y ∈ (U ∪ W), H.w x y * (F x - F y) ^ 2) / 2 := by
    unfold WGraph.dirichlet
    congr 1
    rw [← sum_coe_sort (U ∪ W)]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_coe_sort (U ∪ W)]
    refine sum_congr rfl fun y _ => ?_
    rw [hF, hF]
    rfl
  have hdU : ∀ i ∈ U, dd i = ∑ j ∈ W, H.w i j := fun i hi => by
    rw [hdd, sum_union_left_zero U W hUW H.w i (fun y hy => hU i hi y hy)]
  have hdW : ∀ j ∈ W, dd j = ∑ i ∈ U, H.w i j := fun j hj => by
    rw [hdd, sum_union_right_zero U W hUW H.w j (fun y hy => hW j hj y hy)]
    exact sum_congr rfl fun i _ => H.symm _ _
  have hE : (∑ x ∈ (U ∪ W), ∑ y ∈ (U ∪ W), H.w x y * (F x - F y) ^ 2) / 2 =
      ∑ i ∈ U, ∑ j ∈ W, H.w i j * ((F i - t) - (F j - t)) ^ 2 := by
    rw [bip_sum U W hUW H.w H.symm hU hW (fun x y => (F x - F y) ^ 2),
      div_eq_iff two_ne_zero, mul_comm, two_mul, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  have hen := energy_expand U W H.w dd dd hdU hdW (fun i => F i - t) (fun j => F j - t)
  have hsplit : ∑ i ∈ U, ∑ j ∈ W, (F i - t) * H.w i j * (F j - t) =
      ∑ i ∈ U, ∑ j ∈ W, (F i - t) * Fm i j * (F j - t) +
        lam * ((∑ i ∈ U, p i * (F i - t)) * (∑ j ∈ W, q j * (F j - t))) := by
    rw [sum_mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun j hj => by rw [hK i hi j hj]; ring
  have hzero : ∑ i ∈ U, p i * (F i - t) + ∑ j ∈ W, q j * (F j - t) = 0 := by
    have e1 : ∑ i ∈ U, p i * (F i - t) = ∑ i ∈ U, p i * F i - t * ∑ i ∈ U, p i := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    have e2 : ∑ j ∈ W, q j * (F j - t) = ∑ j ∈ W, q j * F j - t * ∑ j ∈ W, q j := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun j _ => by ring
    have e3 : t * (∑ i ∈ U, p i + ∑ j ∈ W, q j) =
        ∑ i ∈ U, p i * F i + ∑ j ∈ W, q j * F j := by
      rw [ht, div_mul_cancel₀ _ hpq.ne']
    rw [e1, e2]
    linarith
  have hbil' := hbil (fun i => F i - t) (fun j => F j - t)
  have hlo : δ₁ * (∑ i ∈ U, (F i - t) ^ 2 + ∑ j ∈ W, (F j - t) ^ 2) ≤
      ∑ i ∈ U, dd i * (F i - t) ^ 2 + ∑ j ∈ W, dd j * (F j - t) ^ 2 := by
    rw [mul_add, mul_sum, mul_sum]
    refine add_le_add (sum_le_sum fun i hi => ?_) (sum_le_sum fun j hj => ?_)
    · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [hdd]; exact (hdeg i (mem_union_left _ hi)).1
    · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [hdd]; exact (hdeg j (mem_union_right _ hj)).1
  have hhi : ∑ i ∈ U, dd i * (F i - t) ^ 2 + ∑ j ∈ W, dd j * (F j - t) ^ 2 ≤
      δ₂ * (∑ i ∈ U, (F i - t) ^ 2 + ∑ j ∈ W, (F j - t) ^ 2) := by
    rw [mul_add, mul_sum, mul_sum]
    refine add_le_add (sum_le_sum fun i hi => ?_) (sum_le_sum fun j hj => ?_)
    · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [hdd]; exact (hdeg i (mem_union_left _ hi)).2
    · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [hdd]; exact (hdeg j (mem_union_right _ hj)).2
  have hXY : 0 ≤ ∑ i ∈ U, (F i - t) ^ 2 + ∑ j ∈ W, (F j - t) ^ 2 :=
    add_nonneg (sum_nonneg fun i _ => sq_nonneg _) (sum_nonneg fun j _ => sq_nonneg _)
  have hPQ : lam * ((∑ i ∈ U, p i * (F i - t)) * (∑ j ∈ W, q j * (F j - t))) ≤ 0 := by
    have hq : ∑ j ∈ W, q j * (F j - t) = -∑ i ∈ U, p i * (F i - t) := by linarith
    rw [hq]
    nlinarith [sq_nonneg (∑ i ∈ U, p i * (F i - t))]
  rw [hLHS, hRHS, hE, hen, hsplit, sum_union hUW]
  have h2 := mul_le_mul_of_nonneg_left hhi hs
  have h3 := mul_le_mul_of_nonneg_right hsδ hXY
  nlinarith

/-- The deterministic core: degree and bilinear bounds for the sample give the conclusion of
Lemma 2.3 (with `c₂ = 1/4`). -/
lemma good_of_bounds [DecidableEq V] (H : WGraph V) (A B U W : Finset V) (hAB : Disjoint A B)
    (hA : ∀ x ∈ A, ∀ y ∈ A, H.w x y = 0) (hB : ∀ x ∈ B, ∀ y ∈ B, H.w x y = 0)
    (hUA : U ⊆ A) (hWB : W ⊆ B) (hUne : U.Nonempty) (deg : V → ℝ) (hdpos : ∀ x, 0 < deg x)
    (e : ℝ) (he : 0 < e) (P c₁ c₁' σ β : ℝ) (hc : c₁' ≤ c₁) (hσ : 0 < σ) (hP : 0 < P)
    (hβ : 0 ≤ β)
    (hdU : ∀ i ∈ U, |∑ j ∈ W, H.w i j - P| ≤ c₁' * σ * P)
    (hdW : ∀ j ∈ W, |∑ i ∈ U, H.w i j - P| ≤ c₁' * σ * P)
    (hop : ∀ v : V → ℝ, ∑ i ∈ U, (∑ j ∈ W, (H.w i j - deg i * deg j / e) * v j) ^ 2 ≤
      β ^ 2 * ∑ j ∈ W, v j ^ 2)
    (hnum : 1 / 4 * σ * ((1 + c₁' * σ) * P) ≤ (1 - c₁' * σ) * P - β) :
    (H.induce (U ∪ W)).DegNear P (c₁ * σ) ∧ (H.induce (U ∪ W)).HasGap (1 / 4 * σ) := by
  have hUW : Disjoint U W := disjoint_of_subset_left hUA (disjoint_of_subset_right hWB hAB)
  have hU' : ∀ x ∈ U, ∀ y ∈ U, H.w x y = 0 := fun x hx y hy => hA x (hUA hx) y (hUA hy)
  have hW' : ∀ x ∈ W, ∀ y ∈ W, H.w x y = 0 := fun x hx y hy => hB x (hWB hx) y (hWB hy)
  have hdeg' : ∀ v ∈ U ∪ W, |∑ y ∈ U ∪ W, H.w v y - P| ≤ c₁' * σ * P := by
    intro v hv
    rcases mem_union.1 hv with hv | hv
    · rw [sum_union_left_zero U W hUW H.w v (fun y hy => hU' v hv y hy)]
      exact hdU v hv
    · rw [sum_union_right_zero U W hUW H.w v (fun y hy => hW' v hv y hy),
        show ∑ y ∈ U, H.w v y = ∑ i ∈ U, H.w i v from sum_congr rfl fun i _ => H.symm _ _]
      exact hdW v hv
  refine ⟨fun x => ?_, ?_⟩
  · have e1 : (H.induce (U ∪ W)).deg x = ∑ y ∈ U ∪ W, H.w x y :=
      sum_coe_sort (U ∪ W) (fun y => H.w x y)
    rw [e1]
    refine (hdeg' x x.2).trans ?_
    have := mul_le_mul_of_nonneg_right hc (mul_nonneg hσ.le hP.le)
    nlinarith
  · refine gap_suff H U W hUW hU' hW' (fun i j => H.w i j - deg i * deg j / e) (1 / e)
      (by positivity) deg deg (fun i _ j _ => by field_simp; ring) ?_ β
      ((1 - c₁' * σ) * P) ((1 + c₁' * σ) * P) (1 / 4 * σ)
      (fun x y => bil_of_op U W _ β hβ hop x y) (fun v hv => ?_) (by positivity) hnum
    · exact add_pos_of_pos_of_nonneg (sum_pos (fun i _ => hdpos i) hUne)
        (sum_nonneg fun j _ => (hdpos j).le)
    · have := abs_le.1 (hdeg' v hv)
      constructor <;> nlinarith

/-- A Chernoff upper-tail exponent is at least `t` under the stated comparisons. -/
lemma tail_upper_le {μ T t P : ℝ} (hμ0 : 0 ≤ μ) (hT : 0 < T) (hμ : μ ≤ 33 / 32 * P)
    (hTP : T ≤ P) (ht : 0 ≤ t) (h : t * (3 * P) ≤ T ^ 2) :
    Real.exp (-(T ^ 2) / (2 * (μ + T / 3))) ≤ Real.exp (-t) := by
  have hX : 0 < 2 * (μ + T / 3) := by positivity
  apply Real.exp_le_exp.2
  rw [neg_div, neg_le_neg_iff, le_div_iff₀ hX]
  have : 2 * (μ + T / 3) ≤ 3 * P := by linarith
  nlinarith

/-- A Chernoff lower-tail exponent is at least `t` under the stated comparisons. -/
lemma tail_lower_le {μ T t P : ℝ} (hμ0 : 0 < μ) (hμ : μ ≤ 33 / 32 * P) (ht : 0 ≤ t)
    (h : t * (3 * P) ≤ T ^ 2) :
    Real.exp (-(T ^ 2) / (2 * μ)) ≤ Real.exp (-t) := by
  have hX : 0 < 2 * μ := by positivity
  apply Real.exp_le_exp.2
  rw [neg_div, neg_le_neg_iff, le_div_iff₀ hX]
  have : 2 * μ ≤ 3 * P := by linarith
  nlinarith

lemma card_biUnion_prod_le {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset α)
    (T : α → Finset β) (b : ℝ) (hb : ∀ a ∈ s, ((T a).card : ℝ) ≤ b) :
    ((s.biUnion fun a => ({a} : Finset α) ×ˢ T a).card : ℝ) ≤ s.card * b := by
  calc ((s.biUnion fun a => ({a} : Finset α) ×ˢ T a).card : ℝ)
      ≤ ((∑ a ∈ s, (({a} : Finset α) ×ˢ T a).card : ℕ) : ℝ) :=
        Nat.cast_le.2 card_biUnion_le
    _ = ∑ a ∈ s, ((T a).card : ℝ) := by
        push_cast
        exact sum_congr rfl fun a _ => by rw [card_product, card_singleton, one_mul]
    _ ≤ ∑ a ∈ s, b := sum_le_sum hb
    _ = s.card * b := by rw [sum_const, nsmul_eq_mul]

lemma card_biUnion_le_real {α β : Type*} [DecidableEq β] (s : Finset α) (T : α → Finset β)
    (b : ℝ) (hb : ∀ a ∈ s, ((T a).card : ℝ) ≤ b) :
    ((s.biUnion T).card : ℝ) ≤ s.card * b := by
  calc ((s.biUnion T).card : ℝ) ≤ ((∑ a ∈ s, (T a).card : ℕ) : ℝ) :=
        Nat.cast_le.2 card_biUnion_le
    _ = ∑ a ∈ s, ((T a).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ a ∈ s, b := sum_le_sum hb
    _ = s.card * b := by rw [sum_const, nsmul_eq_mul]

lemma card_union5_le {α : Type*} [DecidableEq α] (s₁ s₂ s₃ s₄ s₅ : Finset α) :
    (s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅).card ≤ s₁.card + s₂.card + s₃.card + s₄.card + s₅.card := by
  have h1 := card_union_le (s₁ ∪ s₂ ∪ s₃ ∪ s₄) s₅
  have h2 := card_union_le (s₁ ∪ s₂ ∪ s₃) s₄
  have h3 := card_union_le (s₁ ∪ s₂) s₃
  have h4 := card_union_le s₁ s₂
  omega

/-! ### Numerical lemmas -/

lemma num_rank_one {di dj e D N η : ℝ} (hdi : 0 < di) (hdj : 0 < dj) (hdi' : di ≤ (1 + η) * D)
    (hdj' : dj ≤ (1 + η) * D) (he : N * ((1 - η) * D) ≤ e) (hN : 0 < N) (hD : 0 < D)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 32) (hepos : 0 < e) : di * dj / e ≤ 2 * D / N := by
  rw [div_le_div_iff₀ hepos hN]
  have h1 : di * dj ≤ ((1 + η) * D) * ((1 + η) * D) :=
    mul_le_mul hdi' hdj' hdj.le (mul_nonneg (by linarith) hD.le)
  have h2 : ((1 + η) * D) * ((1 + η) * D) ≤ 2 * D * ((1 - η) * D) := by
    have h3 : (1 + η) ^ 2 ≤ 2 * (1 - η) := by nlinarith
    have hD2 : 0 ≤ D * D := mul_nonneg hD.le hD.le
    nlinarith [mul_le_mul_of_nonneg_right h3 hD2]
  calc di * dj * N ≤ ((1 + η) * D) * ((1 + η) * D) * N := mul_le_mul_of_nonneg_right h1 hN.le
    _ ≤ 2 * D * ((1 - η) * D) * N := mul_le_mul_of_nonneg_right h2 hN.le
    _ = 2 * D * (N * ((1 - η) * D)) := by ring
    _ ≤ 2 * D * e := mul_le_mul_of_nonneg_left he (by linarith)

lemma num_entry_sq {w r D N : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 2 * D / N) (hD : 0 < D) (hN : 0 < N) (hDN : D ≤ 2 * N) :
    (w - r) ^ 2 ≤ 2 * w + 16 * D / N := by
  have hDN' : D / N ≤ 2 := by rw [div_le_iff₀ hN]; linarith
  have h3 : 0 ≤ D / N := div_nonneg hD.le hN.le
  have hr1' : r ≤ 2 * (D / N) := by rw [mul_div_assoc] at hr1; exact hr1
  have hr2 : r ^ 2 ≤ 8 * (D / N) := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.2 hr1'), mul_nonneg h3 (sub_nonneg.2 hr1'),
      mul_nonneg h3 (sub_nonneg.2 hDN')]
  have hww : w * w ≤ w := by nlinarith
  have h5 : 16 * D / N = 16 * (D / N) := by ring
  rw [h5]
  nlinarith [sq_nonneg (w + r)]

lemma num_beta {p M D t C₀ σ : ℝ} (hp : 0 < p) (hD : 0 < D) (ht : 0 < t) (hσ : 0 < σ)
    (hPtC : 10000 * C₀ ^ 2 * t ≤ σ ^ 2 * (p * D)) :
    Real.sqrt p * (Real.sqrt p * M + C₀ * Real.sqrt (24 * D) * Real.sqrt t) +
      C₀ * Real.sqrt (24 * (p * D)) * Real.sqrt t ≤ p * M + σ * (p * D) / 8 := by
  have hP : 0 < p * D := mul_pos hp hD
  have e1 : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp.le
  have e2 : Real.sqrt p * Real.sqrt (24 * D) = Real.sqrt (24 * (p * D)) := by
    rw [← Real.sqrt_mul hp.le]; congr 1; ring
  have hX2 : (Real.sqrt (24 * (p * D)) * Real.sqrt t) ^ 2 = 24 * (p * D) * t := by
    rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt ht.le]
  have hsq : (2 * C₀ * (Real.sqrt (24 * (p * D)) * Real.sqrt t)) ^ 2 ≤
      (σ * (p * D) / 8) ^ 2 := by
    rw [mul_pow, hX2]
    have h1 := mul_le_mul_of_nonneg_right hPtC hP.le
    have h2 : 0 ≤ C₀ ^ 2 * t * (p * D) := mul_nonneg (mul_nonneg (sq_nonneg _) ht.le) hP.le
    nlinarith
  have hlin : 2 * C₀ * (Real.sqrt (24 * (p * D)) * Real.sqrt t) ≤ σ * (p * D) / 8 :=
    le_trans (le_abs_self _) (abs_le_of_sq_le_sq hsq
      (div_nonneg (mul_nonneg hσ.le hP.le) (by norm_num)))
  calc Real.sqrt p * (Real.sqrt p * M + C₀ * Real.sqrt (24 * D) * Real.sqrt t) +
        C₀ * Real.sqrt (24 * (p * D)) * Real.sqrt t
      = Real.sqrt p * Real.sqrt p * M + C₀ * (Real.sqrt p * Real.sqrt (24 * D)) * Real.sqrt t +
        C₀ * Real.sqrt (24 * (p * D)) * Real.sqrt t := by ring
    _ = p * M + 2 * C₀ * (Real.sqrt (24 * (p * D)) * Real.sqrt t) := by rw [e1, e2]; ring
    _ ≤ _ := by linarith

lemma num_gap {σ η c P pM β : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hη0 : 0 ≤ η) (hη : η ≤ σ / 32)
    (hc : c ≤ 1 / 4) (hP : 0 < P) (hpM : pM = (1 - σ) * (1 + η) * P)
    (hβ : β ≤ pM + σ * P / 8) :
    1 / 4 * σ * ((1 + c * σ) * P) ≤ (1 - c * σ) * P - β := by
  have hσP : 0 < σ * P := mul_pos hσ hP
  have f1 : c * (σ * P) ≤ 1 / 4 * (σ * P) := mul_le_mul_of_nonneg_right hc hσP.le
  have hcσ : c * σ ≤ 1 / 4 := by nlinarith
  have f2 : c * σ * (σ * P) ≤ 1 / 4 * (σ * P) := mul_le_mul_of_nonneg_right hcσ hσP.le
  have f3 : η * P ≤ σ / 32 * P := mul_le_mul_of_nonneg_right hη hP.le
  have f4 : 0 ≤ σ * η * P := mul_nonneg (mul_nonneg hσ.le hη0) hP.le
  subst hpM
  nlinarith

lemma num_deg_close {s d D p η c σ t₀ : ℝ} (hp : 0 < p) (hD : 0 < D) (hd : |d - D| ≤ η * D)
    (hη : η ≤ c / 8 * σ) (ht₀ : t₀ = c * σ * (p * D) / 2) (h1 : ¬ (p * d + t₀ ≤ s))
    (h2 : ¬ (s ≤ p * d - t₀)) : |s - p * D| ≤ c * σ * (p * D) := by
  have h1' := not_le.1 h1
  have h2' := not_le.1 h2
  have h3 : |p * d - p * D| ≤ t₀ / 4 := by
    rw [← mul_sub, abs_mul, abs_of_pos hp]
    have h4 : η * D ≤ c / 8 * σ * D := mul_le_mul_of_nonneg_right hη hD.le
    calc p * |d - D| ≤ p * (c / 8 * σ * D) := mul_le_mul_of_nonneg_left (hd.trans h4) hp.le
      _ = t₀ / 4 := by rw [ht₀]; ring
  rw [abs_le] at h3 ⊢
  constructor <;> linarith

lemma num_final {N k : ℕ} {a L t : ℝ} (hN : 1 ≤ N) (hkN : k ≤ N)
    (hL : Real.log (2 * N) ≤ L) (ht : t = (a + 5) * L) :
    ((N : ℝ) * (N + 1) + N + k * (N + 1) + 4 * N) * Real.exp (-t) ≤ Real.exp (-(a * L)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hk : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hNL : 2 * (N : ℝ) ≤ Real.exp L := by
    have := Real.exp_le_exp.2 hL
    rwa [Real.exp_log (by linarith)] at this
  have hEL := Real.exp_pos L
  have hEt := Real.exp_pos (-t)
  have e1 : Real.exp (-t) * Real.exp L ^ 5 = Real.exp (-(a * L)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ht]
    congr 1
    push_cast
    ring
  have hpoly : (N : ℝ) * (N + 1) + N + k * (N + 1) + 4 * N ≤ 9 * N ^ 2 := by nlinarith
  have h1 : 9 * (N : ℝ) ^ 2 ≤ 9 / 4 * Real.exp L ^ 2 := by
    have := pow_le_pow_left₀ (by linarith) hNL 2
    nlinarith
  have h2 : Real.exp L ^ 2 * 8 ≤ Real.exp L ^ 5 := by
    have h3 : (2 : ℝ) ^ 3 ≤ Real.exp L ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    calc Real.exp L ^ 2 * 8 ≤ Real.exp L ^ 2 * Real.exp L ^ 3 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); norm_num at h3 ⊢; linarith
      _ = Real.exp L ^ 5 := by ring
  have h9 : (N : ℝ) * (N + 1) + N + k * (N + 1) + 4 * N ≤ Real.exp L ^ 5 := by
    nlinarith [pow_pos hEL 2]
  rw [← e1, mul_comm (Real.exp (-t))]
  exact mul_le_mul_of_nonneg_right h9 hEt.le

/-! ### Tail counts -/

open Classical in
lemma tail_count_upper (S : Finset V) (g : V → ℝ) (hg : ∀ i ∈ S, 0 ≤ g i ∧ g i ≤ 1)
    (N k : ℕ) (hS : S.card = N) (T P t : ℝ) (hμ0 : 0 ≤ (k : ℝ) / N * ∑ i ∈ S, g i)
    (hμ : (k : ℝ) / N * ∑ i ∈ S, g i ≤ 33 / 32 * P) (hT : 0 < T) (hTP : T ≤ P) (ht : 0 ≤ t)
    (h : t * (3 * P) ≤ T ^ 2) :
    (((S.powersetCard k).filter fun U =>
        (k : ℝ) / N * ∑ i ∈ S, g i + T ≤ ∑ i ∈ U, g i).card : ℝ) ≤
      Real.exp (-t) * N.choose k := by
  have h1 := hyp_upper_finset S g hg k T hT.le
  rw [hS] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (tail_upper_le hμ0 hT hμ hTP ht h)
    (Nat.cast_nonneg _))

open Classical in
lemma tail_count_lower (S : Finset V) (g : V → ℝ) (hg : ∀ i ∈ S, 0 ≤ g i ∧ g i ≤ 1)
    (N k : ℕ) (hS : S.card = N) (T P t : ℝ) (hμ0 : 0 < (k : ℝ) / N * ∑ i ∈ S, g i)
    (hμ : (k : ℝ) / N * ∑ i ∈ S, g i ≤ 33 / 32 * P) (hT : 0 ≤ T) (ht : 0 ≤ t)
    (h : t * (3 * P) ≤ T ^ 2) :
    (((S.powersetCard k).filter fun U =>
        ∑ i ∈ U, g i ≤ (k : ℝ) / N * ∑ i ∈ S, g i - T).card : ℝ) ≤
      Real.exp (-t) * N.choose k := by
  have h1 := hyp_lower_finset S g hg k T hT
  rw [hS] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (tail_lower_le hμ0 hμ ht h)
    (Nat.cast_nonneg _))

/-! ### The bad events and their counts -/

open Classical in
/-- First-round bad row sets: `‖F[U, B]‖ > β₁`. -/
noncomputable def bad1 [Fintype V] (H : WGraph V) (A B : Finset V) (k : ℕ) (e β₁ : ℝ) :
    Finset (Finset V) :=
  (A.powersetCard k).filter fun U => ∃ v : V → ℝ, β₁ ^ 2 * ∑ i ∈ U, v i ^ 2 <
    ∑ j ∈ B, (∑ i ∈ U, (H.w i j - H.deg i * H.deg j / e) * v i) ^ 2

open Classical in
/-- Row sets into which some column has too large a degree. -/
noncomputable def bad2 [DecidableEq V] (H : WGraph V) (A B : Finset V) (k : ℕ) (p P : ℝ) : Finset (Finset V) :=
  B.biUnion fun j => (A.powersetCard k).filter fun U =>
    p * ∑ i ∈ A, H.w i j + P ≤ ∑ i ∈ U, H.w i j

open Classical in
/-- Second-round bad pairs, over the row sets outside `Y`: `‖F[U, W]‖ > β₂`. -/
noncomputable def bad3 [Fintype V] [DecidableEq V] (H : WGraph V) (A B : Finset V) (k : ℕ) (e β₂ : ℝ)
    (Y : Finset (Finset V)) : Finset (Finset V × Finset V) :=
  (A.powersetCard k \ Y).biUnion fun U => ({U} : Finset (Finset V)) ×ˢ
    (B.powersetCard k).filter fun W => ∃ v : V → ℝ, β₂ ^ 2 * ∑ j ∈ W, v j ^ 2 <
      ∑ i ∈ U, (∑ j ∈ W, (H.w i j - H.deg i * H.deg j / e) * v j) ^ 2

open Classical in
/-- Pairs where some row vertex has a bad degree into the column sample. -/
noncomputable def bad4 [DecidableEq V] (H : WGraph V) (A B : Finset V) (k : ℕ) (p t₀ : ℝ) :
    Finset (Finset V × Finset V) :=
  A.biUnion fun i => A.powersetCard k ×ˢ
    ((B.powersetCard k).filter (fun W => p * ∑ j ∈ B, H.w i j + t₀ ≤ ∑ j ∈ W, H.w i j) ∪
      (B.powersetCard k).filter (fun W => ∑ j ∈ W, H.w i j ≤ p * ∑ j ∈ B, H.w i j - t₀))

open Classical in
/-- Pairs where some column vertex has a bad degree into the row sample. -/
noncomputable def bad5 [DecidableEq V] (H : WGraph V) (A B : Finset V) (k : ℕ) (p t₀ : ℝ) :
    Finset (Finset V × Finset V) :=
  B.biUnion fun j =>
    ((A.powersetCard k).filter (fun U => p * ∑ i ∈ A, H.w i j + t₀ ≤ ∑ i ∈ U, H.w i j) ∪
      (A.powersetCard k).filter (fun U => ∑ i ∈ U, H.w i j ≤ p * ∑ i ∈ A, H.w i j - t₀)) ×ˢ
    B.powersetCard k

open Classical in
/-- Outside the five bad events the sampled graph has the asserted degrees and gap. -/
lemma sampling_inclusion [Fintype V] [DecidableEq V] (H : WGraph V) (A B : Finset V) (k : ℕ)
    (hAB : Disjoint A B) (hA : ∀ x ∈ A, ∀ y ∈ A, H.w x y = 0)
    (hB : ∀ x ∈ B, ∀ y ∈ B, H.w x y = 0) (hk1 : 1 ≤ k) (hdpos : ∀ x, 0 < H.deg x)
    (hdA : ∀ i ∈ A, H.deg i = ∑ j ∈ B, H.w i j) (hdB : ∀ j ∈ B, H.deg j = ∑ i ∈ A, H.w i j)
    (e P c₁ c₁' σ p t₀ β₂ : ℝ) (he : 0 < e) (hc : c₁' ≤ c₁) (hσ : 0 < σ) (hP : 0 < P)
    (hβ₂ : 0 ≤ β₂) (hnum : 1 / 4 * σ * ((1 + c₁' * σ) * P) ≤ (1 - c₁' * σ) * P - β₂)
    (hdeg_of : ∀ (x : V) (s : ℝ), ¬ (p * H.deg x + t₀ ≤ s) → ¬ (s ≤ p * H.deg x - t₀) →
      |s - P| ≤ c₁' * σ * P)
    (Y1 Y2 : Finset (Finset V)) :
    ((A.powersetCard k ×ˢ B.powersetCard k).filter fun UW =>
        ¬ ((H.induce (UW.1 ∪ UW.2)).DegNear P (c₁ * σ) ∧
          (H.induce (UW.1 ∪ UW.2)).HasGap (1 / 4 * σ))) ⊆
      Y1 ×ˢ B.powersetCard k ∪ Y2 ×ˢ B.powersetCard k ∪ bad3 H A B k e β₂ (Y1 ∪ Y2) ∪
        bad4 H A B k p t₀ ∪ bad5 H A B k p t₀ := by
  rintro ⟨U, W⟩ hUW
  rw [mem_filter] at hUW
  obtain ⟨hmem, hbad⟩ := hUW
  obtain ⟨hU, hW⟩ := mem_product.1 hmem
  by_contra hnot
  apply hbad
  simp only [mem_union, not_or] at hnot
  obtain ⟨⟨⟨⟨n1, n2⟩, n3⟩, n4⟩, n5⟩ := hnot
  have hUsd : U ∈ A.powersetCard k \ (Y1 ∪ Y2) := by
    refine mem_sdiff.2 ⟨hU, fun h => ?_⟩
    rcases mem_union.1 h with h | h
    · exact n1 (mem_product.2 ⟨h, hW⟩)
    · exact n2 (mem_product.2 ⟨h, hW⟩)
  have nb3 : ∀ v : V → ℝ, ∑ i ∈ U, (∑ j ∈ W, (H.w i j - H.deg i * H.deg j / e) * v j) ^ 2 ≤
      β₂ ^ 2 * ∑ j ∈ W, v j ^ 2 := by
    intro v
    by_contra h
    apply n3
    unfold bad3
    exact mem_biUnion.2 ⟨U, hUsd, mem_product.2 ⟨mem_singleton_self U,
      mem_filter.2 ⟨hW, v, not_le.1 h⟩⟩⟩
  have hUA : U ⊆ A := (mem_powersetCard.1 hU).1
  have hUk : U.card = k := (mem_powersetCard.1 hU).2
  have hWB : W ⊆ B := (mem_powersetCard.1 hW).1
  have hUne : U.Nonempty := card_pos.1 (by omega)
  have hdU : ∀ i ∈ U, |∑ j ∈ W, H.w i j - P| ≤ c₁' * σ * P := by
    intro i hi
    have hiA := hUA hi
    refine hdeg_of i _ (fun h => n4 ?_) (fun h => n4 ?_)
    · unfold bad4
      refine mem_biUnion.2 ⟨i, hiA, mem_product.2 ⟨hU, mem_union_left _ (mem_filter.2 ⟨hW, ?_⟩)⟩⟩
      rw [← hdA i hiA]; exact h
    · unfold bad4
      refine mem_biUnion.2 ⟨i, hiA, mem_product.2 ⟨hU, mem_union_right _ (mem_filter.2 ⟨hW, ?_⟩)⟩⟩
      rw [← hdA i hiA]; exact h
  have hdW : ∀ j ∈ W, |∑ i ∈ U, H.w i j - P| ≤ c₁' * σ * P := by
    intro j hj
    have hjB := hWB hj
    refine hdeg_of j _ (fun h => n5 ?_) (fun h => n5 ?_)
    · unfold bad5
      refine mem_biUnion.2 ⟨j, hjB, mem_product.2 ⟨mem_union_left _ (mem_filter.2 ⟨hU, ?_⟩), hW⟩⟩
      rw [← hdB j hjB]; exact h
    · unfold bad5
      refine mem_biUnion.2 ⟨j, hjB, mem_product.2 ⟨mem_union_right _ (mem_filter.2 ⟨hU, ?_⟩), hW⟩⟩
      rw [← hdB j hjB]; exact h
  exact good_of_bounds H A B U W hAB hA hB hUA hWB hUne H.deg hdpos e he P c₁ c₁' σ β₂ hc hσ hP
    hβ₂ hdU hdW nb3 hnum

open Classical in
lemma count_bad1 {C₀ : ℝ} (hC₀ : ColSampProp C₀) [Fintype V] [DecidableEq V] (H : WGraph V)
    (A B : Finset V) (N k : ℕ) (hAcard : A.card = N) (hBcard : B.card = N) (hkN : k ≤ N)
    (e M D t β₁ : ℝ) (hM0 : 0 ≤ M) (hD : 0 ≤ D) (ht : 0 < t)
    (hop1 : ∀ v : V → ℝ, ∑ j ∈ B, (∑ i ∈ A, (H.w i j - H.deg i * H.deg j / e) * v i) ^ 2 ≤
      M ^ 2 * ∑ i ∈ A, v i ^ 2)
    (hrow : ∀ i ∈ A, ∑ j ∈ B, (H.w i j - H.deg i * H.deg j / e) ^ 2 ≤ 24 * D)
    (hβ₁ : β₁ = Real.sqrt ((k : ℝ) / N) * M + C₀ * Real.sqrt (24 * D) * Real.sqrt t) :
    ((bad1 H A B k e β₁).card : ℝ) ≤ N * (N + 1) * Real.exp (-t) * N.choose k := by
  have h := column_sampling_finset hC₀ B A (fun x y => H.w y x - H.deg y * H.deg x / e) M
    (Real.sqrt (24 * D)) (fun v => hop1 v)
    (fun i hi => by rw [Real.sq_sqrt (by linarith)]; exact hrow i hi) hM0 (Real.sqrt_nonneg _)
    k (by rw [hAcard]; exact hkN) t ht
  rw [hAcard, hBcard] at h
  refine le_trans (Nat.cast_le.2 (card_le_card fun U hU => ?_)) h
  unfold bad1 at hU
  rw [mem_filter] at hU ⊢
  rw [hβ₁] at hU
  exact hU

open Classical in
lemma count_bad2 [Fintype V] [DecidableEq V] (H : WGraph V) (A B : Finset V) (N k : ℕ) (hAcard : A.card = N)
    (hBcard : B.card = N) (hw : ∀ x y, 0 ≤ H.w x y ∧ H.w x y ≤ 1) (p D η t : ℝ)
    (hp : p = (k : ℝ) / N) (hp0 : 0 < p) (hdB : ∀ j ∈ B, H.deg j = ∑ i ∈ A, H.w i j)
    (hdpos : ∀ x, 0 < H.deg x) (hdhi : ∀ x, H.deg x ≤ (1 + η) * D) (hη : η ≤ 1 / 32)
    (hPpos : 0 < p * D) (ht : 0 ≤ t) (hPt3 : 3 * t ≤ p * D) :
    ((bad2 H A B k p (p * D)).card : ℝ) ≤ N * (Real.exp (-t) * N.choose k) := by
  unfold bad2
  refine le_trans (card_biUnion_le_real B _ (Real.exp (-t) * N.choose k) fun j hj => ?_)
    (le_of_eq (by rw [hBcard]))
  have hμ0 : 0 ≤ (k : ℝ) / N * ∑ i ∈ A, H.w i j := by
    rw [← hp, ← hdB j hj]; exact mul_nonneg hp0.le (hdpos j).le
  have hμ : (k : ℝ) / N * ∑ i ∈ A, H.w i j ≤ 33 / 32 * (p * D) := by
    rw [← hp, ← hdB j hj]
    linarith [mul_le_mul_of_nonneg_left (hdhi j) hp0.le,
      mul_le_mul_of_nonneg_right hη hPpos.le]
  have h := tail_count_upper A (fun i => H.w i j) (fun i _ => hw i j) N k hAcard (p * D)
    (p * D) t hμ0 hμ hPpos le_rfl ht (by nlinarith)
  refine le_trans (Nat.cast_le.2 (card_le_card fun U hU => ?_)) h
  rw [mem_filter] at hU ⊢
  rw [← hp]
  exact hU

open Classical in
lemma count_bad3 {C₀ : ℝ} (hC₀ : ColSampProp C₀) [Fintype V] [DecidableEq V] (H : WGraph V)
    (A B : Finset V) (N k : ℕ) (hAcard : A.card = N) (hBcard : B.card = N) (hkN : k ≤ N)
    (e p D η t β₁ β₂ : ℝ) (hp : p = (k : ℝ) / N) (hp0 : 0 < p) (hPpos : 0 < p * D)
    (ht : 0 < t) (hβ₁0 : 0 ≤ β₁)
    (hβ₂ : β₂ = Real.sqrt p * β₁ + C₀ * Real.sqrt (24 * (p * D)) * Real.sqrt t)
    (hFm2 : ∀ i ∈ A, ∀ j ∈ B,
      (H.w i j - H.deg i * H.deg j / e) ^ 2 ≤ 2 * H.w i j + 16 * D / N)
    (hdB : ∀ j ∈ B, H.deg j = ∑ i ∈ A, H.w i j) (hdhi : ∀ x, H.deg x ≤ (1 + η) * D)
    (hη : η ≤ 1 / 32) :
    ((bad3 H A B k e β₂ (bad1 H A B k e β₁ ∪ bad2 H A B k p (p * D))).card : ℝ) ≤
      N.choose k * (k * (N + 1) * Real.exp (-t) * N.choose k) := by
  unfold bad3
  refine le_trans (card_biUnion_prod_le _ _ (k * (N + 1) * Real.exp (-t) * N.choose k)
    fun U hU => ?_) ?_
  · obtain ⟨hUSA, hUY⟩ := mem_sdiff.1 hU
    have hUY1 : U ∉ bad1 H A B k e β₁ := fun h => hUY (mem_union_left _ h)
    have hUY2 : U ∉ bad2 H A B k p (p * D) := fun h => hUY (mem_union_right _ h)
    have hUA : U ⊆ A := (mem_powersetCard.1 hUSA).1
    have hUk : U.card = k := (mem_powersetCard.1 hUSA).2
    have nb1 : ∀ y : V → ℝ,
        ∑ j ∈ B, (∑ i ∈ U, (H.w i j - H.deg i * H.deg j / e) * y i) ^ 2 ≤
          β₁ ^ 2 * ∑ i ∈ U, y i ^ 2 := by
      intro y
      by_contra h
      exact hUY1 (by unfold bad1; exact mem_filter.2 ⟨hUSA, y, not_le.1 h⟩)
    have nb2 : ∀ j ∈ B, ∑ i ∈ U, H.w i j < p * ∑ i ∈ A, H.w i j + p * D := by
      intro j hj
      by_contra h
      exact hUY2 (by unfold bad2; exact mem_biUnion.2 ⟨j, hj, mem_filter.2 ⟨hUSA, not_lt.1 h⟩⟩)
    have hop2 := op_transpose B U (fun j i => H.w i j - H.deg i * H.deg j / e) β₁ hβ₁0 nb1
    have hcol2 : ∀ j ∈ B, ∑ i ∈ U, (H.w i j - H.deg i * H.deg j / e) ^ 2 ≤
        Real.sqrt (24 * (p * D)) ^ 2 := by
      intro j hj
      rw [Real.sq_sqrt (by linarith)]
      have h1 := nb2 j hj
      rw [← hdB j hj] at h1
      have e1 : (k : ℝ) * (16 * D / N) = 16 * (p * D) := by rw [hp]; ring
      calc ∑ i ∈ U, (H.w i j - H.deg i * H.deg j / e) ^ 2
          ≤ ∑ i ∈ U, (2 * H.w i j + 16 * D / N) :=
            sum_le_sum fun i hi => hFm2 i (hUA hi) j hj
        _ = 2 * ∑ i ∈ U, H.w i j + k * (16 * D / N) := by
            rw [sum_add_distrib, ← mul_sum, sum_const, hUk, nsmul_eq_mul]
        _ ≤ 24 * (p * D) := by
            rw [e1]
            linarith [mul_le_mul_of_nonneg_left (hdhi j) hp0.le,
              mul_le_mul_of_nonneg_right hη hPpos.le]
    have h := column_sampling_finset hC₀ U B (fun i j => H.w i j - H.deg i * H.deg j / e) β₁
      (Real.sqrt (24 * (p * D))) hop2 hcol2 hβ₁0 (Real.sqrt_nonneg _) k
      (by rw [hBcard]; exact hkN) t ht
    rw [hBcard, hUk, ← hp] at h
    refine le_trans (Nat.cast_le.2 (card_le_card fun W hW => ?_)) h
    rw [mem_filter] at hW ⊢
    rw [hβ₂] at hW
    exact hW
  · have hb0 : 0 ≤ (k : ℝ) * (N + 1) * Real.exp (-t) * N.choose k := by positivity
    calc ((A.powersetCard k \ (bad1 H A B k e β₁ ∪ bad2 H A B k p (p * D))).card : ℝ) *
          (k * (N + 1) * Real.exp (-t) * N.choose k)
        ≤ ((A.powersetCard k).card : ℝ) * (k * (N + 1) * Real.exp (-t) * N.choose k) :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.2 (card_le_card sdiff_subset)) hb0
      _ = _ := by rw [card_powersetCard, hAcard]

open Classical in
lemma count_bad4 [Fintype V] [DecidableEq V] (H : WGraph V) (A B : Finset V) (N k : ℕ)
    (hAcard : A.card = N) (hBcard : B.card = N) (hw : ∀ x y, 0 ≤ H.w x y ∧ H.w x y ≤ 1)
    (p D η t t₀ : ℝ) (hp : p = (k : ℝ) / N) (hp0 : 0 < p)
    (hdA : ∀ i ∈ A, H.deg i = ∑ j ∈ B, H.w i j) (hdpos : ∀ x, 0 < H.deg x)
    (hdhi : ∀ x, H.deg x ≤ (1 + η) * D) (hη : η ≤ 1 / 32) (hPpos : 0 < p * D) (ht : 0 ≤ t)
    (ht₀ : 0 < t₀) (ht₀le : t₀ ≤ p * D) (ht₀sq : t * (3 * (p * D)) ≤ t₀ ^ 2) :
    ((bad4 H A B k p t₀).card : ℝ) ≤ N * (N.choose k * (2 * (Real.exp (-t) * N.choose k))) := by
  unfold bad4
  refine le_trans (card_biUnion_le_real A _ (N.choose k * (2 * (Real.exp (-t) * N.choose k)))
    fun i hi => ?_) (le_of_eq (by rw [hAcard]))
  rw [card_product, Nat.cast_mul, card_powersetCard, hAcard]
  refine mul_le_mul_of_nonneg_left (le_trans (Nat.cast_le.2 (card_union_le _ _)) ?_)
    (Nat.cast_nonneg _)
  rw [Nat.cast_add, two_mul]
  have hμ0 : 0 < (k : ℝ) / N * ∑ j ∈ B, H.w i j := by
    rw [← hp, ← hdA i hi]; exact mul_pos hp0 (hdpos i)
  have hμ : (k : ℝ) / N * ∑ j ∈ B, H.w i j ≤ 33 / 32 * (p * D) := by
    rw [← hp, ← hdA i hi]
    linarith [mul_le_mul_of_nonneg_left (hdhi i) hp0.le,
      mul_le_mul_of_nonneg_right hη hPpos.le]
  refine add_le_add ?_ ?_
  · have h := tail_count_upper B (fun j => H.w i j) (fun j _ => hw i j) N k hBcard t₀ (p * D) t
      hμ0.le hμ ht₀ ht₀le ht ht₀sq
    refine le_trans (Nat.cast_le.2 (card_le_card fun W hW => ?_)) h
    rw [mem_filter] at hW ⊢
    rw [← hp]
    exact hW
  · have h := tail_count_lower B (fun j => H.w i j) (fun j _ => hw i j) N k hBcard t₀ (p * D) t
      hμ0 hμ ht₀.le ht ht₀sq
    refine le_trans (Nat.cast_le.2 (card_le_card fun W hW => ?_)) h
    rw [mem_filter] at hW ⊢
    rw [← hp]
    exact hW

open Classical in
lemma count_bad5 [Fintype V] [DecidableEq V] (H : WGraph V) (A B : Finset V) (N k : ℕ)
    (hAcard : A.card = N) (hBcard : B.card = N) (hw : ∀ x y, 0 ≤ H.w x y ∧ H.w x y ≤ 1)
    (p D η t t₀ : ℝ) (hp : p = (k : ℝ) / N) (hp0 : 0 < p)
    (hdB : ∀ j ∈ B, H.deg j = ∑ i ∈ A, H.w i j) (hdpos : ∀ x, 0 < H.deg x)
    (hdhi : ∀ x, H.deg x ≤ (1 + η) * D) (hη : η ≤ 1 / 32) (hPpos : 0 < p * D) (ht : 0 ≤ t)
    (ht₀ : 0 < t₀) (ht₀le : t₀ ≤ p * D) (ht₀sq : t * (3 * (p * D)) ≤ t₀ ^ 2) :
    ((bad5 H A B k p t₀).card : ℝ) ≤ N * (2 * (Real.exp (-t) * N.choose k) * N.choose k) := by
  unfold bad5
  refine le_trans (card_biUnion_le_real B _ (2 * (Real.exp (-t) * N.choose k) * N.choose k)
    fun j hj => ?_) (le_of_eq (by rw [hBcard]))
  rw [card_product, Nat.cast_mul, card_powersetCard, hBcard]
  refine mul_le_mul_of_nonneg_right (le_trans (Nat.cast_le.2 (card_union_le _ _)) ?_)
    (Nat.cast_nonneg _)
  rw [Nat.cast_add, two_mul]
  have hμ0 : 0 < (k : ℝ) / N * ∑ i ∈ A, H.w i j := by
    rw [← hp, ← hdB j hj]; exact mul_pos hp0 (hdpos j)
  have hμ : (k : ℝ) / N * ∑ i ∈ A, H.w i j ≤ 33 / 32 * (p * D) := by
    rw [← hp, ← hdB j hj]
    linarith [mul_le_mul_of_nonneg_left (hdhi j) hp0.le,
      mul_le_mul_of_nonneg_right hη hPpos.le]
  refine add_le_add ?_ ?_
  · have h := tail_count_upper A (fun i => H.w i j) (fun i _ => hw i j) N k hAcard t₀ (p * D) t
      hμ0.le hμ ht₀ ht₀le ht ht₀sq
    refine le_trans (Nat.cast_le.2 (card_le_card fun U hU => ?_)) h
    rw [mem_filter] at hU ⊢
    rw [← hp]
    exact hU
  · have h := tail_count_lower A (fun i => H.w i j) (fun i _ => hw i j) N k hAcard t₀ (p * D) t
      hμ0 hμ ht₀.le ht ht₀sq
    refine le_trans (Nat.cast_le.2 (card_le_card fun U hU => ?_)) h
    rw [mem_filter] at hU ⊢
    rw [← hp]
    exact hU

end BipSampling

open Classical in
/-- **Lemma 2.3 (Bipartite sampling).** Let `H` be bipartite with classes `A, B` of size `N`,
weights in `[ω, 1]`, degrees `(1 ± η) D`, and normalized upper gap `σ`, with `η ≤ cσ` and
`L ≥ log (2N)`. Choose independent uniform `k`-subsets `U ⊆ A`, `W ⊆ B` (`p = k/N`). If
`pD ≥ C σ^{-2} L`, then with failure probability at most `e^{-aL}` the graph between `U` and `W`
has degrees `(1 ± c₁σ) pD` and normalized upper gap at least `c₂σ`. Here `a` can be any fixed
constant and `c₁` any small constant, by increasing `C` (and decreasing `c`). -/
theorem bipartite_sampling (ω : ℝ) (hω : 0 < ω) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ a c₁ : ℝ, 0 < a → 0 < c₁ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (A B : Finset V) (N k : ℕ)
        (η D σ L : ℝ),
        Disjoint A B → A ∪ B = univ → A.card = N → B.card = N →
        (∀ x ∈ A, ∀ y ∈ A, H.w x y = 0) → (∀ x ∈ B, ∀ y ∈ B, H.w x y = 0) →
        H.WeightsIn ω → H.DegNear D η → H.HasGap σ → 0 < σ → σ ≤ 1 → η ≤ c * σ →
        Real.log (2 * N) ≤ L → k ≤ N → C * σ ^ (-2 : ℝ) * L ≤ (k : ℝ) / N * D →
        (((A.powersetCard k ×ˢ B.powersetCard k).filter fun UW =>
            ¬ ((H.induce (UW.1 ∪ UW.2)).DegNear ((k : ℝ) / N * D) (c₁ * σ) ∧
              (H.induce (UW.1 ∪ UW.2)).HasGap (c₂ * σ))).card : ℝ) ≤
          Real.exp (-(a * L)) * ((N.choose k : ℕ) : ℝ) ^ 2 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := BipSampling.exists_colSampProp
  refine ⟨1 / 4, by norm_num, fun a c₁ ha hc₁ => ?_⟩
  obtain ⟨c₁', hc₁'pos, hc₁'le, hc₁'c⟩ : ∃ c₁' : ℝ, 0 < c₁' ∧ c₁' ≤ 1 / 4 ∧ c₁' ≤ c₁ :=
    ⟨min c₁ (1 / 4), lt_min hc₁ (by norm_num), min_le_right _ _, min_le_left _ _⟩
  refine ⟨c₁' / 8, (a + 5) * (12 / c₁' ^ 2 + 10000 * C₀ ^ 2 + 3), by positivity,
    by positivity, ?_⟩
  intro V _ _ H A B N k η D σ L hAB hAB' hAcard hBcard hA hB hwt hdeg hgap hσ hσ1 hη hL hkN hpD
  -- the degenerate case `N = 0`
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · have hV : ∀ x : V, False := by
      intro x
      have hx : x ∈ A ∪ B := hAB' ▸ mem_univ x
      rcases mem_union.1 hx with hx | hx
      · have := card_pos.2 ⟨x, hx⟩; omega
      · have := card_pos.2 ⟨x, hx⟩; omega
    rw [filter_false_of_mem]
    · simp only [card_empty, Nat.cast_zero]; positivity
    · intro UW _
      rw [not_not]
      refine ⟨fun x => (hV x.1).elim, fun f => ⟨0, ?_⟩⟩
      have : IsEmpty ↥(UW.1 ∪ UW.2) := ⟨fun x => hV x.1⟩
      simp [WGraph.dirichlet]
  -- basic numerics
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (a + 5) * (12 / c₁' ^ 2 + 10000 * C₀ ^ 2 + 3) := ⟨_, rfl⟩
  rw [← hC] at hpD
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (k : ℝ) / N := ⟨_, rfl⟩
  rw [← hp] at hpD ⊢
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hNpos' : (0 : ℝ) < N := by linarith
  have hlog2 : Real.log 2 ≤ L :=
    le_trans (Real.log_le_log (by norm_num) (by linarith)) hL
  have hLpos : 0 < L := lt_of_lt_of_le (Real.log_pos (by norm_num)) hlog2
  have hCpos : 0 < C := by rw [hC]; positivity
  have hCL : C * L ≤ σ ^ 2 * (p * D) := by
    rw [Real.rpow_neg hσ.le, Real.rpow_two] at hpD
    have h1 := mul_le_mul_of_nonneg_left hpD (sq_nonneg σ)
    have h2 : σ ^ 2 * (C * (σ ^ 2)⁻¹ * L) = C * L := by field_simp
    linarith
  have hpDpos : 0 < p * D :=
    pos_of_mul_pos_right (lt_of_lt_of_le (mul_pos hCpos hLpos) hCL) (sq_nonneg σ)
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      rw [hp, h, Nat.cast_zero, zero_div, zero_mul] at hpDpos
      exact lt_irrefl 0 hpDpos
    · exact h
  have hp0 : 0 < p := by rw [hp]; exact div_pos (by exact_mod_cast hk1) hNpos'
  have hD : 0 < D := pos_of_mul_pos_right hpDpos hp0.le
  -- degrees
  obtain ⟨i₀, hi₀⟩ : A.Nonempty := card_pos.1 (by omega)
  have hη0 : 0 ≤ η := nonneg_of_mul_nonneg_left (le_trans (abs_nonneg _) (hdeg i₀)) hD
  have hη' : η ≤ σ / 32 := by
    have : c₁' / 8 * σ ≤ 1 / 4 / 8 * σ := by gcongr
    linarith
  have hη32 : η ≤ 1 / 32 := by linarith
  have hdlo : ∀ x, (1 - η) * D ≤ H.deg x := fun x => by
    have := abs_le.1 (hdeg x); linarith only [this.1]
  have hdhi : ∀ x, H.deg x ≤ (1 + η) * D := fun x => by
    have := abs_le.1 (hdeg x); linarith only [this.2]
  have hdpos : ∀ x, 0 < H.deg x := fun x =>
    lt_of_lt_of_le (mul_pos (by linarith only [hη32]) hD) (hdlo x)
  have hwle : ∀ x y, H.w x y ≤ 1 := fun x y => by
    rcases (H.nonneg x y).lt_or_eq with h | h
    · exact (hwt x y h).2
    · rw [← h]; norm_num
  have hw : ∀ x y, 0 ≤ H.w x y ∧ H.w x y ≤ 1 := fun x y => ⟨H.nonneg x y, hwle x y⟩
  have hdA : ∀ i ∈ A, H.deg i = ∑ j ∈ B, H.w i j := fun i hi => by
    unfold WGraph.deg
    rw [← hAB', BipSampling.sum_union_left_zero A B hAB H.w i (fun y hy => hA i hi y hy)]
  have hdB : ∀ j ∈ B, H.deg j = ∑ i ∈ A, H.w i j := fun j hj => by
    unfold WGraph.deg
    rw [← hAB', BipSampling.sum_union_right_zero A B hAB H.w j (fun y hy => hB j hj y hy)]
    exact sum_congr rfl fun i _ => H.symm _ _
  have hdN : ∀ i ∈ A, H.deg i ≤ N := fun i hi => by
    rw [hdA i hi, ← hBcard]
    calc ∑ j ∈ B, H.w i j ≤ ∑ j ∈ B, (1 : ℝ) := sum_le_sum fun j _ => hwle i j
      _ = B.card := by simp
  have hDN : (1 - η) * D ≤ N := le_trans (hdlo i₀) (hdN i₀ hi₀)
  have hDN2 : D ≤ 2 * N := by
    nlinarith only [hDN, mul_le_mul_of_nonneg_right hη32 hD.le, hD]
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ∑ l ∈ A, H.deg l := ⟨_, rfl⟩
  have he_lo : N * ((1 - η) * D) ≤ e := by
    have : ∑ l ∈ A, (1 - η) * D ≤ ∑ l ∈ A, H.deg l := sum_le_sum fun l _ => hdlo l
    rw [sum_const, hAcard, nsmul_eq_mul, ← he] at this
    exact this
  have hepos : 0 < e :=
    lt_of_lt_of_le (mul_pos hNpos' (mul_pos (by linarith only [hη32]) hD)) he_lo
  -- the matrix `F = K - d_A d_Bᵀ / e`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (1 - σ) * ((1 + η) * D) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (by linarith only [hσ1]) (mul_nonneg (by linarith only [hη0]) hD.le)
  have hspec := BipSampling.spectral_bound H A B hAB hAB' hA hB σ ((1 + η) * D) hgap hσ.le hσ1
    hdhi hdA hdB (by rw [← he]; exact hepos)
  rw [← he, ← hM] at hspec
  have hop1 := BipSampling.op_of_bil' A B (fun i j => H.w i j - H.deg i * H.deg j / e) M hM0
    hspec
  have hFm2 : ∀ i ∈ A, ∀ j ∈ B,
      (H.w i j - H.deg i * H.deg j / e) ^ 2 ≤ 2 * H.w i j + 16 * D / N := fun i _ j _ =>
    BipSampling.num_entry_sq (H.nonneg i j) (hwle i j)
      (div_nonneg (mul_nonneg (hdpos i).le (hdpos j).le) hepos.le)
      (BipSampling.num_rank_one (hdpos i) (hdpos j) (hdhi i) (hdhi j) he_lo hNpos' hD hη0 hη32
        hepos) hD hNpos' hDN2
  have hrow : ∀ i ∈ A, ∑ j ∈ B, (H.w i j - H.deg i * H.deg j / e) ^ 2 ≤ 24 * D := by
    intro i hi
    have e1 : (N : ℝ) * (16 * D / N) = 16 * D := by field_simp
    calc ∑ j ∈ B, (H.w i j - H.deg i * H.deg j / e) ^ 2
        ≤ ∑ j ∈ B, (2 * H.w i j + 16 * D / N) := sum_le_sum fun j hj => hFm2 i hi j hj
      _ = 2 * H.deg i + 16 * D := by
          rw [sum_add_distrib, ← mul_sum, ← hdA i hi, sum_const, hBcard, nsmul_eq_mul, e1]
      _ ≤ 24 * D := by
          linarith only [hdhi i, hD, mul_le_mul_of_nonneg_right hη32 hD.le]
  -- parameters of the two sampling rounds
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = (a + 5) * L := ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_def]; positivity
  have hCLt : C * L = t * (12 / c₁' ^ 2 + 10000 * C₀ ^ 2 + 3) := by rw [hC, ht_def]; ring
  have h12pos : 0 ≤ 12 / c₁' ^ 2 := by positivity
  have htC₀ : 0 ≤ t * C₀ ^ 2 := mul_nonneg ht.le (sq_nonneg _)
  have ht12 : 0 ≤ t * (12 / c₁' ^ 2) := mul_nonneg ht.le h12pos
  have hσ21 : σ ^ 2 ≤ 1 := by nlinarith only [hσ, hσ1]
  have hPt3 : 3 * t ≤ p * D := by
    have h1 : 3 * t ≤ C * L := by rw [hCLt]; linarith only [htC₀, ht12]
    linarith only [h1, hCL, mul_le_mul_of_nonneg_right hσ21 hpDpos.le]
  have hPt12 : 12 * t ≤ c₁' ^ 2 * (σ ^ 2 * (p * D)) := by
    have h1 : t * (12 / c₁' ^ 2) ≤ C * L := by rw [hCLt]; linarith only [htC₀, ht]
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hCL) (sq_nonneg c₁')
    have h3 : c₁' ^ 2 * (t * (12 / c₁' ^ 2)) = 12 * t := by field_simp
    linarith only [h2, h3]
  have hPtC : 10000 * C₀ ^ 2 * t ≤ σ ^ 2 * (p * D) := by
    have h1 : 10000 * C₀ ^ 2 * t ≤ C * L := by rw [hCLt]; linarith only [ht12, ht]
    linarith only [h1, hCL]
  obtain ⟨β₁, hβ₁⟩ : ∃ β : ℝ, β = Real.sqrt p * M + C₀ * Real.sqrt (24 * D) * Real.sqrt t :=
    ⟨_, rfl⟩
  obtain ⟨β₂, hβ₂⟩ : ∃ β : ℝ,
      β = Real.sqrt p * β₁ + C₀ * Real.sqrt (24 * (p * D)) * Real.sqrt t := ⟨_, rfl⟩
  have hβ₁0 : 0 ≤ β₁ := by
    rw [hβ₁]
    exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hM0)
      (mul_nonneg (mul_nonneg hC₀pos.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hβ₂0 : 0 ≤ β₂ := by
    rw [hβ₂]
    exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hβ₁0)
      (mul_nonneg (mul_nonneg hC₀pos.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hβ₂le : β₂ ≤ p * M + σ * (p * D) / 8 := by
    rw [hβ₂, hβ₁]; exact BipSampling.num_beta hp0 hD ht hσ hPtC
  have hnum : 1 / 4 * σ * ((1 + c₁' * σ) * (p * D)) ≤ (1 - c₁' * σ) * (p * D) - β₂ :=
    BipSampling.num_gap hσ hσ1 hη0 hη' hc₁'le hpDpos (by rw [hM]; ring) hβ₂le
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = c₁' * σ * (p * D) / 2 := ⟨_, rfl⟩
  have ht₀pos : 0 < t₀ := by
    rw [ht₀]; exact div_pos (mul_pos (mul_pos hc₁'pos hσ) hpDpos) (by norm_num)
  have ht₀le : t₀ ≤ p * D := by
    rw [ht₀]
    have h1 : c₁' * σ ≤ 1 := by nlinarith only [hc₁'le, hσ1, hc₁'pos, hσ]
    nlinarith only [h1, hpDpos]
  have ht₀sq : t * (3 * (p * D)) ≤ t₀ ^ 2 := by
    rw [ht₀]; nlinarith only [mul_le_mul_of_nonneg_right hPt12 hpDpos.le]
  have hdeg_of : ∀ (x : V) (s : ℝ), ¬ (p * H.deg x + t₀ ≤ s) → ¬ (s ≤ p * H.deg x - t₀) →
      |s - p * D| ≤ c₁' * σ * (p * D) :=
    fun x s h1 h2 => BipSampling.num_deg_close hp0 hD (hdeg x) hη ht₀ h1 h2
  -- the union bound
  have hinc := BipSampling.sampling_inclusion H A B k hAB hA hB hk1 hdpos hdA hdB e (p * D) c₁
    c₁' σ p t₀ β₂ hepos hc₁'c hσ hpDpos hβ₂0 hnum hdeg_of (BipSampling.bad1 H A B k e β₁)
    (BipSampling.bad2 H A B k p (p * D))
  refine le_trans (Nat.cast_le.2 (card_le_card hinc)) ?_
  refine le_trans (Nat.cast_le.2 (BipSampling.card_union5_le _ _ _ _ _)) ?_
  have hc1 := BipSampling.count_bad1 hC₀ H A B N k hAcard hBcard hkN e M D t β₁ hM0 hD.le ht
    hop1 hrow (by rw [hβ₁, hp])
  have hc2 := BipSampling.count_bad2 H A B N k hAcard hBcard hw p D η t hp hp0 hdB hdpos hdhi
    hη32 hpDpos ht.le hPt3
  have hc3 := BipSampling.count_bad3 hC₀ H A B N k hAcard hBcard hkN e p D η t β₁ β₂ hp hp0
    hpDpos ht hβ₁0 hβ₂ hFm2 hdB hdhi hη32
  have hc4 := BipSampling.count_bad4 H A B N k hAcard hBcard hw p D η t t₀ hp hp0 hdA hdpos
    hdhi hη32 hpDpos ht.le ht₀pos ht₀le ht₀sq
  have hc5 := BipSampling.count_bad5 H A B N k hAcard hBcard hw p D η t t₀ hp hp0 hdB hdpos
    hdhi hη32 hpDpos ht.le ht₀pos ht₀le ht₀sq
  have hfin := BipSampling.num_final (a := a) hNpos hkN hL ht_def
  have hK : (0 : ℝ) ≤ N.choose k := Nat.cast_nonneg _
  simp only [Nat.cast_add, card_product, Nat.cast_mul, card_powersetCard, hBcard]
  calc _ ≤ (N * (N + 1) * Real.exp (-t) * N.choose k) * N.choose k +
        (N * (Real.exp (-t) * N.choose k)) * N.choose k +
        N.choose k * (k * (N + 1) * Real.exp (-t) * N.choose k) +
        N * (N.choose k * (2 * (Real.exp (-t) * N.choose k))) +
        N * (2 * (Real.exp (-t) * N.choose k) * N.choose k) :=
        add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hc1 hK)
          (mul_le_mul_of_nonneg_right hc2 hK)) hc3) hc4) hc5
    _ = ((N : ℝ) * (N + 1) + N + k * (N + 1) + 4 * N) * Real.exp (-t) *
        ((N.choose k : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ Real.exp (-(a * L)) * ((N.choose k : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hfin (sq_nonneg _)


end Lovasz
