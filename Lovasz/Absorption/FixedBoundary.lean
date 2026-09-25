/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Absorption.Basic
import Lovasz.BipartiteSampling

/-!
# Lemma 2.4: fixed boundary, fresh layer

DAG node `L2.4` of `docs/BLUEPRINT.md`.

The proof is the second stage of Lemma 2.3 (`bipartite_sampling`), with the first stage replaced
by the hypothesis `OneSided`: the operator bound on `F[U, B]` restricts to `F[U, B']`, Lemma 2.2
over the pool `B'` bounds `F[U, W]`, the degrees from `W` to `U` are given by `OneSided.deg_near`,
the degrees from `U` to `W` concentrate about `p' d(u, B')` with `p' = k / |B'|`, and
`BipSampling.good_of_bounds` gives the gap.
-/

universe u

namespace Lovasz

open Finset

namespace LocalAbsorption

/-- Comparison of the sampling ratios `p = k / N` and `p' = k / |B'|` for `|B'| ≥ (1 - x) N`. -/
lemma fb_ratio {p p' b N x : ℝ} (hN : 0 < N) (hp : 0 ≤ p) (hpp : p' * b = p * N)
    (hb : (1 - x) * N ≤ b) (hbN : b ≤ N) (hx : x ≤ 1 / 2) :
    p ≤ p' ∧ p' * (1 - x) ≤ p := by
  have hb0 : 0 < b := by nlinarith
  have hp' : 0 ≤ p' := nonneg_of_mul_nonneg_left (by rw [hpp]; positivity) hb0
  refine ⟨le_of_mul_le_mul_right (by rw [hpp]; exact mul_le_mul_of_nonneg_left hbN hp) hb0,
    le_of_mul_le_mul_right ?_ hN⟩
  calc p' * (1 - x) * N = p' * ((1 - x) * N) := by ring
    _ ≤ p' * b := mul_le_mul_of_nonneg_left hb hp'
    _ = p * N := hpp

/-- The mean degree `p' d(u, B')` is `(1 ± 4x) p D`. -/
lemma fb_bias {p p' d D x : ℝ} (hp : 0 < p) (hpp : p ≤ p') (hpp' : p' * (1 - x) ≤ p)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) (hD : 0 < D) (hdlo : (1 - 2 * x) * D ≤ d)
    (hdhi : d ≤ (1 + x) * D) :
    0 < p' * d ∧ p' * d ≤ (1 + 4 * x) * (p * D) ∧ |p' * d - p * D| ≤ 4 * x * (p * D) := by
  have hd : 0 < d := by nlinarith
  have hp'0 : 0 < p' := lt_of_lt_of_le hp hpp
  have h5 : 0 < 1 - x := by linarith
  have h2 : p' * (1 + x) ≤ p * (1 + 4 * x) := by
    have h3 : p' * (1 - x) * (1 + x) ≤ p * (1 + x) :=
      mul_le_mul_of_nonneg_right hpp' (by linarith)
    have h4 : p * (1 + x) ≤ p * (1 + 4 * x) * (1 - x) := by
      nlinarith [mul_nonneg (mul_nonneg hp.le hx0) (by linarith : (0 : ℝ) ≤ 1 - 2 * x)]
    refine le_of_mul_le_mul_right ?_ h5
    nlinarith
  have hup : p' * d ≤ (1 + 4 * x) * (p * D) := by
    have h1 : p' * d ≤ p' * ((1 + x) * D) := mul_le_mul_of_nonneg_left hdhi hp'0.le
    nlinarith [mul_le_mul_of_nonneg_right h2 hD.le]
  have hlo : p * ((1 - 2 * x) * D) ≤ p' * d :=
    mul_le_mul hpp hdlo (by nlinarith) hp'0.le
  have hxpD : 0 ≤ x * (p * D) := mul_nonneg hx0 (mul_pos hp hD).le
  refine ⟨mul_pos hp'0 hd, hup, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩

/-- The operator bound after the column sampling from the pool:
`√p' ‖F[U, B']‖ + C₀ c √t ≤ (1 + x)(1 - σ/2) p D + σ p D / 16`. -/
lemma fb_beta {p p' D σ K C₀ t L x : ℝ} (hp : 0 < p) (hpp : p ≤ p') (hpp' : p' * (1 - x) ≤ p)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (hD : 0 < D) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hK : 0 < K)
    (ht : 0 < t) (hL : 0 < L)
    (h1 : 2048 * K ^ 2 * L ≤ σ ^ 2 * (p * D)) (h2 : 1024 * C₀ ^ 2 * K * t ≤ σ ^ 2 * (p * D)) :
    Real.sqrt p' * (Real.sqrt p * (1 - σ / 2) * D + K * Real.sqrt (D * L)) +
      C₀ * Real.sqrt (K * p * D) * Real.sqrt t ≤
      (1 + x) * (1 - σ / 2) * (p * D) + σ * (p * D) / 16 := by
  have hP : 0 < p * D := mul_pos hp hD
  have hp'0 : 0 < p' := lt_of_lt_of_le hp hpp
  have hp'2 : p' ≤ 2 * p := by
    nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ 1 - x by linarith) hp'0.le]
  have hp'x : p' ≤ (1 + 2 * x) * p := by
    nlinarith [mul_le_mul_of_nonneg_left hp'2 hx0]
  have hσP : 0 ≤ σ * (p * D) / 32 := by positivity
  have e1 : Real.sqrt p' * Real.sqrt p ≤ (1 + x) * p := by
    rw [← Real.sqrt_mul hp'0.le]
    calc Real.sqrt (p' * p) ≤ Real.sqrt (((1 + x) * p) ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith [mul_le_mul_of_nonneg_right hp'x hp.le, mul_nonneg (sq_nonneg x) (sq_nonneg p)]
      _ = (1 + x) * p := Real.sqrt_sq (by positivity)
  have e2 : Real.sqrt p' * (K * Real.sqrt (D * L)) ≤ σ * (p * D) / 32 := by
    have hsq : (Real.sqrt p' * (K * Real.sqrt (D * L))) ^ 2 ≤ (σ * (p * D) / 32) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hp'0.le, Real.sq_sqrt (by positivity)]
      have : p' * (K ^ 2 * (D * L)) ≤ 2 * p * (K ^ 2 * (D * L)) :=
        mul_le_mul_of_nonneg_right hp'2 (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right h1 hP.le]
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq hsq hσP)
  have e3 : C₀ * Real.sqrt (K * p * D) * Real.sqrt t ≤ σ * (p * D) / 32 := by
    have hsq : (C₀ * Real.sqrt (K * p * D) * Real.sqrt t) ^ 2 ≤ (σ * (p * D) / 32) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt ht.le]
      nlinarith [mul_le_mul_of_nonneg_right h2 hP.le]
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq hsq hσP)
  have h1σ : 0 ≤ (1 - σ / 2) * D := mul_nonneg (by linarith) hD.le
  have e1' : Real.sqrt p' * Real.sqrt p * ((1 - σ / 2) * D) ≤
      (1 + x) * p * ((1 - σ / 2) * D) :=
    mul_le_mul_of_nonneg_right e1 h1σ
  calc Real.sqrt p' * (Real.sqrt p * (1 - σ / 2) * D + K * Real.sqrt (D * L)) +
        C₀ * Real.sqrt (K * p * D) * Real.sqrt t
      = Real.sqrt p' * Real.sqrt p * ((1 - σ / 2) * D) +
          Real.sqrt p' * (K * Real.sqrt (D * L)) +
          C₀ * Real.sqrt (K * p * D) * Real.sqrt t := by ring
    _ ≤ (1 + x) * p * ((1 - σ / 2) * D) + σ * (p * D) / 32 + σ * (p * D) / 32 := by linarith
    _ = _ := by ring

/-- The numerical gap condition of `BipSampling.good_of_bounds` with degree tolerance `δ σ`. -/
lemma fb_num_gap {σ δ P β : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hδ : 0 < δ) (hδ₀ : δ ≤ 1 / 16)
    (hP : 0 < P) (hβ : β ≤ (1 + δ / 64 * σ) * (1 - σ / 2) * P + σ * P / 16) :
    1 / 4 * σ * ((1 + δ * σ) * P) ≤ (1 - δ * σ) * P - β := by
  have hσP : 0 < σ * P := mul_pos hσ hP
  have h1 : δ * (σ * P) ≤ 1 / 16 * (σ * P) := mul_le_mul_of_nonneg_right hδ₀ hσP.le
  have h2 : δ * σ * P * σ ≤ δ * σ * P * 1 := mul_le_mul_of_nonneg_left hσ1 (by positivity)
  nlinarith

open Classical in
/-- **Lemma 2.4 (Fixed boundary, fresh layer)** (DAG node `L2.4`), the per-transition input of
the fresh-layer step `T3.2f`. Let `H` be bipartite with classes `A, B` of size `N`, weights in
`[ω, 1]`, degrees `(1 ± η) D`, gap `σ`, `η ≤ cσ`, `L ≥ log (2N)`. Let `U ⊆ A` be a fixed set of
`k = pN` rows satisfying the one-sided events (2.9) (`OneSided`, constants `K, δ`), and let
`B' ⊆ B` be any column pool with `|B'| ≥ (1 - cσ) N` from which every vertex has lost at most
`cσD` weighted neighbours, and `pD ≥ C σ^{-2} L`. Then all but an `e^{-aL}` fraction of the
`k`-subsets `W ⊆ B'` give a graph `H[U ∪ W]` with degrees `(1 ± δσ) pD` and gap at least
`c₂ σ`. The pool is deterministic: no independence of its choice is assumed. -/
theorem fixed_boundary_fresh_layer (ω : ℝ) (hω : 0 < ω) :
    ∃ c₂ δ₀ : ℝ, 0 < c₂ ∧ 0 < δ₀ ∧ ∀ a K δ : ℝ, 0 < a → 0 < K → 0 < δ → δ ≤ δ₀ →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (A B U B' : Finset V)
        (N k : ℕ) (η D σ L : ℝ),
        Disjoint A B → A ∪ B = univ → A.card = N → B.card = N →
        (∀ x ∈ A, ∀ y ∈ A, H.w x y = 0) → (∀ x ∈ B, ∀ y ∈ B, H.w x y = 0) →
        H.WeightsIn ω → H.DegNear D η → H.HasGap σ → 0 < σ → σ ≤ 1 → η ≤ c * σ →
        Real.log (2 * N) ≤ L → U ⊆ A → U.card = k →
        OneSided H A B U ((k : ℝ) / N) D σ L K δ →
        B' ⊆ B → (1 - c * σ) * N ≤ B'.card → (∀ v, H.degOn v (B \ B') ≤ c * σ * D) →
        C * σ ^ (-2 : ℝ) * L ≤ (k : ℝ) / N * D →
        (((B'.powersetCard k).filter fun W =>
            ¬ ((H.induce (U ∪ W)).DegNear ((k : ℝ) / N * D) (δ * σ) ∧
              (H.induce (U ∪ W)).HasGap (c₂ * σ))).card : ℝ) ≤
          Real.exp (-(a * L)) * (B'.card.choose k : ℕ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := BipSampling.exists_colSampProp
  refine ⟨1 / 4, 1 / 16, by norm_num, by norm_num, fun a K δ ha hK hδ hδ₀ => ?_⟩
  refine ⟨δ / 64, 2048 * K ^ 2 + (a + 5) * (1024 * C₀ ^ 2 * K + 12 / δ ^ 2), by positivity,
    by positivity, ?_⟩
  intro V _ _ H A B U B' N k η D σ L hAB hAB' hAcard hBcard hA hB hwt hdeg hgap hσ hσ1 hη hL
    hUA hUk hOS hB'B hB'card hloss hpD
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 2048 * K ^ 2 + (a + 5) * (1024 * C₀ ^ 2 * K + 12 / δ ^ 2) :=
    ⟨_, rfl⟩
  rw [← hC] at hpD
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = δ / 64 * σ := ⟨_, rfl⟩
  rw [← hx] at hη hB'card hloss
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (k : ℝ) / N := ⟨_, rfl⟩
  rw [← hp] at hpD hOS ⊢
  have hCpos : 0 < C := by rw [hC]; positivity
  -- the degenerate cases
  by_cases hkB' : B'.card < k
  · rw [powersetCard_eq_empty.2 hkB', filter_empty, card_empty, Nat.cast_zero]
    positivity
  rw [not_lt] at hkB'
  by_cases hL0 : L ≤ 0
  · calc _ ≤ ((B'.powersetCard k).card : ℝ) := by exact_mod_cast card_filter_le _ _
      _ = (B'.card.choose k : ℕ) := by rw [card_powersetCard]
      _ ≤ _ := le_mul_of_one_le_left (Nat.cast_nonneg _)
          (Real.one_le_exp (by linarith only [mul_le_mul_of_nonneg_left hL0 ha.le]))
  rw [not_le] at hL0
  have hLpos : 0 < L := hL0
  -- basic numerics
  have hCL : C * L ≤ σ ^ 2 * (p * D) := by
    rw [Real.rpow_neg hσ.le, Real.rpow_two] at hpD
    have h1 := mul_le_mul_of_nonneg_left hpD (sq_nonneg σ)
    have h2 : σ ^ 2 * (C * (σ ^ 2)⁻¹ * L) = C * L := by field_simp
    linarith
  have hpDpos : 0 < p * D :=
    pos_of_mul_pos_right (lt_of_lt_of_le (mul_pos hCpos hLpos) hCL) (sq_nonneg σ)
  have hp0' : 0 ≤ p := by rw [hp]; positivity
  have hp0 : 0 < p := lt_of_le_of_ne hp0' (fun h => by
    rw [← h, zero_mul] at hpDpos; exact lt_irrefl _ hpDpos)
  have hD : 0 < D := pos_of_mul_pos_right hpDpos hp0'
  have hNpos : 0 < N := Nat.pos_of_ne_zero (fun h => by
    rw [hp, h, Nat.cast_zero, div_zero] at hp0; exact lt_irrefl _ hp0)
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (fun h => by
    rw [hp, h, Nat.cast_zero, zero_div] at hp0; exact lt_irrefl _ hp0)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hNpos' : (0 : ℝ) < N := by linarith
  have hkN : k ≤ N := by rw [← hUk, ← hAcard]; exact card_le_card hUA
  have hB'N : B'.card ≤ N := by rw [← hBcard]; exact card_le_card hB'B
  have hbR : (B'.card : ℝ) ≤ N := by exact_mod_cast hB'N
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hkN
  -- degrees
  obtain ⟨i₀, hi₀⟩ : A.Nonempty := card_pos.1 (by omega)
  have hη0 : 0 ≤ η := nonneg_of_mul_nonneg_left (le_trans (abs_nonneg _) (hdeg i₀)) hD
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hxs : x ≤ 1 / 1024 := by
    rw [hx]
    linarith only [mul_le_mul_of_nonneg_left hσ1 (by positivity : (0 : ℝ) ≤ δ / 64), hδ₀]
  have hdlo : ∀ v, (1 - η) * D ≤ H.deg v := fun v => by
    have := abs_le.1 (hdeg v); linarith only [this.1]
  have hdhi : ∀ v, H.deg v ≤ (1 + η) * D := fun v => by
    have := abs_le.1 (hdeg v); linarith only [this.2]
  have hdpos : ∀ v, 0 < H.deg v := fun v =>
    lt_of_lt_of_le (mul_pos (by linarith) hD) (hdlo v)
  have hwle : ∀ u v, H.w u v ≤ 1 := fun u v => by
    rcases (H.nonneg u v).lt_or_eq with h | h
    · exact (hwt u v h).2
    · rw [← h]; norm_num
  have hw : ∀ u v, 0 ≤ H.w u v ∧ H.w u v ≤ 1 := fun u v => ⟨H.nonneg u v, hwle u v⟩
  have hdA : ∀ i ∈ A, H.deg i = ∑ j ∈ B, H.w i j := fun i hi => by
    unfold WGraph.deg
    rw [← hAB', BipSampling.sum_union_left_zero A B hAB H.w i (fun y hy => hA i hi y hy)]
  have hdB : ∀ j ∈ B, H.deg j = ∑ i ∈ A, H.w i j := fun j hj => by
    unfold WGraph.deg
    rw [← hAB', BipSampling.sum_union_right_zero A B hAB H.w j (fun y hy => hB j hj y hy)]
    exact sum_congr rfl fun i _ => H.symm _ _
  have hdB' : ∀ j ∈ B, H.degOn j A = H.deg j := fun j hj => by
    unfold WGraph.degOn
    rw [hdB j hj]
    exact sum_congr rfl fun i _ => H.symm _ _
  have hdA' : ∀ i ∈ A, H.degOn i B = H.deg i := fun i hi => (hdA i hi).symm
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ∑ l ∈ A, H.deg l := ⟨_, rfl⟩
  have hepos : 0 < e := by rw [he]; exact sum_pos (fun l _ => hdpos l) ⟨i₀, hi₀⟩
  have hedge : H.edgeWeight A B = e := by
    rw [he]
    unfold WGraph.edgeWeight
    exact sum_congr rfl fun i hi => (hdA i hi).symm
  have hcent : ∀ i ∈ A, ∀ j ∈ B, centred H A B i j = H.w i j - H.deg i * H.deg j / e := by
    intro i hi j hj
    unfold centred
    rw [hdB' j hj, hdA' i hi, hedge]
  -- the sampling ratio of the pool
  have hb0 : (0 : ℝ) < B'.card := by
    linarith only [hB'card, mul_le_mul_of_nonneg_right hxs hNpos'.le, hNpos']
  obtain ⟨p', hp'⟩ : ∃ p' : ℝ, p' = (k : ℝ) / B'.card := ⟨_, rfl⟩
  have hpp' : p' * B'.card = p * N := by
    rw [hp', hp, div_mul_cancel₀ _ hb0.ne', div_mul_cancel₀ _ hNpos'.ne']
  obtain ⟨hpp, hpp'x⟩ := fb_ratio hNpos' hp0' hpp' hB'card hbR (by linarith)
  -- degrees of the fixed rows into the pool
  have hduB' : ∀ u ∈ U, (1 - 2 * x) * D ≤ ∑ j ∈ B', H.w u j ∧
      ∑ j ∈ B', H.w u j ≤ (1 + x) * D := by
    intro u hu
    have hsplit := sum_sdiff hB'B (f := fun j => H.w u j)
    rw [← hdA u (hUA hu)] at hsplit
    have hl := hloss u
    unfold WGraph.degOn at hl
    have hnn : 0 ≤ ∑ j ∈ B \ B', H.w u j := sum_nonneg fun j _ => H.nonneg u j
    have h1 := hdlo u
    have h2 := hdhi u
    have h3 : η * D ≤ x * D := mul_le_mul_of_nonneg_right hη hD.le
    constructor <;> linarith
  have hμ : ∀ u ∈ U, 0 < p' * ∑ j ∈ B', H.w u j ∧
      p' * ∑ j ∈ B', H.w u j ≤ (1 + 4 * x) * (p * D) ∧
      |p' * ∑ j ∈ B', H.w u j - p * D| ≤ 4 * x * (p * D) := fun u hu =>
    fb_bias hp0 hpp hpp'x hx0 (by linarith) hD (hduB' u hu).1 (hduB' u hu).2
  -- parameters
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = (a + 5) * L := ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_def]; positivity
  have hK1 : 2048 * K ^ 2 * L ≤ σ ^ 2 * (p * D) := by
    have h0 : 0 ≤ (a + 5) * (1024 * C₀ ^ 2 * K + 12 / δ ^ 2) * L := by positivity
    have : 2048 * K ^ 2 * L ≤ C * L := by rw [hC]; linarith
    linarith
  have hK2 : 1024 * C₀ ^ 2 * K * t ≤ σ ^ 2 * (p * D) := by
    have h1 : 0 ≤ 2048 * K ^ 2 * L := by positivity
    have h2 : 0 ≤ (a + 5) * (12 / δ ^ 2) * L := by positivity
    have : 1024 * C₀ ^ 2 * K * t ≤ C * L := by rw [hC, ht_def]; linarith
    linarith
  have hPt12 : 12 * t ≤ δ ^ 2 * (σ ^ 2 * (p * D)) := by
    have h1 : t * (12 / δ ^ 2) ≤ C * L := by
      have h1 : 0 ≤ 2048 * K ^ 2 * L := by positivity
      have h2 : 0 ≤ (a + 5) * (1024 * C₀ ^ 2 * K) * L := by positivity
      rw [hC, ht_def]; linarith
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hCL) (sq_nonneg δ)
    have h3 : δ ^ 2 * (t * (12 / δ ^ 2)) = 12 * t := by field_simp
    linarith
  obtain ⟨β₁, hβ₁⟩ : ∃ β : ℝ, β = Real.sqrt p * (1 - σ / 2) * D + K * Real.sqrt (D * L) :=
    ⟨_, rfl⟩
  obtain ⟨β₂, hβ₂⟩ : ∃ β : ℝ,
      β = Real.sqrt p' * β₁ + C₀ * Real.sqrt (K * p * D) * Real.sqrt t := ⟨_, rfl⟩
  have hβ₁0 : 0 ≤ β₁ := by
    rw [hβ₁]
    exact add_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) hD.le)
      (mul_nonneg hK.le (Real.sqrt_nonneg _))
  have hβ₂0 : 0 ≤ β₂ := by
    rw [hβ₂]
    exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hβ₁0)
      (mul_nonneg (mul_nonneg hC₀pos.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hβ₂le : β₂ ≤ (1 + x) * (1 - σ / 2) * (p * D) + σ * (p * D) / 16 := by
    rw [hβ₂, hβ₁]
    exact fb_beta hp0 hpp hpp'x hx0 (by linarith) hD hσ hσ1 hK ht hLpos hK1 hK2
  have hnum : 1 / 4 * σ * ((1 + δ * σ) * (p * D)) ≤ (1 - δ * σ) * (p * D) - β₂ :=
    fb_num_gap hσ hσ1 hδ hδ₀ hpDpos (by rw [hx] at hβ₂le; exact hβ₂le)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = δ * σ * (p * D) / 2 := ⟨_, rfl⟩
  have hTpos : 0 < T := by rw [hT]; positivity
  have hTle : T ≤ p * D := by
    rw [hT]
    have h1 : δ * σ ≤ 1 := by linarith only [mul_le_mul_of_nonneg_left hσ1 hδ.le, hδ₀]
    linarith only [mul_le_mul_of_nonneg_right h1 hpDpos.le, hpDpos]
  have hTsq : t * (3 * (p * D)) ≤ T ^ 2 := by
    rw [hT]; linarith only [mul_le_mul_of_nonneg_right hPt12 hpDpos.le]
  -- the two bad events
  obtain ⟨badA, hbadA⟩ : ∃ s : Finset (Finset V), s = (B'.powersetCard k).filter fun W =>
      ∃ v : V → ℝ, β₂ ^ 2 * ∑ j ∈ W, v j ^ 2 <
        ∑ i ∈ U, (∑ j ∈ W, (H.w i j - H.deg i * H.deg j / e) * v j) ^ 2 := ⟨_, rfl⟩
  obtain ⟨badB, hbadB⟩ : ∃ s : Finset (Finset V), s = U.biUnion fun i =>
      (B'.powersetCard k).filter (fun W => p' * ∑ j ∈ B', H.w i j + T ≤ ∑ j ∈ W, H.w i j) ∪
      (B'.powersetCard k).filter (fun W => ∑ j ∈ W, H.w i j ≤ p' * ∑ j ∈ B', H.w i j - T) :=
    ⟨_, rfl⟩
  -- outside the bad events the sample is good
  have key : ∀ W ∈ B'.powersetCard k, W ∉ badA → W ∉ badB →
      (H.induce (U ∪ W)).DegNear (p * D) (δ * σ) ∧ (H.induce (U ∪ W)).HasGap (1 / 4 * σ) := by
    intro W hW hWA hWB
    have hWB' : W ⊆ B' := (mem_powersetCard.1 hW).1
    have hWsub : W ⊆ B := hWB'.trans hB'B
    have hUne : U.Nonempty := card_pos.1 (by omega)
    have hop : ∀ v : V → ℝ, ∑ i ∈ U, (∑ j ∈ W, (H.w i j - H.deg i * H.deg j / e) * v j) ^ 2 ≤
        β₂ ^ 2 * ∑ j ∈ W, v j ^ 2 := by
      intro v
      by_contra hc
      exact hWA (by rw [hbadA, mem_filter]; exact ⟨hW, v, not_le.1 hc⟩)
    have hdU : ∀ i ∈ U, |∑ j ∈ W, H.w i j - p * D| ≤ δ * σ * (p * D) := by
      intro i hi
      have h1 : ∑ j ∈ W, H.w i j < p' * ∑ j ∈ B', H.w i j + T := not_le.1 fun h =>
        hWB (by rw [hbadB]; exact mem_biUnion.2 ⟨i, hi, mem_union_left _ (mem_filter.2 ⟨hW, h⟩)⟩)
      have h2 : p' * ∑ j ∈ B', H.w i j - T < ∑ j ∈ W, H.w i j := not_le.1 fun h =>
        hWB (by rw [hbadB]; exact mem_biUnion.2 ⟨i, hi, mem_union_right _ (mem_filter.2 ⟨hW, h⟩)⟩)
      obtain ⟨-, -, hμ3⟩ := hμ i hi
      have h4 : 4 * x * (p * D) ≤ T := by
        rw [hT, hx]; linarith only [mul_pos (mul_pos hδ hσ) hpDpos]
      rw [abs_le] at hμ3 ⊢
      constructor <;> linarith
    have hdW : ∀ j ∈ W, |∑ i ∈ U, H.w i j - p * D| ≤ δ * σ * (p * D) := by
      intro j hj
      have h := hOS.deg_near j (hWsub hj)
      have e1 : H.degOn j U = ∑ i ∈ U, H.w i j := sum_congr rfl fun i _ => H.symm _ _
      rw [e1] at h
      calc _ ≤ δ * σ * p * D := h
        _ = _ := by ring
    exact BipSampling.good_of_bounds H A B U W hAB hA hB hUA hWsub hUne H.deg hdpos e hepos
      (p * D) δ δ σ β₂ le_rfl hσ hpDpos hβ₂0 hdU hdW hop hnum
  -- counting the first bad event (Lemma 2.2 over the pool)
  have hcA : (badA.card : ℝ) ≤ U.card * (B'.card + 1) * Real.exp (-t) * B'.card.choose k := by
    have hnorm : ∀ v : V → ℝ, ∑ i ∈ U, (∑ j ∈ B', (H.w i j - H.deg i * H.deg j / e) * v j) ^ 2 ≤
        β₁ ^ 2 * ∑ j ∈ B', v j ^ 2 := by
      intro v
      have h := hOS.norm_le (fun y => if y ∈ B' then v y else 0)
      have e1 : ∀ i ∈ U, ∑ y ∈ B, centred H A B i y * (if y ∈ B' then v y else 0) =
          ∑ j ∈ B', (H.w i j - H.deg i * H.deg j / e) * v j := by
        intro i hi
        calc ∑ y ∈ B, centred H A B i y * (if y ∈ B' then v y else 0)
            = ∑ y ∈ B', centred H A B i y * (if y ∈ B' then v y else 0) :=
              (sum_subset hB'B fun y _ hy => by rw [ite_eq_right hy, mul_zero]).symm
          _ = _ := sum_congr rfl fun y hy => by
              rw [ite_eq_left hy, hcent i (hUA hi) y (hB'B hy)]
      have e2 : ∑ y ∈ B, (if y ∈ B' then v y else 0) ^ 2 = ∑ j ∈ B', v j ^ 2 := by
        calc ∑ y ∈ B, (if y ∈ B' then v y else 0) ^ 2
            = ∑ y ∈ B', (if y ∈ B' then v y else 0) ^ 2 :=
              (sum_subset hB'B fun y _ hy => by rw [ite_eq_right hy]; ring).symm
          _ = _ := sum_congr rfl fun y hy => by rw [ite_eq_left hy]
      calc ∑ i ∈ U, (∑ j ∈ B', (H.w i j - H.deg i * H.deg j / e) * v j) ^ 2
          = ∑ i ∈ U, (∑ y ∈ B, centred H A B i y * (if y ∈ B' then v y else 0)) ^ 2 :=
            sum_congr rfl fun i hi => by rw [e1 i hi]
        _ ≤ (Real.sqrt p * (1 - σ / 2) * D + K * Real.sqrt (D * L)) ^ 2 *
            ∑ y ∈ B, (if y ∈ B' then v y else 0) ^ 2 := h
        _ = β₁ ^ 2 * ∑ j ∈ B', v j ^ 2 := by rw [e2, hβ₁]
    have hcol : ∀ j ∈ B', ∑ i ∈ U, (H.w i j - H.deg i * H.deg j / e) ^ 2 ≤
        Real.sqrt (K * p * D) ^ 2 := by
      intro j hj
      rw [Real.sq_sqrt (by positivity)]
      calc _ = ∑ i ∈ U, centred H A B i j ^ 2 :=
            sum_congr rfl fun i hi => by rw [hcent i (hUA hi) j (hB'B hj)]
        _ ≤ K * p * D := hOS.col_le j (hB'B hj)
    have h := BipSampling.column_sampling_finset hC₀ U B'
      (fun i j => H.w i j - H.deg i * H.deg j / e) β₁ (Real.sqrt (K * p * D)) hnorm hcol hβ₁0
      (Real.sqrt_nonneg _) k hkB' t ht
    refine le_trans (Nat.cast_le.2 (card_le_card fun W hW => ?_)) h
    rw [hbadA, mem_filter] at hW
    rw [mem_filter]
    obtain ⟨hW1, v, hv⟩ := hW
    refine ⟨hW1, v, ?_⟩
    rw [hβ₂, hp'] at hv
    exact hv
  -- counting the second bad event (hypergeometric tails)
  have hcB : (badB.card : ℝ) ≤ U.card * (2 * (Real.exp (-t) * B'.card.choose k)) := by
    rw [hbadB]
    refine BipSampling.card_biUnion_le_real U _ _ fun i hi => ?_
    refine le_trans (Nat.cast_le.2 (card_union_le _ _)) ?_
    rw [Nat.cast_add, two_mul]
    obtain ⟨hμ1, hμ2, -⟩ := hμ i hi
    have hμ' : p' * ∑ j ∈ B', H.w i j ≤ 33 / 32 * (p * D) := by
      linarith only [hμ2, mul_le_mul_of_nonneg_right hxs hpDpos.le, hpDpos]
    refine add_le_add ?_ ?_
    · have h1 := BipSampling.hyp_upper_finset B' (fun j => H.w i j) (fun j _ => hw i j) k T
        hTpos.le
      rw [← hp'] at h1
      refine le_trans (Nat.cast_le.2 (card_le_card fun W hW => ?_))
        (h1.trans (mul_le_mul_of_nonneg_right
          (BipSampling.tail_upper_le hμ1.le hTpos hμ' hTle ht.le hTsq) (Nat.cast_nonneg _)))
      rw [mem_filter] at hW ⊢
      exact hW
    · have h1 := BipSampling.hyp_lower_finset B' (fun j => H.w i j) (fun j _ => hw i j) k T
        hTpos.le
      rw [← hp'] at h1
      refine le_trans (Nat.cast_le.2 (card_le_card fun W hW => ?_))
        (h1.trans (mul_le_mul_of_nonneg_right
          (BipSampling.tail_lower_le hμ1 hμ' ht.le hTsq) (Nat.cast_nonneg _)))
      rw [mem_filter] at hW ⊢
      exact hW
  -- the union bound
  have hfin := BipSampling.num_final (a := a) hNpos hkN hL ht_def
  have hch : (0 : ℝ) ≤ B'.card.choose k := Nat.cast_nonneg _
  have hU : (U.card : ℝ) = k := by rw [hUk]
  have hpoly : (k : ℝ) * (B'.card + 1) + 2 * k ≤ (N : ℝ) * (N + 1) + N + k * (N + 1) + 4 * N := by
    linarith only [mul_le_mul_of_nonneg_left hbR (Nat.cast_nonneg (α := ℝ) k), hkR, hN1,
      mul_self_nonneg (N : ℝ)]
  calc _ ≤ ((badA ∪ badB).card : ℝ) := by
        refine Nat.cast_le.2 (card_le_card fun W hW => ?_)
        rw [mem_filter] at hW
        rw [mem_union]
        by_contra hn
        rw [not_or] at hn
        exact hW.2 (key W hW.1 hn.1 hn.2)
    _ ≤ (badA.card : ℝ) + badB.card := by exact_mod_cast card_union_le _ _
    _ ≤ U.card * (B'.card + 1) * Real.exp (-t) * B'.card.choose k +
        U.card * (2 * (Real.exp (-t) * B'.card.choose k)) := add_le_add hcA hcB
    _ = ((k : ℝ) * (B'.card + 1) + 2 * k) * Real.exp (-t) * B'.card.choose k := by
        rw [hU]; ring
    _ ≤ ((N : ℝ) * (N + 1) + N + k * (N + 1) + 4 * N) * Real.exp (-t) * B'.card.choose k :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le) hch
    _ ≤ Real.exp (-(a * L)) * B'.card.choose k := mul_le_mul_of_nonneg_right hfin hch

end LocalAbsorption

end Lovasz
