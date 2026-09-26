/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Hoffman's circulation theorem (classical input, via max-flow/min-cut)

DAG node `K.hoffman` of `docs/BLUEPRINT.md`: the circulation criterion (4.6), which the paper
derives from max-flow/min-cut.
-/

namespace Lovasz

open Finset

namespace Circulation

variable {N A : Type*} [Fintype A] [DecidableEq N] (tail head : A → N)

/-- Net inflow (inflow minus outflow) of `g` at the vertex `v`. -/
noncomputable def netIn (g : A → ℝ) (v : N) : ℝ :=
  ∑ a, g a * ((if head a = v then 1 else 0) - (if tail a = v then 1 else 0))

/-- The vertices incident to some arc. -/
def verts : Finset N := univ.image head ∪ univ.image tail

/-- Total imbalance `∑_v |in_g(v) - out_g(v)|`. -/
noncomputable def imbalance (g : A → ℝ) : ℝ := ∑ v ∈ verts tail head, |netIn tail head g v|

lemma head_mem_verts (a : A) : head a ∈ verts tail head :=
  mem_union_left _ (mem_image_of_mem _ (mem_univ a))

lemma tail_mem_verts (a : A) : tail a ∈ verts tail head :=
  mem_union_right _ (mem_image_of_mem _ (mem_univ a))

lemma netIn_add_smul (g x : A → ℝ) (c : ℝ) (v : N) :
    netIn tail head (fun a => g a + c * x a) v =
      netIn tail head g v + c * netIn tail head x v := by
  simp only [netIn, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

lemma netIn_indicator [DecidableEq A] (a₀ : A) (v : N) :
    netIn tail head (fun a => if a = a₀ then 1 else 0) v =
      (if head a₀ = v then 1 else 0) - (if tail a₀ = v then 1 else 0) := by
  simp [netIn, ite_mul, Finset.sum_ite_eq']

lemma netIn_zero (v : N) : netIn tail head (fun _ => 0) v = 0 := by
  simp [netIn]

lemma sum_netIn (g : A → ℝ) (J : Finset N) :
    ∑ v ∈ J, netIn tail head g v =
      ∑ a, g a * ((if head a ∈ J then 1 else 0) - (if tail a ∈ J then 1 else 0)) := by
  unfold netIn
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]

lemma netIn_eq_zero_of_notMem (g : A → ℝ) {v : N} (hv : v ∉ verts tail head) :
    netIn tail head g v = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  have h1 : head a ≠ v := fun h => hv (h ▸ head_mem_verts tail head a)
  have h2 : tail a ≠ v := fun h => hv (h ▸ tail_mem_verts tail head a)
  simp [h1, h2]

lemma mem_verts_of_netIn_ne_zero (g : A → ℝ) {v : N} (hv : netIn tail head g v ≠ 0) :
    v ∈ verts tail head := by
  by_contra h
  exact hv (netIn_eq_zero_of_notMem tail head g h)

lemma sum_netIn_verts (g : A → ℝ) : ∑ v ∈ verts tail head, netIn tail head g v = 0 := by
  rw [sum_netIn]
  refine Finset.sum_eq_zero fun a _ => ?_
  simp [head_mem_verts, tail_mem_verts]

lemma conservation_iff (g : A → ℝ) (v : N) :
    (∑ a ∈ univ.filter (fun a => head a = v), g a =
      ∑ a ∈ univ.filter (fun a => tail a = v), g a) ↔ netIn tail head g v = 0 := by
  rw [Finset.sum_filter, Finset.sum_filter, netIn, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [mul_sub, mul_ite, mul_one, mul_zero]

lemma exists_netIn_pos (g : A → ℝ) {v : N} (hv : netIn tail head g v ≠ 0) :
    ∃ s, 0 < netIn tail head g s := by
  by_contra h
  push Not at h
  have hz := (Finset.sum_eq_zero_iff_of_nonpos (fun w _ => h w)).1 (sum_netIn_verts tail head g)
  exact hv (hz v (mem_verts_of_netIn_ne_zero tail head g hv))

/-- Pushing a small amount of flow along a residual `s`–`t` route `x` from an excess vertex `s`
to a deficit vertex `t` strictly decreases the total imbalance. -/
lemma push (l u g x : A → ℝ) (hgb : ∀ a, l a ≤ g a ∧ g a ≤ u a)
    (hxp : ∀ a, 0 < x a → g a < u a) (hxn : ∀ a, x a < 0 → l a < g a) (s t : N)
    (hxdiv : ∀ v, netIn tail head x v = (if v = t then 1 else 0) - (if v = s then 1 else 0))
    (hs : 0 < netIn tail head g s) (ht : netIn tail head g t < 0) :
    ∃ g' : A → ℝ, (∀ a, l a ≤ g' a ∧ g' a ≤ u a) ∧
      imbalance tail head g' < imbalance tail head g := by
  have h0 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε := self_mem_nhdsWithin
  have h1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε ≤ netIn tail head g s :=
    nhdsWithin_le_nhds ((eventually_lt_nhds hs).mono fun ε h => h.le)
  have h2 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε ≤ -netIn tail head g t :=
    nhdsWithin_le_nhds ((eventually_lt_nhds (neg_pos.2 ht)).mono fun ε h => h.le)
  have h3 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ a, l a ≤ g a + ε * x a ∧ g a + ε * x a ≤ u a := by
    refine Filter.eventually_all.2 fun a => ?_
    have hc : Filter.Tendsto (fun ε : ℝ => g a + ε * x a) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (g a)) := by
      have : Filter.Tendsto (fun ε : ℝ => g a + ε * x a) (nhds 0) (nhds (g a + 0 * x a)) :=
        ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    rcases lt_trichotomy (x a) 0 with hxa | hxa | hxa
    · filter_upwards [hc.eventually (lt_mem_nhds (hxn a hxa)), h0] with ε hε hε0
      exact ⟨hε.le, by nlinarith [(hgb a).2]⟩
    · exact Filter.Eventually.of_forall fun ε => by simp [hxa, hgb a]
    · filter_upwards [hc.eventually (gt_mem_nhds (hxp a hxa)), h0] with ε hε hε0
      exact ⟨by nlinarith [(hgb a).1], hε.le⟩
  obtain ⟨ε, hε0, hεs, hεt, hbox⟩ := (h0.and (h1.and (h2.and h3))).exists
  refine ⟨fun a => g a + ε * x a, hbox, ?_⟩
  have hst : s ≠ t := by
    rintro rfl
    linarith
  have hsV : s ∈ verts tail head := mem_verts_of_netIn_ne_zero tail head g hs.ne'
  unfold imbalance
  refine Finset.sum_lt_sum (fun v _ => ?_) ⟨s, hsV, ?_⟩
  · rw [netIn_add_smul, hxdiv v]
    by_cases hvs : v = s
    · subst hvs
      rw [ite_eq_right hst, ite_eq_left rfl, abs_of_pos hs, abs_of_nonneg (by linarith)]
      linarith
    · by_cases hvt : v = t
      · subst hvt
        rw [ite_eq_left rfl, ite_eq_right hvs, abs_of_neg ht, abs_of_nonpos (by linarith)]
        linarith
      · rw [ite_eq_right hvt, ite_eq_right hvs]
        simp
  · rw [netIn_add_smul, hxdiv s, ite_eq_right hst, ite_eq_left rfl, abs_of_pos hs,
      abs_of_nonneg (by linarith)]
    linarith

/-- If no deficit vertex is residually reachable from an excess vertex `s`, the cut condition
is violated by the reachable set. -/
lemma cut_contra (l u g : A → ℝ) (hgb : ∀ a, l a ≤ g a ∧ g a ≤ u a)
    (hcut : ∀ J : Finset N,
      ∑ a ∈ univ.filter (fun a => head a ∈ J ∧ tail a ∉ J), l a ≤
        ∑ a ∈ univ.filter (fun a => tail a ∈ J ∧ head a ∉ J), u a)
    (R : Set N) (s : N) (hsR : s ∈ R)
    (hfwd : ∀ a, tail a ∈ R → g a < u a → head a ∈ R)
    (hbwd : ∀ a, head a ∈ R → l a < g a → tail a ∈ R)
    (hnn : ∀ t ∈ R, 0 ≤ netIn tail head g t) (hs : 0 < netIn tail head g s) : False := by
  classical
  set J := (verts tail head).filter (· ∈ R) with hJ
  have hsJ : s ∈ J := mem_filter.2 ⟨mem_verts_of_netIn_ne_zero tail head g hs.ne', hsR⟩
  have hhJ : ∀ a, head a ∈ J ↔ head a ∈ R := fun a => by
    simp [hJ, head_mem_verts]
  have htJ : ∀ a, tail a ∈ J ↔ tail a ∈ R := fun a => by
    simp [hJ, tail_mem_verts]
  have h1 : netIn tail head g s ≤ ∑ v ∈ J, netIn tail head g v :=
    single_le_sum (fun v hv => hnn v (mem_filter.1 hv).2) hsJ
  rw [sum_netIn] at h1
  have h2 : ∑ a, g a * ((if head a ∈ J then 1 else 0) - (if tail a ∈ J then 1 else 0)) =
      ∑ a ∈ univ.filter (fun a => head a ∈ J ∧ tail a ∉ J), l a -
        ∑ a ∈ univ.filter (fun a => tail a ∈ J ∧ head a ∉ J), u a := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hh : head a ∈ J <;> by_cases ht : tail a ∈ J <;> simp only [hh, ht] <;>
      simp only [ite_true, ite_false, not_true, not_false_eq_true, and_true, and_false]
    · ring
    · have : g a = l a := by
        by_contra hne
        exact ht ((htJ a).2 (hbwd a ((hhJ a).1 hh) (lt_of_le_of_ne (hgb a).1 (Ne.symm hne))))
      rw [this]
      ring
    · have : g a = u a := by
        by_contra hne
        exact hh ((hhJ a).2 (hfwd a ((htJ a).1 ht) (lt_of_le_of_ne (hgb a).2 hne)))
      rw [this]
      ring
    · ring
  linarith [hcut J]

end Circulation

open Circulation in
/-- **Circulation criterion (4.6).** A finite directed multigraph with capacities
`l ≤ u` has a feasible circulation if `l(δ⁻(J)) ≤ u(δ⁺(J))` for every vertex set `J`. -/
theorem hoffman_circulation {N A : Type*} [Fintype A] [DecidableEq N]
    (tail head : A → N) (l u : A → ℝ) (hlu : ∀ a, l a ≤ u a)
    (hcut : ∀ J : Finset N,
      ∑ a ∈ univ.filter (fun a => head a ∈ J ∧ tail a ∉ J), l a ≤
        ∑ a ∈ univ.filter (fun a => tail a ∈ J ∧ head a ∉ J), u a) :
    ∃ g : A → ℝ, (∀ a, l a ≤ g a ∧ g a ≤ u a) ∧
      ∀ v, ∑ a ∈ univ.filter (fun a => head a = v), g a =
        ∑ a ∈ univ.filter (fun a => tail a = v), g a := by
  classical
  set K : Set (A → ℝ) := Set.pi Set.univ (fun a => Set.Icc (l a) (u a)) with hK
  have hKc : IsCompact K := isCompact_univ_pi fun a => isCompact_Icc
  have hKne : K.Nonempty := ⟨l, fun a _ => ⟨le_rfl, hlu a⟩⟩
  have hΦc : Continuous (imbalance tail head) := by
    refine continuous_finsetSum _ fun v _ => continuous_abs.comp ?_
    exact continuous_finsetSum _ fun a _ => (continuous_apply a).mul continuous_const
  obtain ⟨g, hgK, hmin⟩ := hKc.exists_isMinOn hKne hΦc.continuousOn
  have hgb : ∀ a, l a ≤ g a ∧ g a ≤ u a := fun a => hgK a (Set.mem_univ a)
  refine ⟨g, hgb, fun v => ?_⟩
  rw [conservation_iff]
  by_contra hv
  obtain ⟨s, hs⟩ := exists_netIn_pos tail head g hv
  let R : Set N := {t | ∃ x : A → ℝ, (∀ a, 0 < x a → g a < u a) ∧ (∀ a, x a < 0 → l a < g a) ∧
    ∀ w, netIn tail head x w = (if w = t then 1 else 0) - (if w = s then 1 else 0)}
  by_cases hdef : ∃ t ∈ R, netIn tail head g t < 0
  · obtain ⟨t, ⟨x, hxp, hxn, hxdiv⟩, ht⟩ := hdef
    obtain ⟨g', hg'b, hlt⟩ := push tail head l u g x hgb hxp hxn s t hxdiv hs ht
    have := (isMinOn_iff.1 hmin) g' (fun a _ => hg'b a)
    exact absurd this (not_le.2 hlt)
  · push Not at hdef
    refine cut_contra tail head l u g hgb hcut R s ?_ ?_ ?_ hdef hs
    · refine ⟨fun _ => 0, fun a h => absurd h (lt_irrefl 0), fun a h => absurd h (lt_irrefl 0),
        fun w => ?_⟩
      rw [netIn_zero]
      ring
    · rintro a ⟨x, hxp, hxn, hxdiv⟩ hlt
      refine ⟨fun b => x b + 1 * (if b = a then 1 else 0), fun b hb => ?_, fun b hb => ?_,
        fun w => ?_⟩
      · by_cases hba : b = a
        · subst hba
          exact hlt
        · simp only [hba, ite_false, mul_zero, add_zero] at hb
          exact hxp b hb
      · by_cases hba : b = a
        · subst hba
          simp only [ite_true, mul_one] at hb
          exact hxn b (by linarith)
        · simp only [hba, ite_false, mul_zero, add_zero] at hb
          exact hxn b hb
      · rw [netIn_add_smul, hxdiv w, netIn_indicator]
        simp only [@eq_comm _ (head a) w, @eq_comm _ (tail a) w]
        ring
    · rintro a ⟨x, hxp, hxn, hxdiv⟩ hlt
      refine ⟨fun b => x b + (-1) * (if b = a then 1 else 0), fun b hb => ?_, fun b hb => ?_,
        fun w => ?_⟩
      · by_cases hba : b = a
        · subst hba
          simp only [ite_true, mul_one] at hb
          exact hxp b (by linarith)
        · simp only [hba, ite_false, mul_zero, add_zero] at hb
          exact hxp b hb
      · by_cases hba : b = a
        · subst hba
          exact hlt
        · simp only [hba, ite_false, mul_zero, add_zero] at hb
          exact hxn b hb
      · rw [netIn_add_smul, hxdiv w, netIn_indicator]
        simp only [@eq_comm _ (head a) w, @eq_comm _ (tail a) w]
        ring

end Lovasz
