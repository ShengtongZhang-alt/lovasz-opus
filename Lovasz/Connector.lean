/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent)
-/
import Lovasz.Connecting.LabelSampling
import Lovasz.Connecting.Reservation
import Lovasz.Connecting.AllocationCuts
import Lovasz.Connecting.BipStateCuts
import Lovasz.Connecting.Matching
import Lovasz.Connecting.Integral

/-!
# Proposition 6.1: the sparse connecting system

DAG node `P6.1` of `docs/BLUEPRINT.md` (Section 6 of the paper). The shared definitions and the
proved steps are in `Lovasz/Connecting/Basic.lean` and `Lovasz/Connecting/Integral.lean`; the
remaining steps each have their own file in `Lovasz/Connecting/`. This file contains the
assembly `connector_of_outcome` and the proposition.
-/

universe u

noncomputable section

namespace Lovasz

open Finset Classical

namespace Connector

/-! ### Assembly of the connector from a good outcome of the joint experiment -/

section Outcome

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

/-- The deterministic and matching part of the proof of Proposition 6.1: from a successful
allocation, added labels `S₁`, retained labels `S_s` satisfying (6.2), (6.6) and Lemma 6.3, and the
parameter regime, construct the connecting system. -/
theorem connector_of_outcome (S T Ap Am S₁ Ss : Finset G) (𝒜 : Allocation G)
    (cT A₀ cN CN cD CD a c₃ CB K P₀ D σ η ω L d : ℝ)
    (hL : Real.log (Fintype.card G) = L) (hd : (S.card : ℝ) = d)
    (hS : IsConnectionSet S) (hconn : (cayleyGraph S).Connected) (hT : IsTemplate S T Ap Am cT)
    (hgood : 𝒜.Good S T Ap Am (A₀ * L) D σ η ω cN CN)
    (hA₀ : 0 < A₀) (hcN : 0 < cN) (ha : 0 < a) (hc₃ : 0 < c₃) (hCB : 0 < CB) (hK : 0 < K)
    (hL3 : 3 ≤ L) (hdpos : 0 < d) (hD₁ : cD * d / L ≤ D) (hD₂ : D ≤ CD * d / L)
    (hS₀conn : IsConnectionSet (S₁ ∪ Ss)) (hS₀S : S₁ ∪ Ss ⊆ S) (hTne : T.Nonempty)
    (hkK : ((S₁ ∪ Ss).card : ℝ) ≤ K * L ^ 2)
    (htwo : CN * d / (A₀ * L) < cT * d - 1)
    (h3B : 3 * (CB * (K * L ^ 2) * L) ≤ c₃ * d / L) (hμ6 : 6 ≤ c₃ * d / L)
    (hpk : P₀ * L / (c₃ * d / L) * (K * L ^ 2) ^ 2 ≤ 1) (hP1100 : 1100 ≤ P₀ * L)
    (hP2048 : 32 * (3 + 2 * L) + 4 ≤ P₀ * L / 2048)
    (hpkE : 4 * (P₀ * L / (c₃ * d / L) * (K * L ^ 2)) ≤ a * Real.log L / L ^ 7)
    (hEV : 4 ≤ a * Real.log L / L ^ 7 * (cN * d / (A₀ * L)))
    (hEVlog : 3 + 2 * L ≤ 3 / 40 * (a * Real.log L / L ^ 7 * (cN * d / (A₀ * L)) - 2))
    (hpkN : 2 * (P₀ * L / (c₃ * d / L) * (K * L ^ 2)) * (CN * d / (A₀ * L)) + 2 ≤
      a * (cD * d / L) / L ^ 6)
    (hNlog : 3 + 2 * L ≤ 3 / 40 * (a * (cD * d / L) / L ^ 6 - 2))
    (hεN : a * (CD * d / L) / L ^ 6 ≤ cN * d / (A₀ * L))
    (hres : Odd (Nat.card (Subgroup.closure (T : Set G))) →
      Res66 T (S₁ ∪ Ss) 𝒜.W (CB * (S₁ ∪ Ss).card * L))
    (hcuts : ∀ π : G → Fin 𝒜.t, (∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v)) →
      (IsNonbip S → ∀ J : Finset (Fin 𝒜.t × Bool), J.Nonempty → J ≠ univ →
          c₃ * S.card / Real.log (Fintype.card G) ≤
            cutCnt π (sgnOf 𝒜 Ap π) J (conY (S₁ ∪ Ss) 𝒜.W).edgeFinset) ∧
        (Odd (Nat.card (Subgroup.closure (T : Set G))) →
          ∀ (H : G ⧸ Subgroup.closure (T : Set G)) (J : Finset (Fin 𝒜.t × Bool)),
            (∃ v, v ∉ 𝒜.W ∧ (v : G ⧸ Subgroup.closure (T : Set G)) = H ∧ ∃ β, (π v, β) ∈ J) →
            (∃ v, v ∉ 𝒜.W ∧ (v : G ⧸ Subgroup.closure (T : Set G)) = H ∧ ∃ β, (π v, β) ∉ J) →
            c₃ * S.card / Real.log (Fintype.card G) ≤
              cutCnt π (sgnOf 𝒜 Ap π) J ((conY (S₁ ∪ Ss) 𝒜.W).edgeFinset.filter fun e =>
                ∀ v ∈ e, (v : G ⧸ Subgroup.closure (T : Set G)) = H)) ∧
        (¬ IsNonbip S → ∀ I : Finset (Fin 𝒜.t), I.Nonempty → I ≠ univ →
          c₃ * S.card / Real.log (Fintype.card G) ≤
            ((conY (S₁ ∪ Ss) 𝒜.W).edgeFinset.filter (PartCross π I)).card)) :
    ∃ M : SimpleGraph G, 𝒜.IsConnector S T Ap Am M (a * Real.log L / L ^ 7) (a * D / L ^ 6) := by
  subst hd
  simp only [hL] at hcuts
  set n := Fintype.card G
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < n := by linarith only [hn1]
  have hLpos : 0 < L := by linarith only [hL3]
  have hΛpos : 0 < Real.log L := Real.log_pos (by linarith only [hL3])
  have hlam : 0 < A₀ * L := mul_pos hA₀ hLpos
  have hsize : 0 < cN * S.card / (A₀ * L) := div_pos (mul_pos hcN hdpos) hlam
  have ht2 : 2 ≤ 𝒜.t := two_le_t hS hT hgood hlam hTne htwo
  have ht0 : 0 < 𝒜.t := by omega
  -- the part map and the copies of the reserved vertices
  let π : G → Fin 𝒜.t := fun v =>
    if h : ∃ i, v ∈ 𝒜.part i then Classical.choose h else ⟨0, ht0⟩
  have hπ : ∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v) := by
    intro v hv
    have h : ∃ i, v ∈ 𝒜.part i := (hgood.part_unique v hv).exists
    have : π v = Classical.choose h := dif_pos h
    rw [this]
    exact Classical.choose_spec h
  let ι : G → Fin 𝒜.t := fun w =>
    if h : ∃ i, w ∈ copyVerts Ap Am (𝒜.g i) then Classical.choose h else ⟨0, ht0⟩
  have hι : ∀ w ∈ 𝒜.W, w ∈ copyVerts Ap Am (𝒜.g (ι w)) := by
    intro w _
    have h := exists_copy hgood hTne w
    have : ι w = Classical.choose h := dif_pos h
    rw [this]
    exact Classical.choose_spec h
  obtain ⟨hA, hLoc, hBip⟩ := hcuts π hπ
  clear hcuts
  set S₀ := S₁ ∪ Ss
  set μ₀ := c₃ * S.card / L
  have hμ₀pos : 0 < μ₀ := div_pos (mul_pos hc₃ hdpos) hLpos
  set k := S₀.card
  set Y := conY S₀ 𝒜.W
  set sg := sgnOf 𝒜 Ap π
  have hdir := fun J => directional_balance S T Ap Am S₀ cT 𝒜 (A₀ * L) D _ _ ω cN CN μ₀
    (CB * k * L) π ι hT hgood hsize hπ hι hS₀conn
    (by
      have : CB * k * L ≤ CB * (K * L ^ 2) * L :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkK hCB.le) hLpos.le
      linarith only [this, h3B])
    hres hLoc J
  -- the gap, the part cuts and cut counting
  have hB456 : (∀ J, cutCnt π sg J Y.edgeFinset = 0 ∨ μ₀ ≤ cutCnt π sg J Y.edgeFinset) ∧
      (∀ I : Finset (Fin 𝒜.t), I.Nonempty → I ≠ univ →
        μ₀ ≤ cutCnt π sg (I ×ˢ univ) Y.edgeFinset) ∧
      (∀ j : ℕ, (((univ : Finset (Finset (Fin 𝒜.t × Bool))).filter fun J =>
        (cutCnt π sg J Y.edgeFinset : ℝ) < (j + 1) * μ₀).card : ℝ) ≤
          (4 * (𝒜.t + Y.edgeFinset.card)) ^ (16 * (j + 1))) := by
    by_cases hnb : IsNonbip S
    · have hA' := hA hnb
      refine ⟨fun J => ?_, fun I hI hI' => hA' _ (hI.product univ_nonempty) ?_,
        fun j => state_cut_count ht0 π sg _ μ₀ hμ6 hA' j⟩
      · by_cases hJ : J.Nonempty
        · by_cases hJ' : J = univ
          · left
            rw [hJ']
            exact cutCnt_univ _ _ _
          · right
            exact hA' J hJ hJ'
        · left
          rw [not_nonempty_iff_eq_empty.1 hJ]
          exact cutCnt_empty _ _ _
      · intro h
        apply hI'
        ext i
        refine ⟨fun _ => mem_univ _, fun _ => ?_⟩
        have : (i, true) ∈ I ×ˢ (univ : Finset Bool) := by rw [h]; exact mem_univ _
        exact (mem_product.1 this).1
    · have hB' := hBip hnb
      obtain ⟨hgap, hcount⟩ := bip_state_cuts S T Ap Am S₀ cT 𝒜 (A₀ * L) D _ _ ω cN CN μ₀ π hS
        hconn hnb hT hgood hπ hS₀S hμ6 hB'
      refine ⟨hgap, fun I hI hI' => ?_, hcount⟩
      rw [cutCnt_prod_univ]
      push_cast
      have := hB' I hI hI'
      linarith only [this, hμ₀pos]
  -- the random matching
  set p := P₀ * L / μ₀
  have hppos : 0 < p := div_pos (lt_of_lt_of_le (by norm_num) hP1100) hμ₀pos
  have hpμ : p * μ₀ = P₀ * L := div_mul_cancel₀ _ hμ₀pos.ne'
  have htn : (𝒜.t : ℝ) ≤ n := by exact_mod_cast t_le_card hgood hsize
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := le_self_pow₀ hn1 (by norm_num)
  have hEcard : (Y.edgeFinset.card : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h1 := SimpleGraph.card_edgeFinset_le_card_choose_two (G := Y)
    have h2 := Nat.choose_le_pow n 2
    exact_mod_cast h1.trans h2
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith only [this]
  have hlogN : Real.log (4 * ((𝒜.t : ℝ) + Y.edgeFinset.card)) ≤ 3 + 2 * L := by
    have ht0' : (0 : ℝ) < 𝒜.t := by exact_mod_cast ht0
    have hE0 : (0 : ℝ) ≤ Y.edgeFinset.card := Nat.cast_nonneg _
    have hpos : (0 : ℝ) < 4 * ((𝒜.t : ℝ) + Y.edgeFinset.card) := by
      linarith only [ht0', hE0]
    have hle : 4 * ((𝒜.t : ℝ) + Y.edgeFinset.card) ≤ 8 * (n : ℝ) ^ 2 := by
      linarith only [htn, hEcard, hnn]
    have h1 := Real.log_le_log hpos hle
    rw [Real.log_mul (by norm_num) (pow_pos hnpos 2).ne', Real.log_pow, hL] at h1
    have h8 : Real.log 8 < 3 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      linarith only [hlog2]
    push_cast at h1
    linarith only [h1, h8]
  set εE := a * Real.log L / L ^ 7
  set εN := a * D / L ^ 6
  let tests : Finset (Finset G × ℝ) :=
    (univ.image fun i : Fin 𝒜.t => (𝒜.part i, εE * (𝒜.part i).card - 2)) ∪
      univ.biUnion fun i : Fin 𝒜.t => (copyVerts Ap Am (𝒜.g i)).image fun v =>
        ((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y, εN - 2)
  have htests_card : (tests.card : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
    have h1 : tests.card ≤ 𝒜.t + 𝒜.t * n := by
      refine (card_union_le _ _).trans (add_le_add ?_ ?_)
      · exact card_image_le.trans (by simp)
      · refine card_biUnion_le.trans ?_
        calc ∑ i : Fin 𝒜.t, ((copyVerts Ap Am (𝒜.g i)).image fun v =>
              ((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y, εN - 2)).card
            ≤ ∑ _i : Fin 𝒜.t, n := sum_le_sum fun i _ => card_image_le.trans (card_le_univ _)
          _ = 𝒜.t * n := by simp
    have h1' : (tests.card : ℝ) ≤ 𝒜.t + 𝒜.t * n := by exact_mod_cast h1
    have h3 : (𝒜.t : ℝ) * n ≤ (n : ℝ) ^ 2 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right htn hnpos.le
    linarith only [h1', h3, htn, hnn]
  have hlogtests : Real.log tests.card ≤ 1 + 2 * L := by
    rcases Nat.eq_zero_or_pos tests.card with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      linarith only [hLpos]
    · have h := Real.log_le_log (by exact_mod_cast hpos) htests_card
      rw [Real.log_mul (by norm_num) (pow_pos hnpos 2).ne', Real.log_pow, hL] at h
      push_cast at h
      linarith only [h, hlog2]
  have hpk_le : p * k ≤ p * (K * L ^ 2) := mul_le_mul_of_nonneg_left hkK hppos.le
  have hεE0 : 0 ≤ εE := div_nonneg (mul_nonneg ha.le hΛpos.le) (pow_nonneg hLpos.le 7)
  have htests : ∀ q ∈ tests, p * k * q.1.card ≤ q.2 / 2 ∧
      Real.log tests.card + 2 ≤ 3 / 40 * q.2 := by
    intro q hq
    rcases mem_union.1 hq with hq | hq
    · obtain ⟨i, -, rfl⟩ := mem_image.1 hq
      have hV : cN * S.card / (A₀ * L) ≤ (𝒜.part i).card := hgood.size_lower i
      have h2 : εE * (cN * S.card / (A₀ * L)) ≤ εE * (𝒜.part i).card :=
        mul_le_mul_of_nonneg_left hV hεE0
      refine ⟨?_, ?_⟩
      · have h0 : p * k ≤ εE / 4 := by linarith only [hpk_le, hpkE]
        have h1 : p * k * (𝒜.part i).card ≤ εE / 4 * (𝒜.part i).card :=
          mul_le_mul_of_nonneg_right h0 (Nat.cast_nonneg _)
        show p * k * (𝒜.part i).card ≤ (εE * (𝒜.part i).card - 2) / 2
        linarith only [h1, h2, hEV]
      · show Real.log tests.card + 2 ≤ 3 / 40 * (εE * (𝒜.part i).card - 2)
        linarith only [h2, hEVlog, hlogtests]
    · obtain ⟨i, -, hq⟩ := mem_biUnion.1 hq
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hq
      have hA : (((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y).card : ℝ) ≤
          CN * S.card / (A₀ * L) := hgood.nbhd_upper i v hv
      have hεN' : a * (cD * S.card / L) / L ^ 6 ≤ εN :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hD₁ ha.le) (pow_nonneg hLpos.le 6)
      refine ⟨?_, ?_⟩
      · have h1 : p * k * (((𝒜.part i).filter fun y =>
            (copyGraph T Ap Am (𝒜.g i)).Adj v y).card : ℝ) ≤
            (p * (K * L ^ 2)) * (CN * S.card / (A₀ * L)) :=
          mul_le_mul hpk_le hA (Nat.cast_nonneg _)
            (le_trans (mul_nonneg hppos.le (Nat.cast_nonneg _)) hpk_le)
        show p * k * (((𝒜.part i).filter fun y =>
            (copyGraph T Ap Am (𝒜.g i)).Adj v y).card : ℝ) ≤ (εN - 2) / 2
        linarith only [h1, hpkN, hεN']
      · show Real.log tests.card + 2 ≤ 3 / 40 * (εN - 2)
        linarith only [hNlog, hεN', hlogtests]
  obtain ⟨R, Z₀, hZR, hRY, hRmatch, hcutsR, hconnZ, hslackR, htestsR⟩ :=
    exists_matching Y π sg k (fun v => conY_degree_le S₀ 𝒜.W hS₀conn.1 v) p μ₀ hppos
      (by
        have : p * (k : ℝ) ^ 2 ≤ p * (K * L ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hkK 2) hppos.le
        linarith only [this, hpk])
      hμ6 (by rw [hpμ]; linarith only [hP1100])
      (by rw [hpμ]; linarith only [hP2048, hlogN])
      (fun J => ⟨(hdir J).1, (hdir J).2.1⟩) hB456.1 hB456.2.1 hB456.2.2 tests htests
  -- the integral connector
  have hRadj : ∀ e ∈ R, (cayleyGraph S).Adj e.out.1 e.out.2 ∧ e.out.1 ∉ 𝒜.W ∧
      e.out.2 ∉ 𝒜.W := by
    intro e he
    have heY := hRY he
    rw [SimpleGraph.mem_edgeFinset, ← mk_out e, SimpleGraph.mem_edgeSet] at heY
    obtain ⟨h1, h2, h3⟩ := heY
    exact ⟨SimpleGraph.mulCayley_mono (by exact_mod_cast hS₀S) h1, h2, h3⟩
  have hfew : ∀ i, (((𝒜.part i).filter (· ∈ vtx R)).card : ℝ) + 2 ≤
      εE * (𝒜.part i).card := by
    intro i
    have h := htestsR (𝒜.part i, εE * (𝒜.part i).card - 2)
      (mem_union_left _ (mem_image.2 ⟨i, mem_univ _, rfl⟩))
    have h' : (((𝒜.part i).filter (· ∈ vtx R)).card : ℝ) ≤ εE * (𝒜.part i).card - 2 := h
    linarith only [h']
  have hsparse : ∀ i, ∀ v ∈ copyVerts Ap Am (𝒜.g i),
      (((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y ∧
        y ∈ vtx R).card : ℝ) + 2 ≤ εN := by
    intro i v hv
    have h := htestsR _ (mem_union_right _ (mem_biUnion.2 ⟨i, mem_univ _,
      mem_image.2 ⟨v, hv, rfl⟩⟩))
    simp only [filter_filter] at h
    linarith only [h]
  have hεN'' : εN ≤ cN * S.card / (A₀ * L) := by
    have : εN ≤ a * (CD * S.card / L) / L ^ 6 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hD₂ ha.le) (pow_nonneg hLpos.le 6)
    linarith only [this, hεN]
  exact connector_of_matching S T Ap Am cT 𝒜 (A₀ * L) D _ _ ω cN CN hT hgood
    ht2 π ι hπ hι R Z₀ hZR hRadj hRmatch (fun J => (cutCnt π sg J Y.edgeFinset : ℝ)) p μ₀ εE εN
    (fun J => Nat.cast_nonneg _) hμ₀pos (by rw [hpμ]; linarith only [hP1100])
    (fun J => (hcutsR J).1) (fun J => (hcutsR J).2.2.1) (fun J => (hcutsR J).2.2.2)
    (fun J => (hdir J).2.2) hconnZ hslackR hfew hsparse hεN''

end Outcome

end Connector

open Connector

/-- **Proposition 6.1 (Connecting system).** Assume (1.1) with a large constant `C₀`. For a
random allocation as produced by Proposition 5.3 (successful with probability at least `7/8`,
reserved set distributed by (5.7)), some successful outcome admits a connecting system `M`: a
physical matching on `G \ W` plus a path `a_H w_H b_H` through each reserved vertex, with
distinct endpoints, connected contraction on the parts, and endpoint sets `E_i` that are
nonempty, balanced between the local sides, and satisfy (6.1):
`|E_i| ≤ a Λ |V_i| / L⁷` and `|N_{F_i}(v) ∩ V_i ∩ E_i| ≤ a D / L⁶`, where `Λ = log L`. -/
theorem connecting_system (cT ω A₀ cσ cD CD cN CN : ℝ) (hcT : 0 < cT) (hω : 0 < ω)
    (hA₀ : 0 < A₀) (hcσ : 0 < cσ) (hcD : 0 < cD) (hCD : cD ≤ CD) (hcN : 0 < cN) (hCN : cN ≤ CN)
    (a : ℝ) (ha : 0 < a) :
    ∃ C₀ : ℝ, ∃ n₀ : ℕ, 0 < C₀ ∧
      ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S T Ap Am : Finset G) (c₁ D : ℝ)
        (μ : FinDist (Allocation G)),
        IsConnectionSet S → (cayleyGraph S).Connected → n₀ ≤ Fintype.card G →
        C₀ * Real.log (Fintype.card G) ^ 13 / Real.log (Real.log (Fintype.card G)) ≤ S.card →
        IsTemplate S T Ap Am cT →
        cD * S.card / Real.log (Fintype.card G) ≤ D →
        D ≤ CD * S.card / Real.log (Fintype.card G) →
        μ.P (fun 𝒜 => ¬ 𝒜.Good S T Ap Am (A₀ * Real.log (Fintype.card G)) D
          (cσ / Real.log (Fintype.card G) ^ 2)
          (c₁ * (cσ / Real.log (Fintype.card G) ^ 2)) ω cN CN) ≤ 1 / 8 →
        ReservationLaw μ T →
        ∃ 𝒜 ∈ μ.support, 𝒜.Good S T Ap Am (A₀ * Real.log (Fintype.card G)) D
            (cσ / Real.log (Fintype.card G) ^ 2)
            (c₁ * (cσ / Real.log (Fintype.card G) ^ 2)) ω cN CN ∧
          ∃ M : SimpleGraph G, 𝒜.IsConnector S T Ap Am M
            (a * Real.log (Real.log (Fintype.card G)) / Real.log (Fintype.card G) ^ 7)
            (a * D / Real.log (Fintype.card G) ^ 6) := by
  obtain ⟨A₁, c₂, hA₁, hc₂, n₁, hlabel⟩ := label_sampling.{u} cT A₀ cN hcT hA₀ hcN
  obtain ⟨Cres, CB, hCres, hCB, n₂, hres⟩ := reservation_estimates.{u}
  obtain ⟨c₃, hc₃, n₃, hcuts⟩ :=
    allocation_cuts.{u} cT A₀ cN c₂ 8 hcT hA₀ hcN hc₂ (by norm_num)
  set K : ℝ := 8 + 4 * A₁ * A₀ with hK_def
  have hK : 0 < K := by positivity
  set P₀ : ℝ := 2 ^ 19 with hP₀_def
  obtain ⟨L₀, hL₀3, hreg⟩ := regime cT A₀ cN CN cD CD a c₃ Cres CB K P₀ hcT hA₀ hcN
    (hcN.trans_le hCN) hcD (hcD.trans_le hCD) ha hc₃ hCres hCB hK le_rfl
  refine ⟨1, max (max n₁ n₂) (max n₃ ⌈Real.exp L₀⌉₊), one_pos, ?_⟩
  intro G _ _ _ S T Ap Am c₁ D μ hS hconn hn hd hT hD₁ hD₂ hfail hlaw
  have hn₁ : n₁ ≤ Fintype.card G := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂ : n₂ ≤ Fintype.card G := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn₃ : n₃ ≤ Fintype.card G := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnL : ⌈Real.exp L₀⌉₊ ≤ Fintype.card G :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  set n := Fintype.card G with hn_def
  set L := Real.log n with hL_def
  set d : ℝ := (S.card : ℝ) with hd_def
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < n := by linarith
  have hLL₀ : L₀ ≤ L := by
    rw [hL_def, Real.le_log_iff_exp_le hnpos]
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast hnL)
  have hL3 : 3 ≤ L := hL₀3.trans hLL₀
  have hLpos : 0 < L := by linarith
  have hΛpos : 0 < Real.log L := Real.log_pos (by linarith)
  have hdL : L ^ 13 ≤ Real.log L * d := by
    have h := hd
    rw [one_mul, div_le_iff₀ hΛpos] at h
    linarith
  obtain ⟨hL12, htwo, hlog2, hCresK, h3B, hμ6, hpk, hP1100, hP2048, hpkE, hEV, hEVlog,
    hpkN, hNlog, hεN⟩ := hreg L d hLL₀ hdL
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hL12
  have hTcard : cT * d ≤ T.card := hT.card_T
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < T.card := lt_of_lt_of_le (by positivity) hTcard
    exact_mod_cast this
  -- the added labels
  obtain ⟨S₁, hS₁S, hS₁symm, hS₁card, hS₁gen, hS₁nb⟩ := added_labels S hS hconn
  have hS₁L : (S₁.card : ℝ) ≤ 8 * L := by
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : (Nat.log 2 (2 * n) : ℝ) ≤ (Real.log 2 + L) / Real.log 2 := by
      have hpow := Nat.pow_log_le_self 2 (show 2 * n ≠ 0 by positivity)
      rw [le_div_iff₀ hlog2pos]
      have : Real.log ((2 : ℝ) ^ Nat.log 2 (2 * n)) ≤ Real.log (2 * n) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hpow)
      rw [Real.log_pow, Real.log_mul (by norm_num) hnpos.ne'] at this
      linarith
    have h2 : (S₁.card : ℝ) ≤ 2 * ((Nat.log 2 (2 * n) : ℝ) + 1) := by exact_mod_cast hS₁card
    linarith
  -- the label experiment and the joint union bound
  set U := Subgroup.closure (T : Set G) with hU_def
  have hsampT : ∀ ξ, sampled T ξ ⊆ T := fun ξ => filter_subset _ _
  have hS₀conn : ∀ ξ, IsConnectionSet (S₁ ∪ sampled T ξ) := by
    intro ξ
    refine ⟨fun s hs => ?_, fun h1 => ?_⟩
    · rcases mem_union.1 hs with h | h
      · exact mem_union_left _ (hS₁symm s h)
      · exact mem_union_right _ (sampled_symm T hT.symm ξ s h)
    · rcases mem_union.1 h1 with h | h
      · exact hS.2 (hS₁S h)
      · exact hS.2 (hT.sub (hsampT ξ h))
  have hS₀S : ∀ ξ, S₁ ∪ sampled T ξ ⊆ S := fun ξ => union_subset hS₁S ((hsampT ξ).trans hT.sub)
  have hS₀gen : ∀ ξ, Subgroup.closure ((S₁ ∪ sampled T ξ : Finset G) : Set G) = ⊤ := by
    intro ξ
    rw [eq_top_iff, ← hS₁gen]
    exact Subgroup.closure_mono (by rw [Finset.coe_union]; exact Set.subset_union_left)
  have hX₀conn : ∀ ξ, (cayleyGraph (S₁ ∪ sampled T ξ)).Connected :=
    fun ξ => cayley_connected _ (hS₀conn ξ).1 (hS₀gen ξ)
  have hkL : ∀ ξ, ((sampled T ξ).card : ℝ) ≤ 4 * A₁ * A₀ * L ^ 2 →
      ((S₁ ∪ sampled T ξ).card : ℝ) ≤ K * L ^ 2 := by
    intro ξ hξ
    have h' : ((S₁ ∪ sampled T ξ).card : ℝ) ≤ S₁.card + (sampled T ξ).card := by
      exact_mod_cast card_union_le S₁ (sampled T ξ)
    have hL1 : 8 * L ≤ 8 * L ^ 2 := by nlinarith
    rw [hK_def]
    linarith
  have hu : (T.card : ℝ) ≤ Nat.card U := by exact_mod_cast card_le_closure T
  obtain ⟨𝒜, h𝒜, ξ, -, hgood, h62, hKξ, hC⟩ := joint_union_bound μ
    (labelLaw G (A₁ * A₀ * L ^ 2 / S.card))
    (fun 𝒜 => 𝒜.Good S T Ap Am (A₀ * L) D (cσ / L ^ 2) (c₁ * (cσ / L ^ 2)) ω cN CN)
    (fun 𝒜 ξ => Sampled62 𝒜 T Ap Am ξ (c₂ * L))
    (fun ξ => ((sampled T ξ).card : ℝ) ≤ 4 * A₁ * A₀ * L ^ 2)
    (fun 𝒜 ξ => Odd (Nat.card U) → Res65 T (S₁ ∪ sampled T ξ) 𝒜.W ∧
      Res66 T (S₁ ∪ sampled T ξ) 𝒜.W (CB * (S₁ ∪ sampled T ξ).card * L))
    (1 / 4) (1 / 4) hfail
    (fun 𝒜 _ hgood => hlabel G S T Ap Am 𝒜 D _ _ ω CN hn₁ hS hL12 hT hgood)
    (fun ξ _ hξ => by
      by_cases hodd : Odd (Nat.card U)
      · rw [P_congr _ (E' := fun 𝒜 => ¬ (Res65 T (S₁ ∪ sampled T ξ) 𝒜.W ∧
          Res66 T (S₁ ∪ sampled T ξ) 𝒜.W (CB * (S₁ ∪ sampled T ξ).card * L)))
          (fun 𝒜 => by simp only [hodd, true_implies])]
        refine hres G T (S₁ ∪ sampled T ξ) μ _ hn₂ (hS₀conn ξ) (hX₀conn ξ) le_rfl ?_ hlaw hodd
        have hk := hkL ξ hξ
        calc Cres * ((S₁ ∪ sampled T ξ).card : ℝ) * L ≤ Cres * (K * L ^ 2) * L := by gcongr
          _ ≤ cT * d := hCresK
          _ ≤ T.card := hTcard
          _ ≤ Nat.card U := hu
      · rw [P_congr _ (E' := fun _ => False) (fun 𝒜 => by simp only [hodd, false_implies,
          not_true_eq_false]), P_false]
        norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  clear hlabel hres hreg
  refine ⟨𝒜, h𝒜, hgood, connector_of_outcome S T Ap Am S₁ (sampled T ξ) 𝒜 cT A₀ cN CN cD CD a c₃
    CB K P₀ D _ _ ω L d rfl rfl hS hconn hT hgood hA₀ hcN ha hc₃ hCB hK hL3 hdpos hD₁ hD₂
    (hS₀conn ξ) (hS₀S ξ) hTne (hkL ξ hKξ) htwo h3B hμ6 hpk hP1100 hP2048 hpkE hEV hEVlog hpkN
    hNlog hεN (fun hodd => (hC hodd).2) (fun π hπ => hcuts G S T Ap Am S₁ (sampled T ξ) 𝒜 D _ _ ω
      CN π hn₃ hS hconn hL12 hT hgood hπ (hS₀conn ξ) (hS₀S ξ) (hsampT ξ) hS₁gen hS₁nb hS₁L h62
      (fun hodd => (hC hodd).1))⟩

end Lovasz
