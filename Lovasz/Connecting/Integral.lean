/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Connecting.Basic

/-!
# The integral connector (Section 6.5)

DAG node `E6.int` of `docs/BLUEPRINT.md`: reserved-vertex paths, the circulation, and the
integral connector via Lemmas 4.4, 4.1 and the circulation criterion (4.6).
-/

universe u

noncomputable section

namespace Lovasz

open Finset Classical

namespace Connector

/-! ### Step E6.int: the reserved-vertex paths and the integral connector -/

section Integral

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

/-- **Inserting the reserved vertices and choosing an integral connector (§6.5).** Given the
matching `R ⊇ Z₀` with the cut estimates (6.13)–(6.15), the endpoint bounds (6.17), and the loop
bound (6.18), choose the paths `a_H w_H b_H`, a feasible circulation (4.6) with the capacities
`[1, 1]` on `Z₀ ∪ P` and `[ε, 1 - ε]` (`ε = 1/256`) on `R \ Z₀`, symmetrize it (Lemma 4.4), and
round it by Lemma 4.1; the resulting `M` is a connecting system. -/
theorem connector_of_matching (S T Ap Am : Finset G) (cT : ℝ) (𝒜 : Allocation G)
    (lam D σ η ω cN CN : ℝ) (hT : IsTemplate S T Ap Am cT)
    (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN) (ht : 2 ≤ 𝒜.t) (π ι : G → Fin 𝒜.t)
    (hπ : ∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v))
    (hι : ∀ w ∈ 𝒜.W, w ∈ copyVerts Ap Am (𝒜.g (ι w)))
    (R Z₀ : Finset (Sym2 G)) (hZR : Z₀ ⊆ R)
    (hRadj : ∀ e ∈ R, (cayleyGraph S).Adj e.out.1 e.out.2 ∧ e.out.1 ∉ 𝒜.W ∧ e.out.2 ∉ 𝒜.W)
    (hRmatch : ∀ e ∈ R, ∀ f ∈ R, e ≠ f → ∀ v ∈ e, v ∉ f)
    (s : Finset (Fin 𝒜.t × Bool) → ℝ) (p μ εE εN : ℝ) (hs : ∀ J, 0 ≤ s J) (hμ : 0 < μ)
    (hpμ : 40 ≤ p * μ)
    (hout : ∀ J, p * s J / 12 ≤ outCnt π (sgnOf 𝒜 Ap π) J R)
    (hcutR : ∀ J, (cutCnt π (sgnOf 𝒜 Ap π) J R : ℝ) ≤ 2 * p * s J)
    (hcutZ : ∀ J, (cutCnt π (sgnOf 𝒜 Ap π) J Z₀ : ℝ) ≤ p * s J / 64)
    (hloop : ∀ J, μ * loopCnt ι (loopSgn 𝒜 Am ι) J 𝒜.W ≤ 2 * s J)
    (hconn : ∀ I : Finset (Fin 𝒜.t), I.Nonempty → I ≠ univ → ∃ e ∈ Z₀, PartCross π I e)
    (hslack : ∀ I : Finset (Fin 𝒜.t), I.Nonempty → I ≠ univ →
      256 ≤ ((R \ Z₀).filter (PartCross π I)).card)
    (hfew : ∀ i, (((𝒜.part i).filter (· ∈ vtx R)).card : ℝ) + 2 ≤ εE * (𝒜.part i).card)
    (hsparse : ∀ i, ∀ v ∈ copyVerts Ap Am (𝒜.g i),
      (((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y ∧ y ∈ vtx R).card : ℝ) +
        2 ≤ εN)
    (hεN : εN ≤ cN * S.card / lam) :
    ∃ M : SimpleGraph G, 𝒜.IsConnector S T Ap Am M εE εN := by
  -- basic facts
  have hpartW : ∀ i, ∀ v ∈ 𝒜.part i, v ∉ 𝒜.W := fun i v hv h =>
    disjoint_left.1 (hgood.part_disjoint i) hv h
  have hπeq : ∀ i, ∀ v ∈ 𝒜.part i, π v = i := fun i v hv => pi_eq_of_mem hgood hπ hv
  have hRmem : ∀ r : Sym2 G, ∀ v ∈ r, v = r.out.1 ∨ v = r.out.2 := by
    intro r v hv
    rw [← mk_out r, Sym2.mem_iff] at hv
    exact hv
  have hRW : ∀ r ∈ R, ∀ v ∈ r, v ∉ 𝒜.W := by
    intro r hr v hv
    rcases hRmem r v hv with rfl | rfl
    · exact (hRadj r hr).2.1
    · exact (hRadj r hr).2.2
  have hRne : ∀ r ∈ R, r.out.1 ≠ r.out.2 := fun r hr => (hRadj r hr).1.ne
  have hmatch : ∀ e ∈ R, ∀ f ∈ R, ∀ v, v ∈ e → v ∈ f → e = f := by
    intro e he f hf v hve hvf
    by_contra hne
    exact hRmatch e he f hf hne v hve hvf
  have hιinj : ∀ w ∈ 𝒜.W, ∀ w' ∈ 𝒜.W, ι w = ι w' → w = w' := by
    intro w hw w' hw' h
    refine reserved_unique hgood w w w' hw hw' (by simp) ?_
    exact copy_coset hT _ (hι w hw) (by rw [h]; exact hι w' hw')
  -- the paths `a_H w_H b_H`
  have hpath : ∀ w ∈ 𝒜.W, ∃ x y : G, x ≠ y ∧ x ∈ 𝒜.part (ι w) ∧ y ∈ 𝒜.part (ι w) ∧
      (copyGraph T Ap Am (𝒜.g (ι w))).Adj w x ∧ (copyGraph T Ap Am (𝒜.g (ι w))).Adj w y ∧
      x ∉ vtx R ∧ y ∉ vtx R := by
    intro w hw
    have h1 := hgood.nbhd_lower (ι w) w (hι w hw)
    have h2 := hsparse (ι w) w (hι w hw)
    have hsplit := card_filter_add_card_filter_not (s := (𝒜.part (ι w)).filter fun y =>
      (copyGraph T Ap Am (𝒜.g (ι w))).Adj w y) (fun y => y ∈ vtx R)
    simp only [filter_filter] at hsplit
    have h3 : (1 : ℝ) < ((𝒜.part (ι w)).filter fun y =>
        (copyGraph T Ap Am (𝒜.g (ι w))).Adj w y ∧ y ∉ vtx R).card := by
      have h4 : (((𝒜.part (ι w)).filter fun y => (copyGraph T Ap Am (𝒜.g (ι w))).Adj w y ∧
          y ∈ vtx R).card : ℝ) + ((𝒜.part (ι w)).filter fun y =>
          (copyGraph T Ap Am (𝒜.g (ι w))).Adj w y ∧ y ∉ vtx R).card =
          (((𝒜.part (ι w)).filter fun y => (copyGraph T Ap Am (𝒜.g (ι w))).Adj w y).card : ℝ) := by
        exact_mod_cast hsplit
      linarith
    obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.1 (by exact_mod_cast h3)
    rw [mem_filter] at hx hy
    exact ⟨x, y, hxy, hx.1, hy.1, hx.2.1, hy.2.1, hx.2.2, hy.2.2⟩
  choose! pa pb hpab using hpath
  have hpa_ne : ∀ w ∈ 𝒜.W, pa w ≠ pb w := fun w hw => (hpab w hw).1
  have hpa_part : ∀ w ∈ 𝒜.W, pa w ∈ 𝒜.part (ι w) := fun w hw => (hpab w hw).2.1
  have hpb_part : ∀ w ∈ 𝒜.W, pb w ∈ 𝒜.part (ι w) := fun w hw => (hpab w hw).2.2.1
  have hpa_adj : ∀ w ∈ 𝒜.W, (copyGraph T Ap Am (𝒜.g (ι w))).Adj w (pa w) :=
    fun w hw => (hpab w hw).2.2.2.1
  have hpb_adj : ∀ w ∈ 𝒜.W, (copyGraph T Ap Am (𝒜.g (ι w))).Adj w (pb w) :=
    fun w hw => (hpab w hw).2.2.2.2.1
  have hpa_R : ∀ w ∈ 𝒜.W, pa w ∉ vtx R := fun w hw => (hpab w hw).2.2.2.2.2.1
  have hpb_R : ∀ w ∈ 𝒜.W, pb w ∉ vtx R := fun w hw => (hpab w hw).2.2.2.2.2.2
  have hpa_W : ∀ w ∈ 𝒜.W, pa w ∉ 𝒜.W := fun w hw => hpartW _ _ (hpa_part w hw)
  have hpb_W : ∀ w ∈ 𝒜.W, pb w ∉ 𝒜.W := fun w hw => hpartW _ _ (hpb_part w hw)
  have hend_part : ∀ w ∈ 𝒜.W, ∀ x, (x = pa w ∨ x = pb w) → x ∈ 𝒜.part (ι w) := by
    rintro w hw x (rfl | rfl)
    exacts [hpa_part w hw, hpb_part w hw]
  have hpend : ∀ w ∈ 𝒜.W, ∀ w' ∈ 𝒜.W, ∀ x, (x = pa w ∨ x = pb w) → (x = pa w' ∨ x = pb w') →
      w = w' := by
    intro w hw w' hw' x hx hx'
    exact hιinj w hw w' hw' ((hπeq _ _ (hend_part w hw x hx)).symm.trans
      (hπeq _ _ (hend_part w' hw' x hx')))
  have hsg_nbr : ∀ w ∈ 𝒜.W, ∀ x, x ∈ 𝒜.part (ι w) →
      (copyGraph T Ap Am (𝒜.g (ι w))).Adj w x → sgnOf 𝒜 Ap π x = loopSgn 𝒜 Am ι w := by
    intro w hw x hx hadj
    unfold sgnOf loopSgn
    rw [hπeq _ _ hx]
    rcases hadj.2.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h3 : (𝒜.g (ι w))⁻¹ * x ∉ Ap := fun h => disjoint_left.1 hT.disjoint h h2
      have h4 : (𝒜.g (ι w))⁻¹ * w ∉ Am := fun h => disjoint_left.1 hT.disjoint h1 h
      simp [h3, h4]
    · have h3 : (𝒜.g (ι w))⁻¹ * x ∈ Ap := h2
      simp [h3, h1]
  have hcay : ∀ w ∈ 𝒜.W, ∀ x, (copyGraph T Ap Am (𝒜.g (ι w))).Adj w x →
      (cayleyGraph S).Adj w x := by
    intro w _ x h
    rw [SimpleGraph.mulCayley_adj]
    refine ⟨h.ne, ?_⟩
    rcases copyGraph_adj_label h with h' | h'
    · exact Or.inl (hT.sub h')
    · exact Or.inr (hT.sub h')
  have hp : 0 < p := by
    rcases mul_pos_iff.1 (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 40) hpμ) with h | h
    · exact h.1
    · exact absurd h.2 (not_lt.2 hμ.le)
  -- the signed graph of `R ∪ P` and its capacities
  let Γ : SignedGraph (Fin 𝒜.t) ({r // r ∈ R} ⊕ {w // w ∈ 𝒜.W}) :=
    { fst := Sum.elim (fun r => π r.1.out.1) (fun w => ι w.1)
      snd := Sum.elim (fun r => π r.1.out.2) (fun w => ι w.1)
      sfst := Sum.elim (fun r => sgnOf 𝒜 Ap π r.1.out.1) (fun w => loopSgn 𝒜 Am ι w.1)
      ssnd := Sum.elim (fun r => sgnOf 𝒜 Ap π r.1.out.2) (fun w => loopSgn 𝒜 Am ι w.1) }
  have htR : ∀ r b, Γ.twinTail (Sum.inl r, b) = arcTail π (sgnOf 𝒜 Ap π) r.1 b := by
    intro r b; cases b <;> rfl
  have hhR : ∀ r b, Γ.twinHead (Sum.inl r, b) = arcHead π (sgnOf 𝒜 Ap π) r.1 b := by
    intro r b; cases b <;> rfl
  have htW : ∀ w b, Γ.twinTail (Sum.inr w, b) = (ι w.1, loopSgn 𝒜 Am ι w.1) := by
    intro w b; cases b <;> rfl
  have hhW : ∀ w b, Γ.twinHead (Sum.inr w, b) = (ι w.1, !loopSgn 𝒜 Am ι w.1) := by
    intro w b; cases b <;> rfl
  let lo : {r // r ∈ R} ⊕ {w // w ∈ 𝒜.W} → ℝ :=
    Sum.elim (fun r => if r.1 ∈ Z₀ then 1 else 1 / 256) (fun _ => 1)
  let up : {r // r ∈ R} ⊕ {w // w ∈ 𝒜.W} → ℝ :=
    Sum.elim (fun r => if r.1 ∈ Z₀ then 1 else 1 - 1 / 256) (fun _ => 1)
  have hlu : ∀ a : ({r // r ∈ R} ⊕ {w // w ∈ 𝒜.W}) × Bool, lo a.1 ≤ up a.1 := by
    rintro ⟨r | w, b⟩
    · show (if r.1 ∈ Z₀ then (1 : ℝ) else 1 / 256) ≤ if r.1 ∈ Z₀ then 1 else 1 - 1 / 256
      split_ifs <;> norm_num
    · exact le_refl (1 : ℝ)
  -- the circulation criterion (4.6)
  have hcutJ : ∀ J : Finset (Fin 𝒜.t × Bool),
      ∑ a ∈ univ.filter (fun a => Γ.twinHead a ∈ J ∧ Γ.twinTail a ∉ J), lo a.1 ≤
        ∑ a ∈ univ.filter (fun a => Γ.twinTail a ∈ J ∧ Γ.twinHead a ∉ J), up a.1 := by
    intro J
    have hL : ∑ a ∈ univ.filter (fun a => Γ.twinHead a ∈ J ∧ Γ.twinTail a ∉ J), lo a.1 ≤
        1 / 256 * inCnt π (sgnOf 𝒜 Ap π) J R + cutCnt π (sgnOf 𝒜 Ap π) J Z₀ +
          loopCnt ι (loopSgn 𝒜 Am ι) J 𝒜.W := by
      rw [sum_filter, Fintype.sum_prod_type, Fintype.sum_sum_type]
      simp only [sum_bool_ite]
      have h1 : ∑ r : {r // r ∈ R}, lo (Sum.inl r) * ((univ.filter fun b =>
          Γ.twinHead (Sum.inl r, b) ∈ J ∧ Γ.twinTail (Sum.inl r, b) ∉ J).card : ℝ) =
          ∑ r ∈ R, (if r ∈ Z₀ then 1 else 1 / 256) * (inArcs π (sgnOf 𝒜 Ap π) J r : ℝ) := by
        rw [← Finset.sum_coe_sort R]
        refine Fintype.sum_congr _ _ fun r => ?_
        simp only [htR, hhR]
        rfl
      have h2 : ∑ w : {w // w ∈ 𝒜.W}, lo (Sum.inr w) * ((univ.filter fun b =>
          Γ.twinHead (Sum.inr w, b) ∈ J ∧ Γ.twinTail (Sum.inr w, b) ∉ J).card : ℝ) ≤
          loopCnt ι (loopSgn 𝒜 Am ι) J 𝒜.W := by
        unfold loopCnt
        push_cast
        rw [← Finset.sum_coe_sort 𝒜.W]
        refine Finset.sum_le_sum fun w _ => ?_
        simp only [htW, hhW]
        show (1 : ℝ) * ((univ.filter fun _ : Bool => (ι w.1, !loopSgn 𝒜 Am ι w.1) ∈ J ∧
          (ι w.1, loopSgn 𝒜 Am ι w.1) ∉ J).card : ℝ) ≤ _
        by_cases hc : (ι w.1, !loopSgn 𝒜 Am ι w.1) ∈ J ∧ (ι w.1, loopSgn 𝒜 Am ι w.1) ∉ J
        · rw [if_pos (Or.inr hc)]
          have h5 : (univ.filter fun _ : Bool => (ι w.1, !loopSgn 𝒜 Am ι w.1) ∈ J ∧
              (ι w.1, loopSgn 𝒜 Am ι w.1) ∉ J).card ≤ 2 := (card_filter_le _ _).trans (by simp)
          have h6 : ((univ.filter fun _ : Bool => (ι w.1, !loopSgn 𝒜 Am ι w.1) ∈ J ∧
              (ι w.1, loopSgn 𝒜 Am ι w.1) ∉ J).card : ℝ) ≤ 2 := by exact_mod_cast h5
          linarith
        · rw [Finset.filter_false_of_mem (fun _ _ => hc)]
          simp only [card_empty, Nat.cast_zero, mul_zero]
          split_ifs <;> norm_num
      have h3 : ∑ r ∈ R, (if r ∈ Z₀ then 1 else 1 / 256) * (inArcs π (sgnOf 𝒜 Ap π) J r : ℝ) ≤
          1 / 256 * inCnt π (sgnOf 𝒜 Ap π) J R + cutCnt π (sgnOf 𝒜 Ap π) J Z₀ := by
        have hZ : (cutCnt π (sgnOf 𝒜 Ap π) J Z₀ : ℝ) = ∑ r ∈ R, if r ∈ Z₀ then
            ((outArcs π (sgnOf 𝒜 Ap π) J r : ℝ) + inArcs π (sgnOf 𝒜 Ap π) J r) else 0 := by
          rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.2 hZR]
          unfold cutCnt outCnt inCnt
          push_cast
          rw [sum_add_distrib]
        have hI : (inCnt π (sgnOf 𝒜 Ap π) J R : ℝ) =
            ∑ r ∈ R, (inArcs π (sgnOf 𝒜 Ap π) J r : ℝ) := by
          unfold inCnt
          push_cast
          rfl
        rw [hZ, hI, mul_sum, ← sum_add_distrib]
        refine sum_le_sum fun r _ => ?_
        have h0 : (0 : ℝ) ≤ outArcs π (sgnOf 𝒜 Ap π) J r := Nat.cast_nonneg _
        have h0' : (0 : ℝ) ≤ inArcs π (sgnOf 𝒜 Ap π) J r := Nat.cast_nonneg _
        split_ifs <;> linarith
      linarith [h1, h2, h3]
    have hU : (1 - 1 / 256) * (outCnt π (sgnOf 𝒜 Ap π) J R : ℝ) ≤
        ∑ a ∈ univ.filter (fun a => Γ.twinTail a ∈ J ∧ Γ.twinHead a ∉ J), up a.1 := by
      rw [sum_filter, Fintype.sum_prod_type, Fintype.sum_sum_type]
      simp only [sum_bool_ite]
      have h1 : ∑ r : {r // r ∈ R}, up (Sum.inl r) * ((univ.filter fun b =>
          Γ.twinTail (Sum.inl r, b) ∈ J ∧ Γ.twinHead (Sum.inl r, b) ∉ J).card : ℝ) =
          ∑ r ∈ R, (if r ∈ Z₀ then 1 else 1 - 1 / 256) * (outArcs π (sgnOf 𝒜 Ap π) J r : ℝ) := by
        rw [← Finset.sum_coe_sort R]
        refine Fintype.sum_congr _ _ fun r => ?_
        simp only [htR, hhR]
        rfl
      have h2 : 0 ≤ ∑ w : {w // w ∈ 𝒜.W}, up (Sum.inr w) * ((univ.filter fun b =>
          Γ.twinTail (Sum.inr w, b) ∈ J ∧ Γ.twinHead (Sum.inr w, b) ∉ J).card : ℝ) :=
        sum_nonneg fun w _ => mul_nonneg zero_le_one (Nat.cast_nonneg _)
      have h3 : (1 - 1 / 256) * (outCnt π (sgnOf 𝒜 Ap π) J R : ℝ) ≤
          ∑ r ∈ R, (if r ∈ Z₀ then 1 else 1 - 1 / 256) * (outArcs π (sgnOf 𝒜 Ap π) J r : ℝ) := by
        unfold outCnt
        push_cast
        rw [mul_sum]
        refine sum_le_sum fun r _ => ?_
        have h0 : (0 : ℝ) ≤ outArcs π (sgnOf 𝒜 Ap π) J r := Nat.cast_nonneg _
        split_ifs <;> linarith
      linarith [h1, h2, h3]
    have hloopb : (loopCnt ι (loopSgn 𝒜 Am ι) J 𝒜.W : ℝ) ≤ p * s J / 20 := by
      have h1 := mul_le_mul_of_nonneg_left (hloop J) hp.le
      have h2 := mul_le_mul_of_nonneg_right hpμ
        (Nat.cast_nonneg (loopCnt ι (loopSgn 𝒜 Am ι) J 𝒜.W) : (0 : ℝ) ≤ _)
      linarith
    have hin : (inCnt π (sgnOf 𝒜 Ap π) J R : ℝ) ≤ cutCnt π (sgnOf 𝒜 Ap π) J R := by
      unfold cutCnt
      push_cast
      linarith [(Nat.cast_nonneg (outCnt π (sgnOf 𝒜 Ap π) J R) : (0 : ℝ) ≤ _)]
    have hps : 0 ≤ p * s J := mul_nonneg hp.le (hs J)
    linarith [hL, hU, hout J, hcutR J, hcutZ J, hloopb, hin, hps]
  obtain ⟨g, hgb, hgc⟩ := hoffman_circulation Γ.twinTail Γ.twinHead (fun a => lo a.1)
    (fun a => up a.1) hlu hcutJ
  obtain ⟨f, hflu, hfB⟩ := signed_circulation Γ lo up g (fun e b => hgb (e, b)) hgc
  have hf01 : ∀ e, 0 ≤ f e ∧ f e ≤ 1 := by
    intro e
    obtain ⟨h1, h2⟩ := hflu e
    rcases e with r | w
    · have hl : (0 : ℝ) ≤ lo (Sum.inl r) := by
        show (0 : ℝ) ≤ if r.1 ∈ Z₀ then 1 else 1 / 256
        split_ifs <;> norm_num
      have hu : up (Sum.inl r) ≤ 1 := by
        show (if r.1 ∈ Z₀ then (1 : ℝ) else 1 - 1 / 256) ≤ 1
        split_ifs <;> norm_num
      exact ⟨hl.trans h1, h2.trans hu⟩
    · exact ⟨le_trans (by norm_num : (0 : ℝ) ≤ 1) h1, h2⟩
  -- the slack-cut condition (4.2)
  have hslackU : ∀ U : Finset (Fin 𝒜.t), (∀ v ∈ U, ∀ w ∈ U, Γ.underlying.Reachable v w) →
      (∃ v ∈ U, ∃ w ∉ U, Γ.underlying.Reachable v w) →
      1 ≤ ∑ e ∈ univ.filter (fun e => Γ.crosses (U : Set (Fin 𝒜.t)) e),
        min (f e) (1 - f e) := by
    rintro U - ⟨v, hv, w, hw, -⟩
    have hcnt := hslack U ⟨v, hv⟩ (fun h => hw (h ▸ mem_univ w))
    have hm0 : ∀ e, 0 ≤ min (f e) (1 - f e) := fun e =>
      le_min (hf01 e).1 (by linarith [(hf01 e).2])
    rw [sum_filter, Fintype.sum_sum_type]
    have h2 : 0 ≤ ∑ w : {w // w ∈ 𝒜.W}, (if Γ.crosses (U : Set (Fin 𝒜.t)) (Sum.inr w) then
        min (f (Sum.inr w)) (1 - f (Sum.inr w)) else 0) :=
      sum_nonneg fun w _ => by split_ifs; exacts [hm0 _, le_rfl]
    have hpt : ∀ r : {r // r ∈ R}, (if r.1 ∉ Z₀ ∧ PartCross π U r.1 then (1 : ℝ) / 256 else 0) ≤
        (if Γ.crosses (U : Set (Fin 𝒜.t)) (Sum.inl r) then
          min (f (Sum.inl r)) (1 - f (Sum.inl r)) else 0) := by
      intro r
      by_cases hr : r.1 ∉ Z₀ ∧ PartCross π U r.1
      · rw [if_pos hr]
        have hcr : Γ.crosses (U : Set (Fin 𝒜.t)) (Sum.inl r) := by
          show (π r.1.out.1 ∈ (U : Set (Fin 𝒜.t))) ≠ (π r.1.out.2 ∈ (U : Set (Fin 𝒜.t)))
          simp only [Finset.mem_coe]
          rcases hr.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · intro h
            exact h2 (cast h h1)
          · intro h
            exact h2 (cast h.symm h1)
        rw [if_pos hcr]
        obtain ⟨h1, h2⟩ := hflu (Sum.inl r)
        have hl : lo (Sum.inl r) = 1 / 256 := by
          show (if r.1 ∈ Z₀ then (1 : ℝ) else 1 / 256) = 1 / 256
          rw [if_neg hr.1]
        have hu : up (Sum.inl r) = 1 - 1 / 256 := by
          show (if r.1 ∈ Z₀ then (1 : ℝ) else 1 - 1 / 256) = 1 - 1 / 256
          rw [if_neg hr.1]
        rw [hl] at h1
        rw [hu] at h2
        exact le_min h1 (by linarith)
      · rw [if_neg hr]
        split_ifs
        · exact hm0 _
        · exact le_rfl
    calc (1 : ℝ) ≤ 1 / 256 * ((R \ Z₀).filter (PartCross π U)).card := by
          have : (256 : ℝ) ≤ ((R \ Z₀).filter (PartCross π U)).card := by exact_mod_cast hcnt
          linarith
      _ = ∑ r ∈ R, (if r ∉ Z₀ ∧ PartCross π U r then (1 : ℝ) / 256 else 0) := by
          rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm, sdiff_eq_filter, filter_filter]
      _ = ∑ r : {r // r ∈ R}, (if r.1 ∉ Z₀ ∧ PartCross π U r.1 then (1 : ℝ) / 256 else 0) :=
          (Finset.sum_coe_sort R
            (fun r => if r ∉ Z₀ ∧ PartCross π U r then (1 : ℝ) / 256 else 0)).symm
      _ ≤ _ := sum_le_sum fun r _ => hpt r
      _ ≤ _ := le_add_of_nonneg_right h2
  -- Lemma 4.1 and the choice of an integral point
  have hconv := robust_signed_integrality Γ (fun _ => 0) (fun v => by simp) f hf01
    (fun v => by rw [hfB v]; simp) hslackU
  obtain ⟨z, hz, hz1⟩ := exists_face_point hconv (fun z hz e => by
    rcases hz.1 e with h | h <;> rw [h] <;> norm_num)
  have hzZ : ∀ r (hr : r ∈ R), r ∈ Z₀ → z (Sum.inl ⟨r, hr⟩) = 1 := by
    intro r hr hrZ
    refine hz1 _ ?_
    obtain ⟨h1, h2⟩ := hflu (Sum.inl ⟨r, hr⟩)
    have hl : lo (Sum.inl ⟨r, hr⟩) = 1 := by
      show (if r ∈ Z₀ then (1 : ℝ) else 1 / 256) = 1
      rw [if_pos hrZ]
    have hu : up (Sum.inl ⟨r, hr⟩) = 1 := by
      show (if r ∈ Z₀ then (1 : ℝ) else 1 - 1 / 256) = 1
      rw [if_pos hrZ]
    rw [hl] at h1
    rw [hu] at h2
    exact le_antisymm h2 h1
  have hzW : ∀ w : {w // w ∈ 𝒜.W}, z (Sum.inr w) = 1 := fun w =>
    hz1 _ (le_antisymm (hflu (Sum.inr w)).2 (hflu (Sum.inr w)).1)
  -- the selected edges and the connector
  obtain ⟨Msel, hMsel⟩ : ∃ Msel : Finset (Sym2 G),
      Msel = R.filter (fun r => ∃ h : r ∈ R, z (Sum.inl ⟨r, h⟩) = 1) := ⟨_, rfl⟩
  have hmemM : ∀ r, r ∈ Msel ↔ ∃ h : r ∈ R, z (Sum.inl ⟨r, h⟩) = 1 := by
    intro r
    rw [hMsel, mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  have hMR : Msel ⊆ R := fun r hr => ((hmemM r).1 hr).1
  have hZM : Z₀ ⊆ Msel := fun r hr => (hmemM r).2 ⟨hZR hr, hzZ r (hZR hr) hr⟩
  have hzM : ∀ r : {r // r ∈ R}, z (Sum.inl r) = if r.1 ∈ Msel then 1 else 0 := by
    intro r
    rcases hz.1 (Sum.inl r) with h | h
    · rw [if_neg]
      · exact h
      · intro hm
        obtain ⟨_, h'⟩ := (hmemM r.1).1 hm
        have h'' : z (Sum.inl r) = 1 := h'
        rw [h''] at h
        norm_num at h
    · rw [if_pos ((hmemM r.1).2 ⟨r.2, h⟩)]
      exact h
  obtain ⟨M, hMdef⟩ : ∃ M : SimpleGraph G, M = SimpleGraph.fromEdgeSet ((Msel : Set (Sym2 G)) ∪
      {e | ∃ w ∈ 𝒜.W, e = s(w, pa w) ∨ e = s(w, pb w)}) := ⟨_, rfl⟩
  have hMadj : ∀ x y, M.Adj x y ↔ (s(x, y) ∈ Msel ∨ ∃ w ∈ 𝒜.W, s(x, y) = s(w, pa w) ∨
      s(x, y) = s(w, pb w)) ∧ x ≠ y := by
    intro x y
    rw [hMdef]
    simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq]
  have hvtxM : ∀ r ∈ Msel, ∀ v ∈ r, v ∈ vtx R := fun r hr v hv =>
    mem_vtx.2 ⟨r, hMR hr, hv⟩
  have hcases : ∀ v y, v ∉ 𝒜.W → M.Adj v y →
      s(v, y) ∈ Msel ∨ ∃ w ∈ 𝒜.W, (v = pa w ∨ v = pb w) ∧ y = w := by
    intro v y hv h
    rw [hMadj] at h
    rcases h.1 with h1 | ⟨w, hw, h1 | h1⟩
    · exact Or.inl h1
    · rcases Sym2.eq_iff.1 h1 with ⟨rfl, -⟩ | ⟨h3, h4⟩
      · exact absurd hw hv
      · exact Or.inr ⟨w, hw, Or.inl h3, h4⟩
    · rcases Sym2.eq_iff.1 h1 with ⟨rfl, -⟩ | ⟨h3, h4⟩
      · exact absurd hw hv
      · exact Or.inr ⟨w, hw, Or.inr h3, h4⟩
  have hsub : ∀ v, v ∉ 𝒜.W → ∀ y y', M.Adj v y → M.Adj v y' → y = y' := by
    intro v hv y y' h h'
    rcases hcases v y hv h with h1 | ⟨w, hw, hvw, hyw⟩ <;>
      rcases hcases v y' hv h' with h2 | ⟨w', hw', hvw', hyw'⟩
    · have := hmatch _ (hMR h1) _ (hMR h2) v (Sym2.mem_mk_left v y) (Sym2.mem_mk_left v y')
      exact Sym2.congr_right.1 this
    · exfalso
      have := hvtxM _ h1 v (Sym2.mem_mk_left v y)
      rcases hvw' with rfl | rfl
      exacts [hpa_R w' hw' this, hpb_R w' hw' this]
    · exfalso
      have := hvtxM _ h2 v (Sym2.mem_mk_left v y')
      rcases hvw with rfl | rfl
      exacts [hpa_R w hw this, hpb_R w hw this]
    · rw [hyw, hyw']
      exact hpend w hw w' hw' v hvw hvw'
  have hends : ∀ v, v ∉ 𝒜.W →
      ((∃ y, M.Adj v y) ↔ (v ∈ vtx Msel ∨ ∃ w ∈ 𝒜.W, v = pa w ∨ v = pb w)) := by
    intro v hv
    constructor
    · rintro ⟨y, hy⟩
      rcases hcases v y hv hy with h1 | ⟨w, hw, hvw, -⟩
      · exact Or.inl (mem_vtx.2 ⟨_, h1, Sym2.mem_mk_left v y⟩)
      · exact Or.inr ⟨w, hw, hvw⟩
    · rintro (h | ⟨w, hw, hvw⟩)
      · obtain ⟨r, hr, hvr⟩ := mem_vtx.1 h
        obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 hvr
        refine ⟨y, (hMadj v y).2 ⟨Or.inl hr, fun hvy => ?_⟩⟩
        subst hvy
        exact hRne _ (hMR hr) (by simp)
      · refine ⟨w, (hMadj v w).2 ⟨Or.inr ⟨w, hw, ?_⟩, fun h => hv (by rw [h]; exact hw)⟩⟩
        rcases hvw with rfl | rfl
        · exact Or.inl Sym2.eq_swap
        · exact Or.inr Sym2.eq_swap
  have hdegW : ∀ w ∈ 𝒜.W, M.neighborSet w = {pa w, pb w} := by
    intro w hw
    ext y
    simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [hMadj] at h
      rcases h.1 with h1 | ⟨w', hw', h1 | h1⟩
      · exact absurd hw (hRW _ (hMR h1) w (Sym2.mem_mk_left w y))
      · rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨h3, -⟩
        · exact Or.inl rfl
        · exact absurd (h3 ▸ hw) (hpa_W _ hw')
      · rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨h3, -⟩
        · exact Or.inr rfl
        · exact absurd (h3 ▸ hw) (hpb_W _ hw')
    · rintro (rfl | rfl)
      · exact (hMadj _ _).2 ⟨Or.inr ⟨w, hw, Or.inl rfl⟩,
          fun h => hpa_W w hw (by rw [← h]; exact hw)⟩
      · exact (hMadj _ _).2 ⟨Or.inr ⟨w, hw, Or.inr rfl⟩,
          fun h => hpb_W w hw (by rw [← h]; exact hw)⟩
  have hdeg_le : ∀ v, v ∉ 𝒜.W → (M.neighborSet v).ncard ≤ 1 := fun v hv =>
    (Set.ncard_le_one (Set.toFinite _)).2 fun y hy y' hy' => hsub v hv y y' hy hy'
  have hdeg1 : ∀ v, v ∉ 𝒜.W → ((M.neighborSet v).ncard = 1 ↔
      (v ∈ vtx Msel ∨ ∃ w ∈ 𝒜.W, v = pa w ∨ v = pb w)) := by
    intro v hv
    rw [ncard_eq_one_iff_nonempty (M.neighborSet v) (fun y hy y' hy' => hsub v hv y y' hy hy')]
    exact hends v hv
  -- the path endpoints in a part
  let pathEnds : Fin 𝒜.t → Finset G := fun i =>
    (𝒜.W.filter fun w => ι w = i).biUnion fun w => {pa w, pb w}
  have hWi : ∀ i, (𝒜.W.filter fun w => ι w = i).card ≤ 1 := fun i =>
    card_le_one.2 fun w hw w' hw' => by
      rw [mem_filter] at hw hw'
      exact hιinj w hw.1 w' hw'.1 (hw.2.trans hw'.2.symm)
  have hpathcard : ∀ i, (pathEnds i).card ≤ 2 := by
    intro i
    calc (pathEnds i).card ≤ ∑ w ∈ 𝒜.W.filter (fun w => ι w = i),
          ({pa w, pb w} : Finset G).card := card_biUnion_le
      _ ≤ ∑ w ∈ 𝒜.W.filter (fun w => ι w = i), 2 :=
          sum_le_sum fun w _ => (card_insert_le _ _).trans (by simp)
      _ = 2 * (𝒜.W.filter fun w => ι w = i).card := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 := by have := hWi i; omega
  have hpath_mem : ∀ i v, v ∈ pathEnds i ↔ ∃ w ∈ 𝒜.W, ι w = i ∧ (v = pa w ∨ v = pb w) := by
    intro i v
    simp only [pathEnds, mem_biUnion, mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨w, ⟨hw, hwi⟩, hv⟩
      exact ⟨w, hw, hwi, hv⟩
    · rintro ⟨w, hw, hwi, hv⟩
      exact ⟨w, ⟨hw, hwi⟩, hv⟩
  have hEsub : ∀ i v, v ∈ 𝒜.part i → (M.neighborSet v).ncard = 1 →
      v ∈ vtx R ∨ v ∈ pathEnds i := by
    intro i v hv h1
    rcases (hdeg1 v (hpartW i v hv)).1 h1 with h | ⟨w, hw, hvw⟩
    · obtain ⟨r, hr, hvr⟩ := mem_vtx.1 h
      exact Or.inl (hvtxM r hr v hvr)
    · refine Or.inr ((hpath_mem i v).2 ⟨w, hw, ?_, hvw⟩)
      exact (hπeq _ _ (hend_part w hw v hvw)).symm.trans (hπeq i v hv)
  refine ⟨M, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `M` uses edges of `X`
    intro x y h
    rw [hMadj] at h
    obtain ⟨h1, -⟩ := h
    rw [← SimpleGraph.mem_edgeSet]
    rcases h1 with h1 | ⟨w, hw, h1 | h1⟩
    · have := (hRadj _ (hMR h1)).1
      rw [← SimpleGraph.mem_edgeSet, mk_out] at this
      exact this
    · rw [h1, SimpleGraph.mem_edgeSet]
      exact hcay w hw _ (hpa_adj w hw)
    · rw [h1, SimpleGraph.mem_edgeSet]
      exact hcay w hw _ (hpb_adj w hw)
  · intro w hw
    rw [hdegW w hw, Set.ncard_pair (hpa_ne w hw)]
  · intro w hw y hy
    have : y ∈ M.neighborSet w := hy
    rw [hdegW w hw] at this
    rcases this with rfl | rfl
    exacts [hpa_W w hw, hpb_W w hw]
  · exact hdeg_le
  · -- the contraction is connected
    haveI : Nonempty (Fin 𝒜.t) := ⟨⟨0, by omega⟩⟩
    refine connected_of_forall_cut _ fun I hI hI' => ?_
    obtain ⟨e, he, hcross⟩ := hconn I hI hI'
    have heR := hZR he
    have hadj : M.Adj e.out.1 e.out.2 :=
      (hMadj _ _).2 ⟨Or.inl (by rw [mk_out]; exact hZM he), hRne e heR⟩
    have h1 := hπ _ (hRadj e heR).2.1
    have h2 := hπ _ (hRadj e heR).2.2
    rcases hcross with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · refine ⟨π e.out.1, hi, π e.out.2, hj, ?_⟩
      rw [SimpleGraph.fromRel_adj]
      exact ⟨fun h => hj (h ▸ hi), Or.inl ⟨e.out.1, h1, e.out.2, h2, hRne e heR, hadj.reachable⟩⟩
    · refine ⟨π e.out.2, hi, π e.out.1, hj, ?_⟩
      rw [SimpleGraph.fromRel_adj]
      exact ⟨fun h => hj (h ▸ hi), Or.inr ⟨e.out.1, h1, e.out.2, h2, hRne e heR, hadj.reachable⟩⟩
  · -- the endpoints are balanced (signed balance of `z`)
    intro i
    have hEi : (𝒜.part i).filter (fun v => (M.neighborSet v).ncard = 1) =
        ((𝒜.part i).filter (· ∈ vtx Msel)) ∪ pathEnds i := by
      ext v
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨hv, h1⟩
        rcases (hdeg1 v (hpartW i v hv)).1 h1 with h | ⟨w, hw, hvw⟩
        · exact Or.inl ⟨hv, h⟩
        · refine Or.inr ((hpath_mem i v).2 ⟨w, hw, ?_, hvw⟩)
          exact (hπeq _ _ (hend_part w hw v hvw)).symm.trans (hπeq i v hv)
      · rintro (⟨hv, h⟩ | h)
        · exact ⟨hv, (hdeg1 v (hpartW i v hv)).2 (Or.inl h)⟩
        · obtain ⟨w, hw, hwi, hvw⟩ := (hpath_mem i v).1 h
          have hv : v ∈ 𝒜.part i := hwi ▸ hend_part w hw v hvw
          exact ⟨hv, (hdeg1 v (hpartW i v hv)).2 (Or.inr ⟨w, hw, hvw⟩)⟩
    have hdisj : Disjoint ((𝒜.part i).filter (· ∈ vtx Msel)) (pathEnds i) := by
      rw [disjoint_left]
      intro v hv hv'
      obtain ⟨w, hw, -, hvw⟩ := (hpath_mem i v).1 hv'
      obtain ⟨r, hr, hvr⟩ := mem_vtx.1 (mem_filter.1 hv).2
      have := hvtxM r hr v hvr
      rcases hvw with rfl | rfl
      exacts [hpa_R w hw this, hpb_R w hw this]
    let χ : G → ℝ := fun v => SignedGraph.signVal (sgnOf 𝒜 Ap π v)
    have hsigned : ∀ A : Finset G, A ⊆ 𝒜.part i →
        ∑ v ∈ A, χ v = ((A.filter fun v => (𝒜.g i)⁻¹ * v ∈ Ap).card : ℝ) -
          (A.filter fun v => (𝒜.g i)⁻¹ * v ∈ Am).card := by
      intro A hA
      have hχ : ∀ v ∈ A, χ v = (if (𝒜.g i)⁻¹ * v ∈ Ap then 1 else 0) -
          (if (𝒜.g i)⁻¹ * v ∈ Am then 1 else 0) := by
        intro v hv
        have hvi := hA hv
        have hc : (𝒜.g i)⁻¹ * v ∈ Ap ∪ Am := mem_copyVerts.1 (hgood.part_sub i hvi)
        simp only [χ, sgnOf, hπeq i v hvi, SignedGraph.signVal]
        by_cases h1 : (𝒜.g i)⁻¹ * v ∈ Ap
        · have h2 : (𝒜.g i)⁻¹ * v ∉ Am := fun h => disjoint_left.1 hT.disjoint h1 h
          simp [h1, h2]
        · have h2 : (𝒜.g i)⁻¹ * v ∈ Am := (mem_union.1 hc).resolve_left h1
          simp [h1, h2]
      rw [sum_congr rfl hχ, sum_sub_distrib, sum_boole, sum_boole]
    have happly : Γ.apply z i =
        ∑ v ∈ (𝒜.part i).filter (fun v => (M.neighborSet v).ncard = 1), χ v := by
      rw [hEi, sum_union hdisj]
      unfold SignedGraph.apply
      rw [Fintype.sum_sum_type]
      congr 1
      · have hinc : ∀ r : {r // r ∈ R}, Γ.incidence i (Sum.inl r) * z (Sum.inl r) =
            if r.1 ∈ Msel then ((if π r.1.out.1 = i then χ r.1.out.1 else 0) +
              (if π r.1.out.2 = i then χ r.1.out.2 else 0)) else 0 := by
          intro r
          have hi : Γ.incidence i (Sum.inl r) = (if π r.1.out.1 = i then χ r.1.out.1 else 0) +
              (if π r.1.out.2 = i then χ r.1.out.2 else 0) := by
            unfold SignedGraph.incidence
            congr
          rw [hi, hzM r]
          by_cases hm : r.1 ∈ Msel
          · simp only [hm, if_true, mul_one]
          · simp only [hm, if_false, mul_zero]
        rw [Fintype.sum_congr _ _ hinc, Finset.sum_coe_sort R (fun r => if r ∈ Msel then
          ((if π r.out.1 = i then χ r.out.1 else 0) + (if π r.out.2 = i then χ r.out.2 else 0))
          else 0), ← sum_filter, filter_mem_eq_inter, inter_eq_right.2 hMR]
        have hset : (𝒜.part i).filter (· ∈ vtx Msel) = (Msel.biUnion fun r =>
            ({r.out.1, r.out.2} : Finset G)).filter (fun v => π v = i) := by
          ext v
          simp only [mem_filter, mem_biUnion, mem_insert, mem_singleton]
          constructor
          · rintro ⟨hv, hvM⟩
            obtain ⟨r, hr, hvr⟩ := mem_vtx.1 hvM
            exact ⟨⟨r, hr, hRmem r v hvr⟩, hπeq i v hv⟩
          · rintro ⟨⟨r, hr, hvr⟩, hvi⟩
            have hvr' : v ∈ r := by
              rcases hvr with rfl | rfl
              exacts [Sym2.out_fst_mem r, Sym2.out_snd_mem r]
            refine ⟨?_, mem_vtx.2 ⟨r, hr, hvr'⟩⟩
            have := hπ v (hRW r (hMR hr) v hvr')
            rwa [hvi] at this
        rw [hset, Finset.sum_filter (fun v => π v = i)]
        have hpd : (Msel : Set (Sym2 G)).PairwiseDisjoint
            (fun r => ({r.out.1, r.out.2} : Finset G)) := by
          intro r hr r' hr' hne
          simp only [Function.onFun]
          rw [disjoint_left]
          intro v hv hv'
          have h1 : v ∈ r := by
            simp only [mem_insert, mem_singleton] at hv
            rcases hv with rfl | rfl
            exacts [Sym2.out_fst_mem r, Sym2.out_snd_mem r]
          have h2 : v ∈ r' := by
            simp only [mem_insert, mem_singleton] at hv'
            rcases hv' with rfl | rfl
            exacts [Sym2.out_fst_mem r', Sym2.out_snd_mem r']
          exact hRmatch r (hMR hr) r' (hMR hr') hne v h1 h2
        rw [sum_biUnion hpd]
        refine sum_congr rfl fun r hr => ?_
        rw [sum_pair (hRne r (hMR hr))]
      · have hinc : ∀ w : {w // w ∈ 𝒜.W}, Γ.incidence i (Sum.inr w) * z (Sum.inr w) =
            if ι w.1 = i then 2 * SignedGraph.signVal (loopSgn 𝒜 Am ι w.1) else 0 := by
          intro w
          have hi : Γ.incidence i (Sum.inr w) =
              (if ι w.1 = i then SignedGraph.signVal (loopSgn 𝒜 Am ι w.1) else 0) +
              (if ι w.1 = i then SignedGraph.signVal (loopSgn 𝒜 Am ι w.1) else 0) := by
            unfold SignedGraph.incidence
            congr
          rw [hi, hzW w]
          split_ifs <;> ring
        rw [Fintype.sum_congr _ _ hinc, Finset.sum_coe_sort 𝒜.W (fun w => if ι w = i then
          2 * SignedGraph.signVal (loopSgn 𝒜 Am ι w) else 0), ← sum_filter]
        have hpd : ((𝒜.W.filter fun w => ι w = i : Finset G) : Set G).PairwiseDisjoint
            (fun w => ({pa w, pb w} : Finset G)) := by
          intro w hw w' hw' hne
          simp only [Function.onFun]
          rw [disjoint_left]
          intro v hv hv'
          simp only [mem_insert, mem_singleton] at hv hv'
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hw hw'
          exact hne (hpend w hw.1 w' hw'.1 v hv hv')
        show _ = ∑ v ∈ (𝒜.W.filter fun w => ι w = i).biUnion
          (fun w => ({pa w, pb w} : Finset G)), χ v
        rw [sum_biUnion hpd]
        refine sum_congr rfl fun w hw => ?_
        rw [mem_filter] at hw
        rw [sum_pair (hpa_ne w hw.1)]
        simp only [χ, hsg_nbr w hw.1 (pa w) (hpa_part w hw.1) (hpa_adj w hw.1),
          hsg_nbr w hw.1 (pb w) (hpb_part w hw.1) (hpb_adj w hw.1)]
        ring
    have hzero : ∑ v ∈ (𝒜.part i).filter (fun v => (M.neighborSet v).ncard = 1), χ v = 0 := by
      rw [← happly]
      simpa using hz.2 i
    rw [hsigned _ (filter_subset _ _)] at hzero
    simp only [filter_filter] at hzero
    have : (((𝒜.part i).filter fun v => (M.neighborSet v).ncard = 1 ∧
        (𝒜.g i)⁻¹ * v ∈ Ap).card : ℝ) = ((𝒜.part i).filter fun v =>
        (M.neighborSet v).ncard = 1 ∧ (𝒜.g i)⁻¹ * v ∈ Am).card := by linarith
    exact_mod_cast this
  · -- every part contains an endpoint
    intro i
    have hI' : ({i} : Finset (Fin 𝒜.t)) ≠ univ := by
      intro h
      obtain ⟨j, hj⟩ : ∃ j : Fin 𝒜.t, j ≠ i := by
        by_cases h0 : i.val = 0
        · exact ⟨⟨1, by omega⟩, fun h' => by
            have := congrArg Fin.val h'
            simp only at this
            omega⟩
        · exact ⟨⟨0, by omega⟩, fun h' => by
            have := congrArg Fin.val h'
            simp only at this
            omega⟩
      have := mem_univ j
      rw [← h, mem_singleton] at this
      exact hj this
    obtain ⟨e, he, hcross⟩ := hconn {i} (singleton_nonempty i) hI'
    have heR := hZR he
    have hmem : ∀ v ∈ e, v ∈ vtx Msel := fun v hv => mem_vtx.2 ⟨e, hZM he, hv⟩
    rcases hcross with ⟨hi, -⟩ | ⟨hi, -⟩
    · rw [mem_singleton] at hi
      exact ⟨e.out.1, hi ▸ hπ _ (hRadj e heR).2.1,
        (hdeg1 _ (hRadj e heR).2.1).2 (Or.inl (hmem _ (Sym2.out_fst_mem e)))⟩
    · rw [mem_singleton] at hi
      exact ⟨e.out.2, hi ▸ hπ _ (hRadj e heR).2.2,
        (hdeg1 _ (hRadj e heR).2.2).2 (Or.inl (hmem _ (Sym2.out_snd_mem e)))⟩
  · -- few endpoints in every part
    intro i
    have hsub' : (𝒜.part i).filter (fun v => (M.neighborSet v).ncard = 1) ⊆
        (𝒜.part i).filter (· ∈ vtx R) ∪ pathEnds i := by
      intro v hv
      rw [mem_filter] at hv
      rcases hEsub i v hv.1 hv.2 with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨hv.1, h⟩)
      · exact mem_union_right _ h
    have h1 := (card_le_card hsub').trans (card_union_le _ _)
    have h2 : (((𝒜.part i).filter (fun v => (M.neighborSet v).ncard = 1)).card : ℝ) ≤
        ((𝒜.part i).filter (· ∈ vtx R)).card + 2 := by
      have := h1.trans (Nat.add_le_add_left (hpathcard i) _)
      exact_mod_cast this
    linarith [hfew i]
  · -- few endpoints among the neighbours of any full-copy vertex
    intro i v hv
    have hsub' : ((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y ∧
        (M.neighborSet y).ncard = 1) ⊆ ((𝒜.part i).filter fun y =>
          (copyGraph T Ap Am (𝒜.g i)).Adj v y ∧ y ∈ vtx R) ∪ pathEnds i := by
      intro y hy
      rw [mem_filter] at hy
      rcases hEsub i y hy.1 hy.2.2 with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨hy.1, hy.2.1, h⟩)
      · exact mem_union_right _ h
    have h1 := (card_le_card hsub').trans (card_union_le _ _)
    have h2 : (((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y ∧
        (M.neighborSet y).ncard = 1).card : ℝ) ≤ ((𝒜.part i).filter fun y =>
          (copyGraph T Ap Am (𝒜.g i)).Adj v y ∧ y ∈ vtx R).card + 2 := by
      have := h1.trans (Nat.add_le_add_left (hpathcard i) _)
      exact_mod_cast this
    linarith [hsparse i v hv]

end Integral

end Connector

end Lovasz
