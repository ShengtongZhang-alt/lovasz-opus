/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Connecting.Basic

/-!
# State cuts in the bipartite case

DAG node `E6.bip` of `docs/BLUEPRINT.md` (Sections 6.2–6.3 of the paper, bipartite case).
-/

universe u

noncomputable section

namespace Lovasz

open Finset Classical

namespace Connector

section CutCount

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
/-- A connected bipartite Cayley graph has a character `χ : G → C₂` (written in `Bool`, with
`xor` as the group law) taking the value `1` on every label: the lifts `(s, 1)` generate a proper
subgroup of `G × C₂` projecting onto `G`, which is therefore the graph of such a character. -/
lemma exists_char (S : Finset G) (hconn : (cayleyGraph S).Connected) (hbip : ¬ IsNonbip S) :
    ∃ χ : G → Bool, (∀ a b, χ (a * b) = (χ a ^^ χ b)) ∧ ∀ s ∈ S, χ s = true := by
  set H := Subgroup.closure (liftSet S) with hH
  let e : Bool → Multiplicative (ZMod 2) := fun b => if b then Multiplicative.ofAdd 1 else 1
  have he_mul : ∀ a b, e (a ^^ b) = e a * e b := by
    intro a b; cases a <;> cases b <;> decide
  have he_inj : ∀ a b, e a = e b → a = b := by
    intro a b; cases a <;> cases b <;> decide
  have h2 : ∀ c c' : Multiplicative (ZMod 2), c ≠ c' → c = c' * Multiplicative.ofAdd 1 := by
    decide
  have h3 : ∀ c c' : Multiplicative (ZMod 2), c ≠ c' → c⁻¹ * c' = Multiplicative.ofAdd 1 := by
    decide
  have h4 : ∀ c : Multiplicative (ZMod 2), c ≠ Multiplicative.ofAdd 1 → c = 1 := by
    decide
  have hfst : ∀ g, ∃ c, (g, c) ∈ H := by
    intro g
    have hmap : Subgroup.map (MonoidHom.fst G (Multiplicative (ZMod 2))) H = ⊤ := by
      rw [hH, MonoidHom.map_closure]
      have : (MonoidHom.fst G (Multiplicative (ZMod 2))) '' liftSet S = (S : Set G) := by
        ext x; simp [liftSet]
      rw [this]
      exact closure_eq_top_of_connected S hconn
    have : g ∈ Subgroup.map (MonoidHom.fst _ _) H := hmap ▸ Subgroup.mem_top g
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 this
    exact ⟨p.2, by simpa using hp⟩
  have hnot : ((1 : G), Multiplicative.ofAdd (1 : ZMod 2)) ∉ H := by
    intro h1
    apply hbip
    rw [IsNonbip, ← hH, eq_top_iff]
    rintro ⟨g, c⟩ -
    obtain ⟨c', hc'⟩ := hfst g
    by_cases hcc : c = c'
    · subst hcc; exact hc'
    · rw [h2 c c' hcc]
      have := H.mul_mem hc' h1
      simpa using this
  have huniq : ∀ g c c', (g, c) ∈ H → (g, c') ∈ H → c = c' := by
    intro g c c' h h'
    by_contra hne
    apply hnot
    have := H.mul_mem (H.inv_mem h) h'
    have e1 : ((g, c)⁻¹ * (g, c') : G × Multiplicative (ZMod 2)) =
        (1, Multiplicative.ofAdd 1) := by
      refine Prod.ext ?_ ?_
      · simp
      · simp only [Prod.snd_mul, Prod.snd_inv]
        exact h3 c c' hne
    convert this using 1
    exact e1.symm
  let χ : G → Bool := fun g => decide ((g, Multiplicative.ofAdd (1 : ZMod 2)) ∈ H)
  have hmem : ∀ g, (g, e (χ g)) ∈ H := by
    intro g
    by_cases h : (g, Multiplicative.ofAdd (1 : ZMod 2)) ∈ H
    · simp [χ, e, h]
    · obtain ⟨c, hc⟩ := hfst g
      have hc1 : c = 1 := h4 c (fun hc' => h (hc' ▸ hc))
      subst hc1
      simpa [χ, e, h] using hc
  refine ⟨χ, fun a b => ?_, fun s hs => ?_⟩
  · apply he_inj
    rw [he_mul]
    exact huniq (a * b) _ _ (hmem (a * b)) (H.mul_mem (hmem a) (hmem b))
  · have : (s, Multiplicative.ofAdd (1 : ZMod 2)) ∈ H := Subgroup.subset_closure ⟨s, hs, rfl⟩
    simp [χ, this]


/-- In a connected template, the side of a vertex is determined by the character: there is
`ε₀` with `a ∈ A⁺ ↔ ε₀ + χ(a) = 1` for every `a ∈ A⁺ ∪ A⁻`. -/
lemma template_sign {S T Ap Am : Finset G} {cT : ℝ} (hT : IsTemplate S T Ap Am cT)
    (χ : G → Bool) (hχ : ∀ a b, χ (a * b) = (χ a ^^ χ b)) (hχS : ∀ s ∈ S, χ s = true) :
    ∃ ε₀ : Bool, ∀ a ∈ Ap ∪ Am, (a ∈ Ap ↔ (ε₀ ^^ χ a) = true) := by
  obtain ⟨⟨a₀, ha₀⟩⟩ := hT.connected.nonempty
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀, ε₀ = (decide (a₀ ∈ Ap) ^^ χ a₀) := ⟨_, rfl⟩
  refine ⟨ε₀, ?_⟩
  have hstep : ∀ c d : G, (templateGraph T Ap Am).Adj c d →
      decide (d ∈ Ap) = !decide (c ∈ Ap) ∧ χ d = !χ c := by
    intro c d h
    obtain ⟨-, hside, hlab⟩ := h
    constructor
    · rcases hside with ⟨hc, hd⟩ | ⟨hc, hd⟩
      · have : d ∉ Ap := fun h' => disjoint_left.1 hT.disjoint h' hd
        simp [hc, this]
      · have : c ∉ Ap := fun h' => disjoint_left.1 hT.disjoint h' hc
        simp [hd, this]
    · rcases hlab with h' | h'
      · have := hχ c (c⁻¹ * d)
        rw [mul_inv_cancel_left, hχS _ (hT.sub h'), Bool.xor_true] at this
        exact this
      · have := hχ d (d⁻¹ * c)
        rw [mul_inv_cancel_left, hχS _ (hT.sub h'), Bool.xor_true] at this
        rw [this, Bool.not_not]
  have key : ∀ w : ↥((Ap ∪ Am : Finset G) : Set G),
      ((templateGraph T Ap Am).induce ((Ap ∪ Am : Finset G) : Set G)).Reachable ⟨a₀, ha₀⟩ w →
        decide (w.1 ∈ Ap) = (ε₀ ^^ χ w.1) := by
    intro w hw
    rw [SimpleGraph.reachable_iff_reflTransGen] at hw
    induction hw with
    | refl => rw [hε₀, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    | tail _ hadj ih =>
      rename_i c d _
      obtain ⟨h1, h2⟩ := hstep c.1 d.1 hadj
      rw [h1, h2, ih, Bool.xor_not]
  intro a ha
  rw [← key ⟨a, ha⟩ (hT.connected.preconnected _ _), decide_eq_true_iff]

omit [Group G] [Fintype G] [DecidableEq G] in
/-- The twin arcs of `e` crossing the state set `J`, arc by arc. -/
lemma arcs_eq {t : ℕ} (π : G → Fin t) (sg : G → Bool) (J : Finset (Fin t × Bool)) (e : Sym2 G) :
    outArcs π sg J e + inArcs π sg J e =
      (if (arcTail π sg e false ∈ J) ≠ (arcHead π sg e false ∈ J) then 1 else 0) +
        (if (arcTail π sg e true ∈ J) ≠ (arcHead π sg e true ∈ J) then 1 else 0) := by
  unfold outArcs inArcs
  simp only [card_filter, Fintype.sum_bool]
  by_cases h1 : arcTail π sg e true ∈ J <;> by_cases h2 : arcHead π sg e true ∈ J <;>
    by_cases h3 : arcTail π sg e false ∈ J <;> by_cases h4 : arcHead π sg e false ∈ J <;>
    simp [h1, h2, h3, h4]

/-- **State cuts in the bipartite case (§6.3).** If `X = Cay(G, S)` is bipartite, the two-state
graph of `Y` splits into two copies of the ordinary contraction (one oriented from the global
positive side to the negative side, one reversed). Hence, if the ordinary contraction has minimum
cut at least `µ ≥ 6`, every state cut has `0` or at least `µ` arcs, and the state cuts with fewer
than `(j+1)µ` arcs number at most `(4 (t + |E(Y)|))^{16(j+1)}`.

Proof sketch: `¬ IsNonbip S` gives a character `χ : G → C₂` with `χ(s) = 1` on `S`; `W = ∅` since
`χ` maps `⟨T⟩` onto `C₂`, so `u` is even. By connectivity of the template, the local sign of `v`
in its part is `ε_{π v} + χ(v)`. Hence the arc of an edge `xy` with tail at `x` joins
`π x, π y` inside the component `χ(x)` of the state graph, where component `c` consists of the
states `(i, c + ε_i)`. Writing `J_c = {i : (i, c + ε_i) ∈ J}`, the state cut of `J` is the sum of
the two ordinary part cuts of `J₀, J₁`, and `J ↦ (J₀, J₁)` is injective; apply (6.4) to the
ordinary contraction. -/
theorem bip_state_cuts (S T Ap Am S₀ : Finset G) (cT : ℝ) (𝒜 : Allocation G)
    (lam D σ η ω cN CN μ : ℝ) (π : G → Fin 𝒜.t) (hS : IsConnectionSet S)
    (hconn : (cayleyGraph S).Connected) (hbip : ¬ IsNonbip S)
    (hT : IsTemplate S T Ap Am cT) (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN)
    (hπ : ∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v)) (hS₀ : S₀ ⊆ S) (hμ : 6 ≤ μ)
    (hcut : ∀ I : Finset (Fin 𝒜.t), I.Nonempty → I ≠ univ →
      μ ≤ ((conY S₀ 𝒜.W).edgeFinset.filter (PartCross π I)).card) :
    (∀ J : Finset (Fin 𝒜.t × Bool),
      cutCnt π (sgnOf 𝒜 Ap π) J (conY S₀ 𝒜.W).edgeFinset = 0 ∨
        μ ≤ cutCnt π (sgnOf 𝒜 Ap π) J (conY S₀ 𝒜.W).edgeFinset) ∧
    ∀ j : ℕ, (((univ : Finset (Finset (Fin 𝒜.t × Bool))).filter fun J =>
      (cutCnt π (sgnOf 𝒜 Ap π) J (conY S₀ 𝒜.W).edgeFinset : ℝ) < (j + 1) * μ).card : ℝ) ≤
        (4 * (𝒜.t + (conY S₀ 𝒜.W).edgeFinset.card)) ^ (16 * (j + 1)) := by
  obtain ⟨χ, hχ, hχS⟩ := exists_char S hconn hbip
  obtain ⟨ε₀, hε₀⟩ := template_sign hT χ hχ hχS
  set E := (conY S₀ 𝒜.W).edgeFinset with hE
  let ε : Fin 𝒜.t → Bool := fun i => (ε₀ ^^ χ (𝒜.g i)⁻¹)
  have hsg : ∀ v, v ∉ 𝒜.W → sgnOf 𝒜 Ap π v = (ε (π v) ^^ χ v) := by
    intro v hv
    have ha := mem_copyVerts.1 (hgood.part_sub _ (hπ v hv))
    rw [Bool.eq_iff_iff]
    unfold sgnOf
    simp only [decide_eq_true_eq]
    rw [hε₀ _ ha, hχ, Bool.xor_assoc]
  have hedge : ∀ e ∈ E, e.out.1 ∉ 𝒜.W ∧ e.out.2 ∉ 𝒜.W ∧ χ e.out.2 = !χ e.out.1 := by
    intro e he
    rw [hE, SimpleGraph.mem_edgeFinset, ← mk_out e, SimpleGraph.mem_edgeSet] at he
    obtain ⟨hadj, hx, hy⟩ := he
    refine ⟨hx, hy, ?_⟩
    rw [SimpleGraph.mulCayley_adj] at hadj
    rcases hadj.2 with h | h
    · have := hχ e.out.1 (e.out.1⁻¹ * e.out.2)
      rw [mul_inv_cancel_left, hχS _ (hS₀ h), Bool.xor_true] at this
      exact this
    · have := hχ e.out.2 (e.out.2⁻¹ * e.out.1)
      rw [mul_inv_cancel_left, hχS _ (hS₀ h), Bool.xor_true] at this
      rw [this, Bool.not_not]
  let Jc : Finset (Fin 𝒜.t × Bool) → Bool → Finset (Fin 𝒜.t) :=
    fun J c => univ.filter fun i => (i, (c ^^ ε i)) ∈ J
  have hsplit : ∀ J, cutCnt π (sgnOf 𝒜 Ap π) J E =
      (E.filter (PartCross π (Jc J false))).card + (E.filter (PartCross π (Jc J true))).card := by
    intro J
    have key : ∀ e ∈ E, outArcs π (sgnOf 𝒜 Ap π) J e + inArcs π (sgnOf 𝒜 Ap π) J e =
        (if PartCross π (Jc J false) e then 1 else 0) +
          (if PartCross π (Jc J true) e then 1 else 0) := by
      intro e he
      obtain ⟨hx, hy, hχxy⟩ := hedge e he
      rw [arcs_eq]
      simp only [arcTail, arcHead, PartCross, Jc, mem_filter, mem_univ, true_and]
      simp only [hsg _ hx, hsg _ hy, hχxy]
      generalize χ e.out.1 = c
      generalize π e.out.1 = p
      generalize π e.out.2 = q
      generalize ε p = a
      generalize ε q = b
      cases a <;> cases b <;> cases c <;>
        by_cases h1 : (p, true) ∈ J <;> by_cases h2 : (p, false) ∈ J <;>
        by_cases h3 : (q, true) ∈ J <;> by_cases h4 : (q, false) ∈ J <;>
        simp [h1, h2, h3, h4]
    unfold cutCnt outCnt inCnt
    rw [← sum_add_distrib, sum_congr rfl key, sum_add_distrib, ← card_filter, ← card_filter]
  have hpart : ∀ I : Finset (Fin 𝒜.t), (E.filter (PartCross π I)).card = 0 ∨
      μ ≤ (E.filter (PartCross π I)).card := by
    intro I
    by_cases h1 : I.Nonempty
    · by_cases h2 : I = univ
      · left
        subst h2
        simp [PartCross]
      · exact Or.inr (hcut I h1 h2)
    · left
      rw [not_nonempty_iff_eq_empty] at h1
      subst h1
      simp [PartCross]
  refine ⟨fun J => ?_, fun j => ?_⟩
  · rw [hsplit J]
    have hc0 : (0 : ℝ) ≤ (E.filter (PartCross π (Jc J false))).card := Nat.cast_nonneg _
    have hc1 : (0 : ℝ) ≤ (E.filter (PartCross π (Jc J true))).card := Nat.cast_nonneg _
    rcases hpart (Jc J false) with h0 | h0 <;> rcases hpart (Jc J true) with h1 | h1
    · left
      omega
    · right
      push_cast
      linarith
    · right
      push_cast
      linarith
    · right
      push_cast
      linarith
  · have : Nonempty (Fin 𝒜.t) := ⟨π 1⟩
    set A := (univ : Finset (Finset (Fin 𝒜.t))).filter fun I =>
      ((E.filter (PartCross π I)).card : ℝ) < (j + 1) * μ with hA
    have hsq : ((univ : Finset (Finset (Fin 𝒜.t × Bool))).filter fun J =>
        (cutCnt π (sgnOf 𝒜 Ap π) J E : ℝ) < (j + 1) * μ).card ≤ (A ×ˢ A).card := by
      refine card_le_card_of_injOn (fun J => (Jc J false, Jc J true)) ?_ ?_
      · intro J hJ
        rw [mem_coe, mem_filter, hsplit J] at hJ
        push_cast at hJ
        have hc0 : (0 : ℝ) ≤ (E.filter (PartCross π (Jc J false))).card := Nat.cast_nonneg _
        have hc1 : (0 : ℝ) ≤ (E.filter (PartCross π (Jc J true))).card := Nat.cast_nonneg _
        simp only [mem_coe, mem_product, hA, mem_filter, mem_univ, true_and]
        constructor <;> linarith
      · intro J _ J' _ hJJ
        simp only [Prod.mk.injEq] at hJJ
        obtain ⟨h0, h1⟩ := hJJ
        ext ⟨i, b⟩
        have key : ∀ K : Finset (Fin 𝒜.t × Bool), (i, b) ∈ K ↔ i ∈ Jc K (b ^^ ε i) := by
          intro K
          simp [Jc]
        rw [key J, key J']
        generalize (b ^^ ε i) = c
        cases c
        · rw [h0]
        · rw [h1]
    set μ' : ℕ := ⌊μ⌋₊ with hμ'
    have hμ0 : 0 ≤ μ := by linarith
    have hμ'6 : 6 ≤ μ' := Nat.le_floor (by exact_mod_cast hμ)
    have hμ'le : (μ' : ℝ) ≤ μ := Nat.floor_le hμ0
    have hμ'gt : μ < μ' + 1 := Nat.lt_floor_add_one μ
    let ends : {e // e ∈ E} → Fin 𝒜.t × Fin 𝒜.t := fun e => (π e.1.out.1, π e.1.out.2)
    have hcross : ∀ U : Finset (Fin 𝒜.t),
        (univ.filter fun e => ((ends e).1 ∈ U) ≠ ((ends e).2 ∈ U)).card =
          (E.filter (PartCross π U)).card := by
      intro U
      rw [card_eq_sum_ones, sum_filter, card_eq_sum_ones, sum_filter, ← Finset.sum_coe_sort E]
      refine Fintype.sum_congr _ _ fun e => ?_
      simp only [ends, PartCross]
      by_cases h1 : π e.1.out.1 ∈ U <;> by_cases h2 : π e.1.out.2 ∈ U <;> simp [h1, h2]
    have hcut' : ∀ U : Finset (Fin 𝒜.t), U.Nonempty → U ≠ univ →
        μ' ≤ (univ.filter fun e => ((ends e).1 ∈ U) ≠ ((ends e).2 ∈ U)).card := by
      intro U hU hU'
      rw [hcross U]
      have := hcut U hU hU'
      exact_mod_cast hμ'le.trans this
    have hcc := cut_count ends μ' hμ'6 hcut' (2 * j + 1)
    have hsub : A ⊆ (univ : Finset (Finset (Fin 𝒜.t))).filter fun U =>
        (univ.filter fun e => ((ends e).1 ∈ U) ≠ ((ends e).2 ∈ U)).card <
          (2 * j + 1 + 1) * μ' := by
      intro I hI
      rw [hA, mem_filter] at hI
      rw [mem_filter]
      refine ⟨hI.1, ?_⟩
      rw [hcross I]
      have h1 : (j + 1 : ℝ) * μ ≤ (2 * j + 1 + 1) * μ' := by
        have : μ ≤ 2 * μ' := by
          have : (6 : ℝ) ≤ μ' := by exact_mod_cast hμ'6
          linarith
        have hj : (0 : ℝ) ≤ j + 1 := by positivity
        nlinarith
      have h2 : ((E.filter (PartCross π I)).card : ℝ) < (2 * j + 1 + 1) * μ' :=
        lt_of_lt_of_le hI.2 h1
      exact_mod_cast h2
    have hcardV : Fintype.card (Fin 𝒜.t) = 𝒜.t := Fintype.card_fin _
    have hcardE : Fintype.card {e // e ∈ E} = E.card := Fintype.card_coe E
    rw [hcardV, hcardE] at hcc
    have hAle := (card_le_card hsub).trans hcc
    have hfin : (A ×ˢ A).card ≤ (4 * (𝒜.t + E.card)) ^ (16 * (j + 1)) := by
      rw [card_product]
      calc A.card * A.card ≤ (2 * (𝒜.t + E.card)) ^ (4 * (2 * j + 1 + 1)) *
            (2 * (𝒜.t + E.card)) ^ (4 * (2 * j + 1 + 1)) := Nat.mul_le_mul hAle hAle
        _ = (2 * (𝒜.t + E.card)) ^ (16 * (j + 1)) := by rw [← pow_add]; ring_nf
        _ ≤ (4 * (𝒜.t + E.card)) ^ (16 * (j + 1)) := Nat.pow_le_pow_left (by omega) _
    exact_mod_cast hsq.trans hfin

end CutCount

end Connector

end Lovasz
