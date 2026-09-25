/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Absorption.InitialPartition
import Lovasz.Absorption.RouterStep
import Lovasz.Absorption.FreshLayers

/-!
# Theorem 3.2: local absorption

DAG node `T3.2` of `docs/BLUEPRINT.md`: Section 3.3 of the paper. The shared definitions and
the proved steps (`T3.2a`, `T3.2e`, `T3.2g`) are in `Lovasz/Absorption/Basic.lean`; the steps
`T3.2b`, `T3.2c`, `T3.2f` and Lemma 2.4 each have their own file in `Lovasz/Absorption/`. This
file contains the deterministic bookkeeping `absorb_of_partition` and the theorem.
-/

universe u

namespace Lovasz

open Finset

namespace LocalAbsorption

/-- **The deterministic part of §3.3.** Given the initial partition, the router, attachments,
divisibility and fresh-layer steps (as hypotheses `RouterSpec`, `ConnSpec`, `DivSpec`,
`FreshSpec`), and the properties of `H₀ = H - E`, the path system required by
`IsMatchingAbsorbing` exists for the matching `J`. -/
theorem absorb_of_partition {V : Type u} [Fintype V] [DecidableEq V]
    {ω εR c₇ C₇ c34 C34 cdfs cF δ κ K CF c C : ℝ}
    (hRouter : RouterSpec.{u} ω εR c₇ C₇) (hConn : ConnSpec.{u} (1 / 2) c34 C34)
    (hDiv : DivSpec.{u} cdfs) (hFresh : FreshSpec.{u} ω cF δ κ K CF)
    {H : WGraph V} {col : V → Bool} {N ℓ : ℕ} {η D σ L g η₀ : ℝ} {E : Finset V}
    {J : SimpleGraph V}
    (hyp : LocalAbsorptionHyp ω c C H col N ℓ η D σ L g E) (hC : 0 < C)
    (hJ : IsPerfectMatchingOn J ↑E)
    (h₀deg : (H.induce (univ \ E)).DegNear D η₀) (h₀gap : (H.induce (univ \ E)).HasGap (σ / 2))
    (hη₀ : 0 ≤ η₀) (hη₀' : η₀ ≤ cF * (σ / 2))
    (Pt : InitPartition εR c₇ C₇ (c34 / 4) cdfs δ κ K CF H col E J (N - ℓ) D σ L g) :
    ∃ P : SimpleGraph V, P ≤ H.supp ∧ (∀ x ∈ (E : Set V), (P.neighborSet x).ncard = 1) ∧
      (∀ x ∉ (E : Set V), (P.neighborSet x).ncard = 2) ∧ (P ⊔ J).Connected := by
  classical
  have hbip := hyp.bipartite
  have hσ := hyp.sigma_pos
  have hm1 := Pt.one_le_m
  have hD : 0 < D := by
    have h1 := hyp.deg_large
    have hL : 0 < L := by linarith [hyp.ten_le]
    have hg : 0 < g := by linarith [hyp.four_le]
    have : 0 < C * σ ^ (-(9 / 2 : ℝ)) * L ^ 2 * g := by
      have := Real.rpow_pos_of_pos hσ (-(9 / 2 : ℝ))
      positivity
    linarith
  -- labels
  have hEl : ∀ x, x ∈ E ↔ Pt.lab x = Cell.ends := fun x => (Pt.lab_ends x).symm
  have hportlab : ∀ x ∈ E, Pt.lab (Pt.port x) = Cell.lu ∨ Pt.lab (Pt.port x) = Cell.lv := by
    intro x hx
    cases h : Pt.tail x
    · exact Or.inr (Pt.port_head x hx h).1
    · exact Or.inl (Pt.port_tail x hx h).1
  have hportE : ∀ x ∈ E, Pt.port x ∉ E := by
    intro x hx h
    rw [hEl] at h
    rcases hportlab x hx with h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)
  have hportimg : ∀ v ∈ E.image Pt.port, Pt.lab v = Cell.lu ∨ Pt.lab v = Cell.lv := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    exact hportlab x hx
  -- the router (`T3.2c`)
  have hcard2 : ∀ c, (c = Cell.inp ∨ c = Cell.out ∨ c = Cell.lu ∨ c = Cell.lv) →
      (cellSet Pt.lab c).card = 2 * Pt.m := fun c hc => by
    rw [card_eq_ccount col, ccount, ccount, Pt.block_card c true hc, Pt.block_card c false hc]
    ring
  obtain ⟨AS, hIOAS, hASsub, hASR⟩ := hRouter H col (cellSet Pt.lab Cell.cyc)
    (cellSet Pt.lab Cell.rtr) (cellSet Pt.lab Cell.inp) (cellSet Pt.lab Cell.out) (2 * Pt.m)
    Pt.DC Pt.ΔQ Pt.σQ L g hbip hyp.weights (cellSet_disjoint _ (by decide))
    (cellSet_disjoint _ (by decide)) (cellSet_disjoint _ (by decide))
    (cellSet_disjoint _ (by decide)) (cellSet_disjoint _ (by decide))
    (cellSet_disjoint _ (by decide)) (hcard2 _ (by simp)) (hcard2 _ (by simp)) (by omega)
    Pt.cyc_deg Pt.cyc_DC Pt.cyc_girth (by push_cast; exact Pt.cyc_many) Pt.rtr_pos Pt.rtr_deg
    Pt.rtr_gap Pt.rtr_σ.1 Pt.rtr_σ.2 Pt.rtr_log
    (fun x hx => Pt.rtr_ends x (by simp only [Finset.mem_union, mem_cellSet] at hx; tauto))
    Pt.rtr_sparse
  have hASlab : ∀ v ∈ AS, Pt.lab v = Cell.cyc ∨ Pt.lab v = Cell.rtr ∨ Pt.lab v = Cell.inp ∨
      Pt.lab v = Cell.out := by
    intro v hv
    have := hASsub hv
    simp only [Finset.mem_union, mem_cellSet] at this
    tauto
  -- the attachments (`T3.2d`, Lemma 3.4 in `R₁`)
  have hpairs : ∀ j : E, (j : V) ∉ cellSet Pt.lab Cell.att ∧
      Pt.port j ∉ cellSet Pt.lab Cell.att ∧ (j : V) ≠ Pt.port j := by
    intro j
    have h1 := (hEl j).1 j.2
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [mem_cellSet, h1] at h; exact absurd h (by decide)
    · rw [mem_cellSet] at h
      rcases hportlab j j.2 with h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)
    · exact hportE j j.2 (by rw [← h]; exact j.2)
  have hmult : ∀ x, (univ.filter fun j : E => (j : V) = x ∨ Pt.port j = x).card ≤ 10 := by
    intro x
    have h1 : (univ.filter fun j : E => (j : V) = x).card ≤ 1 :=
      Finset.card_le_one.2 fun a ha b hb => Subtype.ext (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb; rw [ha, hb])
    have h2 : (univ.filter fun j : E => Pt.port j = x).card ≤ 1 :=
      Finset.card_le_one.2 fun a ha b hb => Subtype.ext (Pt.port_inj a.2 b.2 (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb; rw [ha, hb]))
    calc _ ≤ (univ.filter fun j : E => (j : V) = x).card +
          (univ.filter fun j : E => Pt.port j = x).card := by
          rw [Finset.filter_or]; exact Finset.card_union_le _ _
      _ ≤ 10 := by omega
  have hends : ∀ j : E, 1 / 4 * Pt.Δ₁ ≤ H.degOn j (cellSet Pt.lab Cell.att) ∧
      1 / 4 * Pt.Δ₁ ≤ H.degOn (Pt.port j) (cellSet Pt.lab Cell.att) :=
    fun j => ⟨Pt.att_ends j (Finset.mem_union_left _ j.2),
      Pt.att_ends _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ j.2))⟩
  have hsparse : ∀ v ∈ cellSet Pt.lab Cell.att, H.degOn v (univ.image (fun j : E => (j : V)) ∪
      univ.image (fun j : E => Pt.port j)) ≤ c34 * (1 / 4) * Pt.σ₁ ^ (3 / 2 : ℝ) * Pt.Δ₁ / L := by
    intro v hv
    refine (degOn_mono H v ?_).trans ((Pt.att_sparse v hv).trans (le_of_eq (by ring)))
    intro y hy
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hy ⊢
    rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl j.2
    · exact Or.inr ⟨j, j.2, rfl⟩
  obtain ⟨patt, hpattP, -, hpattR, hpattD⟩ := hConn H (cellSet Pt.lab Cell.att) Pt.Δ₁ Pt.σ₁ L
    (1 / 4) (fun j : E => (j : V)) (fun j : E => Pt.port j) Pt.att_pos Pt.att_deg Pt.att_gap
    Pt.att_σ.1 Pt.att_σ.2 Pt.att_log (by norm_num) (by norm_num) hpairs hmult hends hsparse
  have hattv : ∀ (x : E), ∀ v ∈ (patt x).support, v = x ∨ v = Pt.port x ∨
      Pt.lab v = Cell.att := by
    intro x v hv
    by_cases h1 : v = x
    · exact Or.inl h1
    by_cases h2 : v = Pt.port x
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (mem_cellSet.1 (hpattR x v hv h1 h2)))
  have hattD : ∀ x y : E, x ≠ y → ∀ v ∈ (patt x).support, v ∉ (patt y).support := by
    intro x y hxy v hvx hvy
    rcases hattv x v hvx with h1 | h1 | h1 <;> rcases hattv y v hvy with h2 | h2 | h2
    · exact hxy (Subtype.ext (h1.symm.trans h2))
    · exact hportE y y.2 (by rw [← h2, h1]; exact x.2)
    · rw [h1, (hEl x).1 x.2] at h2; exact absurd h2 (by decide)
    · exact hportE x x.2 (by rw [← h1, h2]; exact y.2)
    · exact hxy (Subtype.ext (Pt.port_inj x.2 y.2 (h1.symm.trans h2)))
    · rw [h1] at h2
      rcases hportlab x x.2 with h' | h' <;> rw [h'] at h2 <;> exact absurd h2 (by decide)
    · rw [h2, (hEl y).1 y.2] at h1; exact absurd h1 (by decide)
    · rw [h2] at h1
      rcases hportlab y y.2 with h' | h' <;> rw [h'] at h1 <;> exact absurd h1 (by decide)
    · exact hpattD x y hxy v (mem_cellSet.2 h1) hvx hvy
  obtain ⟨Rem₁, hRem₁⟩ : ∃ X : Finset V,
      X = (univ.filter fun v => ∃ x : E, v ∈ (patt x).support) \ E.image Pt.port := ⟨_, rfl⟩
  have hRem₁lab : ∀ v ∈ Rem₁, Pt.lab v = Cell.ends ∨ Pt.lab v = Cell.att := by
    intro v hv
    rw [hRem₁, Finset.mem_sdiff, Finset.mem_filter] at hv
    obtain ⟨⟨-, x, hx⟩, hvp⟩ := hv
    rcases hattv x v hx with h | h | h
    · exact Or.inl (h ▸ (hEl x).1 x.2)
    · exact absurd (Finset.mem_image.2 ⟨(x : V), x.2, h.symm⟩) hvp
    · exact Or.inr h
  have hERem₁ : E ⊆ Rem₁ := by
    intro x hx
    rw [hRem₁, Finset.mem_sdiff, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, ⟨x, hx⟩, (patt ⟨x, hx⟩).start_mem_support⟩, fun h => ?_⟩
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.1 h
    exact hportE y hy (hxy ▸ hx)
  -- the divisibility residue and path (`T3.2e`)
  obtain ⟨Out, hOut⟩ : ∃ X : Finset V, X = univ \ (Rem₁ ∪ AS) := ⟨_, rfl⟩
  obtain ⟨n', hn'⟩ : ∃ n : ℕ, n = ccount col Out true := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = (n' - 1) % Pt.m + 1 := ⟨_, rfl⟩
  have hrm : r ≤ Pt.m := by
    rw [hr]; have := Nat.mod_lt (n' - 1) (by omega : 0 < Pt.m); omega
  have hr1 : 1 ≤ r := by omega
  obtain ⟨zA, zB, pd, hpd, hpdlen, hzAcol, hzBcol, hpdZ⟩ := hDiv H col (cellSet Pt.lab Cell.div)
    Pt.DZ Pt.σZ r hbip Pt.div_pos Pt.div_deg Pt.div_gap Pt.div_σ.1 Pt.div_σ.2
    (by have h1 := Pt.div_long; have h2 : (r : ℝ) ≤ Pt.m := by exact_mod_cast hrm
        linarith)
  have hzAlab : Pt.lab zA = Cell.div := mem_cellSet.1 (hpdZ zA pd.start_mem_support)
  have hzBlab : Pt.lab zB = Cell.div := mem_cellSet.1 (hpdZ zB pd.end_mem_support)
  have hzAB : zA ≠ zB := fun h => by rw [h, hzBcol] at hzAcol; exact absurd hzAcol (by decide)
  have hattpd : ∀ x : E, ∀ v ∈ (patt x).support, v ∉ pd.support := by
    intro x v hv hv'
    have h1 := mem_cellSet.1 (hpdZ v hv')
    rcases hattv x v hv with h | h | h
    · rw [h, (hEl x).1 x.2] at h1; exact absurd h1 (by decide)
    · rw [h] at h1
      rcases hportlab x x.2 with h' | h' <;> rw [h'] at h1 <;> exact absurd h1 (by decide)
    · rw [h] at h1; exact absurd h1 (by decide)
  have hzAE : zA ∉ E := fun h => by rw [hEl, hzAlab] at h; exact absurd h (by decide)
  have hzBE : zB ∉ E := fun h => by rw [hEl, hzBlab] at h; exact absurd h (by decide)
  -- the remaining sets
  obtain ⟨dI, hdI⟩ : ∃ X : Finset V, X = pd.support.toFinset \ {zA, zB} := ⟨_, rfl⟩
  have hdIlab : ∀ v ∈ dI, Pt.lab v = Cell.div ∧ v ≠ zA ∧ v ≠ zB := by
    intro v hv
    rw [hdI, Finset.mem_sdiff, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton,
      not_or] at hv
    exact ⟨mem_cellSet.1 (hpdZ v hv.1), hv.2⟩
  obtain ⟨Rem, hRemdef⟩ : ∃ X : Finset V, X = Rem₁ ∪ dI := ⟨_, rfl⟩
  obtain ⟨U', hU'⟩ : ∃ X : Finset V, X = insert zA ((cellSet Pt.lab Cell.lu).erase Pt.dA) :=
    ⟨_, rfl⟩
  obtain ⟨W', hW'⟩ : ∃ X : Finset V, X = insert zB ((cellSet Pt.lab Cell.lv).erase Pt.dB) :=
    ⟨_, rfl⟩
  have hU'mem : ∀ v, v ∈ U' ↔ v = zA ∨ (v ≠ Pt.dA ∧ Pt.lab v = Cell.lu) := by
    intro v; rw [hU', Finset.mem_insert, Finset.mem_erase, mem_cellSet]
  have hW'mem : ∀ v, v ∈ W' ↔ v = zB ∨ (v ≠ Pt.dB ∧ Pt.lab v = Cell.lv) := by
    intro v; rw [hW', Finset.mem_insert, Finset.mem_erase, mem_cellSet]
  obtain ⟨P, hP⟩ : ∃ X : Finset V, X = Out \ (dI ∪ U' ∪ W') := ⟨_, rfl⟩
  obtain ⟨Fend, hFend⟩ : ∃ X : Finset V, X = E.image Pt.port ∪ {zA, zB} := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ G' : SimpleGraph V, G' = SimpleGraph.fromEdgeSet
      ({e | ∃ x y, J.Adj x y ∧ e = s(Pt.port x, Pt.port y)} ∪ {s(zA, zB)}) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ G' : SimpleGraph V, G' = SimpleGraph.fromEdgeSet
      ({e | ∃ x : E, e ∈ (patt x).edges} ∪ {e | e ∈ pd.edges}) := ⟨_, rfl⟩
  have hRemiff : ∀ v, v ∈ Rem ↔
      ((∃ x : E, v ∈ (patt x).support) ∨ v ∈ pd.support) ∧ v ∉ Fend := by
    intro v
    rw [hRemdef, hRem₁, hdI, hFend]
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨⟨x, hx⟩, hvp⟩ | ⟨hv, hvz⟩)
      · refine ⟨Or.inl ⟨x, hx⟩, ?_⟩
        rintro (h | h | h)
        · exact hvp h
        · exact hattpd x v hx (by rw [h]; exact pd.start_mem_support)
        · exact hattpd x v hx (by rw [h]; exact pd.end_mem_support)
      · refine ⟨Or.inr hv, ?_⟩
        rintro (h | h)
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
          exact hattpd ⟨y, hy⟩ _ (patt ⟨y, hy⟩).end_mem_support hv
        · exact hvz h
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl ⟨h1, fun h => h2 (Or.inl h)⟩
      · exact Or.inr ⟨h1, fun h => h2 (Or.inr h)⟩
  obtain ⟨hFend', hFm, hXG, hXps, hXrem, hERem, hFreach, hRemreach⟩ := expansion E Pt.port zA zB
    patt pd F X Fend Rem hF hX hFend hRemiff hJ hpattP hpd (by omega) (fun x => (hpairs x).2.2)
    hattD hattpd hportE hzAE hzBE
  -- the special transition `U–V`: the formal matching `J'` and the divisibility edge
  obtain ⟨FU, hFU⟩ : ∃ X : Finset V,
      X = (E.filter fun x => Pt.tail x = true).image Pt.port ∪ {zA} := ⟨_, rfl⟩
  obtain ⟨FW, hFW⟩ : ∃ X : Finset V,
      X = (E.filter fun x => Pt.tail x = false).image Pt.port ∪ {zB} := ⟨_, rfl⟩
  have hFUmem : ∀ v, v ∈ FU ↔ (∃ x, (x ∈ E ∧ Pt.tail x = true) ∧ Pt.port x = v) ∨ v = zA := by
    intro v; rw [hFU, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    simp only [Finset.mem_filter]
  have hFWmem : ∀ v, v ∈ FW ↔ (∃ x, (x ∈ E ∧ Pt.tail x = false) ∧ Pt.port x = v) ∨ v = zB := by
    intro v; rw [hFW, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    simp only [Finset.mem_filter]
  have hFUsub : FU ⊆ U' := by
    intro v hv
    rw [hFUmem] at hv; rw [hU'mem]
    rcases hv with ⟨x, ⟨hx, ht⟩, rfl⟩ | rfl
    · exact Or.inr ⟨(Pt.port_tail x hx ht).2, (Pt.port_tail x hx ht).1⟩
    · exact Or.inl rfl
  have hFWsub : FW ⊆ W' := by
    intro v hv
    rw [hFWmem] at hv; rw [hW'mem]
    rcases hv with ⟨x, ⟨hx, ht⟩, rfl⟩ | rfl
    · exact Or.inr ⟨(Pt.port_head x hx ht).2, (Pt.port_head x hx ht).1⟩
    · exact Or.inl rfl
  have hU'W' : Disjoint U' W' := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    rw [hU'mem] at h1; rw [hW'mem] at h2
    rcases h1 with rfl | ⟨-, h1⟩ <;> rcases h2 with h2 | ⟨-, h2⟩
    · exact hzAB h2
    · rw [hzAlab] at h2; exact absurd h2 (by decide)
    · rw [h2, hzBlab] at h1; exact absurd h1 (by decide)
    · rw [h1] at h2; exact absurd h2 (by decide)
  have hkey : ∀ a b, J.Adj a b → Pt.tail a = true → Pt.port a ∈ FU ∧ Pt.port b ∈ FW := by
    intro a b hab hta
    have htb : Pt.tail b = false := by
      cases hb : Pt.tail b
      · rfl
      · exact absurd (hta.trans hb.symm) (Pt.tail_adj a b hab)
    exact ⟨(hFUmem _).2 (Or.inl ⟨a, ⟨(hJ.1 a b hab).1, hta⟩, rfl⟩),
      (hFWmem _).2 (Or.inl ⟨b, ⟨(hJ.1 a b hab).2, htb⟩, rfl⟩)⟩
  have hFcases : ∀ u v, F.Adj u v → (u ∈ FU ∧ v ∈ FW) ∨ (u ∈ FW ∧ v ∈ FU) := by
    intro u v huv
    rw [hF, SimpleGraph.fromEdgeSet_adj] at huv
    obtain ⟨h | h, -⟩ := huv
    · obtain ⟨x, y, hxy, he⟩ := h
      have hflip : ∀ a b, J.Adj a b → Pt.tail a = false → Pt.port a ∈ FW ∧ Pt.port b ∈ FU :=
        fun a b hab hta => by
          have htb : Pt.tail b = true := by
            cases hb : Pt.tail b
            · exact absurd (hta.trans hb.symm) (Pt.tail_adj a b hab)
            · rfl
          exact (hkey b a hab.symm htb).symm
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · cases hxt : Pt.tail x
        · exact Or.inr (hflip x y hxy hxt)
        · exact Or.inl (hkey x y hxy hxt)
      · cases hyt : Pt.tail y
        · exact Or.inr (hflip y x hxy.symm hyt)
        · exact Or.inl (hkey y x hxy.symm hyt)
    · rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨(hFUmem _).2 (Or.inr rfl), (hFWmem _).2 (Or.inr rfl)⟩
      · exact Or.inr ⟨(hFWmem _).2 (Or.inr rfl), (hFUmem _).2 (Or.inr rfl)⟩
  have hFUend : FU ⊆ Fend := by
    intro v hv; rw [hFUmem] at hv; rw [hFend, Finset.mem_union]
    rcases hv with ⟨x, ⟨hx, -⟩, rfl⟩ | rfl
    · exact Or.inl (Finset.mem_image_of_mem _ hx)
    · exact Or.inr (by simp)
  have hFWend : FW ⊆ Fend := by
    intro v hv; rw [hFWmem] at hv; rw [hFend, Finset.mem_union]
    rcases hv with ⟨x, ⟨hx, -⟩, rfl⟩ | rfl
    · exact Or.inl (Finset.mem_image_of_mem _ hx)
    · exact Or.inr (by simp)
  have hfillU : U' \ FU = filler Pt.lab Cell.lu Pt.dA E Pt.port := by
    ext v
    rw [Finset.mem_sdiff, hU'mem, hFUmem, filler, Finset.mem_sdiff, Finset.mem_erase, mem_cellSet,
      Finset.mem_image]
    constructor
    · rintro ⟨h1 | ⟨h1, h2⟩, h3⟩
      · exact absurd (Or.inr h1) h3
      · refine ⟨⟨h1, h2⟩, ?_⟩
        rintro ⟨x, hx, rfl⟩
        cases ht : Pt.tail x
        · rw [(Pt.port_head x hx ht).1] at h2; exact absurd h2 (by decide)
        · exact h3 (Or.inl ⟨x, ⟨hx, ht⟩, rfl⟩)
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨Or.inr ⟨h1, h2⟩, ?_⟩
      rintro (⟨x, ⟨hx, -⟩, rfl⟩ | rfl)
      · exact h3 ⟨x, hx, rfl⟩
      · rw [hzAlab] at h2; exact absurd h2 (by decide)
  have hfillW : W' \ FW = filler Pt.lab Cell.lv Pt.dB E Pt.port := by
    ext v
    rw [Finset.mem_sdiff, hW'mem, hFWmem, filler, Finset.mem_sdiff, Finset.mem_erase, mem_cellSet,
      Finset.mem_image]
    constructor
    · rintro ⟨h1 | ⟨h1, h2⟩, h3⟩
      · exact absurd (Or.inr h1) h3
      · refine ⟨⟨h1, h2⟩, ?_⟩
        rintro ⟨x, hx, rfl⟩
        cases ht : Pt.tail x
        · exact h3 (Or.inl ⟨x, ⟨hx, ht⟩, rfl⟩)
        · rw [(Pt.port_tail x hx ht).1] at h2; exact absurd h2 (by decide)
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨Or.inr ⟨h1, h2⟩, ?_⟩
      rintro (⟨x, ⟨hx, -⟩, rfl⟩ | rfl)
      · exact h3 ⟨x, hx, rfl⟩
      · rw [hzBlab] at h2; exact absurd h2 (by decide)
  obtain ⟨τ, hτbij, hτadj, hτF⟩ := uv_bijection H.supp F U' W' FU FW Pt.μ hFUsub hFWsub hU'W'
    hFcases hFm (fun u hu => (hFend' u).2 (hFUend hu))
    (fun v hv => by obtain ⟨u, hu⟩ := (hFend' v).2 (hFWend hv); exact ⟨u, hu.symm⟩)
    (by rw [hfillU, hfillW]; exact Pt.μ_bij) (by rw [hfillU]; exact Pt.μ_adj)
  -- colour counts
  have hcc_univ : ∀ b, ccount col univ b = N := by
    intro b; cases b
    · exact hyp.card_false
    · exact hyp.card_true
  have hcc_E : ∀ b, ccount col E b = ℓ := by
    intro b; cases b
    · exact hyp.ends_false
    · exact hyp.ends_true
  have hAS_bal : ccount col AS true = ccount col AS false := by
    obtain ⟨β⟩ : Nonempty (↥(↑(cellSet Pt.lab Cell.out) : Set V) ≃
        ↥(↑(cellSet Pt.lab Cell.inp) : Set V)) := by
      rw [← Finite.card_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]; exact hASR.2.1.symm
    obtain ⟨PS, hPS, hPSsys, -, -⟩ := hASR.2.2.2 β
    have hsys : IsPathSystem PS (↑AS : Set V)
        (↑(cellSet Pt.lab Cell.inp ∪ cellSet Pt.lab Cell.out) : Set V) := by
      rw [Finset.coe_union]; exact hPSsys
    have h := card_balance_of_pathSystem col (fun x y hxy => hbip x y (hPS hxy)) hsys
    have hIO : ∀ b, ((cellSet Pt.lab Cell.inp ∪ cellSet Pt.lab Cell.out).filter
        fun x => col x = b).card = 2 * Pt.m := by
      intro b
      have := ccount_union col (cellSet_disjoint Pt.lab (by decide : Cell.inp ≠ Cell.out)) b
      unfold ccount at this
      rw [this, Pt.block_card _ b (by simp), Pt.block_card _ b (by simp)]; ring
    rw [hIO, hIO] at h
    unfold ccount; omega
  have hRemFend : Disjoint Rem Fend :=
    Finset.disjoint_left.2 fun v h1 h2 => ((hRemiff v).1 h1).2 h2
  have hEFend : Disjoint E Fend :=
    Finset.disjoint_left.2 fun v h1 h2 => ((hRemiff v).1 (hERem h1)).2 h2
  have hcc_ports : ∀ b, ccount col (E.image Pt.port) b = ℓ := by
    intro b
    have h := hcc_E b
    unfold ccount at h ⊢
    rw [Finset.filter_image, Finset.card_image_of_injOn]
    · refine Eq.trans ?_ h
      congr 1
      exact Finset.filter_congr fun x hx => by rw [Pt.port_col x hx]
    · exact Pt.port_inj.mono fun x hx => (Finset.mem_filter.1 hx).1
  have hcc_zz : ∀ b, ccount col {zA, zB} b = 1 := by
    intro b; unfold ccount
    rw [Finset.filter_insert, Finset.filter_singleton]
    cases b <;> simp [hzAcol, hzBcol]
  have hpz : Disjoint (E.image Pt.port) {zA, zB} := by
    rw [Finset.disjoint_left]
    intro v hv hvz
    rw [Finset.mem_insert, Finset.mem_singleton] at hvz
    rcases hportimg v hv with h | h <;> rcases hvz with rfl | rfl
    · rw [hzAlab] at h; exact absurd h (by decide)
    · rw [hzBlab] at h; exact absurd h (by decide)
    · rw [hzAlab] at h; exact absurd h (by decide)
    · rw [hzBlab] at h; exact absurd h (by decide)
  have hcc_Fend : ∀ b, ccount col Fend b = ℓ + 1 := by
    intro b
    rw [hFend, ccount_union col hpz b, hcc_ports, hcc_zz]
  have hRem_bal : ccount col Rem true = ccount col Rem false := by
    have hsys : IsPathSystem X (↑(Rem ∪ Fend) : Set V) (↑(E ∪ Fend) : Set V) := by
      rw [Finset.coe_union, Finset.coe_union]; exact hXps
    have h := card_balance_of_pathSystem col (fun x y hxy => hbip x y (hXG hxy)) hsys
    have e1 := ccount_union col hRemFend
    have e2 := ccount_union col hEFend
    have f1 := hcc_Fend true
    have f2 := hcc_Fend false
    have g1 := hcc_E true
    have g2 := hcc_E false
    unfold ccount at e1 e2 f1 f2 g1 g2
    rw [e1, e1, e2, e2, f1, f2, g1, g2] at h
    unfold ccount; omega
  have hdI_cc : ∀ b, ccount col dI b = r := by
    obtain ⟨hle, hsysd, -⟩ := pathSystem_of_paths (G := H.supp) (κ := Unit) (fun _ => zA)
      (fun _ => zB) (fun _ => pd) (fun _ => hpd) (fun _ => hzAB)
      (fun j k hjk => absurd (Subsingleton.elim j k) hjk)
    have e1 : {v | ∃ _j : Unit, v ∈ pd.support} = (↑pd.support.toFinset : Set V) := by
      ext v; simp
    have e2 : {v | ∃ _j : Unit, v = zA ∨ v = zB} = (↑({zA, zB} : Finset V) : Set V) := by
      ext v; simp
    rw [e1, e2] at hsysd
    have h := card_balance_of_pathSystem col (fun x y hxy => hbip x y (hle hxy)) hsysd
    have hsub : ({zA, zB} : Finset V) ⊆ pd.support.toFinset := by
      intro v hv
      rw [Finset.mem_insert, Finset.mem_singleton] at hv
      rw [List.mem_toFinset]
      rcases hv with rfl | rfl
      · exact pd.start_mem_support
      · exact pd.end_mem_support
    have hcard : pd.support.toFinset.card = 2 * r + 2 := by
      rw [List.toFinset_card_of_nodup hpd.support_nodup, SimpleGraph.Walk.length_support, hpdlen]
    have s1 := ccount_sdiff col hsub true
    have s2 := ccount_sdiff col hsub false
    have c1 := card_eq_ccount col pd.support.toFinset
    have z1 := hcc_zz true
    have z2 := hcc_zz false
    rw [← hdI] at s1 s2
    unfold ccount at s1 s2 c1 z1 z2
    rw [z1, z2] at h
    intro b; cases b <;> (unfold ccount; omega)
  have hRem₁dI : Disjoint Rem₁ dI := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    have h2' := (hdIlab v h2).1
    rcases hRem₁lab v h1 with h | h <;> rw [h] at h2' <;> exact absurd h2' (by decide)
  have hRem₁_bal : ccount col Rem₁ true = ccount col Rem₁ false := by
    have e1 := ccount_union col hRem₁dI true
    have e2 := ccount_union col hRem₁dI false
    rw [← hRemdef] at e1 e2
    have := hdI_cc true
    have := hdI_cc false
    omega
  have hRem₁AS : Disjoint Rem₁ AS := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    rcases hRem₁lab v h1 with h | h <;> rcases hASlab v h2 with h' | h' | h' | h' <;>
      rw [h] at h' <;> exact absurd h' (by decide)
  have hOut_cc : ∀ b, ccount col Out b + (ccount col Rem₁ b + ccount col AS b) = N := by
    intro b
    rw [← ccount_union col hRem₁AS, hOut, ccount_sdiff col (Finset.subset_univ _), hcc_univ]
  have hnotRem₁AS : ∀ v, (Pt.lab v = Cell.div ∨ Pt.lab v = Cell.lu ∨ Pt.lab v = Cell.lv ∨
      Pt.lab v = Cell.pool) → v ∈ Out := by
    intro v hv
    rw [hOut, Finset.mem_sdiff, Finset.mem_union]
    refine ⟨Finset.mem_univ _, ?_⟩
    rintro (h | h)
    · rcases hRem₁lab v h with h' | h' <;> rcases hv with hv | hv | hv | hv <;>
        rw [hv] at h' <;> exact absurd h' (by decide)
    · rcases hASlab v h with h' | h' | h' | h' <;> rcases hv with hv | hv | hv | hv <;>
        rw [hv] at h' <;> exact absurd h' (by decide)
  have hU'lab : ∀ v ∈ U', Pt.lab v = Cell.div ∨ Pt.lab v = Cell.lu := by
    intro v hv
    rcases (hU'mem v).1 hv with rfl | ⟨-, h⟩
    · exact Or.inl hzAlab
    · exact Or.inr h
  have hW'lab : ∀ v ∈ W', Pt.lab v = Cell.div ∨ Pt.lab v = Cell.lv := by
    intro v hv
    rcases (hW'mem v).1 hv with rfl | ⟨-, h⟩
    · exact Or.inl hzBlab
    · exact Or.inr h
  have hsubOut : dI ∪ U' ∪ W' ⊆ Out := by
    intro v hv
    rw [Finset.mem_union, Finset.mem_union] at hv
    rcases hv with (hv | hv) | hv
    · exact hnotRem₁AS v (Or.inl (hdIlab v hv).1)
    · rcases hU'lab v hv with h | h
      · exact hnotRem₁AS v (Or.inl h)
      · exact hnotRem₁AS v (Or.inr (Or.inl h))
    · rcases hW'lab v hv with h | h
      · exact hnotRem₁AS v (Or.inl h)
      · exact hnotRem₁AS v (Or.inr (Or.inr (Or.inl h)))
  have hdIU' : Disjoint dI U' := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    obtain ⟨hl, hA, -⟩ := hdIlab v h1
    rcases (hU'mem v).1 h2 with h | ⟨-, h⟩
    · exact hA h
    · rw [hl] at h; exact absurd h (by decide)
  have hdIU'W' : Disjoint (dI ∪ U') W' := by
    rw [Finset.disjoint_union_left]
    refine ⟨?_, hU'W'⟩
    rw [Finset.disjoint_left]
    intro v h1 h2
    obtain ⟨hl, -, hB⟩ := hdIlab v h1
    rcases (hW'mem v).1 h2 with h | ⟨-, h⟩
    · exact hB h
    · rw [hl] at h; exact absurd h (by decide)
  have hcc_U' : ∀ b, ccount col U' b = Pt.m := by
    intro b
    rw [hU', ccount_swap col (mem_cellSet.2 Pt.dA_lab)
      (fun h => by rw [mem_cellSet, hzAlab] at h; exact absurd h (by decide))
      (Pt.dA_col.trans hzAcol.symm)]
    exact Pt.block_card _ b (by simp)
  have hcc_W' : ∀ b, ccount col W' b = Pt.m := by
    intro b
    rw [hW', ccount_swap col (mem_cellSet.2 Pt.dB_lab)
      (fun h => by rw [mem_cellSet, hzBlab] at h; exact absurd h (by decide))
      (Pt.dB_col.trans hzBcol.symm)]
    exact Pt.block_card _ b (by simp)
  have hP_cc : ∀ b, ccount col P b + (ccount col dI b + ccount col U' b + ccount col W' b) =
      ccount col Out b := by
    intro b
    rw [hP, ← ccount_union col hdIU', ← ccount_union col hdIU'W', ccount_sdiff col hsubOut]
  have hn'5 : 5 * Pt.m ≤ n' := by
    rw [hn']
    refine le_trans (Pt.pool_large true) (Finset.card_le_card (Finset.filter_subset_filter _ ?_))
    intro v hv
    exact hnotRem₁AS v (Or.inr (Or.inr (Or.inr (mem_cellSet.1 hv))))
  have hPt : ccount col P true + r + 2 * Pt.m = n' := by
    have := hP_cc true
    rw [hdI_cc, hcc_U', hcc_W', ← hn'] at this
    omega
  have hPf : ccount col P false = ccount col P true := by
    have h1 := hP_cc false
    have h2 := hOut_cc true
    have h3 := hOut_cc false
    rw [hdI_cc, hcc_U', hcc_W'] at h1
    rw [← hn'] at h2
    omega
  have hmdvd : Pt.m ∣ ccount col P true := by
    obtain ⟨q, hq⟩ : ∃ q, q = (n' - 1) / Pt.m := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t, t = (n' - 1) % Pt.m := ⟨_, rfl⟩
    have h1 := Nat.div_add_mod (n' - 1) Pt.m
    rw [← hq, ← ht] at h1
    rw [← ht] at hr
    obtain ⟨M, hM⟩ : ∃ M, M = Pt.m * q := ⟨_, rfl⟩
    rw [← hM] at h1
    have h2 : ccount col P true = M - 2 * Pt.m := by omega
    rw [h2, hM]
    exact Nat.dvd_sub (dvd_mul_right _ _) (dvd_mul_left _ _)
  -- the fresh layers (`T3.2f`)
  have hclass : ∀ b, (classOf E col b).card = N - ℓ := by
    intro b
    have h1 := ccount_sdiff col (Finset.subset_univ E) b
    rw [hcc_univ, hcc_E] at h1
    have h2 : (classOf E col b).card = ccount col (univ \ E) b := rfl
    omega
  have hlogN : Real.log (2 * ((N - ℓ : ℕ) : ℝ)) ≤ L := by
    rcases Nat.eq_zero_or_pos (N - ℓ) with h | h
    · rw [h]; simp only [Nat.cast_zero, mul_zero, Real.log_zero]; linarith [hyp.ten_le]
    · refine le_trans (Real.log_le_log (by positivity) ?_) hyp.log_le
      have : ((N - ℓ : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N ℓ
      linarith
  have hblocks : ∀ X : Finset V, (X = cellSet Pt.lab Cell.out ∨ X = cellSet Pt.lab Cell.inp ∨
      X = cellSet Pt.lab Cell.lu ∨ X = cellSet Pt.lab Cell.lv) → Disjoint X E ∧
      ∀ b, (X.filter fun x => col x = b).card = Pt.m ∧
        OneSided H (classOf E col b) (classOf E col (!b)) (X.filter fun x => col x = b)
          ((Pt.m : ℝ) / ((N - ℓ : ℕ) : ℝ)) D (σ / 2) L K δ := by
    rintro X (rfl | rfl | rfl | rfl) <;>
      refine ⟨Finset.disjoint_left.2 fun v h1 h2 => ?_,
        fun b => ⟨Pt.block_card _ b (by simp), Pt.one_sided _ b (by simp)⟩⟩ <;>
      rw [mem_cellSet] at h1 <;> rw [hEl, h1] at h2 <;> exact absurd h2 (by decide)
  have hzAout : zA ∉ cellSet Pt.lab Cell.out ∪ cellSet Pt.lab Cell.inp ∪
      cellSet Pt.lab Cell.lu ∪ cellSet Pt.lab Cell.lv := by
    simp only [Finset.mem_union, mem_cellSet, hzAlab]; decide
  have hzBout : zB ∉ cellSet Pt.lab Cell.out ∪ cellSet Pt.lab Cell.inp ∪
      cellSet Pt.lab Cell.lu ∪ cellSet Pt.lab Cell.lv := by
    simp only [Finset.mem_union, mem_cellSet, hzBlab]; decide
  have hPOut : P ⊆ Out := by rw [hP]; exact Finset.sdiff_subset
  have hPnot : ∀ v ∈ P, v ∉ dI ∧ v ∉ U' ∧ v ∉ W' := by
    intro v hv
    rw [hP, Finset.mem_sdiff, Finset.mem_union, Finset.mem_union, not_or, not_or] at hv
    exact ⟨hv.2.1.1, hv.2.1.2, hv.2.2⟩
  have hOutnot : ∀ v ∈ Out, v ∉ Rem₁ ∧ v ∉ AS := by
    intro v hv
    rw [hOut, Finset.mem_sdiff, Finset.mem_union, not_or] at hv
    exact hv.2
  have hPE : Disjoint P E :=
    Finset.disjoint_left.2 fun v h1 h2 => (hOutnot v (hPOut h1)).1 (hERem₁ h2)
  have hPlayers : Disjoint P (cellSet Pt.lab Cell.out ∪ cellSet Pt.lab Cell.inp ∪ U' ∪ W') := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    obtain ⟨-, hU, hW⟩ := hPnot v h1
    have hAS := (hOutnot v (hPOut h1)).2
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_union] at h2
    rcases h2 with ((h | h) | h) | h
    · exact hAS (hIOAS (Finset.mem_union_right _ h))
    · exact hAS (hIOAS (Finset.mem_union_left _ h))
    · exact hU h
    · exact hW h
  have hPenv : (univ \ E) \ P ⊆ envelope Pt.lab := by
    intro v hv
    rw [Finset.mem_sdiff, Finset.mem_sdiff] at hv
    obtain ⟨⟨-, hvE⟩, hvP⟩ := hv
    rw [envelope, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun hpool => hvP ?_, fun h => hvE ((hEl v).2 h)⟩
    have hvOut := hnotRem₁AS v (Or.inr (Or.inr (Or.inr hpool)))
    rw [hP, Finset.mem_sdiff]
    refine ⟨hvOut, ?_⟩
    rw [Finset.mem_union, Finset.mem_union]
    rintro ((h | h) | h)
    · rw [(hdIlab v h).1] at hpool; exact absurd hpool (by decide)
    · rcases hU'lab v h with h' | h' <;> rw [h'] at hpool <;> exact absurd hpool (by decide)
    · rcases hW'lab v h with h' | h' <;> rw [h'] at hpool <;> exact absurd hpool (by decide)
  obtain ⟨k, hk4, φ, hφinj, hφO, hφI, hφU, hφW, hφP, hφτ, hφadj⟩ := hFresh H col E
    (cellSet Pt.lab Cell.out) (cellSet Pt.lab Cell.inp) (cellSet Pt.lab Cell.lu)
    (cellSet Pt.lab Cell.lv) U' W' P (envelope Pt.lab) (N - ℓ) Pt.m η₀ D (σ / 2) L Pt.dA Pt.dB
    zA zB τ hbip hyp.weights (hclass true) (hclass false) h₀deg h₀gap (by positivity)
    (by linarith [hyp.sigma_le]) hη₀ hη₀' hD hlogN hyp.ten_le hm1 hblocks
    (cellSet_disjoint _ (by decide)) (cellSet_disjoint _ (by decide))
    (cellSet_disjoint _ (by decide)) (cellSet_disjoint _ (by decide))
    (cellSet_disjoint _ (by decide)) (cellSet_disjoint _ (by decide)) Pt.layer_large
    (mem_cellSet.2 Pt.dA_lab) Pt.dA_col (mem_cellSet.2 Pt.dB_lab) Pt.dB_col hzAE hzAcol hzBE
    hzBcol hzAout hzBout hU' hW' hPE hPlayers hPf.symm hmdvd
    (by have h1 : ccount col P true + r + 2 * Pt.m = n' := hPt
        unfold ccount at h1; omega) hPenv Pt.env_deg
    Pt.env_card hτbij
  -- the final assembly (`T3.2g`)
  have hint : ∀ i j, 0 < j → j < k → φ i j ∈ P ∨ φ i j ∈ U' ∨ φ i j ∈ W' := by
    intro i j hj0 hjk
    rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ 4 ≤ j by omega) with rfl | rfl | rfl | hj
    · exact Or.inl ((hφP _).2 ⟨i, 1, Or.inl rfl, rfl⟩)
    · exact Or.inr (Or.inl ((hφU _).2 ⟨i, rfl⟩))
    · exact Or.inr (Or.inr ((hφW _).2 ⟨i, rfl⟩))
    · exact Or.inl ((hφP _).2 ⟨i, j, Or.inr ⟨hj, hjk⟩, rfl⟩)
  have hU'AS : ∀ v ∈ U', v ∉ AS := fun v hv => (hOutnot v (hsubOut (by
    rw [Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inr hv)))).2
  have hW'AS : ∀ v ∈ W', v ∉ AS := fun v hv => (hOutnot v (hsubOut (by
    rw [Finset.mem_union]; exact Or.inr hv))).2
  have hRemnot : ∀ v ∈ Rem, v ∉ AS ∧ v ∉ U' ∧ v ∉ W' ∧ v ∉ P := by
    intro v hv
    rw [hRemdef, Finset.mem_union] at hv
    rcases hv with hv | hv
    · have hl := hRem₁lab v hv
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => (hOutnot v (hPOut h)).1 hv⟩
      · rcases hl with hl | hl <;> rcases hASlab v h with h' | h' | h' | h' <;>
          rw [hl] at h' <;> exact absurd h' (by decide)
      · rcases hl with hl | hl <;> rcases hU'lab v h with h' | h' <;>
          rw [hl] at h' <;> exact absurd h' (by decide)
      · rcases hl with hl | hl <;> rcases hW'lab v h with h' | h' <;>
          rw [hl] at h' <;> exact absurd h' (by decide)
    · obtain ⟨hl, hA, hB⟩ := hdIlab v hv
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => (hPnot v h).1 hv⟩
      · rcases hASlab v h with h' | h' | h' | h' <;> rw [hl] at h' <;> exact absurd h' (by decide)
      · exact Finset.disjoint_left.1 hdIU' hv h
      · exact Finset.disjoint_left.1 hdIU'W' (Finset.mem_union_left _ hv) h
  have hsetF : {v | ∃ u, F.Adj v u} = (↑Fend : Set V) := Set.ext fun v => hFend' v
  obtain ⟨Pf, hPf1, hPf2, hPf3, hPf4⟩ := assembly_core H.supp J F X ↑E ↑Rem ↑AS
    ↑(cellSet Pt.lab Cell.inp) ↑(cellSet Pt.lab Cell.out) (2 * Pt.m) k φ (by omega) (by omega)
    hASR hφinj (fun v => by rw [Finset.mem_coe]; exact hφO v)
    (fun v => by rw [Finset.mem_coe]; exact hφI v)
    (fun i j hj0 hjk h => by
      rw [Finset.mem_coe] at h
      rcases hint i j hj0 hjk with h' | h' | h'
      · exact (hOutnot _ (hPOut h')).2 h
      · exact hU'AS _ h' h
      · exact hW'AS _ h' h)
    (fun i j hjk hnF => by
      by_cases hj2 : j = 2
      · subst hj2
        have hu : φ i 2 ∈ U' := (hφU _).2 ⟨i, rfl⟩
        show H.supp.Adj (φ i 2) (φ i 3)
        rw [hφτ i]
        rcases hτadj _ hu with h | h
        · exact h
        · exact absurd (by rw [show φ i (2 + 1) = τ (φ i 2) from hφτ i]; exact h) hnF
      · exact hφadj i j hjk hj2)
    (fun u v huv => by
      rcases hτF u v huv with ⟨hu, hτu⟩ | ⟨hv, hτv⟩
      · obtain ⟨i, rfl⟩ := (hφU u).1 hu
        refine ⟨i, 2, by norm_num, by omega, ?_⟩
        rw [← hτu, ← hφτ i]
      · obtain ⟨i, rfl⟩ := (hφU v).1 hv
        refine ⟨i, 2, by norm_num, by omega, ?_⟩
        rw [← hτv, ← hφτ i, Sym2.eq_swap])
    hFm (by rw [hsetF]; exact hXps) hXG (fun u v h => by simpa using hXrem u v h)
    (by exact_mod_cast hERem) hFreach
    (fun v hv => by
      obtain ⟨u, hu, hr⟩ := hRemreach v hv
      exact ⟨u, (hFend' u).2 hu, hr⟩)
    (fun v => by
      by_cases hA : v ∈ AS
      · exact Or.inl hA
      by_cases hR : v ∈ Rem
      · exact Or.inr (Or.inl hR)
      right; right
      have hvOut : v ∈ Out := by
        rw [hOut, Finset.mem_sdiff, Finset.mem_union]
        refine ⟨Finset.mem_univ _, ?_⟩
        rintro (h | h)
        · exact hR (by rw [hRemdef]; exact Finset.mem_union_left _ h)
        · exact hA h
      by_cases hU : v ∈ U'
      · obtain ⟨i, rfl⟩ := (hφU v).1 hU
        exact ⟨i, 2, by norm_num, by omega, rfl⟩
      by_cases hW : v ∈ W'
      · obtain ⟨i, rfl⟩ := (hφW v).1 hW
        exact ⟨i, 3, by norm_num, by omega, rfl⟩
      have hvP : v ∈ P := by
        rw [hP, Finset.mem_sdiff, Finset.mem_union, Finset.mem_union]
        refine ⟨hvOut, ?_⟩
        rintro ((h | h) | h)
        · exact hR (by rw [hRemdef]; exact Finset.mem_union_right _ h)
        · exact hU h
        · exact hW h
      obtain ⟨i, j, hj, rfl⟩ := (hφP v).1 hvP
      exact ⟨i, j, by omega, by omega, rfl⟩)
    (fun v hv => (hRemnot v hv).1)
    (fun i j hjk h => by
      rw [Finset.mem_coe] at h
      have hn := hRemnot _ h
      rcases (show j = 0 ∨ j = k ∨ (0 < j ∧ j < k) by omega) with rfl | rfl | ⟨hj0, hjk'⟩
      · exact hn.1 (hIOAS (Finset.mem_union_right _ ((hφO _).2 ⟨i, rfl⟩)))
      · exact hn.1 (hIOAS (Finset.mem_union_left _ ((hφI _).2 ⟨i, rfl⟩)))
      · rcases hint i j hj0 hjk' with h' | h' | h'
        · exact hn.2.2.2 h'
        · exact hn.2.1 h'
        · exact hn.2.2.1 h')
  exact ⟨Pf, hPf1, hPf2, hPf3, hPf4⟩

end LocalAbsorption

open LocalAbsorption

/-- **Theorem 3.2 (Local absorption).** Fix `ω > 0`. There are constants `c, C > 0` such that
if `H` is bipartite with classes of size `N`, weights in `[ω, 1]`, degrees `(1 ± η) D`,
normalized upper gap at least `σ ∈ (0, 1/10]`, `η ≤ cσ`, `L ≥ max {log (2N), 10}`, `g ≥ 4`,
`D ≥ C σ^{-9/2} L² g`, `g ≥ C L / log (2 + σ^{5/2} D / L)`, and `E` contains `ℓ ≥ 1` vertices
of each class with `ℓ ≤ c σ^{5/2} N / (L g)` and `max_v d_H(v, E) ≤ c σ^{5/2} D / L`, then
`(supp H, E)` is matching-absorbing. -/
theorem local_absorption (ω : ℝ) (hω : 0 < ω) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (α : Type u) [Fintype α] [DecidableEq α] (H : WGraph α) (col : α → Bool)
        (N ℓ : ℕ) (η D σ L g : ℝ) (E : Finset α),
        LocalAbsorptionHyp ω c C H col N ℓ η D σ L g E →
        IsMatchingAbsorbing H.supp (E : Set α) := by
  obtain ⟨εR, c₇, C₇, hεR, hc₇, hC₇, hRouter⟩ := router_step.{u} ω hω
  obtain ⟨c34, C34, hc34, hC34, hsc⟩ := spectral_connection.{u, u} (1 / 2) (by norm_num)
    (by norm_num)
  have hConn : ConnSpec.{u} (1 / 2) c34 C34 := by
    intro V _ _ H R Δ σ L β κ _ _ pa pb
    exact hsc H R Δ σ L β pa pb
  obtain ⟨cdfs, hcdfs, hDiv⟩ := divisibility_step.{u}
  obtain ⟨cF, δ, κ, hcF, hδ, hκ, hfreshK⟩ := fresh_layers.{u} ω hω
  obtain ⟨c₀, hc₀, hdel⟩ := deletion_step.{u}
  obtain ⟨K, hK, hpartK⟩ := initial_partition.{u} ω hω εR c₇ C₇ (c34 / 4) cdfs δ κ hεR hc₇ hC₇
    (by positivity) hcdfs hδ hκ
  obtain ⟨CF, hCF, hFresh⟩ := hfreshK K hK
  obtain ⟨cP, CP, hcP, hCP, hPart⟩ := hpartK CF hCF
  refine ⟨min cP (min c₀ (cF / 4)), CP, lt_min hcP (lt_min hc₀ (by positivity)), hCP, ?_⟩
  intro α _ _ H col N ℓ η D σ L g E hyp
  have hc1 : min cP (min c₀ (cF / 4)) ≤ cP := min_le_left _ _
  have hc2 : min cP (min c₀ (cF / 4)) ≤ c₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hc3 : min cP (min c₀ (cF / 4)) ≤ cF / 4 := (min_le_right _ _).trans (min_le_right _ _)
  set c := min cP (min c₀ (cF / 4)) with hc
  have hc0 : 0 < c := lt_min hcP (lt_min hc₀ (by positivity))
  have hypP := hyp_mono hyp hc1 le_rfl hCP
  have hσ := hyp.sigma_pos
  have hL : 0 < L := by linarith [hyp.ten_le]
  have hg : 0 < g := by linarith [hyp.four_le]
  have hD : 0 < D := by
    have h1 := hyp.deg_large
    have : 0 < CP * σ ^ (-(9 / 2 : ℝ)) * L ^ 2 * g := by
      have := Real.rpow_pos_of_pos hσ (-(9 / 2 : ℝ))
      positivity
    linarith
  obtain ⟨h₀deg, h₀gap⟩ := hdel H E c η D σ L hc0 hc2 hD hyp.degrees hyp.eta_le hyp.gap hσ
    (by linarith [hyp.sigma_le]) hyp.ten_le hyp.ends_sparse
  have hEcard : E.card = ℓ + ℓ := by
    have h1 := Finset.card_filter_add_card_filter_not (s := E) (fun x => col x = true)
    have h2 : (E.filter fun x => ¬ col x = true) = E.filter fun x => col x = false := by
      ext x; simp
    rw [h2, hyp.ends_true, hyp.ends_false] at h1
    omega
  refine ⟨E.finite_toSet, ?_, ?_, fun J hJ => ?_⟩
  · obtain ⟨x, hx⟩ : (E.filter fun x => col x = true).Nonempty := by
      rw [← Finset.card_pos, hyp.ends_true]; exact hyp.one_le
    exact ⟨x, (Finset.mem_filter.1 hx).1⟩
  · rw [Set.ncard_coe_finset, hEcard]; exact ⟨ℓ, rfl⟩
  · obtain ⟨Pt⟩ := hPart H col N ℓ η D σ L g E J hypP hJ
    obtain ⟨P, hP, h1, h2, h3⟩ := absorb_of_partition hRouter hConn hDiv hFresh hyp hCP hJ
      h₀deg h₀gap (by positivity) (by nlinarith) Pt
    exact ⟨P, hP, h1, h2, h3⟩

end Lovasz
