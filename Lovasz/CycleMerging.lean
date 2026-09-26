/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent)
-/
import Lovasz.Defs

/-!
# Lemma 3.8: cycle merging

DAG node `L3.8` of `docs/BLUEPRINT.md`.
-/

universe u

namespace Lovasz

open SimpleGraph

namespace CycleMerging

section General

variable {V : Type*}

/-- Transfer reachability along a map that sends edges to reachable pairs. -/
lemma reachable_of_forall_adj {α β : Type*} {G : SimpleGraph α} {G' : SimpleGraph β} (f : α → β)
    (h : ∀ a b, G.Adj a b → G'.Reachable (f a) (f b)) {a b : α} (hab : G.Reachable a b) :
    G'.Reachable (f a) (f b) := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- A connected spanning `2`-regular subgraph yields a Hamilton cycle. -/
lemma isHamiltonian_of_two_regular [Fintype V] [DecidableEq V] {X Y : SimpleGraph V}
    (hle : Y ≤ X) (hdeg : ∀ v, (Y.neighborSet v).ncard = 2) (hconn : Y.Connected) :
    X.IsHamiltonian := by
  intro _
  obtain ⟨v⟩ := hconn.nonempty
  have hcyc : Y.IsCycles := fun w _ => hdeg w
  have hn : (Y.neighborSet v).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hdeg v]; norm_num)
  obtain ⟨p, hp, hverts⟩ :=
    hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := Y.connectedComponentMk v) rfl hn
  refine ⟨v, p.mapLe hle, ?_⟩
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one]
  refine ⟨hp.mapLe hle, fun a => ?_⟩
  rw [Walk.support_mapLe_eq_support]
  have hmem : a ∈ p.support := by
    rw [← Walk.mem_verts_toSubgraph, hverts, ConnectedComponent.mem_supp_iff,
      ConnectedComponent.eq]
    exact hconn.preconnected a v
  have htail : a ∈ p.support.tail := by
    rw [← Walk.cons_tail_support] at hmem
    rcases List.mem_cons.mp hmem with h | h
    · subst h; exact Walk.end_mem_tail_support hp.not_nil
    · exact h
  exact List.count_eq_one_of_mem hp.support_nodup htail

/-- In a graph of maximum degree two, a connected component contains at most two vertices of
degree one. -/
lemma not_three_ends [Finite V] {G : SimpleGraph V}
    (hle : ∀ v, (G.neighborSet v).ncard ≤ 2) {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hx : (G.neighborSet x).ncard = 1) (hy : (G.neighborSet y).ncard = 1)
    (hz : (G.neighborSet z).ncard = 1) (rxy : G.Reachable x y) (rxz : G.Reachable x z) :
    False := by
  classical
  obtain ⟨p, hp⟩ : ∃ p : G.Walk x y, p.IsPath := ⟨rxy.some.bypass, rxy.some.bypass_isPath⟩
  have hnil : ¬ p.Nil := Walk.not_nil_of_ne hxy
  have key : ∀ u, (G.neighborSet u).ncard ≤ (p.toSubgraph.neighborSet u).ncard →
      ∀ w, G.Adj u w → w ∈ p.support := by
    intro u hu w hw
    have heq : p.toSubgraph.neighborSet u = G.neighborSet u :=
      Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset u) hu (Set.toFinite _)
    have hw' : w ∈ p.toSubgraph.neighborSet u := heq ▸ hw
    exact (Walk.mem_verts_toSubgraph p).mp (p.toSubgraph.neighborSet_subset_verts u hw')
  have closed : ∀ u ∈ p.support, ∀ w, G.Adj u w → w ∈ p.support := by
    intro u hu
    obtain ⟨k, rfl, hk⟩ := Walk.mem_support_iff_exists_getVert.mp hu
    apply key
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Walk.getVert_zero, hp.neighborSet_toSubgraph_startpoint hnil, hx,
        Set.ncard_singleton]
    rcases hk.lt_or_eq with hk1 | rfl
    · rw [hp.ncard_neighborSet_toSubgraph_internal_eq_two hk0.ne' hk1]
      exact hle _
    · rw [Walk.getVert_length, hp.neighborSet_toSubgraph_endpoint hnil, hy,
        Set.ncard_singleton]
  have reach : ∀ {a b : V} (q : G.Walk a b), a ∈ p.support → b ∈ p.support := by
    intro a b q
    induction q with
    | nil => exact id
    | cons hadj _ ih => exact fun ha => ih (closed _ ha _ hadj)
  have hzs : z ∈ p.support := reach rxz.some (Walk.start_mem_support p)
  obtain ⟨k, hkz, hk⟩ := Walk.mem_support_iff_exists_getVert.mp hzs
  have hk0 : k ≠ 0 := by rintro rfl; rw [Walk.getVert_zero] at hkz; exact hxz hkz
  have hk1 : k < p.length := by
    rcases hk.lt_or_eq with h | rfl
    · exact h
    · rw [Walk.getVert_length] at hkz; exact absurd hkz hyz
  have h2 := hp.ncard_neighborSet_toSubgraph_internal_eq_two hk0 hk1
  rw [hkz] at h2
  have := Set.ncard_le_ncard (p.toSubgraph.neighborSet_subset z) (Set.toFinite _)
  omega

/-- Handshake: the component of a vertex of odd degree contains another vertex of odd
degree. -/
lemma exists_other_odd [Finite V] {G : SimpleGraph V} {x : V}
    (hx : Odd (G.neighborSet x).ncard) :
    ∃ y, y ≠ x ∧ G.Reachable x y ∧ Odd (G.neighborSet y).ncard := by
  classical
  have := Fintype.ofFinite V
  let G' : SimpleGraph V :=
    { Adj := fun u v => G.Adj u v ∧ G.Reachable x u
      symm := ⟨fun u v h => ⟨h.1.symm, h.2.trans h.1.reachable⟩⟩
      loopless := ⟨fun u h => h.1.ne rfl⟩ }
  have hG' : ∀ u, G.Reachable x u → G'.neighborSet u = G.neighborSet u := by
    intro u hu
    ext w
    simp [G', hu]
  have hG'' : ∀ u, ¬ G.Reachable x u → G'.neighborSet u = ∅ := by
    intro u hu
    ext w
    simp [G', hu]
  have hodd : Odd (G'.degree x) := by
    rw [← ncard_neighborSet, hG' x (Reachable.refl x)]
    exact hx
  obtain ⟨w, hw, hwodd⟩ := G'.exists_ne_odd_degree_of_exists_odd_degree x hodd
  rw [← ncard_neighborSet] at hwodd
  have hr : G.Reachable x w := by
    by_contra h
    rw [hG'' w h, Set.ncard_empty] at hwodd
    exact Nat.not_odd_zero hwodd
  refine ⟨w, hw, hr, ?_⟩
  rwa [hG' w hr] at hwodd

/-- A finite set of even size has a perfect matching. -/
lemma exists_isPerfectMatchingOn {α : Type*} (E : Set α) (hfin : E.Finite)
    (heven : Even E.ncard) : ∃ J : SimpleGraph α, IsPerfectMatchingOn J E := by
  have : Finite E := hfin.to_subtype
  have hNe : Even (Nat.card E) := by rw [Nat.card_coe_set_eq]; exact heven
  obtain ⟨m, hm⟩ := hNe
  let e : E ≃ Fin (Nat.card E) := Finite.equivFin E
  let J : SimpleGraph α :=
    { Adj := fun a b => ∃ ha : a ∈ E, ∃ hb : b ∈ E, a ≠ b ∧
        (e ⟨a, ha⟩).val / 2 = (e ⟨b, hb⟩).val / 2
      symm := ⟨fun a b ⟨ha, hb, hab, h⟩ => ⟨hb, ha, hab.symm, h.symm⟩⟩
      loopless := ⟨fun a ⟨_, _, h, _⟩ => h rfl⟩ }
  refine ⟨J, fun a b ⟨ha, hb, _⟩ => ⟨ha, hb⟩, fun a ha => ?_⟩
  set k : ℕ := (e ⟨a, ha⟩).val with hk
  have hkN : k < Nat.card E := (e ⟨a, ha⟩).isLt
  set k' : ℕ := if k % 2 = 0 then k + 1 else k - 1 with hk'
  have hk'N : k' < Nat.card E := by rw [hk']; split_ifs <;> omega
  set b : E := e.symm ⟨k', hk'N⟩ with hb
  have heb : (e b).val = k' := by rw [hb, Equiv.apply_symm_apply]
  have hkk' : k ≠ k' := by rw [hk']; split_ifs <;> omega
  refine ⟨b, ⟨ha, b.2, ?_, ?_⟩, ?_⟩
  · intro hab
    apply hkk'
    rw [← heb, hk]
    congr 2
    exact Subtype.ext hab
  · rw [← hk, heb, hk']; split_ifs <;> omega
  · rintro c ⟨ha2, hc, hac, hdiv⟩
    have hne : (e ⟨c, hc⟩).val ≠ k := by
      intro h
      apply hac
      have := e.injective (Fin.ext h)
      exact (congrArg Subtype.val this).symm
    have hck : (e ⟨c, hc⟩).val = k' := by
      rw [← hk] at hdiv
      rw [hk']
      have := (e ⟨c, hc⟩).isLt
      split_ifs <;> omega
    have : (⟨c, hc⟩ : E) = b := by
      apply e.injective
      apply Fin.ext
      rw [hck, heb]
    exact congrArg Subtype.val this

/-- Strict decrease of `Nat.card` along a surjection that is not injective. -/
lemma natCard_lt_of_surj_not_inj {α β : Type*} [Finite α] (f : α → β)
    (hs : Function.Surjective f) (hn : ¬ Function.Injective f) : Nat.card β < Nat.card α := by
  have := Fintype.ofFinite α
  have : Finite β := Finite.of_surjective f hs
  have := Fintype.ofFinite β
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_surjective_not_injective f hs hn

/-- The matching of `E ⊆ s` pairing two vertices when they are joined in `Z`. -/
def pairing (Z : SimpleGraph V) (s : Finset V) (E : Set s) : SimpleGraph s where
  Adj a b := a ≠ b ∧ a ∈ E ∧ b ∈ E ∧ Z.Reachable a b
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- If `Z` has maximum degree two and its degree-one vertices are exactly `E`, then joining two
vertices of `E` when they lie in the same component of `Z` is a perfect matching of `E`. -/
lemma pairing_isPerfectMatchingOn [Finite V] {Z : SimpleGraph V} (s : Finset V) (E : Set s)
    (hle : ∀ v, (Z.neighborSet v).ncard ≤ 2)
    (hE : ∀ v, (Z.neighborSet v).ncard = 1 ↔ ∃ h : v ∈ s, (⟨v, h⟩ : s) ∈ E) :
    IsPerfectMatchingOn (pairing Z s E) E := by
  refine ⟨fun a b h => ⟨h.2.1, h.2.2.1⟩, fun a ha => ?_⟩
  have hdeg : (Z.neighborSet a).ncard = 1 := (hE a).mpr ⟨a.2, ha⟩
  obtain ⟨w, hw, hr, hodd⟩ := exists_other_odd (G := Z) (x := a) (by rw [hdeg]; exact odd_one)
  have hw1 : (Z.neighborSet w).ncard = 1 := by
    have := hle w
    rcases hodd with ⟨k, hk⟩
    omega
  obtain ⟨hws, hwE⟩ := (hE w).mp hw1
  refine ⟨⟨w, hws⟩, ⟨fun h => hw (congrArg Subtype.val h).symm, ha, hwE, hr⟩, ?_⟩
  rintro c ⟨hac, -, hcE, hrc⟩
  by_contra hne
  have hc1 : (Z.neighborSet c).ncard = 1 := (hE c).mpr ⟨c.2, hcE⟩
  refine not_three_ends hle (x := a) (y := w) (z := c) hw.symm
    (fun h => hac (Subtype.ext h)) (fun h => hne (Subtype.ext h.symm)) hdeg hw1 hc1 hr hrc

end General

section Merging

variable {V : Type u} {X : SimpleGraph V}
  {ι : Type*} {part : ι → Finset V} {W : Set V} {M : SimpleGraph V}
  {H : ∀ i, SimpleGraph (part i)}

/-- Push a graph on a finset to the ambient type. -/
def push {s : Finset V} (P : SimpleGraph s) : SimpleGraph V :=
  P.map (Function.Embedding.subtype _)

lemma push_adj {s : Finset V} {P : SimpleGraph s} {u v : V} :
    (push P).Adj u v ↔ ∃ hu : u ∈ s, ∃ hv : v ∈ s, P.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  rw [push, map_adj]
  constructor
  · rintro ⟨⟨u', hu⟩, ⟨v', hv⟩, h, rfl, rfl⟩
    exact ⟨hu, hv, h⟩
  · rintro ⟨hu, hv, h⟩
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, h, rfl, rfl⟩

lemma ncard_push_neighborSet {s : Finset V} {P : SimpleGraph s} {v : V} (hv : v ∈ s) :
    ((push P).neighborSet v).ncard = (P.neighborSet ⟨v, hv⟩).ncard := by
  have : (push P).neighborSet v = Subtype.val '' P.neighborSet ⟨v, hv⟩ := by
    ext w
    simp only [mem_neighborSet, push_adj, Set.mem_image]
    constructor
    · rintro ⟨hv', hw, h⟩
      exact ⟨⟨w, hw⟩, h, rfl⟩
    · rintro ⟨⟨w', hw⟩, h, rfl⟩
      exact ⟨hv, hw, h⟩
  rw [this, Set.ncard_image_of_injective _ Subtype.val_injective]

/-- Remove all edges touching `s`. -/
def restrictOut (R : SimpleGraph V) (s : Finset V) : SimpleGraph V where
  Adj u v := R.Adj u v ∧ u ∉ s ∧ v ∉ s
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- A union `R` of local path systems, one in each part: its edges are edges of the local
graphs `H i`, and every vertex outside `W` has total degree two in `M ⊔ R`. -/
structure GoodLocal (part : ι → Finset V) (W : Set V) (M : SimpleGraph V)
    (H : ∀ i, SimpleGraph (part i)) (R : SimpleGraph V) : Prop where
  adj : ∀ u v, R.Adj u v → ∃ i, ∃ hu : u ∈ part i, ∃ hv : v ∈ part i,
    (H i).Adj ⟨u, hu⟩ ⟨v, hv⟩
  deg : ∀ v, v ∉ W → (R.neighborSet v).ncard + (M.neighborSet v).ncard = 2

lemma notMem_W (hdata : IsMergingData X part W M H) {i : ι} {v : V} (hv : v ∈ part i) :
    v ∉ W :=
  fun hW => Set.disjoint_left.mp (hdata.part_disjoint i) (Finset.mem_coe.mpr hv) hW

lemma part_eq (hdata : IsMergingData X part W M H) {i j : ι} {v : V} (hi : v ∈ part i)
    (hj : v ∈ part j) : i = j :=
  (hdata.part_unique v (notMem_W hdata hi)).unique hi hj

lemma GoodLocal.adj_part (hdata : IsMergingData X part W M H) {R : SimpleGraph V}
    (hR : GoodLocal part W M H R) {i : ι} {u v : V} (h : R.Adj u v) (hu : u ∈ part i) :
    v ∈ part i := by
  obtain ⟨j, hu', hv, -⟩ := hR.adj u v h
  rwa [part_eq hdata hu hu']

lemma GoodLocal.not_M (hdata : IsMergingData X part W M H) {R : SimpleGraph V}
    (hR : GoodLocal part W M H R) {u v : V} (h : R.Adj u v) : ¬ M.Adj u v ∧ X.Adj u v := by
  obtain ⟨j, hu, hv, hH⟩ := hR.adj u v h
  have := hdata.local_le j _ _ hH
  exact ⟨this.2, this.1⟩

lemma GoodLocal.deg_sup [Finite V] (hdata : IsMergingData X part W M H) {R : SimpleGraph V}
    (hR : GoodLocal part W M H R) (v : V) : ((M ⊔ R).neighborSet v).ncard = 2 := by
  have hunion : (M ⊔ R).neighborSet v = M.neighborSet v ∪ R.neighborSet v := by
    ext w
    simp
  have hdisj : Disjoint (M.neighborSet v) (R.neighborSet v) := by
    rw [Set.disjoint_left]
    intro w hM hR'
    exact (hR.not_M hdata hR').1 hM
  rw [hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  by_cases hv : v ∈ W
  · have : R.neighborSet v = ∅ := by
      ext w
      simp only [mem_neighborSet, Set.mem_empty_iff_false, iff_false]
      intro h
      obtain ⟨j, hu, -, -⟩ := hR.adj v w h
      exact notMem_W hdata hu hv
    rw [this, Set.ncard_empty, hdata.deg_W v hv]
  · rw [add_comm]
    exact hR.deg v hv

lemma GoodLocal.le (hdata : IsMergingData X part W M H) {R : SimpleGraph V}
    (hR : GoodLocal part W M H R) : M ⊔ R ≤ X :=
  sup_le hdata.le (fun _ _ h => (hR.not_M hdata h).2)

lemma local_deg (hdata : IsMergingData X part W M H) {i : ι} {P : SimpleGraph (part i)}
    (h1 : ∀ x ∈ connectorEnds M (part i), (P.neighborSet x).ncard = 1)
    (h2 : ∀ x ∉ connectorEnds M (part i), (P.neighborSet x).ncard = 2) (x : part i) :
    (P.neighborSet x).ncard + (M.neighborSet x).ncard = 2 := by
  by_cases hx : x ∈ connectorEnds M (part i)
  · rw [h1 x hx]
    have : (M.neighborSet x).ncard = 1 := hx
    rw [this]
  · rw [h2 x hx]
    have hne : (M.neighborSet x).ncard ≠ 1 := hx
    have hle := hdata.deg_out x (notMem_W hdata x.2)
    omega

lemma exists_goodLocal (hdata : IsMergingData X part W M H)
    (habs : ∀ i, IsMatchingAbsorbing (H i) (connectorEnds M (part i))) :
    ∃ R, GoodLocal part W M H R := by
  have hP : ∀ i, ∃ P : SimpleGraph (part i), P ≤ H i ∧
      (∀ x ∈ connectorEnds M (part i), (P.neighborSet x).ncard = 1) ∧
      (∀ x ∉ connectorEnds M (part i), (P.neighborSet x).ncard = 2) := by
    intro i
    obtain ⟨hfin, -, heven, habsi⟩ := habs i
    obtain ⟨J, hJ⟩ := exists_isPerfectMatchingOn _ hfin heven
    obtain ⟨P, hPH, h1, h2, -⟩ := habsi J hJ
    exact ⟨P, hPH, h1, h2⟩
  choose P hPH h1 h2 using hP
  refine ⟨⨆ i, push (P i), ⟨?_, ?_⟩⟩
  · intro u v h
    rw [iSup_adj] at h
    obtain ⟨i, h⟩ := h
    obtain ⟨hu, hv, h⟩ := push_adj.mp h
    exact ⟨i, hu, hv, hPH i h⟩
  · intro v hv
    obtain ⟨i, hi, -⟩ := hdata.part_unique v hv
    have : (⨆ j, push (P j)).neighborSet v = (push (P i)).neighborSet v := by
      ext w
      simp only [mem_neighborSet, iSup_adj]
      constructor
      · rintro ⟨j, hj⟩
        have hvj : v ∈ part j := (push_adj.mp hj).1
        obtain rfl := part_eq hdata hi hvj
        exact hj
      · exact fun h => ⟨i, h⟩
    rw [this, ncard_push_neighborSet hi]
    exact local_deg hdata (h1 i) (h2 i) ⟨v, hi⟩

/-- If `M ⊔ R` is disconnected, some part meets two of its components. -/
lemma exists_split (hdata : IsMergingData X part W M H)
    (habs : ∀ i, IsMatchingAbsorbing (H i) (connectorEnds M (part i))) {R : SimpleGraph V}
    (hc : ¬ (M ⊔ R).Connected) :
    ∃ i, ∃ a ∈ part i, ∃ b ∈ part i, ¬ (M ⊔ R).Reachable a b := by
  by_contra hne
  push Not at hne
  apply hc
  have hMY : M ≤ M ⊔ R := le_sup_left
  have hne_part : ∀ i, (part i).Nonempty := by
    intro i
    obtain ⟨x, -⟩ := (habs i).2.1
    exact ⟨x, x.2⟩
  choose rep hrep using hne_part
  have hιcon := hdata.contraction_connected
  have hrr : ∀ i j, (M ⊔ R).Reachable (rep i) (rep j) := by
    intro i j
    refine reachable_of_forall_adj rep (fun k l hkl => ?_) (hιcon.preconnected i j)
    rw [fromRel_adj] at hkl
    obtain ⟨-, h | h⟩ := hkl
    · obtain ⟨x, hx, y, hy, -, hxy⟩ := h
      exact (hne k _ (hrep k) x hx).trans ((hxy.mono hMY).trans (hne l y hy _ (hrep l)))
    · obtain ⟨x, hx, y, hy, -, hxy⟩ := h
      exact (hne k _ (hrep k) y hy).trans ((hxy.mono hMY).symm.trans (hne l x hx _ (hrep l)))
  have hv : ∀ v, ∃ i, (M ⊔ R).Reachable v (rep i) := by
    intro v
    obtain ⟨x, hxW, hvx⟩ := hdata.meets_part v
    obtain ⟨i, hi, -⟩ := hdata.part_unique x hxW
    exact ⟨i, (hvx.mono hMY).trans (hne i x hi _ (hrep i))⟩
  obtain ⟨i0⟩ := hιcon.nonempty
  have : Nonempty V := ⟨rep i0⟩
  refine ⟨fun u v => ?_⟩
  obtain ⟨i, hi⟩ := hv u
  obtain ⟨j, hj⟩ := hv v
  exact hi.trans ((hrr i j).trans hj.symm)

/-- The merging step: re-absorbing one part that meets two components strictly decreases the
number of components. -/
lemma merge_step [Finite V] (hdata : IsMergingData X part W M H)
    (habs : ∀ i, IsMatchingAbsorbing (H i) (connectorEnds M (part i))) {R : SimpleGraph V}
    (hR : GoodLocal part W M H R) (i : ι) {a b : V} (ha : a ∈ part i) (hb : b ∈ part i)
    (hab : ¬ (M ⊔ R).Reachable a b) :
    ∃ R', GoodLocal part W M H R' ∧
      Nat.card (M ⊔ R').ConnectedComponent < Nat.card (M ⊔ R).ConnectedComponent := by
  classical
  set Z := M ⊔ restrictOut R (part i) with hZ
  have hZle : Z ≤ M ⊔ R := sup_le_sup_left (fun u v h => h.1) M
  have hZout : ∀ v, v ∉ part i → Z.neighborSet v = (M ⊔ R).neighborSet v := by
    intro v hv
    ext w
    simp only [mem_neighborSet, hZ, sup_adj]
    constructor
    · rintro (h | ⟨h, -, -⟩)
      exacts [Or.inl h, Or.inr h]
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨h, hv, fun hw => hv (hR.adj_part hdata h.symm hw)⟩
  have hZin : ∀ v, v ∈ part i → Z.neighborSet v = M.neighborSet v := by
    intro v hv
    ext w
    simp only [mem_neighborSet, hZ, sup_adj]
    constructor
    · rintro (h | ⟨-, h, -⟩)
      exacts [h, absurd hv h]
    · exact Or.inl
  have hZdeg : ∀ v, (Z.neighborSet v).ncard ≤ 2 := by
    intro v
    rw [← hR.deg_sup hdata v]
    exact Set.ncard_le_ncard (fun w hw => hZle hw) (Set.toFinite _)
  have hZE : ∀ v, (Z.neighborSet v).ncard = 1 ↔
      ∃ h : v ∈ part i, (⟨v, h⟩ : part i) ∈ connectorEnds M (part i) := by
    intro v
    by_cases hv : v ∈ part i
    · rw [hZin v hv]
      exact ⟨fun h => ⟨hv, h⟩, fun ⟨_, h⟩ => h⟩
    · rw [hZout v hv, hR.deg_sup hdata v]
      exact ⟨fun h => absurd h (by norm_num), fun ⟨h, _⟩ => absurd h hv⟩
  have hJ := pairing_isPerfectMatchingOn (part i) (connectorEnds M (part i)) hZdeg hZE
  obtain ⟨P, hPH, h1, h2, hconn⟩ := (habs i).2.2.2 _ hJ
  set R' := restrictOut R (part i) ⊔ push P with hR'
  have hR'good : GoodLocal part W M H R' := by
    refine ⟨fun u v h => ?_, fun v hv => ?_⟩
    · rcases (sup_adj _ _ _ _).mp h with h | h
      · exact hR.adj u v h.1
      · obtain ⟨hu, hv, h⟩ := push_adj.mp h
        exact ⟨i, hu, hv, hPH h⟩
    · by_cases hvi : v ∈ part i
      · have : R'.neighborSet v = (push P).neighborSet v := by
          ext w
          simp only [mem_neighborSet, hR', sup_adj]
          constructor
          · rintro (⟨-, h, -⟩ | h)
            exacts [absurd hvi h, h]
          · exact Or.inr
        rw [this, ncard_push_neighborSet hvi]
        exact local_deg hdata h1 h2 ⟨v, hvi⟩
      · have : R'.neighborSet v = R.neighborSet v := by
          ext w
          simp only [mem_neighborSet, hR', sup_adj]
          constructor
          · rintro (⟨h, -, -⟩ | h)
            · exact h
            · exact absurd (push_adj.mp h).1 hvi
          · intro h
            exact Or.inl ⟨h, hvi, fun hw => hvi (hR.adj_part hdata h.symm hw)⟩
        rw [this]
        exact hR.deg v hv
  have hZle' : Z ≤ M ⊔ R' := sup_le_sup_left le_sup_left M
  have hin : ∀ c d : part i, (M ⊔ R').Reachable c d := by
    intro c d
    refine reachable_of_forall_adj Subtype.val (fun x y hxy => ?_) (hconn.preconnected c d)
    rcases (sup_adj _ _ _ _).mp hxy with hxy | hxy
    · have : R'.Adj x y := (le_sup_right : push P ≤ R') (push_adj.mpr ⟨x.2, y.2, hxy⟩)
      exact ((le_sup_right : R' ≤ M ⊔ R') this).reachable
    · exact hxy.2.2.2.mono hZle'
  have hstep : ∀ u v, (M ⊔ R).Adj u v → (M ⊔ R').Reachable u v := by
    intro u v h
    rcases (sup_adj _ _ _ _).mp h with h | h
    · exact ((le_sup_left : M ≤ M ⊔ R') h).reachable
    · by_cases hu : u ∈ part i
      · exact hin ⟨u, hu⟩ ⟨v, hR.adj_part hdata h hu⟩
      · have hv : v ∉ part i := fun hv => hu (hR.adj_part hdata h.symm hv)
        have : R'.Adj u v := (le_sup_left : restrictOut R (part i) ≤ R') ⟨h, hu, hv⟩
        exact ((le_sup_right : R' ≤ M ⊔ R') this).reachable
  refine ⟨R', hR'good, ?_⟩
  let f : (M ⊔ R).ConnectedComponent → (M ⊔ R').ConnectedComponent :=
    ConnectedComponent.lift (fun v => (M ⊔ R').connectedComponentMk v)
      (fun v w p _ => ConnectedComponent.sound (reachable_of_forall_adj id hstep p.reachable))
  apply natCard_lt_of_surj_not_inj f
  · intro C
    refine ConnectedComponent.ind (fun v => ?_) C
    exact ⟨(M ⊔ R).connectedComponentMk v, rfl⟩
  · intro hinj
    apply hab
    have : f ((M ⊔ R).connectedComponentMk a) = f ((M ⊔ R).connectedComponentMk b) := by
      simp only [f, ConnectedComponent.lift_mk]
      exact ConnectedComponent.sound (hin ⟨a, ha⟩ ⟨b, hb⟩)
    exact ConnectedComponent.exact (hinj this)

end Merging

end CycleMerging

/-- **Lemma 3.8 (Cycle merging).** Suppose the parts partition `V(X) \ W`, `M` is a family of
edges and paths with mutually distinct endpoints in the parts whose interiors partition `W`,
the contraction of `M` on the parts is connected, and for every part `i` the pair
`(H i, E_i)` is matching-absorbing, where `H i` is a spanning graph on the part using no edge of
`M` and `E_i` is the set of endpoints of `M` in the part. Then `X` is Hamiltonian. -/
theorem cycle_merging {V : Type u} [Fintype V] [DecidableEq V] (X : SimpleGraph V)
    {ι : Type*} (part : ι → Finset V) (W : Set V) (M : SimpleGraph V)
    (H : ∀ i, SimpleGraph (part i)) (hdata : IsMergingData X part W M H)
    (habs : ∀ i, IsMatchingAbsorbing (H i) (connectorEnds M (part i))) :
    X.IsHamiltonian := by
  classical
  obtain ⟨R0, hR0⟩ := CycleMerging.exists_goodLocal hdata habs
  suffices h : ∀ n, ∀ R, CycleMerging.GoodLocal part W M H R →
      Nat.card (M ⊔ R).ConnectedComponent = n → X.IsHamiltonian from h _ R0 hR0 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R hR hn
    by_cases hc : (M ⊔ R).Connected
    · exact CycleMerging.isHamiltonian_of_two_regular (hR.le hdata) (hR.deg_sup hdata) hc
    · obtain ⟨i, a, ha, b, hb, hab⟩ := CycleMerging.exists_split hdata habs hc
      obtain ⟨R', hR', hlt⟩ := CycleMerging.merge_step hdata habs hR i ha hb hab
      exact ih _ (hn ▸ hlt) R' hR' rfl

end Lovasz
