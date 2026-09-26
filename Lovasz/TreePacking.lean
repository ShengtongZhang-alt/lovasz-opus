/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.Defs

/-!
# The Nash-Williams–Tutte tree-packing theorem (classical input) and cut counting (6.4)

DAG nodes `K.trees` and `E6.4` of `docs/BLUEPRINT.md`; T. Kaiser, *A short proof of the
tree-packing theorem*, arXiv:0911.2809.

`tree_packing` follows Kaiser's proof, by induction on `k`. Edge sets are handled through
the connectivity relation `TreePack.Conn` (reflexive-transitive closure of adjacency) and
forests through bridges (`TreePack.IsBridge`); edge counts of forests come from counting the
classes of `Conn` (`TreePack.numClasses_union_eq`). Kaiser's partial order on
decompositions is the lexicographic order of `TreePack.score`, and a decomposition whose
first `k` classes are spanning trees and whose score is maximal has a connected last class
(`TreePack.main_step`). The cut condition `2k` gives Kaiser's partition condition by double
counting (`TreePack.step3`).

`cut_count` applies `tree_packing` with `k = ⌊μ/2⌋`: a vertex set `U` is determined by the
tree `F i` meeting its cut least, the set of edges of `F i` in the cut (fewer than
`3(j+1)` of them), and whether a fixed vertex lies in `U`.
-/

namespace Lovasz

open Finset

open Classical in
/-- The edge set `F` of a multigraph (edge ends `ends`) is a spanning tree. -/
def IsSpanningTreeEdges {V E : Type*} [Fintype V] (ends : E → V × V) (F : Finset E) : Prop :=
  F.card = Fintype.card V - 1 ∧
    (SimpleGraph.fromEdgeSet {z | ∃ e ∈ F, z = s((ends e).1, (ends e).2)}).Connected

namespace TreePack

variable {V E : Type*}

section Conn

variable (ends : E → V × V)

/-- The edge `e` joins `x` and `y` (in either orientation). -/
def Joins (e : E) (x y : V) : Prop := ends e = (x, y) ∨ ends e = (y, x)

/-- Connectivity through the edges of `F`. -/
def Conn (F : Set E) : V → V → Prop :=
  Relation.ReflTransGen fun x y => ∃ e ∈ F, Joins ends e x y

/-- `e` is a bridge of `F`: its ends are disconnected in `F \ {e}`. -/
def IsBridge (F : Set E) (e : E) : Prop := ¬ Conn ends (F \ {e}) (ends e).1 (ends e).2

/-- The edges of `F` whose ends lie in one class of `R`. -/
def Inner (R : V → V → Prop) (F : Set E) : Set E := {e | e ∈ F ∧ R (ends e).1 (ends e).2}

variable {ends}

lemma joins_symm {e : E} {x y : V} (h : Joins ends e x y) : Joins ends e y x := h.symm

lemma Conn.refl (F : Set E) (x : V) : Conn ends F x x := Relation.ReflTransGen.refl

lemma Conn.trans {F : Set E} {x y z : V} (h₁ : Conn ends F x y) (h₂ : Conn ends F y z) :
    Conn ends F x z := Relation.ReflTransGen.trans h₁ h₂

lemma Conn.symm {F : Set E} {x y : V} (h : Conn ends F x y) : Conn ends F y x := by
  induction h with
  | refl => exact Conn.refl F _
  | tail _ hst ih =>
    obtain ⟨e, he, hj⟩ := hst
    exact Relation.ReflTransGen.head ⟨e, he, joins_symm hj⟩ ih

lemma conn_equivalence (F : Set E) : Equivalence (Conn ends F) :=
  ⟨Conn.refl F, Conn.symm, Conn.trans⟩

lemma Conn.of_joins {F : Set E} {e : E} {x y : V} (he : e ∈ F) (h : Joins ends e x y) :
    Conn ends F x y := Relation.ReflTransGen.single ⟨e, he, h⟩

lemma Conn.edge {F : Set E} {e : E} (he : e ∈ F) : Conn ends F (ends e).1 (ends e).2 :=
  Conn.of_joins he (Or.inl rfl)

lemma Conn.mono {F G : Set E} (hFG : F ⊆ G) {x y : V} (h : Conn ends F x y) :
    Conn ends G x y := by
  induction h with
  | refl => exact Conn.refl G _
  | tail _ hst ih =>
    obtain ⟨e, he, hj⟩ := hst
    exact ih.trans (Conn.of_joins (hFG he) hj)

lemma Conn.of_forall {F G : Set E} (hFG : ∀ e ∈ F, Conn ends G (ends e).1 (ends e).2) {x y : V}
    (h : Conn ends F x y) : Conn ends G x y := by
  induction h with
  | refl => exact Conn.refl G _
  | tail _ hst ih =>
    obtain ⟨e, he, hj⟩ := hst
    rcases hj with hj | hj
    · exact ih.trans (by simpa [hj] using hFG e he)
    · exact ih.trans (by simpa [hj] using (hFG e he).symm)

lemma conn_empty_iff {x y : V} : Conn ends (∅ : Set E) x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hst _ => obtain ⟨e, he, _⟩ := hst; exact absurd he (Set.notMem_empty e)
  · rintro rfl; exact Conn.refl _ _

/-- The cut lemma: a path through `F` either avoids `f` or passes through its two ends. -/
lemma Conn.cut {F : Set E} (f : E) {x y : V} (h : Conn ends F x y) :
    Conn ends (F \ {f}) x y ∨
      (Conn ends (F \ {f}) x (ends f).1 ∧ Conn ends (F \ {f}) (ends f).2 y) ∨
      (Conn ends (F \ {f}) x (ends f).2 ∧ Conn ends (F \ {f}) (ends f).1 y) := by
  induction h with
  | refl => exact Or.inl (Conn.refl _ _)
  | @tail z w _ hst ih =>
    obtain ⟨e, he, hj⟩ := hst
    by_cases hef : e = f
    · rw [hef] at hj
      rcases hj with hj | hj <;> rw [hj] at ih ⊢ <;> dsimp only at ih ⊢
      · rcases ih with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
        · exact Or.inr (Or.inl ⟨h1, Conn.refl _ _⟩)
        · exact Or.inr (Or.inl ⟨h1, Conn.refl _ _⟩)
        · exact Or.inl h1
      · rcases ih with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
        · exact Or.inr (Or.inr ⟨h1, Conn.refl _ _⟩)
        · exact Or.inl h1
        · exact Or.inr (Or.inr ⟨h1, Conn.refl _ _⟩)
    · have hzw : Conn ends (F \ {f}) z w := Conn.of_joins ⟨he, hef⟩ hj
      rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (h1.trans hzw)
      · exact Or.inr (Or.inl ⟨h1, h2.trans hzw⟩)
      · exact Or.inr (Or.inr ⟨h1, h2.trans hzw⟩)

lemma conn_insert_iff {H : Set E} {f : E} {x y : V} :
    Conn ends (insert f H) x y ↔ Conn ends H x y ∨
      (Conn ends H x (ends f).1 ∧ Conn ends H (ends f).2 y) ∨
      (Conn ends H x (ends f).2 ∧ Conn ends H (ends f).1 y) := by
  have hsub : insert f H \ {f} ⊆ H := fun e he => by
    rcases he.1 with h | h
    · exact absurd h he.2
    · exact h
  have hsub' : H ⊆ insert f H := Set.subset_insert f H
  have hf : Conn ends (insert f H) (ends f).1 (ends f).2 := Conn.edge (Set.mem_insert f H)
  constructor
  · intro h
    rcases h.cut f with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (h.mono hsub)
    · exact Or.inr (Or.inl ⟨h1.mono hsub, h2.mono hsub⟩)
    · exact Or.inr (Or.inr ⟨h1.mono hsub, h2.mono hsub⟩)
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h.mono hsub'
    · exact ((h1.mono hsub').trans hf).trans (h2.mono hsub')
    · exact ((h1.mono hsub').trans hf.symm).trans (h2.mono hsub')

lemma IsBridge.mono {F G : Set E} {e : E} (hFG : F ⊆ G) (h : IsBridge ends G e) :
    IsBridge ends F e :=
  fun h' => h (h'.mono (Set.sdiff_subset_sdiff_left hFG))

/-- Removing a bridge `d` of `F ⊇ G` does not disconnect two vertices that are connected
both in `G \ D` and in `F \ {d}`. -/
lemma conn_remove_bridge {F G D : Set E} {d : E} {u v : V} (hG : G ⊆ F)
    (hd : IsBridge ends F d) (h₁ : Conn ends (G \ D) u v) (h₂ : Conn ends (F \ {d}) u v) :
    Conn ends ((G \ D) \ {d}) u v := by
  have hsub : (G \ D) \ {d} ⊆ F \ {d} := fun x hx => ⟨hG hx.1.1, hx.2⟩
  rcases h₁.cut d with h | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact h
  · exact absurd (((ha.mono hsub).symm.trans h₂).trans (hb.mono hsub).symm) hd
  · exact absurd (((hb.mono hsub).trans h₂.symm).trans (ha.mono hsub)) hd

lemma conn_remove_bridges {F G : Set E} {u v : V} (D : Finset E) (hG : G ⊆ F)
    (hD : ∀ d ∈ D, IsBridge ends F d ∧ Conn ends (F \ {d}) u v) (h : Conn ends G u v) :
    Conn ends (G \ ↑D) u v := by
  classical
  induction D using Finset.induction_on with
  | empty => simpa using h
  | insert d D _ ih =>
    have h' := conn_remove_bridge hG (hD d (mem_insert_self _ _)).1
      (ih fun d' hd' => hD d' (mem_insert_of_mem hd')) (hD d (mem_insert_self _ _)).2
    have heq : G \ ↑(insert d D) = (G \ ↑D) \ {d} := by
      ext x; simp only [coe_insert, Set.mem_sdiff, Set.mem_insert_iff, Finset.mem_coe,
        Set.mem_singleton_iff]; tauto
    rw [heq]; exact h'

lemma inner_subset (R : V → V → Prop) (F : Set E) : Inner ends R F ⊆ F := fun _ he => he.1

lemma conn_inner_rel {R : V → V → Prop} (hR : Equivalence R) {F : Set E} {x y : V}
    (h : Conn ends (Inner ends R F) x y) : R x y := by
  induction h with
  | refl => exact hR.refl _
  | tail _ hst ih =>
    obtain ⟨e, ⟨_, he⟩, hj⟩ := hst
    rcases hj with hj | hj <;> rw [hj] at he
    · exact hR.trans ih he
    · exact hR.trans ih (hR.symm he)

end Conn

section Classes

variable [Fintype V]

open Classical in
/-- The equivalence classes of `R` (as vertex sets). -/
noncomputable def classes (R : V → V → Prop) : Finset (Finset V) :=
  univ.image fun x => univ.filter (R x)

/-- The number of classes of `R`. -/
noncomputable def numClasses (R : V → V → Prop) : ℕ := (classes R).card

open Classical in
lemma cls_eq {R : V → V → Prop} (hR : Equivalence R) {x y : V} (h : R x y) :
    univ.filter (R x) = univ.filter (R y) := by
  ext z; simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun hxz => hR.trans (hR.symm h) hxz, fun hyz => hR.trans h hyz⟩

open Classical in
/-- Merging two classes of an equivalence relation decreases the number of classes by one. -/
lemma numClasses_merge {R R' : V → V → Prop} (hR : Equivalence R) {a b : V} (hab : ¬ R a b)
    (hR' : ∀ x y, R' x y ↔ R x y ∨ (R x a ∧ R b y) ∨ (R x b ∧ R a y)) :
    numClasses R' + 1 = numClasses R := by
  set cl : V → Finset V := fun x => univ.filter (R x) with hcl
  set S : Finset (Finset V) := (univ.filter fun x => ¬ R x a ∧ ¬ R x b).image cl with hS
  have hmemcl : ∀ x y, y ∈ cl x ↔ R x y := fun x y => by simp [cl]
  have hA : classes R = insert (cl a) (insert (cl b) S) := by
    ext X
    simp only [classes, mem_image, mem_univ, true_and, mem_insert, hS, mem_filter]
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hxa : R x a
      · exact Or.inl (cls_eq hR hxa)
      · by_cases hxb : R x b
        · exact Or.inr (Or.inl (cls_eq hR hxb))
        · exact Or.inr (Or.inr ⟨x, ⟨hxa, hxb⟩, rfl⟩)
    · rintro (rfl | rfl | ⟨x, _, rfl⟩)
      · exact ⟨a, rfl⟩
      · exact ⟨b, rfl⟩
      · exact ⟨x, rfl⟩
  have key1 : ∀ x, R x a → univ.filter (R' x) = cl a ∪ cl b := by
    intro x hxa
    have hxb : ¬ R x b := fun hxb => hab (hR.trans (hR.symm hxa) hxb)
    ext y; simp only [mem_filter, mem_univ, true_and, mem_union, hmemcl, hR']
    constructor
    · rintro (h | ⟨_, h⟩ | ⟨h, _⟩)
      · exact Or.inl (hR.trans (hR.symm hxa) h)
      · exact Or.inr h
      · exact absurd h hxb
    · rintro (h | h)
      · exact Or.inl (hR.trans hxa h)
      · exact Or.inr (Or.inl ⟨hxa, h⟩)
  have key2 : ∀ x, R x b → univ.filter (R' x) = cl a ∪ cl b := by
    intro x hxb
    have hxa : ¬ R x a := fun hxa => hab (hR.trans (hR.symm hxa) hxb)
    ext y; simp only [mem_filter, mem_univ, true_and, mem_union, hmemcl, hR']
    constructor
    · rintro (h | ⟨h, _⟩ | ⟨_, h⟩)
      · exact Or.inr (hR.trans (hR.symm hxb) h)
      · exact absurd h hxa
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr (Or.inr ⟨hxb, h⟩)
      · exact Or.inl (hR.trans hxb h)
  have key3 : ∀ x, ¬ R x a → ¬ R x b → univ.filter (R' x) = cl x := by
    intro x hxa hxb
    ext y; simp only [mem_filter, mem_univ, true_and, hmemcl, hR']
    constructor
    · rintro (h | ⟨h, _⟩ | ⟨h, _⟩)
      · exact h
      · exact absurd h hxa
      · exact absurd h hxb
    · exact fun h => Or.inl h
  have hB : classes R' = insert (cl a ∪ cl b) S := by
    ext X
    simp only [classes, mem_image, mem_univ, true_and, mem_insert, hS, mem_filter]
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hxa : R x a
      · exact Or.inl (key1 x hxa)
      · by_cases hxb : R x b
        · exact Or.inl (key2 x hxb)
        · exact Or.inr ⟨x, ⟨hxa, hxb⟩, (key3 x hxa hxb).symm⟩
    · rintro (rfl | ⟨x, ⟨hxa, hxb⟩, rfl⟩)
      · exact ⟨a, key1 a (hR.refl a)⟩
      · exact ⟨x, key3 x hxa hxb⟩
  have hmemS : ∀ X ∈ S, a ∉ X ∧ b ∉ X := by
    intro X hX
    simp only [hS, mem_image, mem_filter, mem_univ, true_and] at hX
    obtain ⟨x, ⟨hxa, hxb⟩, rfl⟩ := hX
    exact ⟨fun h => hxa ((hmemcl x a).mp h), fun h => hxb ((hmemcl x b).mp h)⟩
  have haa : a ∈ cl a := (hmemcl a a).mpr (hR.refl a)
  have hbb : b ∈ cl b := (hmemcl b b).mpr (hR.refl b)
  have h1 : cl a ∉ S := fun h => (hmemS _ h).1 haa
  have h2 : cl b ∉ S := fun h => (hmemS _ h).2 hbb
  have h3 : cl a ≠ cl b := fun h => hab ((hmemcl a b).mp (h ▸ hbb))
  have h4 : cl a ∪ cl b ∉ S := fun h => (hmemS _ h).1 (mem_union_left _ haa)
  unfold numClasses
  rw [hA, hB, card_insert_of_notMem h4, card_insert_of_notMem, card_insert_of_notMem h2]
  simp only [mem_insert, not_or]
  exact ⟨h3, h1⟩

open Classical in
lemma numClasses_eq_card {R : V → V → Prop} (hR : ∀ x y, R x y ↔ x = y) :
    numClasses R = Fintype.card V := by
  unfold numClasses classes
  rw [card_image_of_injective, card_univ]
  intro x y hxy
  have hxy' : univ.filter (R x) = univ.filter (R y) := hxy
  have : y ∈ univ.filter (R y) := by simp [hR]
  rw [← hxy'] at this
  simpa [hR] using this

open Classical in
lemma numClasses_eq_one [Nonempty V] {R : V → V → Prop} (hR : ∀ x y, R x y) :
    numClasses R = 1 := by
  unfold numClasses classes
  rw [card_eq_one]
  refine ⟨univ, ?_⟩
  ext X
  simp only [mem_image, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨x, rfl⟩; ext y; simp [hR]
  · rintro rfl; exact ⟨Classical.arbitrary V, by ext y; simp [hR]⟩

open Classical in
lemma two_le_numClasses {R : V → V → Prop} (hR : Equivalence R) {x y : V} (h : ¬ R x y) :
    2 ≤ numClasses R := by
  unfold numClasses
  rw [Nat.succ_le_iff, one_lt_card]
  refine ⟨univ.filter (R x), mem_image_of_mem _ (mem_univ x), univ.filter (R y),
    mem_image_of_mem _ (mem_univ y), fun hxy => h ?_⟩
  have : y ∈ univ.filter (R y) := by simp [hR.refl y]
  rw [← hxy] at this
  simpa using this

variable {ends : E → V × V}

lemma numClasses_conn_insert (H : Set E) (f : E) :
    numClasses (Conn ends H) ≤ numClasses (Conn ends (insert f H)) + 1 ∧
      (¬ Conn ends H (ends f).1 (ends f).2 →
        numClasses (Conn ends (insert f H)) + 1 = numClasses (Conn ends H)) := by
  by_cases hc : Conn ends H (ends f).1 (ends f).2
  · have heq : Conn ends (insert f H) = Conn ends H := by
      funext x y
      apply propext
      rw [conn_insert_iff]
      constructor
      · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact h
        · exact (h1.trans hc).trans h2
        · exact (h1.trans hc.symm).trans h2
      · exact fun h => Or.inl h
    rw [heq]
    exact ⟨Nat.le_succ _, fun h => absurd hc h⟩
  · have := numClasses_merge (conn_equivalence H) hc (fun x y => conn_insert_iff)
    exact ⟨this.ge, fun _ => this⟩

lemma numClasses_union_le (H : Set E) (B : Finset E) :
    numClasses (Conn ends H) ≤ numClasses (Conn ends (H ∪ ↑B)) + B.card := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb ih =>
    rw [coe_insert, Set.union_insert, card_insert_of_notMem hb]
    have := (numClasses_conn_insert (ends := ends) (H ∪ ↑B) b).1
    omega

lemma numClasses_union_eq (H : Set E) (B : Finset E) (hdisj : ∀ b ∈ B, b ∉ H)
    (hbr : ∀ b ∈ B, IsBridge ends (H ∪ ↑B) b) :
    numClasses (Conn ends (H ∪ ↑B)) + B.card = numClasses (Conn ends H) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb ih =>
    have hsub : H ∪ ↑B ⊆ H ∪ ↑(insert b B) := by
      rw [coe_insert]; exact Set.union_subset_union_right _ (Set.subset_insert _ _)
    have ih' := ih (fun b' hb' => hdisj b' (mem_insert_of_mem hb'))
      (fun b' hb' => (hbr b' (mem_insert_of_mem hb')).mono hsub)
    have hbb := hbr b (mem_insert_self b B)
    rw [coe_insert, Set.union_insert] at hbb ⊢
    have hdiff : insert b (H ∪ ↑B) \ {b} = H ∪ ↑B := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_union, Finset.mem_coe,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact absurd h hx
        · exact h
      · intro h
        refine ⟨Or.inr h, ?_⟩
        rintro rfl
        rcases h with h | h
        · exact hdisj x (mem_insert_self x B) h
        · exact hb h
    unfold IsBridge at hbb
    rw [hdiff] at hbb
    have := (numClasses_conn_insert (ends := ends) (H ∪ ↑B) b).2 hbb
    rw [card_insert_of_notMem hb]
    omega

end Classes

section SpTree

variable [Fintype V] (ends : E → V × V)

/-- `F` is the edge set of a spanning tree (in the counting form). -/
def SpTree (F : Finset E) : Prop :=
  F.card + 1 = Fintype.card V ∧ ∀ x y, Conn ends (↑F : Set E) x y

variable {ends}

lemma card_le_of_conn [Nonempty V] (F : Finset E) (h : ∀ x y, Conn ends (↑F : Set E) x y) :
    Fintype.card V ≤ F.card + 1 := by
  have h1 := numClasses_union_le (ends := ends) ∅ F
  rw [Set.empty_union, numClasses_eq_card (fun _ _ => conn_empty_iff), numClasses_eq_one h] at h1
  omega

lemma SpTree.isBridge {T : Finset E} (hT : SpTree ends T) {e : E} (he : e ∈ T) :
    IsBridge ends ↑T e := by
  classical
  intro h
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by rw [← hT.1]; omega)
  have hc : ∀ x y, Conn ends (↑(T.erase e) : Set E) x y := by
    intro x y
    rw [coe_erase]
    refine Conn.of_forall (fun f hf => ?_) (hT.2 x y)
    by_cases hfe : f = e
    · subst hfe; exact h
    · exact Conn.edge ⟨hf, hfe⟩
  have h1 := card_le_of_conn _ hc
  rw [card_erase_of_mem he] at h1
  have h2 := hT.1
  have h3 : 0 < T.card := card_pos.mpr ⟨e, he⟩
  omega

lemma exists_spTree_of_conn [Nonempty V] (F : Finset E) (h : ∀ x y, Conn ends (↑F : Set E) x y) :
    ∃ F' ⊆ F, SpTree ends F' := by
  classical
  induction F using Finset.strongInduction with
  | H F ih =>
    by_cases hb : ∃ e ∈ F, ¬ IsBridge ends ↑F e
    · obtain ⟨e, he, hnb⟩ := hb
      unfold IsBridge at hnb
      rw [not_not] at hnb
      have hc : ∀ x y, Conn ends (↑(F.erase e) : Set E) x y := by
        intro x y
        rw [coe_erase]
        refine Conn.of_forall (fun f hf => ?_) (h x y)
        by_cases hfe : f = e
        · subst hfe; exact hnb
        · exact Conn.edge ⟨hf, hfe⟩
      obtain ⟨F', hF', hsp⟩ := ih (F.erase e) (erase_ssubset he) hc
      exact ⟨F', hF'.trans (erase_subset e F), hsp⟩
    · have hb' : ∀ e ∈ F, IsBridge ends ↑F e := fun e he => not_not.mp fun h => hb ⟨e, he, h⟩
      have h1 := numClasses_union_eq (ends := ends) ∅ F (by simp) (by simpa using hb')
      rw [Set.empty_union, numClasses_eq_card (fun _ _ => conn_empty_iff),
        numClasses_eq_one h] at h1
      exact ⟨F, subset_refl _, by omega, h⟩

/-- The exchange lemma: adding `e` and deleting an edge `e'` on the cycle it closes keeps a
spanning tree. -/
lemma SpTree.exchange [DecidableEq E] {T : Finset E} (hT : SpTree ends T) {e e' : E} (he : e ∉ T) (he' : e' ∈ T)
    (h : ¬ Conn ends (↑T \ {e'}) (ends e).1 (ends e).2) :
    SpTree ends (insert e (T.erase e')) := by
  refine ⟨?_, fun x y => ?_⟩
  · rw [card_insert_of_notMem (fun h' => he (mem_of_mem_erase h')), card_erase_of_mem he']
    have := hT.1
    have : 0 < T.card := card_pos.mpr ⟨e', he'⟩
    omega
  · rw [coe_insert, coe_erase]
    refine Conn.of_forall (fun f hf => ?_) (hT.2 x y)
    by_cases hfe : f = e'
    · subst hfe
      have hsub : (↑T : Set E) \ {f} ⊆ insert e (↑T \ {f}) := Set.subset_insert _ _
      have hee : Conn ends (insert e (↑T \ {f})) (ends e).1 (ends e).2 :=
        Conn.edge (Set.mem_insert _ _)
      rcases (hT.2 (ends e).1 (ends e).2).cut f with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h1 h
      · exact ((h1.mono hsub).symm.trans hee).trans (h2.mono hsub).symm
      · exact ((h2.mono hsub).trans hee.symm).trans (h1.mono hsub)
    · exact Conn.edge (Set.mem_insert_of_mem _ ⟨hf, hfe⟩)

omit [Fintype V] in
lemma conn_iff_reachable (F : Finset E) (x y : V) :
    Conn ends (↑F : Set E) x y ↔
      (SimpleGraph.fromEdgeSet {z | ∃ e ∈ F, z = s((ends e).1, (ends e).2)}).Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail z w _ hst ih =>
      obtain ⟨e, he, hj⟩ := hst
      by_cases hzw : z = w
      · subst hzw; exact ih
      · refine ih.tail ?_
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨⟨e, he, ?_⟩, hzw⟩
        rcases hj with hj | hj <;> rw [hj]
        exact Sym2.eq_swap
  · intro h
    induction h with
    | refl => exact Conn.refl _ _
    | @tail z w _ hst ih =>
      rw [SimpleGraph.fromEdgeSet_adj] at hst
      obtain ⟨⟨e, he, hze⟩, _⟩ := hst
      refine ih.trans (Conn.of_joins (e := e) (Finset.mem_coe.mpr he) ?_)
      rcases Sym2.eq_iff.mp hze with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Prod.ext h1.symm h2.symm)
      · exact Or.inr (Prod.ext h2.symm h1.symm)

lemma isSpanningTreeEdges_iff [Nonempty V] (F : Finset E) :
    IsSpanningTreeEdges ends F ↔ SpTree ends F := by
  unfold IsSpanningTreeEdges SpTree
  rw [SimpleGraph.connected_iff]
  have hpos := Fintype.card_pos (α := V)
  simp only [SimpleGraph.Preconnected, ← conn_iff_reachable]
  constructor
  · rintro ⟨h1, h2, _⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2, inferInstance⟩

end SpTree

section Counting

lemma geom_le_pow (m t : ℕ) : ∑ i ∈ range (t + 1), m ^ i ≤ (m + 1) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, pow_succ (m + 1)]
    have : m ^ (t + 1) ≤ m * (m + 1) ^ t := by
      rw [pow_succ']; exact Nat.mul_le_mul_left m (Nat.pow_le_pow_left (Nat.le_succ m) t)
    nlinarith

/-- There are at most `(|E| + 1)^t` sets of at most `t` edges. -/
lemma card_small_subsets (E : Type*) [Fintype E] (t : ℕ) :
    (univ.filter fun D : Finset E => D.card ≤ t).card ≤ (Fintype.card E + 1) ^ t := by
  classical
  have hsub : (univ.filter fun D : Finset E => D.card ≤ t) ⊆
      (range (t + 1)).biUnion fun i => powersetCard i (univ : Finset E) := by
    intro D hD
    simp only [mem_filter, mem_univ, true_and] at hD
    simp only [mem_biUnion, mem_range, mem_powersetCard]
    exact ⟨D.card, by omega, subset_univ D, rfl⟩
  calc (univ.filter fun D : Finset E => D.card ≤ t).card
      ≤ ((range (t + 1)).biUnion fun i => powersetCard i (univ : Finset E)).card :=
        card_le_card hsub
    _ ≤ ∑ i ∈ range (t + 1), (powersetCard i (univ : Finset E)).card := card_biUnion_le
    _ = ∑ i ∈ range (t + 1), (Fintype.card E).choose i := by
        simp only [card_powersetCard, card_univ]
    _ ≤ ∑ i ∈ range (t + 1), (Fintype.card E) ^ i :=
        sum_le_sum fun i _ => Nat.choose_le_pow _ _
    _ ≤ (Fintype.card E + 1) ^ t := geom_le_pow _ _

end Counting

section Partition

/-! ### Kaiser's sequence of partitions

For a colouring of the edges (colour classes `T c`, `c < K`), `part T K i` is the partition
`P_i` of Kaiser's proof, as an equivalence relation: `P_0` is trivial, and `P_{i+1}` splits
every class of `P_i` into the components of the least colour class that disconnects some
class of `P_i` (if there is none, the sequence stops). -/

variable (ends : E → V × V)

/-- Colour `c` disconnects some class of `R`. -/
def Bad (T : ℕ → Set E) (R : V → V → Prop) (c : ℕ) : Prop :=
  ∃ x y, R x y ∧ ¬ Conn ends (Inner ends R (T c)) x y

open Classical in
/-- The least colour `< K` disconnecting some class of `R`, or `K` if there is none. -/
noncomputable def nextCol (T : ℕ → Set E) (K : ℕ) (R : V → V → Prop) : ℕ :=
  if h : ∃ c, c < K ∧ Bad ends T R c then Nat.find h else K

/-- The refinement step. -/
noncomputable def nextPart (T : ℕ → Set E) (K : ℕ) (R : V → V → Prop) : V → V → Prop :=
  if nextCol ends T K R < K then Conn ends (Inner ends R (T (nextCol ends T K R))) else R

/-- Kaiser's sequence of partitions `P_i`. -/
noncomputable def part (T : ℕ → Set E) (K : ℕ) : ℕ → V → V → Prop
  | 0 => fun _ _ => True
  | i + 1 => nextPart ends T K (part T K i)

open Classical in
/-- The `i`-th digit of the lexicographic score: the refinement order on `P_i`, then `c_i`. -/
noncomputable def digit [Fintype V] (T : ℕ → Set E) (K : ℕ) (i : ℕ) : ℕ :=
  (univ.filter fun p : V × V => part ends T K i p.1 p.2).card * (K + 1) +
    nextCol ends T K (part ends T K i)

/-- The lexicographic score of a colouring (Kaiser's order `≺`). -/
noncomputable def score [Fintype V] (T : ℕ → Set E) (K : ℕ) : Lex (ℕ → ℕ) :=
  toLex (digit ends T K)

variable {ends}

open Classical in
lemma nextCol_le (T : ℕ → Set E) (K : ℕ) (R : V → V → Prop) : nextCol ends T K R ≤ K := by
  unfold nextCol
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_refl K

open Classical in
lemma bad_nextCol {T : ℕ → Set E} {K : ℕ} {R : V → V → Prop} (h : nextCol ends T K R < K) :
    Bad ends T R (nextCol ends T K R) := by
  unfold nextCol at h ⊢
  split_ifs at h ⊢ with h'
  · exact (Nat.find_spec h').2
  · exact absurd h (lt_irrefl K)

open Classical in
lemma not_bad_of_lt_nextCol {T : ℕ → Set E} {K : ℕ} {R : V → V → Prop} {c : ℕ}
    (hc : c < nextCol ends T K R) : ¬ Bad ends T R c := by
  intro hb
  unfold nextCol at hc
  split_ifs at hc with h'
  · exact Nat.find_min h' hc ⟨hc.trans (Nat.find_spec h').1, hb⟩
  · exact h' ⟨c, hc, hb⟩

lemma le_nextCol {T : ℕ → Set E} {K : ℕ} {R : V → V → Prop} {c : ℕ} (hc : c ≤ K)
    (h : ∀ c' < c, ¬ Bad ends T R c') : c ≤ nextCol ends T K R := by
  by_contra hlt
  rw [not_le] at hlt
  exact h _ hlt (bad_nextCol (lt_of_lt_of_le hlt hc))

lemma part_succ (T : ℕ → Set E) (K i : ℕ) :
    part ends T K (i + 1) = nextPart ends T K (part ends T K i) := rfl

lemma part_equiv (T : ℕ → Set E) (K : ℕ) : ∀ i, Equivalence (part ends T K i)
  | 0 => ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩
  | i + 1 => by
    rw [part_succ]
    unfold nextPart
    split_ifs
    · exact conn_equivalence _
    · exact part_equiv T K i

lemma part_succ_of_lt {T : ℕ → Set E} {K i : ℕ} (h : nextCol ends T K (part ends T K i) < K) :
    part ends T K (i + 1) =
      Conn ends (Inner ends (part ends T K i) (T (nextCol ends T K (part ends T K i)))) := by
  rw [part_succ]; unfold nextPart; simp only [h, ↓reduceIte]

lemma part_succ_of_not_lt {T : ℕ → Set E} {K i : ℕ}
    (h : ¬ nextCol ends T K (part ends T K i) < K) :
    part ends T K (i + 1) = part ends T K i := by
  rw [part_succ]; unfold nextPart; simp only [h, ↓reduceIte]

lemma part_succ_le (T : ℕ → Set E) (K i : ℕ) {x y : V} (h : part ends T K (i + 1) x y) :
    part ends T K i x y := by
  by_cases hc : nextCol ends T K (part ends T K i) < K
  · rw [part_succ_of_lt hc] at h
    exact conn_inner_rel (part_equiv T K i) h
  · rwa [part_succ_of_not_lt hc] at h

lemma part_anti {T : ℕ → Set E} {K : ℕ} {i j : ℕ} (hij : i ≤ j) :
    ∀ {x y : V}, part ends T K j x y → part ends T K i x y := by
  induction j, hij using Nat.le_induction with
  | base => exact fun h => h
  | succ j _ ih => exact fun h => ih (part_succ_le T K j h)

open Classical in
lemma exists_stable [Fintype V] (T : ℕ → Set E) (K : ℕ) :
    ∃ N, nextCol ends T K (part ends T K N) = K := by
  by_contra hno
  simp only [not_exists] at hno
  set pc : ℕ → ℕ := fun i => (univ.filter fun p : V × V => part ends T K i p.1 p.2).card
  have hstep : ∀ i, pc (i + 1) < pc i := by
    intro i
    have hlt : nextCol ends T K (part ends T K i) < K :=
      lt_of_le_of_ne (nextCol_le _ _ _) (hno i)
    obtain ⟨x, y, hxy, hn⟩ := bad_nextCol hlt
    apply card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(x, y), by simpa using hxy, ?_⟩
      simp only [mem_filter, mem_univ, true_and]
      rw [part_succ_of_lt hlt]
      exact hn
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      exact part_succ_le T K i hp
  have hbound : ∀ i, pc i + i ≤ pc 0 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => have := hstep i; omega
  have := hbound (pc 0 + 1)
  omega

open Classical in
lemma score_lt [Fintype V] {T T' : ℕ → Set E} {K j : ℕ}
    (hpre : ∀ i < j, part ends T K i = part ends T' K i ∧
      nextCol ends T K (part ends T K i) = nextCol ends T' K (part ends T' K i))
    (hj : ((∀ x y, part ends T K j x y → part ends T' K j x y) ∧
        ∃ x y, part ends T' K j x y ∧ ¬ part ends T K j x y) ∨
      (part ends T K j = part ends T' K j ∧
        nextCol ends T K (part ends T K j) < nextCol ends T' K (part ends T' K j))) :
    score ends T K < score ends T' K := by
  refine ⟨j, fun i hi => ?_, ?_⟩
  · show digit ends T K i = digit ends T' K i
    simp only [digit]
    rw [(hpre i hi).2, (hpre i hi).1]
  · show digit ends T K j < digit ends T' K j
    simp only [digit]
    rcases hj with ⟨hle, x, y, hxy, hnxy⟩ | ⟨heq, hlt⟩
    · have hcard : (univ.filter fun p : V × V => part ends T K j p.1 p.2).card <
          (univ.filter fun p : V × V => part ends T' K j p.1 p.2).card := by
        apply card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨(x, y), by simpa using hxy, by simpa using hnxy⟩
        · intro p hp
          simp only [mem_filter, mem_univ, true_and] at hp ⊢
          exact hle _ _ hp
      have h1 := nextCol_le (ends := ends) T K (part ends T K j)
      set a := (univ.filter fun p : V × V => part ends T K j p.1 p.2).card
      set a' := (univ.filter fun p : V × V => part ends T' K j p.1 p.2).card
      have h2 : (a + 1) * (K + 1) ≤ a' * (K + 1) := Nat.mul_le_mul_right _ hcard
      nlinarith
    · rw [heq] at hlt ⊢
      omega

/-- Kaiser's Claim 2: if every colour class of `T'` keeps the classes of `P_j` (`j ≤ m`)
connected whenever `T` does, and `T'` is not better than `T`, then `T` and `T'` have the same
partitions `P_j` and colours `c_j` for `j ≤ m`. -/
lemma claim2 [Fintype V] {T T' : ℕ → Set E} {K m : ℕ}
    (hC1 : ∀ j ≤ m, ∀ c x y, Conn ends (Inner ends (part ends T K j) (T c)) x y →
      Conn ends (Inner ends (part ends T K j) (T' c)) x y)
    (hle : score ends T' K ≤ score ends T K) :
    ∀ j ≤ m, part ends T' K j = part ends T K j ∧
      nextCol ends T' K (part ends T' K j) = nextCol ends T K (part ends T K j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hpre : ∀ i < j, part ends T K i = part ends T' K i ∧
        nextCol ends T K (part ends T K i) = nextCol ends T' K (part ends T' K i) :=
      fun i hi => ⟨(ih i hi (by omega)).1.symm, (ih i hi (by omega)).2.symm⟩
    have hPj : part ends T' K j = part ends T K j := by
      cases j with
      | zero => rfl
      | succ i =>
        obtain ⟨h1, h2⟩ := ih i (Nat.lt_succ_self i) (by omega)
        have hle' : ∀ x y, part ends T K (i + 1) x y → part ends T' K (i + 1) x y := by
          intro x y hxy
          by_cases hc : nextCol ends T K (part ends T K i) < K
          · have hc' : nextCol ends T' K (part ends T' K i) < K := by rw [h2]; exact hc
            rw [part_succ_of_lt hc] at hxy
            rw [part_succ_of_lt hc', h2, h1]
            exact hC1 i (by omega) _ x y hxy
          · have hc' : ¬ nextCol ends T' K (part ends T' K i) < K := by rw [h2]; exact hc
            rw [part_succ_of_not_lt hc] at hxy
            rw [part_succ_of_not_lt hc', h1]
            exact hxy
        by_contra hne
        have hex2 : ∃ x y, part ends T' K (i + 1) x y ∧ ¬ part ends T K (i + 1) x y := by
          by_contra hno
          simp only [not_exists, not_and, not_not] at hno
          exact hne (funext fun x => funext fun y => propext ⟨hno x y, hle' x y⟩)
        exact absurd (score_lt hpre (Or.inl ⟨hle', hex2⟩)) (not_lt.mpr hle)
    refine ⟨hPj, ?_⟩
    have hge : nextCol ends T K (part ends T K j) ≤ nextCol ends T' K (part ends T' K j) := by
      rw [hPj]
      apply le_nextCol (nextCol_le _ _ _)
      intro c hc hbad
      obtain ⟨x, y, hxy, hnc⟩ := hbad
      apply hnc
      apply hC1 j hj c x y
      by_contra h
      exact not_bad_of_lt_nextCol hc ⟨x, y, hxy, h⟩
    by_contra hne
    have hlt : nextCol ends T K (part ends T K j) < nextCol ends T' K (part ends T' K j) :=
      lt_of_le_of_ne hge (Ne.symm hne)
    exact absurd (score_lt hpre (Or.inr ⟨hPj.symm, hlt⟩)) (not_lt.mpr hle)

/-- The end of Kaiser's argument: under the hypotheses of `claim2`, the colour class
`T' c_m` cannot join two vertices that `T c_m` leaves in different classes of `P_{m+1}`. -/
lemma claim_final [Fintype V] {T T' : ℕ → Set E} {K m : ℕ}
    (hC1 : ∀ j ≤ m, ∀ c x y, Conn ends (Inner ends (part ends T K j) (T c)) x y →
      Conn ends (Inner ends (part ends T K j) (T' c)) x y)
    (hle : score ends T' K ≤ score ends T K)
    (hcm : nextCol ends T K (part ends T K m) < K) {x y : V}
    (hnew : Conn ends (Inner ends (part ends T K m) (T' (nextCol ends T K (part ends T K m)))) x y)
    (hold : ¬ part ends T K (m + 1) x y) : False := by
  have hC2 := claim2 hC1 hle
  have hpre : ∀ i < m + 1, part ends T K i = part ends T' K i ∧
      nextCol ends T K (part ends T K i) = nextCol ends T' K (part ends T' K i) :=
    fun i hi => ⟨(hC2 i (by omega)).1.symm, (hC2 i (by omega)).2.symm⟩
  obtain ⟨h1, h2⟩ := hC2 m le_rfl
  have hcm' : nextCol ends T' K (part ends T' K m) < K := by rw [h2]; exact hcm
  have hle' : ∀ x y, part ends T K (m + 1) x y → part ends T' K (m + 1) x y := by
    intro x y hxy
    rw [part_succ_of_lt hcm] at hxy
    rw [part_succ_of_lt hcm', h2, h1]
    exact hC1 m le_rfl _ x y hxy
  have hnew' : part ends T' K (m + 1) x y := by
    rw [part_succ_of_lt hcm', h2, h1]
    exact hnew
  exact absurd (score_lt hpre (Or.inl ⟨hle', x, y, hnew', hold⟩)) (not_lt.mpr hle)

end Partition

/-! ### Colourings -/

/-- Colour class `c` of `col`, as a set. -/
def colSet {E : Type*} {k : ℕ} (col : E → Fin (k + 1)) (c : ℕ) : Set E :=
  {e | (col e : ℕ) = c}

open Classical in
/-- Colour class `c` of `col`, as a finset. -/
noncomputable def colFin {E : Type*} [Fintype E] {k : ℕ} (col : E → Fin (k + 1)) (c : ℕ) :
    Finset E :=
  univ.filter fun e => (col e : ℕ) = c

lemma coe_colFin {E : Type*} [Fintype E] {k : ℕ} (col : E → Fin (k + 1)) (c : ℕ) :
    (↑(colFin col c) : Set E) = colSet col c := by
  ext e; simp [colFin, colSet]

/-- The first `k` colour classes of `col` are spanning trees. -/
def Valid [Fintype V] [Fintype E] (ends : E → V × V) (k : ℕ) (col : E → Fin (k + 1)) : Prop :=
  ∀ c < k, SpTree ends (colFin col c)

open Classical in
/-- The edges of the cut `(U, V \ U)`. -/
noncomputable def cutSet [DecidableEq V] [Fintype E] (ends : E → V × V) (U : Finset V) :
    Finset E :=
  univ.filter fun e => ((ends e).1 ∈ U) ≠ ((ends e).2 ∈ U)

section Counting2

variable [Fintype V] [Fintype E] [DecidableEq V] {ends : E → V × V}

open Classical in
/-- Double counting: the cuts of the classes of `P` cover each edge between classes twice. -/
lemma sum_cut_classes_le (P : V → V → Prop) (hP : Equivalence P) :
    ∑ X ∈ classes P, (cutSet ends X).card ≤
      2 * (univ.filter fun e => ¬ P (ends e).1 (ends e).2).card := by
  set Cr := univ.filter fun e => ¬ P (ends e).1 (ends e).2 with hCr
  have hcls : ∀ X ∈ classes P, ∃ x, X = univ.filter (P x) := by
    intro X hX
    simp only [classes, mem_image, mem_univ, true_and] at hX
    obtain ⟨x, rfl⟩ := hX
    exact ⟨x, rfl⟩
  have hmemcut : ∀ x e, e ∈ cutSet ends (univ.filter (P x)) ↔
      (P x (ends e).1 ≠ P x (ends e).2) := by
    intro x e; simp [cutSet]
  have hsub : ∀ X ∈ classes P, cutSet ends X = Cr.filter (fun e => e ∈ cutSet ends X) := by
    intro X hX
    obtain ⟨x, rfl⟩ := hcls X hX
    ext e
    simp only [mem_filter, hCr, mem_univ, true_and]
    constructor
    · intro he
      refine ⟨fun hP12 => ?_, he⟩
      rw [hmemcut] at he
      apply he
      exact propext ⟨fun h => hP.trans h hP12, fun h => hP.trans h (hP.symm hP12)⟩
    · exact fun h => h.2
  have hle2 : ∀ e ∈ Cr, ((classes P).filter fun X => e ∈ cutSet ends X).card ≤ 2 := by
    intro e _
    have hs : ((classes P).filter fun X => e ∈ cutSet ends X) ⊆
        {univ.filter (P (ends e).1), univ.filter (P (ends e).2)} := by
      intro X hX
      rw [mem_filter] at hX
      obtain ⟨x, rfl⟩ := hcls X hX.1
      have h := (hmemcut x e).mp hX.2
      simp only [mem_insert, mem_singleton]
      by_cases h1 : P x (ends e).1
      · exact Or.inl (cls_eq hP h1)
      · have h2 : P x (ends e).2 := by
          by_contra h2
          exact h (propext ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩)
        exact Or.inr (cls_eq hP h2)
    exact (card_le_card hs).trans (card_insert_le _ _)
  calc ∑ X ∈ classes P, (cutSet ends X).card
      = ∑ X ∈ classes P, (Cr.filter fun e => e ∈ cutSet ends X).card :=
        sum_congr rfl fun X hX => by rw [← hsub X hX]
    _ = ∑ e ∈ Cr, ((classes P).filter fun X => e ∈ cutSet ends X).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    _ ≤ ∑ _e ∈ Cr, 2 := sum_le_sum hle2
    _ = 2 * Cr.card := by rw [sum_const, smul_eq_mul, mul_comm]

open Classical in
/-- The counting step of Kaiser's proof: if the stable partition `P` has every colour class
connected on each class, the first `k` classes are spanning trees and the last one is
disconnected, then some non-bridge edge of the last class joins two classes of `P`. -/
lemma step3 {k : ℕ}
    (hcut : ∀ U : Finset V, U.Nonempty → U ≠ univ → 2 * (k + 1) ≤ (cutSet ends U).card)
    (col : E → Fin (k + 1)) (hval : Valid ends k col)
    (hdisc : ¬ ∀ x y, Conn ends (colSet col k) x y)
    (P : V → V → Prop) (hP : Equivalence P)
    (hconn : ∀ c < k + 1, ∀ x y, P x y → Conn ends (Inner ends P (colSet col c)) x y) :
    ∃ e ∈ colSet col k, ¬ IsBridge ends (colSet col k) e ∧ ¬ P (ends e).1 (ends e).2 := by
  by_contra hno
  have hbr : ∀ e ∈ colSet col k, ¬ P (ends e).1 (ends e).2 → IsBridge ends (colSet col k) e :=
    fun e he hPe => by_contra fun h => hno ⟨e, he, h, hPe⟩
  set N := numClasses P with hN
  set B : ℕ → Finset E :=
    fun c => univ.filter fun e => (col e : ℕ) = c ∧ ¬ P (ends e).1 (ends e).2 with hB
  have hsplit : ∀ c, colSet col c = Inner ends P (colSet col c) ∪ ↑(B c) := by
    intro c; ext e
    simp only [colSet, Inner, hB, Set.mem_union, Set.mem_ofPred_eq, coe_filter, mem_univ,
      true_and]
    tauto
  have hdisjB : ∀ c, ∀ b ∈ B c, b ∉ Inner ends P (colSet col c) := by
    intro c b hb hin
    simp only [hB, mem_filter, mem_univ, true_and] at hb
    exact hb.2 hin.2
  have hinner : ∀ c < k + 1, Conn ends (Inner ends P (colSet col c)) = P := by
    intro c hc; funext x y; apply propext
    exact ⟨conn_inner_rel hP, hconn c hc x y⟩
  have hcount : ∀ c < k + 1, numClasses (Conn ends (colSet col c)) + (B c).card = N := by
    intro c hc
    have hbrc : ∀ b ∈ B c, IsBridge ends (Inner ends P (colSet col c) ∪ ↑(B c)) b := by
      intro b hb
      rw [← hsplit c]
      simp only [hB, mem_filter, mem_univ, true_and] at hb
      by_cases hck : c = k
      · subst hck; exact hbr b hb.1 hb.2
      · have hck' : c < k := by omega
        have := (hval c hck').isBridge (e := b) (by simp [colFin, hb.1])
        rwa [coe_colFin] at this
    have := numClasses_union_eq (ends := ends) (Inner ends P (colSet col c)) (B c) (hdisjB c) hbrc
    rw [← hsplit c, hinner c hc] at this
    exact this
  have htree : ∀ c < k, (B c).card + 1 = N := by
    intro c hc
    have h1 := hcount c (by omega)
    have h2 : numClasses (Conn ends (colSet col c)) = 1 := by
      have hne : Nonempty V := Fintype.card_pos_iff.mp (by have := (hval c hc).1; omega)
      apply numClasses_eq_one
      intro x y
      have := (hval c hc).2 x y
      rwa [coe_colFin] at this
    omega
  have hlast : (B k).card + 2 ≤ N := by
    have h1 := hcount k (by omega)
    simp only [not_forall] at hdisc
    obtain ⟨x, y, hxy⟩ := hdisc
    have h2 := two_le_numClasses (conn_equivalence (colSet col k)) hxy
    omega
  set Cr := univ.filter fun e => ¬ P (ends e).1 (ends e).2 with hCr
  have hCrsum : Cr.card = ∑ c ∈ range (k + 1), (B c).card := by
    rw [card_eq_sum_card_fiberwise (f := fun e => (col e : ℕ)) (t := range (k + 1))]
    · apply sum_congr rfl
      intro c _
      congr 1
      ext e
      simp only [hCr, hB, mem_filter, mem_univ, true_and]
      tauto
    · intro e _
      simp only [coe_range, Set.mem_Iio]
      exact (col e).isLt
  have hupper : Cr.card + k + 2 ≤ (k + 1) * N := by
    rw [hCrsum, sum_range_succ]
    have h1 : ∑ c ∈ range k, ((B c).card + 1) = k * N := by
      rw [sum_congr rfl fun c hc => htree c (mem_range.mp hc)]
      simp
    rw [sum_add_distrib] at h1
    simp only [sum_const, card_range, smul_eq_mul, mul_one] at h1
    nlinarith
  have hN2 : 2 ≤ N := by omega
  have hlower : N * (2 * (k + 1)) ≤ 2 * Cr.card := by
    calc N * (2 * (k + 1)) = ∑ _X ∈ classes P, 2 * (k + 1) := by
          rw [sum_const, smul_eq_mul, hN, numClasses]
      _ ≤ ∑ X ∈ classes P, (cutSet ends X).card := by
          apply sum_le_sum
          intro X hX
          simp only [classes, mem_image, mem_univ, true_and] at hX
          obtain ⟨x, rfl⟩ := hX
          apply hcut
          · exact ⟨x, by simp [hP.refl x]⟩
          · intro hX
            have hall : ∀ y z, P y z := by
              intro y z
              have hy : y ∈ univ.filter (P x) := by rw [hX]; exact mem_univ y
              have hz : z ∈ univ.filter (P x) := by rw [hX]; exact mem_univ z
              simp only [mem_filter, mem_univ, true_and] at hy hz
              exact hP.trans (hP.symm hy) hz
            have hne : Nonempty V := ⟨x⟩
            have := numClasses_eq_one hall
            omega
      _ ≤ 2 * Cr.card := sum_cut_classes_le P hP
  nlinarith

end Counting2

section Exchange

variable [Fintype E] {ends : E → V × V}

open Classical in
/-- Kaiser's choice of the exchanged edge `e'`: in a forest `F`, if `u, v` are connected by
edges of `F` inside the classes of `R 0` but not inside those of `R m`, then some edge `e'` of
the `u`–`v` path lies inside a class of `R ℓ` but not of `R (ℓ + 1)` for some `ℓ < m`, and the
rest of the path inside the classes of `R ℓ` joins the ends of `e'` to `u` and `v`. -/
lemma exists_exchange_edge {F : Set E} (hFbr : ∀ f ∈ F, IsBridge ends F f)
    (R : ℕ → V → V → Prop) {u v : V} {m : ℕ} (h0 : Conn ends (Inner ends (R 0) F) u v)
    (hm : ¬ Conn ends (Inner ends (R m) F) u v) :
    ∃ ℓ < m, ∃ e' ∈ F, R ℓ (ends e').1 (ends e').2 ∧ ¬ R (ℓ + 1) (ends e').1 (ends e').2 ∧
      ¬ Conn ends (F \ {e'}) u v ∧
      ∀ S : Set E, Inner ends (R ℓ) F \ {e'} ⊆ S → Conn ends S u v →
        Conn ends S (ends e').1 (ends e').2 := by
  have hm1 : 1 ≤ m := by
    by_contra h0'
    have : m = 0 := by omega
    subst this
    exact hm h0
  have hexl : ∃ i, ¬ Conn ends (Inner ends (R (i + 1)) F) u v :=
    ⟨m - 1, by rw [Nat.sub_add_cancel hm1]; exact hm⟩
  obtain ⟨ℓ, hℓ1, hℓmin⟩ : ∃ ℓ, ¬ Conn ends (Inner ends (R (ℓ + 1)) F) u v ∧
      ∀ i < ℓ, Conn ends (Inner ends (R (i + 1)) F) u v :=
    ⟨Nat.find hexl, Nat.find_spec hexl, fun i hi => not_not.mp (Nat.find_min hexl hi)⟩
  have hℓ0 : Conn ends (Inner ends (R ℓ) F) u v := by
    cases ℓ with
    | zero => exact h0
    | succ i => exact hℓmin i (Nat.lt_succ_self i)
  have hℓm : ℓ < m := by
    by_contra h
    have := hℓmin (m - 1) (by omega)
    rw [Nat.sub_add_cancel hm1] at this
    exact hm this
  obtain ⟨e', he'D, he'nc⟩ : ∃ e' ∈ univ.filter (fun d => d ∈ Inner ends (R ℓ) F ∧
      d ∉ Inner ends (R (ℓ + 1)) F), ¬ Conn ends (Inner ends (R ℓ) F \ {e'}) u v := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have := conn_remove_bridges (F := F) (univ.filter (fun d => d ∈ Inner ends (R ℓ) F ∧
      d ∉ Inner ends (R (ℓ + 1)) F)) (inner_subset _ _)
      (fun d hd => ⟨hFbr d (mem_filter.mp hd).2.1.1,
        (hall d hd).mono (Set.sdiff_subset_sdiff_left (inner_subset _ _))⟩) hℓ0
    apply hℓ1
    refine this.mono (fun f hf => ?_)
    simp only [Set.mem_sdiff, mem_coe, mem_filter, mem_univ, true_and] at hf
    tauto
  simp only [mem_filter, mem_univ, true_and] at he'D
  obtain ⟨⟨he'F, he'R⟩, he'nR⟩ := he'D
  refine ⟨ℓ, hℓm, e', he'F, he'R, fun h => he'nR ⟨he'F, h⟩, fun h => ?_, fun S hS huv => ?_⟩
  · have := conn_remove_bridge (F := F) (G := Inner ends (R ℓ) F) (D := ∅) (inner_subset _ _)
      (hFbr e' he'F) (by simpa using hℓ0) h
    rw [Set.sdiff_empty] at this
    exact he'nc this
  · rcases hℓ0.cut e' with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h he'nc
    · exact ((h1.mono hS).symm.trans huv).trans (h2.mono hS).symm
    · exact ((h2.mono hS).trans huv.symm).trans (h1.mono hS)

open Classical in
/-- If every non-bridge of `L` lies inside a class of `R`, then a non-bridge `e` of `L` closes
a cycle inside the classes of `R`. -/
lemma conn_inner_of_min {L : Set E} {R : V → V → Prop} {e : E} (he : e ∈ L)
    (hnb : ¬ IsBridge ends L e) (hRe : R (ends e).1 (ends e).2)
    (hmin : ∀ f ∈ L, ¬ IsBridge ends L f → R (ends f).1 (ends f).2) :
    Conn ends (Inner ends R L \ {e}) (ends e).1 (ends e).2 := by
  have hnb' : Conn ends (L \ {e}) (ends e).1 (ends e).2 := not_not.mp hnb
  have := conn_remove_bridges (F := L) (G := L \ {e})
    (univ.filter fun d => d ∈ L ∧ ¬ R (ends d).1 (ends d).2) Set.sdiff_subset
    (fun d hd => by
      simp only [mem_filter, mem_univ, true_and] at hd
      refine ⟨by_contra fun h => hd.2 (hmin d hd.1 h), Conn.edge ⟨he, fun h => ?_⟩⟩
      rw [Set.mem_singleton_iff] at h
      rw [← h] at hd
      exact hd.2 hRe)
    hnb'
  refine this.mono (fun f hf => ?_)
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, mem_coe, mem_filter, mem_univ,
    true_and] at hf
  exact ⟨⟨hf.1.1, by_contra fun h => hf.2 ⟨hf.1.1, h⟩⟩, hf.1.2⟩

end Exchange

section MainStep

variable [Fintype V] [Fintype E] [DecidableEq V] {ends : E → V × V}

open Classical in
/-- Kaiser's exchange argument: for a colouring maximising the score among those whose first
`k` colour classes are spanning trees, the last colour class is connected. -/
theorem main_step {k : ℕ}
    (hcut : ∀ U : Finset V, U.Nonempty → U ≠ univ → 2 * (k + 1) ≤ (cutSet ends U).card)
    (col : E → Fin (k + 1)) (hval : Valid ends k col)
    (hmax : ∀ col' : E → Fin (k + 1), Valid ends k col' →
      score ends (colSet col') (k + 1) ≤ score ends (colSet col) (k + 1)) :
    ∀ x y, Conn ends (colSet col k) x y := by
  by_contra hdisc
  have hPeq : ∀ i, Equivalence (part ends (colSet col) (k + 1) i) := part_equiv _ _
  obtain ⟨N, hN⟩ := exists_stable (ends := ends) (colSet col) (k + 1)
  have hNconn : ∀ c < k + 1, ∀ x y, part ends (colSet col) (k + 1) N x y →
      Conn ends (Inner ends (part ends (colSet col) (k + 1) N) (colSet col c)) x y := by
    intro c hc x y hxy
    by_contra hb
    exact not_bad_of_lt_nextCol (c := c) (by rw [hN]; exact hc) ⟨x, y, hxy, hb⟩
  obtain ⟨e₀, he₀, hnb₀, hlev₀⟩ := step3 hcut col hval hdisc _ (hPeq N) hNconn
  -- an edge `e` of minimum level `m` on a cycle of the last colour class
  have hex : ∃ m, ∃ e ∈ colSet col k, ¬ IsBridge ends (colSet col k) e ∧
      ¬ part ends (colSet col) (k + 1) (m + 1) (ends e).1 (ends e).2 := by
    cases N with
    | zero => exact absurd trivial hlev₀
    | succ N => exact ⟨N, e₀, he₀, hnb₀, hlev₀⟩
  obtain ⟨m, ⟨e, he, hnb, hlev⟩, hmmin⟩ : ∃ m, (∃ e ∈ colSet col k,
      ¬ IsBridge ends (colSet col k) e ∧
      ¬ part ends (colSet col) (k + 1) (m + 1) (ends e).1 (ends e).2) ∧
      ∀ m' < m, ¬ ∃ e ∈ colSet col k, ¬ IsBridge ends (colSet col k) e ∧
        ¬ part ends (colSet col) (k + 1) (m' + 1) (ends e).1 (ends e).2 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m' h => Nat.find_min hex h⟩
  have hmin : ∀ f ∈ colSet col k, ¬ IsBridge ends (colSet col k) f →
      part ends (colSet col) (k + 1) m (ends f).1 (ends f).2 := by
    intro f hf hfnb
    by_contra hPf
    cases m with
    | zero => exact hPf trivial
    | succ m' => exact hmmin m' (Nat.lt_succ_self m') ⟨f, hf, hfnb, hPf⟩
  have hPm : part ends (colSet col) (k + 1) m (ends e).1 (ends e).2 := hmin e he hnb
  have hcmK : nextCol ends (colSet col) (k + 1) (part ends (colSet col) (k + 1) m) < k + 1 := by
    by_contra h
    apply hlev
    rw [part_succ_of_not_lt h]
    exact hPm
  have hPm1 := part_succ_of_lt hcmK
  obtain ⟨cm, hcm⟩ : ∃ cm,
      nextCol ends (colSet col) (k + 1) (part ends (colSet col) (k + 1) m) = cm := ⟨_, rfl⟩
  rw [hcm] at hPm1
  have hcmK' : cm < k + 1 := hcm ▸ hcmK
  have hcmk : cm ≠ k := by
    intro h
    apply hlev
    rw [hPm1, h]
    exact Conn.edge ⟨he, hPm⟩
  have hcm_lt : cm < k := by omega
  have hFsp : SpTree ends (colFin col cm) := hval cm hcm_lt
  have hFbr : ∀ f ∈ colSet col cm, IsBridge ends (colSet col cm) f := by
    intro f hf
    have := hFsp.isBridge (e := f) (by rw [← Finset.mem_coe, coe_colFin]; exact hf)
    rwa [coe_colFin] at this
  have hFconn : ∀ x y, Conn ends (colSet col cm) x y := by
    intro x y; have := hFsp.2 x y; rwa [coe_colFin] at this
  have hG0 : Conn ends (Inner ends (part ends (colSet col) (k + 1) 0) (colSet col cm))
      (ends e).1 (ends e).2 :=
    (hFconn _ _).mono fun f (hf : f ∈ colSet col cm) => (⟨hf, trivial⟩ :
      f ∈ Inner ends (part ends (colSet col) (k + 1) 0) (colSet col cm))
  have hGm : ¬ Conn ends (Inner ends (part ends (colSet col) (k + 1) m) (colSet col cm))
      (ends e).1 (ends e).2 := by
    intro h; apply hlev; rw [hPm1]; exact h
  obtain ⟨ℓ, hℓm, e', he'T, he'P, he'nP, he'F, hpath⟩ :=
    exists_exchange_edge hFbr (part ends (colSet col) (k + 1)) hG0 hGm
  have hU1 := conn_inner_of_min he hnb hPm hmin
  have hcole : (col e : ℕ) = k := he
  have hcole' : (col e' : ℕ) = cm := he'T
  have hee' : e ≠ e' := by
    intro h; rw [h] at hcole; omega
  -- the exchanged colouring
  let col' : E → Fin (k + 1) := fun f =>
    if f = e then ⟨cm, hcmK'⟩ else if f = e' then Fin.last k else col f
  have hcol'e : ((col' e : Fin (k + 1)) : ℕ) = cm := by simp [col']
  have hcol'e' : ((col' e' : Fin (k + 1)) : ℕ) = k := by simp [col', hee'.symm]
  have hcol'f : ∀ f, f ≠ e → f ≠ e' → col' f = col f := fun f h1 h2 => by simp [col', h1, h2]
  have hval' : Valid ends k col' := by
    intro c hc
    by_cases hccm : c = cm
    · have hfin : colFin col' c = insert e ((colFin col cm).erase e') := by
        ext f
        simp only [colFin, mem_filter, mem_univ, true_and, mem_insert, mem_erase]
        by_cases h1 : f = e
        · rw [h1]
          constructor
          · intro _; exact Or.inl rfl
          · intro _; rw [hcol'e]; exact hccm.symm
        · by_cases h2 : f = e'
          · rw [h2]
            constructor
            · intro h; rw [hcol'e'] at h; omega
            · rintro (h | ⟨h, _⟩)
              · exact absurd h hee'.symm
              · exact absurd rfl h
          · rw [hcol'f f h1 h2]
            constructor
            · intro h; exact Or.inr ⟨h2, by omega⟩
            · rintro (h | ⟨_, h⟩)
              · exact absurd h h1
              · omega
      rw [hfin]
      refine hFsp.exchange ?_ ?_ ?_
      · simp only [colFin, mem_filter, mem_univ, true_and]; omega
      · simp only [colFin, mem_filter, mem_univ, true_and]; exact hcole'
      · rw [coe_colFin]; exact he'F
    · have hfin : colFin col' c = colFin col c := by
        ext f
        simp only [colFin, mem_filter, mem_univ, true_and]
        by_cases h1 : f = e
        · rw [h1, hcol'e, hcole]; omega
        · by_cases h2 : f = e'
          · rw [h2, hcol'e', hcole']; omega
          · rw [hcol'f f h1 h2]
      rw [hfin]; exact hval c hc
  -- Claim 1 of Kaiser
  have hC1 : ∀ j ≤ m, ∀ c x y,
      Conn ends (Inner ends (part ends (colSet col) (k + 1) j) (colSet col c)) x y →
      Conn ends (Inner ends (part ends (colSet col) (k + 1) j) (colSet col' c)) x y := by
    intro j hj c x y h
    refine Conn.of_forall (fun f hf => ?_) h
    obtain ⟨hfT, hfP⟩ := hf
    have hfT' : (col f : ℕ) = c := hfT
    by_cases h1 : f = e
    · rw [h1] at hfT' ⊢
      have hck : c = k := by omega
      rw [hck]
      refine hU1.mono (fun d hd => ?_)
      obtain ⟨⟨hdT, hdP⟩, hdne⟩ := hd
      have hdT' : (col d : ℕ) = k := hdT
      have hde : d ≠ e := hdne
      have hde' : d ≠ e' := by intro h; rw [h] at hdT'; omega
      refine ⟨?_, part_anti hj hdP⟩
      show ((col' d : Fin (k + 1)) : ℕ) = k
      rw [hcol'f d hde hde']; exact hdT'
    · by_cases h2 : f = e'
      · rw [h2] at hfT' hfP ⊢
        have hcc : c = cm := by omega
        have hjℓ : j ≤ ℓ := by
          by_contra hlt
          exact he'nP (part_anti (by omega) hfP)
        rw [hcc]
        refine hpath _ (fun d hd => ?_) (Conn.edge ⟨?_, part_anti hj hPm⟩)
        · obtain ⟨⟨hdT, hdP⟩, hdne⟩ := hd
          have hdT' : (col d : ℕ) = cm := hdT
          have hde' : d ≠ e' := hdne
          have hde : d ≠ e := by intro h; rw [h] at hdT'; omega
          refine ⟨?_, part_anti hjℓ hdP⟩
          show ((col' d : Fin (k + 1)) : ℕ) = cm
          rw [hcol'f d hde hde']; exact hdT'
        · exact hcol'e
      · refine Conn.edge ⟨?_, hfP⟩
        show ((col' f : Fin (k + 1)) : ℕ) = c
        rw [hcol'f f h1 h2]; exact hfT'
  refine claim_final hC1 (hmax col' hval') hcmK (x := (ends e).1) (y := (ends e).2) ?_ hlev
  rw [hcm]
  exact Conn.edge ⟨hcol'e, hPm⟩

end MainStep


end TreePack

open Classical in
/-- **Tree packing.** A finite multigraph in which every nontrivial cut has at least `2k`
edges has `k` edge-disjoint spanning trees. -/
theorem tree_packing {V E : Type*} [Fintype V] [Nonempty V] [DecidableEq V] [Fintype E]
    (ends : E → V × V) (k : ℕ)
    (hcut : ∀ U : Finset V, U.Nonempty → U ≠ univ →
      2 * k ≤ (univ.filter fun e => ((ends e).1 ∈ U) ≠ ((ends e).2 ∈ U)).card) :
    ∃ F : Fin k → Finset E, (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧
      ∀ i, IsSpanningTreeEdges ends (F i) := by
  induction k with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨F, hFd, hFt⟩ := ih fun U h1 h2 => le_trans (by omega) (hcut U h1 h2)
    have hcut' : ∀ U : Finset V, U.Nonempty → U ≠ univ →
        2 * (k + 1) ≤ (TreePack.cutSet ends U).card := hcut
    -- the colouring given by `k` disjoint spanning trees, with the rest in the last colour
    let col₀ : E → Fin (k + 1) := fun e =>
      if h : ∃ i, e ∈ F i then (Classical.choose h).castSucc else Fin.last k
    have hval₀ : TreePack.Valid ends k col₀ := by
      intro c hc
      have hfin : TreePack.colFin col₀ c = F ⟨c, hc⟩ := by
        ext e
        simp only [TreePack.colFin, mem_filter, mem_univ, true_and, col₀]
        split_ifs with h
        · rw [Fin.val_castSucc]
          constructor
          · intro hc'
            have hspec := Classical.choose_spec h
            have heq : Classical.choose h = ⟨c, hc⟩ := Fin.ext hc'
            rwa [heq] at hspec
          · intro he
            by_contra hne
            exact Finset.disjoint_left.mp (hFd _ _ fun h' => hne (by rw [h']))
              (Classical.choose_spec h) he
        · rw [Fin.val_last]
          constructor
          · intro h'; omega
          · intro he; exact absurd ⟨_, he⟩ h
      rw [hfin]
      exact (TreePack.isSpanningTreeEdges_iff _).mp (hFt _)
    obtain ⟨col, hcol, hmaxc⟩ := exists_max_image (univ.filter (TreePack.Valid ends k))
      (fun col => TreePack.score ends (TreePack.colSet col) (k + 1)) ⟨col₀, by simpa using hval₀⟩
    have hval : TreePack.Valid ends k col := by simpa using hcol
    have hconn := TreePack.main_step hcut' col hval fun col' hv => hmaxc col' (by simpa using hv)
    obtain ⟨L, hLsub, hL⟩ := TreePack.exists_spTree_of_conn (TreePack.colFin col k)
      (by rw [TreePack.coe_colFin]; exact hconn)
    have hsub : ∀ i : Fin (k + 1),
        (if (i : ℕ) < k then TreePack.colFin col i else L) ⊆ TreePack.colFin col i := by
      intro i
      split_ifs with h
      · exact subset_refl _
      · have : (i : ℕ) = k := by omega
        rw [this]; exact hLsub
    refine ⟨fun i => if (i : ℕ) < k then TreePack.colFin col i else L, ?_, ?_⟩
    · intro i j hij
      refine Disjoint.mono (hsub i) (hsub j) ?_
      rw [Finset.disjoint_left]
      intro e hei hej
      simp only [TreePack.colFin, mem_filter, mem_univ, true_and] at hei hej
      exact hij (Fin.ext (hei.symm.trans hej))
    · intro i
      rw [TreePack.isSpanningTreeEdges_iff]
      dsimp only
      split_ifs with h
      · exact hval i h
      · exact hL

open Classical in
/-- **Cut counting (6.4).** In a finite multigraph of minimum cut at least `μ ≥ 6`, the number
of vertex sets `U` whose cut has fewer than `(j+1) μ` edges is at most
`(2(|V| + |E|))^{4(j+1)}`. -/
theorem cut_count {V E : Type*} [Fintype V] [Nonempty V] [DecidableEq V] [Fintype E]
    (ends : E → V × V) (μ : ℕ) (hμ : 6 ≤ μ)
    (hcut : ∀ U : Finset V, U.Nonempty → U ≠ univ →
      μ ≤ (univ.filter fun e => ((ends e).1 ∈ U) ≠ ((ends e).2 ∈ U)).card) (j : ℕ) :
    ((univ : Finset (Finset V)).filter fun U =>
      (univ.filter fun e => ((ends e).1 ∈ U) ≠ ((ends e).2 ∈ U)).card < (j + 1) * μ).card ≤
      (2 * (Fintype.card V + Fintype.card E)) ^ (4 * (j + 1)) := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  set n := Fintype.card V with hn
  set m := Fintype.card E with hm
  have hnpos : 0 < n := Fintype.card_pos
  by_cases hn1 : n = 1
  · calc _ ≤ (univ : Finset (Finset V)).card := card_filter_le _ _
      _ = 2 := by rw [card_univ, Fintype.card_finset, ← hn, hn1]; rfl
      _ ≤ 2 * (n + m) := by omega
      _ ≤ (2 * (n + m)) ^ (4 * (j + 1)) := Nat.le_self_pow (by omega) _
  have hne : ({v} : Finset V) ≠ univ := by
    intro h
    have := congrArg Finset.card h
    rw [card_singleton, card_univ] at this
    omega
  have hμm : μ ≤ m := (hcut {v} (singleton_nonempty v) hne).trans (card_le_univ _)
  set k := μ / 2 with hk
  have hk2 : 2 * k ≤ μ := Nat.mul_div_le μ 2
  have hk3 : μ ≤ 3 * k := by omega
  have hkpos : 0 < k := by omega
  obtain ⟨F, hdisj, htree⟩ := tree_packing ends k fun U h1 h2 => hk2.trans (hcut U h1 h2)
  have hconn : ∀ i x y, TreePack.Conn ends (↑(F i) : Set E) x y := fun i =>
    ((TreePack.isSpanningTreeEdges_iff _).mp (htree i)).2
  set cutE : Finset V → Finset E :=
    fun U => univ.filter fun e => ((ends e).1 ∈ U) ≠ ((ends e).2 ∈ U) with hcutE
  have hmin : ∀ U : Finset V, ∃ i : Fin k, ∀ i', (F i ∩ cutE U).card ≤ (F i' ∩ cutE U).card := by
    intro U
    obtain ⟨i, _, hi⟩ := exists_min_image univ (fun i => (F i ∩ cutE U).card)
      ⟨⟨0, hkpos⟩, mem_univ _⟩
    exact ⟨i, fun i' => hi i' (mem_univ _)⟩
  choose idx hidx using hmin
  set S : Finset (Finset V) := univ.filter fun U => (cutE U).card < (j + 1) * μ with hS
  set D : Finset (Finset E) := univ.filter fun D : Finset E => D.card ≤ 3 * (j + 1) with hD
  let enc : Finset V → Bool × Fin k × Finset E := fun U => (decide (v ∈ U), idx U, F (idx U) ∩ cutE U)
  have hsmall : ∀ U ∈ S, (F (idx U) ∩ cutE U).card ≤ 3 * (j + 1) := by
    intro U hU
    simp only [hS, mem_filter, mem_univ, true_and] at hU
    have hsum : ∑ i : Fin k, (F i ∩ cutE U).card ≤ (cutE U).card := by
      rw [← card_biUnion]
      · exact card_le_card (biUnion_subset.mpr fun i _ => inter_subset_right)
      · intro i _ i' _ hii'
        exact Disjoint.mono inter_subset_left inter_subset_left (hdisj i i' hii')
    have hlow : k * (F (idx U) ∩ cutE U).card ≤ ∑ i : Fin k, (F i ∩ cutE U).card := by
      calc k * (F (idx U) ∩ cutE U).card = ∑ _i : Fin k, (F (idx U) ∩ cutE U).card := by
            simp
        _ ≤ _ := sum_le_sum fun i _ => hidx U i
    have h1 : k * (F (idx U) ∩ cutE U).card < k * (3 * (j + 1)) := by
      calc k * (F (idx U) ∩ cutE U).card < (j + 1) * μ := by omega
        _ ≤ (j + 1) * (3 * k) := Nat.mul_le_mul_left _ hk3
        _ = k * (3 * (j + 1)) := by ring
    exact (Nat.lt_of_mul_lt_mul_left h1).le
  have hmaps : Set.MapsTo enc ↑S ↑((univ : Finset Bool) ×ˢ (univ : Finset (Fin k)) ×ˢ D) := by
    intro U hU
    simp only [coe_product, coe_univ, Set.mem_prod, Set.mem_univ, true_and, mem_coe, hD,
      mem_filter, enc]
    exact ⟨mem_univ _, hsmall U hU⟩
  have hinj : Set.InjOn enc ↑S := by
    intro U _ U' _ hUU'
    simp only [enc, Prod.mk.injEq, decide_eq_decide] at hUU'
    obtain ⟨hv, hi, hF⟩ := hUU'
    rw [← hi] at hF
    set T := F (idx U)
    have hedge : ∀ e ∈ T, (e ∈ cutE U ↔ e ∈ cutE U') := by
      intro e he
      constructor
      · intro h
        have : e ∈ T ∩ cutE U := mem_inter.mpr ⟨he, h⟩
        rw [hF] at this
        exact (mem_inter.mp this).2
      · intro h
        have : e ∈ T ∩ cutE U' := mem_inter.mpr ⟨he, h⟩
        rw [← hF] at this
        exact (mem_inter.mp this).2
    have hprop : ∀ x, TreePack.Conn ends (↑T : Set E) v x → (x ∈ U ↔ x ∈ U') := by
      intro x hx
      induction hx with
      | refl => exact hv
      | @tail z w _ hst ih =>
        obtain ⟨e, he, hj⟩ := hst
        have h2 := hedge e he
        simp only [hcutE, mem_filter, mem_univ, true_and, ne_eq, eq_iff_iff] at h2
        rcases hj with hj | hj <;> rw [hj] at h2 <;> dsimp only at h2 <;> tauto
    ext x
    exact hprop x (hconn _ v x)
  calc S.card ≤ ((univ : Finset Bool) ×ˢ (univ : Finset (Fin k)) ×ˢ D).card :=
        card_le_card_of_injOn enc hmaps hinj
    _ = 2 * k * D.card := by simp [card_product, mul_assoc]
    _ ≤ 2 * k * (m + 1) ^ (3 * (j + 1)) := Nat.mul_le_mul_left _ (TreePack.card_small_subsets E _)
    _ ≤ m * (m + 1) ^ (3 * (j + 1)) := Nat.mul_le_mul_right _ (by omega)
    _ ≤ (m + 1) ^ (3 * (j + 1) + 1) := by
        rw [pow_succ']; exact Nat.mul_le_mul_right _ (Nat.le_succ m)
    _ ≤ (2 * (n + m)) ^ (3 * (j + 1) + 1) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (2 * (n + m)) ^ (4 * (j + 1)) := Nat.pow_le_pow_right (by omega) (by omega)

end Lovasz
