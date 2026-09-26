/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Watkins's connectivity bound for Cayley graphs (classical input)

DAG node `K.watkins` of `docs/BLUEPRINT.md`; M. E. Watkins, *Connectivity of transitive
graphs*, JCT 8 (1970), in the weak form "vertex connectivity at least `k/2`" used in Section 5.1,
applied to each connected component of a Cayley graph.

The proof is the atom argument of Watkins and Mader, run inside the component
`H = ⟨T⟩` of `1`, on which the left translations by elements of `H` act transitively.
A *fragment* is a nonempty `X ⊆ H` such that `H \ (X ∪ N(X))` is nonempty, where `N(X)` is the
outer vertex boundary. Let `κ` be the least boundary size of a fragment and `A` a fragment of
boundary `κ` and least size (an atom). Two atoms that meet coincide, so the translates of `A`
meeting `N(A)` lie inside `N(A)`, whence `|A| ≤ κ`; and a vertex of `A` has its `k = |T|`
neighbours in `A ∪ N(A)`, whence `k + 1 ≤ |A| + κ ≤ 2κ`.
-/

universe u

namespace Lovasz

open Finset

namespace Watkins

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

/-- The outer vertex boundary `N(X) \ X` of `X` in `Cay(G, T)` (for symmetric `T`). -/
def bd (T X : Finset G) : Finset G := univ.filter fun v => v ∉ X ∧ ∃ s ∈ T, v * s ∈ X

/-- The vertices of `H` outside `X ∪ N(X)`. -/
def co (T H X : Finset G) : Finset G := H \ (X ∪ bd T X)

/-- A fragment of `Cay(H, T)`: a nonempty `X ⊆ H` with `H \ (X ∪ N(X))` nonempty. -/
structure IsFrag (T H X : Finset G) : Prop where
  sub : X ⊆ H
  nonempty : X.Nonempty
  co_nonempty : (co T H X).Nonempty

variable {T H X A : Finset G}

lemma mem_bd {v : G} : v ∈ bd T X ↔ v ∉ X ∧ ∃ s ∈ T, v * s ∈ X := by
  simp [bd]

lemma mem_co {v : G} : v ∈ co T H X ↔ v ∈ H ∧ v ∉ X ∧ v ∉ bd T X := by
  simp [co, not_or]

lemma co_subset : co T H X ⊆ H := sdiff_subset

lemma mul_mem_or_mem_bd (hT : IsConnectionSet T) {w s : G} (hw : w ∈ X) (hs : s ∈ T) :
    w * s ∈ X ∨ w * s ∈ bd T X := by
  by_cases h : w * s ∈ X
  · exact Or.inl h
  · exact Or.inr (mem_bd.2 ⟨h, s⁻¹, hT.1 s hs, by simpa using hw⟩)

lemma bd_subset (hH : ∀ v, v ∈ H ↔ v ∈ Subgroup.closure (T : Set G)) (hX : X ⊆ H) :
    bd T X ⊆ H := by
  intro v hv
  obtain ⟨-, s, hs, hvs⟩ := mem_bd.1 hv
  have h1 := (hH _).1 (hX hvs)
  have h2 : s ∈ Subgroup.closure (T : Set G) := Subgroup.subset_closure hs
  rw [hH]
  simpa using mul_mem h1 (inv_mem h2)

lemma mem_trichotomy {w : G} (hw : w ∈ H) : w ∈ X ∨ w ∈ bd T X ∨ w ∈ co T H X := by
  by_cases h1 : w ∈ X
  · exact Or.inl h1
  by_cases h2 : w ∈ bd T X
  · exact Or.inr (Or.inl h2)
  exact Or.inr (Or.inr (mem_co.2 ⟨hw, h1, h2⟩))

lemma mem_or_mem_bd_of_mem_bd {P : Finset G} (hPA : P ⊆ A) {w : G} (hw : w ∈ bd T P) :
    w ∈ A ∨ w ∈ bd T A := by
  obtain ⟨-, s, hs, hws⟩ := mem_bd.1 hw
  by_cases h : w ∈ A
  · exact Or.inl h
  · exact Or.inr (mem_bd.2 ⟨h, s, hs, hPA hws⟩)

lemma mem_co_or_mem_bd_of_mem_bd (hT : IsConnectionSet T)
    (hH : ∀ v, v ∈ H ↔ v ∈ Subgroup.closure (T : Set G)) {Q : Finset G}
    (hQ : Q ⊆ co T H A) {w : G} (hw : w ∈ bd T Q) : w ∈ co T H A ∨ w ∈ bd T A := by
  have hwH := bd_subset hH (hQ.trans co_subset) hw
  obtain ⟨-, s, hs, hws⟩ := mem_bd.1 hw
  have hwA : w ∉ A := by
    intro h
    have := mem_co.1 (hQ hws)
    rcases mul_mem_or_mem_bd hT h hs with h' | h'
    · exact this.2.1 h'
    · exact this.2.2 h'
  by_cases h : w ∈ bd T A
  · exact Or.inr h
  · exact Or.inl (mem_co.2 ⟨hwH, hwA, h⟩)

lemma card_add_card_bd_add_card_co (hH : ∀ v, v ∈ H ↔ v ∈ Subgroup.closure (T : Set G))
    (hX : X ⊆ H) : X.card + (bd T X).card + (co T H X).card = H.card := by
  have hdisj : Disjoint X (bd T X) := by
    rw [disjoint_left]
    intro a ha hb
    exact (mem_bd.1 hb).1 ha
  have hsub : X ∪ bd T X ⊆ H := union_subset hX (bd_subset hH hX)
  have := card_sdiff_add_card_eq_card hsub
  rw [card_union_of_disjoint hdisj] at this
  unfold co
  omega

omit [Fintype G] in
lemma mem_image_mul_left {g v : G} : v ∈ X.image (g * ·) ↔ g⁻¹ * v ∈ X := by
  constructor
  · intro h
    obtain ⟨w, hw, rfl⟩ := mem_image.1 h
    simpa using hw
  · intro h
    exact mem_image.2 ⟨_, h, by simp⟩

lemma bd_image (g : G) : bd T (X.image (g * ·)) = (bd T X).image (g * ·) := by
  ext v
  simp only [mem_bd, mem_image_mul_left, mul_assoc]

omit [Fintype G] in
lemma card_image_mul_left (g : G) : (X.image (g * ·)).card = X.card :=
  card_image_of_injective _ (mul_right_injective g)

omit [Fintype G] in
lemma image_subset (hH : ∀ v, v ∈ H ↔ v ∈ Subgroup.closure (T : Set G)) (hX : X ⊆ H) {g : G}
    (hg : g ∈ H) : X.image (g * ·) ⊆ H := by
  intro v hv
  rw [mem_image_mul_left] at hv
  have := (hH _).1 (hX hv)
  rw [hH]
  simpa using mul_mem ((hH _).1 hg) this

lemma card_co_image (hH : ∀ v, v ∈ H ↔ v ∈ Subgroup.closure (T : Set G)) (hX : X ⊆ H) {g : G}
    (hg : g ∈ H) : (co T H (X.image (g * ·))).card = (co T H X).card := by
  have e1 := card_add_card_bd_add_card_co hH hX
  have e2 := card_add_card_bd_add_card_co hH (image_subset hH hX hg)
  rw [bd_image, card_image_mul_left, card_image_mul_left] at e2
  omega

lemma IsFrag.image (hH : ∀ v, v ∈ H ↔ v ∈ Subgroup.closure (T : Set G)) (hX : IsFrag T H X)
    {g : G} (hg : g ∈ H) : IsFrag T H (X.image (g * ·)) where
  sub := image_subset hH hX.sub hg
  nonempty := hX.nonempty.image _
  co_nonempty := by
    rw [← card_pos, card_co_image hH hX.sub hg, card_pos]
    exact hX.co_nonempty

/-- The complement `H \ (X ∪ N(X))` of a fragment is a fragment with smaller boundary. -/
lemma IsFrag.co_frag (hT : IsConnectionSet T)
    (hH : ∀ v, v ∈ H ↔ v ∈ Subgroup.closure (T : Set G)) (hX : IsFrag T H X) :
    IsFrag T H (co T H X) ∧ bd T (co T H X) ⊆ bd T X := by
  refine ⟨⟨co_subset, hX.co_nonempty, ?_⟩, ?_⟩
  · obtain ⟨a, ha⟩ := hX.nonempty
    refine ⟨a, mem_co.2 ⟨hX.sub ha, fun h => (mem_co.1 h).2.1 ha, fun h => ?_⟩⟩
    rcases mem_co_or_mem_bd_of_mem_bd hT hH subset_rfl h with h' | h'
    · exact (mem_co.1 h').2.1 ha
    · exact (mem_bd.1 h').1 ha
  · intro w hw
    rcases mem_co_or_mem_bd_of_mem_bd hT hH subset_rfl hw with h' | h'
    · exact absurd h' (mem_bd.1 hw).1
    · exact h'

/-- A fragment has a nonempty boundary, since `Cay(H, T)` is connected. -/
lemma IsFrag.bd_nonempty (hT : IsConnectionSet T)
    (hH : ∀ v, v ∈ H ↔ v ∈ Subgroup.closure (T : Set G)) (hX : IsFrag T H X) :
    (bd T X).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hclosed : ∀ a ∈ X, ∀ s ∈ T, a * s ∈ X := by
    intro a ha s hs
    rcases mul_mem_or_mem_bd hT ha hs with h | h
    · exact h
    · rw [hne] at h
      simp at h
  have key : ∀ h ∈ Subgroup.closure (T : Set G), ∀ a ∈ X, a * h ∈ X := by
    intro h hh
    induction hh using Subgroup.closure_induction'' with
    | mem s hs => exact fun a ha => hclosed a ha s hs
    | inv_mem s hs => exact fun a ha => hclosed a ha s⁻¹ (hT.1 s hs)
    | one => simp
    | mul x y _ _ ihx ihy =>
      intro a ha
      rw [← mul_assoc]
      exact ihy _ (ihx a ha)
  obtain ⟨w, hw⟩ := hX.co_nonempty
  obtain ⟨a, ha⟩ := hX.nonempty
  have hwH := (mem_co.1 hw).1
  have hmem : a⁻¹ * w ∈ Subgroup.closure (T : Set G) :=
    mul_mem (inv_mem ((hH a).1 (hX.sub ha))) ((hH w).1 hwH)
  have := key _ hmem a ha
  rw [mul_inv_cancel_left] at this
  exact (mem_co.1 hw).2.1 this

/-- **Intersection lemma.** An atom `A` meeting a fragment `X` of minimum boundary with
`|X| ≤ |H \ (A ∪ N(A))|` lies inside `X`. -/
lemma atom_subset (hT : IsConnectionSet T)
    (hH : ∀ v, v ∈ H ↔ v ∈ Subgroup.closure (T : Set G)) {κ : ℕ}
    (hκ : ∀ Y, IsFrag T H Y → κ ≤ (bd T Y).card)
    (hA : IsFrag T H A) (hAκ : (bd T A).card = κ)
    (hAmin : ∀ Y, IsFrag T H Y → (bd T Y).card = κ → A.card ≤ Y.card)
    (hXκ : (bd T X).card = κ) (hAX : (A ∩ X).Nonempty) (hsize : X.card ≤ (co T H A).card) : A ⊆ X := by
  set P := A ∩ X with hP
  have hPA : P ⊆ A := inter_subset_left
  have hPX : P ⊆ X := inter_subset_right
  have hPfrag : IsFrag T H P := by
    refine ⟨hPA.trans hA.sub, hAX, ?_⟩
    obtain ⟨w, hw⟩ := hA.co_nonempty
    refine ⟨w, ?_⟩
    obtain ⟨hwH, hwA, hwb⟩ := mem_co.1 hw
    refine mem_co.2 ⟨hwH, fun h => hwA (hPA h), fun h => ?_⟩
    rcases mem_or_mem_bd_of_mem_bd hPA h with h' | h'
    · exact hwA h'
    · exact hwb h'
  have hbdP : ∀ w ∈ bd T P, (w ∈ A ∨ w ∈ bd T A) ∧ (w ∈ X ∨ w ∈ bd T X) ∧
      ¬(w ∈ A ∧ w ∈ X) := fun w hw =>
    ⟨mem_or_mem_bd_of_mem_bd hPA hw, mem_or_mem_bd_of_mem_bd hPX hw,
      fun h => (mem_bd.1 hw).1 (mem_inter.2 h)⟩
  have hPκ := hκ P hPfrag
  by_cases hQ : (co T H A ∩ co T H X).Nonempty
  · set Q := co T H A ∩ co T H X with hQdef
    have hQA : Q ⊆ co T H A := inter_subset_left
    have hQX : Q ⊆ co T H X := inter_subset_right
    have hbdQ : ∀ w ∈ bd T Q, (w ∈ co T H A ∨ w ∈ bd T A) ∧ (w ∈ co T H X ∨ w ∈ bd T X) ∧
        ¬(w ∈ co T H A ∧ w ∈ co T H X) := fun w hw =>
      ⟨mem_co_or_mem_bd_of_mem_bd hT hH hQA hw, mem_co_or_mem_bd_of_mem_bd hT hH hQX hw,
        fun h => (mem_bd.1 hw).1 (mem_inter.2 h)⟩
    have hQfrag : IsFrag T H Q := by
      refine ⟨hQA.trans co_subset, hQ, ?_⟩
      obtain ⟨w, hw⟩ := hAX
      refine ⟨w, mem_co.2 ⟨hA.sub (hPA hw), fun h => ?_, fun h => ?_⟩⟩
      · exact (mem_co.1 (hQA h)).2.1 (hPA hw)
      · rcases mem_co_or_mem_bd_of_mem_bd hT hH hQA h with h' | h'
        · exact (mem_co.1 h').2.1 (hPA hw)
        · exact (mem_bd.1 h').1 (hPA hw)
    have hQκ := hκ Q hQfrag
    have hU : bd T P ∪ bd T Q ⊆ bd T A ∪ bd T X := by
      intro w hw
      rw [mem_union] at hw ⊢
      rcases hw with hw | hw
      · obtain ⟨h1, h2, h3⟩ := hbdP w hw
        tauto
      · obtain ⟨h1, h2, h3⟩ := hbdQ w hw
        tauto
    have hI : bd T P ∩ bd T Q ⊆ bd T A ∩ bd T X := by
      intro w hw
      rw [mem_inter] at hw ⊢
      obtain ⟨h1, h2, h3⟩ := hbdP w hw.1
      obtain ⟨h4, h5, h6⟩ := hbdQ w hw.2
      have dA : ¬(w ∈ A ∧ w ∈ co T H A) := fun h => (mem_co.1 h.2).2.1 h.1
      have dX : ¬(w ∈ X ∧ w ∈ co T H X) := fun h => (mem_co.1 h.2).2.1 h.1
      tauto
    have e1 := card_union_add_card_inter (bd T P) (bd T Q)
    have e2 := card_union_add_card_inter (bd T A) (bd T X)
    have c1 := card_le_card hU
    have c2 := card_le_card hI
    have hPeq : (bd T P).card = κ := by omega
    have hPA' : P = A := eq_of_subset_of_card_le hPA (hAmin P hPfrag hPeq)
    intro w hw
    rw [← hPA'] at hw
    exact hPX hw
  · rw [not_nonempty_iff_eq_empty] at hQ
    exfalso
    have hcoA : co T H A ⊆ X ∪ bd T X := by
      intro w hw
      have hwH := (mem_co.1 hw).1
      rw [mem_union]
      by_contra hcon
      simp only [not_or] at hcon
      have : w ∈ co T H A ∩ co T H X := mem_inter.2 ⟨hw, mem_co.2 ⟨hwH, hcon.1, hcon.2⟩⟩
      rw [hQ] at this
      simp at this
    have hbP : bd T P ⊆ (bd T X \ co T H A) ∪ (bd T A ∩ X) := by
      intro w hw
      obtain ⟨h1, h2, h3⟩ := hbdP w hw
      rw [mem_union, mem_sdiff, mem_inter]
      have dA : w ∈ co T H A → ¬w ∈ A ∧ ¬w ∈ bd T A := fun h =>
        ⟨(mem_co.1 h).2.1, (mem_co.1 h).2.2⟩
      tauto
    have hXs : P ∪ (bd T A ∩ X) ⊆ X \ co T H A := by
      intro w hw
      rw [mem_union] at hw
      rw [mem_sdiff]
      rcases hw with hw | hw
      · exact ⟨hPX hw, fun h => (mem_co.1 h).2.1 (hPA hw)⟩
      · rw [mem_inter] at hw
        exact ⟨hw.2, fun h => (mem_co.1 h).2.2 hw.1⟩
    have hdisj : Disjoint P (bd T A ∩ X) := by
      rw [disjoint_left]
      intro w hw hw'
      exact (mem_bd.1 (mem_inter.1 hw').1).1 (hPA hw)
    have hcs : co T H A \ X ⊆ bd T X ∩ co T H A := by
      intro w hw
      rw [mem_sdiff] at hw
      rw [mem_inter]
      have := hcoA hw.1
      rw [mem_union] at this
      rcases this with h | h
      · exact absurd h hw.2
      · exact ⟨h, hw.1⟩
    have f1 := card_sdiff_add_card_inter X (co T H A)
    have f2 := card_sdiff_add_card_inter (co T H A) X
    have f3 : (X ∩ co T H A).card = (co T H A ∩ X).card := by rw [inter_comm]
    have f4 := card_sdiff_add_card_inter (bd T X) (co T H A)
    have f5 := (card_le_card hbP).trans (card_union_le _ _)
    have f6 := card_le_card hXs
    rw [card_union_of_disjoint hdisj] at f6
    have f7 := card_le_card hcs
    have f8 : (bd T X ∩ co T H A).card = (bd T X ∩ co T H A).card := rfl
    have f9 := hAX.card_pos
    omega

/-- A vertex of `A` has its `|T|` neighbours in `A ∪ N(A)`. -/
lemma card_add_one_le (hT : IsConnectionSet T) (hA : IsFrag T H A) :
    T.card + 1 ≤ A.card + (bd T A).card := by
  obtain ⟨a, ha⟩ := hA.nonempty
  have hsub : T.image (a * ·) ⊆ (A ∪ bd T A).erase a := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hv
    refine mem_erase.2 ⟨?_, mem_union.2 (mul_mem_or_mem_bd hT ha hs)⟩
    intro h
    have h1 : s = 1 := by simpa using h
    exact hT.2 (h1 ▸ hs)
  have c1 := card_le_card hsub
  rw [card_image_of_injective _ (mul_right_injective a),
    card_erase_of_mem (mem_union_left _ ha)] at c1
  have c2 := card_union_le A (bd T A)
  have c3 : 1 ≤ (A ∪ bd T A).card := card_pos.2 ⟨a, mem_union_left _ ha⟩
  omega

/-- An atom is no larger than its boundary: its translates meeting `N(A)` lie in `N(A)`. -/
lemma atom_card_le (hT : IsConnectionSet T)
    (hH : ∀ v, v ∈ H ↔ v ∈ Subgroup.closure (T : Set G)) {κ : ℕ}
    (hκ : ∀ Y, IsFrag T H Y → κ ≤ (bd T Y).card)
    (hA : IsFrag T H A) (hAκ : (bd T A).card = κ)
    (hAmin : ∀ Y, IsFrag T H Y → (bd T Y).card = κ → A.card ≤ Y.card) : A.card ≤ κ := by
  obtain ⟨v, hv⟩ := hA.bd_nonempty hT hH
  obtain ⟨a, ha⟩ := hA.nonempty
  have hvH : v ∈ H := bd_subset hH hA.sub hv
  have hg : v * a⁻¹ ∈ H := by
    rw [hH]
    exact mul_mem ((hH v).1 hvH) (inv_mem ((hH a).1 (hA.sub ha)))
  set A' := A.image ((v * a⁻¹) * ·) with hA'def
  have hvA' : v ∈ A' := mem_image.2 ⟨a, ha, by simp⟩
  have hA'frag : IsFrag T H A' := hA.image hH hg
  have hA'card : A'.card = A.card := card_image_mul_left _
  have hA'κ : (bd T A').card = κ := by
    rw [hA'def, bd_image, card_image_mul_left, hAκ]
  have hA'min : ∀ Y, IsFrag T H Y → (bd T Y).card = κ → A'.card ≤ Y.card :=
    fun Y hY hYκ => hA'card ▸ hAmin Y hY hYκ
  have hco : (co T H A').card = (co T H A).card := card_co_image hH hA.sub hg
  obtain ⟨hcA, hcAsub⟩ := hA.co_frag hT hH
  have hcAκ : (bd T (co T H A)).card = κ :=
    le_antisymm (hAκ ▸ card_le_card hcAsub) (hκ _ hcA)
  have hAco : A.card ≤ (co T H A).card := hAmin _ hcA hcAκ
  have hsub : A' ⊆ bd T A := by
    intro w hw
    have hwH := hA'frag.sub hw
    rcases mem_trichotomy (T := T) (X := A) hwH with h | h | h
    · exfalso
      have := atom_subset hT hH hκ hA'frag hA'κ hA'min hAκ ⟨w, mem_inter.2 ⟨hw, h⟩⟩
        (by omega)
      exact (mem_bd.1 hv).1 (this hvA')
    · exact h
    · exfalso
      have := atom_subset hT hH hκ hA'frag hA'κ hA'min hcAκ ⟨w, mem_inter.2 ⟨hw, h⟩⟩
        (by omega)
      exact (mem_co.1 (this hvA')).2.2 hv
  have := card_le_card hsub
  omega

/-- **Weak Watkins bound.** Every fragment of `Cay(H, T)` has at least `|T|/2` boundary
vertices. -/
theorem card_le_two_mul_card_bd (hT : IsConnectionSet T)
    (hH : ∀ v, v ∈ H ↔ v ∈ Subgroup.closure (T : Set G)) (hX : IsFrag T H X) :
    T.card ≤ 2 * (bd T X).card := by
  classical
  let F := H.powerset.filter (fun Y => IsFrag T H Y)
  have hmemF : ∀ Y, IsFrag T H Y → Y ∈ F := fun Y hY =>
    mem_filter.2 ⟨mem_powerset.2 hY.sub, hY⟩
  obtain ⟨X1, hX1F, hmin1⟩ := F.exists_min_image (fun Y => (bd T Y).card) ⟨X, hmemF X hX⟩
  set κ := (bd T X1).card with hκdef
  have hκ : ∀ Y, IsFrag T H Y → κ ≤ (bd T Y).card := fun Y hY => hmin1 Y (hmemF Y hY)
  let F2 := F.filter (fun Y => (bd T Y).card = κ)
  obtain ⟨A, hAF2, hAmin'⟩ := F2.exists_min_image card ⟨X1, mem_filter.2 ⟨hX1F, rfl⟩⟩
  obtain ⟨hAF, hAκ⟩ := mem_filter.1 hAF2
  have hA : IsFrag T H A := (mem_filter.1 hAF).2
  have hAmin : ∀ Y, IsFrag T H Y → (bd T Y).card = κ → A.card ≤ Y.card := fun Y hY hYκ =>
    hAmin' Y (mem_filter.2 ⟨hmemF Y hY, hYκ⟩)
  have h1 := card_add_one_le hT hA
  have h2 := atom_card_le hT hH hκ hA hAκ hAmin
  have h3 := hκ X hX
  omega

end Watkins

open Watkins in
/-- **Watkins.** In a Cayley graph `Cay(G, T)` of degree `k = |T|`, deleting fewer than `k/2`
vertices leaves every connected component (a left coset of `⟨T⟩`) connected. -/
theorem watkins_cayley {G : Type u} [Group G] [Fintype G] [DecidableEq G] (T : Finset G)
    (hT : IsConnectionSet T) (B : Finset G) (hB : 2 * B.card < T.card) (x y : G) (hx : x ∉ B)
    (hy : y ∉ B) (hxy : x⁻¹ * y ∈ Subgroup.closure (T : Set G)) :
    ((cayleyGraph T).induce ((B : Set G)ᶜ)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  classical
  by_contra hne
  set H : Finset G := univ.filter (· ∈ Subgroup.closure (T : Set G)) with hHdef
  have hH : ∀ v, v ∈ H ↔ v ∈ Subgroup.closure (T : Set G) := fun v => by simp [H]
  set Γ := (cayleyGraph T).induce ((B : Set G)ᶜ) with hΓ
  set X : Finset G :=
    H.filter (fun w => ∃ h : x * w ∉ B, Γ.Reachable ⟨x, hx⟩ ⟨x * w, h⟩) with hXdef
  have hmemX : ∀ w, w ∈ X ↔ w ∈ H ∧ ∃ h : x * w ∉ B, Γ.Reachable ⟨x, hx⟩ ⟨x * w, h⟩ :=
    fun w => mem_filter
  have hbd : ∀ w ∈ bd T X, x * w ∈ B := by
    intro w hw
    obtain ⟨hwX, s, hs, hwsX⟩ := mem_bd.1 hw
    by_contra hwB
    obtain ⟨-, hB', hreach⟩ := (hmemX _).1 hwsX
    have hwH : w ∈ H := bd_subset hH (filter_subset _ _) hw
    apply hwX
    refine (hmemX w).2 ⟨hwH, hwB, hreach.trans ?_⟩
    apply SimpleGraph.Adj.reachable
    show (cayleyGraph T).Adj (x * (w * s)) (x * w)
    rw [SimpleGraph.mulCayley_adj]
    refine ⟨?_, Or.inr ?_⟩
    · intro h
      have h1 : s = 1 := by simpa using h
      exact hT.2 (h1 ▸ hs)
    · rw [show (x * w)⁻¹ * (x * (w * s)) = s by group]
      exact hs
  have hXfrag : IsFrag T H X := by
    refine ⟨filter_subset _ _, ⟨1, ?_⟩, ⟨x⁻¹ * y, ?_⟩⟩
    · have h1 : x * 1 ∉ B := by simpa using hx
      have e : (⟨x * 1, h1⟩ : ↥((B : Set G)ᶜ)) = ⟨x, hx⟩ := Subtype.ext (mul_one x)
      exact (hmemX 1).2 ⟨(hH 1).2 (one_mem _), h1, e ▸ SimpleGraph.Reachable.refl _⟩
    · refine mem_co.2 ⟨(hH _).2 hxy, fun h => ?_, fun h => ?_⟩
      · obtain ⟨-, h1, h2⟩ := (hmemX _).1 h
        have e : (⟨x * (x⁻¹ * y), h1⟩ : ↥((B : Set G)ᶜ)) = ⟨y, hy⟩ :=
          Subtype.ext (mul_inv_cancel_left x y)
        exact hne (e ▸ h2)
      · exact hy (by simpa using hbd _ h)
  have hcard : (bd T X).card ≤ B.card := by
    refine card_le_card_of_injOn (fun w => x * w) (fun w hw => hbd w hw) ?_
    intro a _ b _ hab
    exact mul_left_cancel hab
  have := card_le_two_mul_card_bd hT hH hXfrag
  omega

end Lovasz
