/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent)
-/
import Lovasz.Defs

/-!
# Haxell's hypergraph matching theorem (classical input)

DAG node `K.haxell` of `docs/BLUEPRINT.md`; P. E. Haxell, *A condition for matchability in
hypergraphs*, Graphs Combin. 11 (1995), in the form stated before Lemma 3.4 of the paper.

## Proof

Haxell's alternating-tree argument. By induction on the set `D` of vertices to be matched, it
suffices to extend a matching `M` of `D` to `insert a₀ D`. A *tree* for `M` is a list of pairs
`(aᵢ, eᵢ)` (newest first) with `eᵢ ∈ edges aᵢ`, where `aᵢ` is already reached, `eᵢ` avoids the
earlier `eⱼ` and the `M`-edges of reached vertices, and `eᵢ` meets the `M`-edges of a nonempty set
`Yᵢ` of new vertices, which become reached. The union of the tree edges and the `M`-edges of the
reached set `I` has at most `(2r - 3)(|I| - 1)` elements, so the hypothesis yields an edge `e` at a
reached vertex avoiding all of it. If `e` meets some `M`-edge the tree grows; otherwise swapping
`e` into `M` either matches `a₀` or shrinks some `Yᵢ` (cascading back along the tree). The vector
`(|Y₁|, |Y₂|, …)` improves lexicographically at each step, so the process terminates.
-/

namespace Lovasz

open Finset

namespace Haxell

variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

/-- Vertices whose `M`-edge meets `e`. -/
def Y (M : α → Finset β) (e : Finset β) : Finset α :=
  univ.filter fun v => ¬ Disjoint (M v) e

/-- Vertices reached by the tree `L` (newest pair first). -/
def reach (a₀ : α) (M : α → Finset β) : List (α × Finset β) → Finset α
  | [] => {a₀}
  | x :: L => reach a₀ M L ∪ Y M x.2

/-- Union of the tree edges. -/
def used : List (α × Finset β) → Finset β
  | [] => ∅
  | x :: L => used L ∪ x.2

/-- Validity of an alternating tree with respect to `M`. -/
def Valid (edges : α → Finset (Finset β)) (a₀ : α) (M : α → Finset β) :
    List (α × Finset β) → Prop
  | [] => True
  | x :: L => Valid edges a₀ M L ∧ x.1 ∈ reach a₀ M L ∧ x.2 ∈ edges x.1 ∧
      Disjoint x.2 (used L) ∧ (∀ v ∈ reach a₀ M L, Disjoint x.2 (M v)) ∧ (Y M x.2).Nonempty

/-- Lexicographic potential: at position `i` (oldest first) the digit `|α| + 1 - |Yᵢ|`. -/
def pot (M : α → Finset β) : List (α × Finset β) → ℕ → ℕ
  | [] => fun _ => 0
  | x :: L => Function.update (pot M L) L.length (Fintype.card α + 1 - (Y M x.2).card)

/-- `M` is a matching saturating `D` (and empty outside `D`). -/
def IsMatchingOn (edges : α → Finset (Finset β)) (D : Finset α) (M : α → Finset β) : Prop :=
  (∀ v ∈ D, M v ∈ edges v) ∧ (∀ v ∉ D, M v = ∅) ∧ ∀ v w, v ≠ w → Disjoint (M v) (M w)

omit [DecidableEq α] in
lemma mem_Y {M : α → Finset β} {e : Finset β} {v : α} : v ∈ Y M e ↔ ¬ Disjoint (M v) e := by
  simp [Y]

lemma mem_reach_self (a₀ : α) (M : α → Finset β) :
    ∀ L : List (α × Finset β), a₀ ∈ reach a₀ M L
  | [] => by simp [reach]
  | x :: L => by simp only [reach]; exact mem_union_left _ (mem_reach_self a₀ M L)

lemma card_reach (edges : α → Finset (Finset β)) (a₀ : α) (M : α → Finset β) :
    ∀ L : List (α × Finset β), Valid edges a₀ M L → L.length + 1 ≤ (reach a₀ M L).card
  | [] => by simp [reach]
  | x :: L => by
    rintro ⟨hV, -, -, -, hxr, hY⟩
    have ih := card_reach edges a₀ M L hV
    have hdisj : Disjoint (reach a₀ M L) (Y M x.2) := by
      rw [disjoint_left]
      intro v hv hvY
      exact mem_Y.1 hvY (hxr v hv).symm
    simp only [reach, List.length_cons]
    rw [card_union_of_disjoint hdisj]
    have := hY.card_pos
    omega

lemma length_lt_card (edges : α → Finset (Finset β)) (a₀ : α) (M : α → Finset β)
    (L : List (α × Finset β)) (hV : Valid edges a₀ M L) : L.length < Fintype.card α := by
  have h1 := card_reach edges a₀ M L hV
  have h2 := card_le_univ (reach a₀ M L)
  omega

omit [DecidableEq α] in
lemma pot_of_ge (M : α → Finset β) :
    ∀ (L : List (α × Finset β)) (j : ℕ), L.length ≤ j → pot M L j = 0
  | [], j, _ => rfl
  | x :: L, j, hj => by
    simp only [List.length_cons] at hj
    simp only [pot]
    rw [Function.update_of_ne (by omega)]
    exact pot_of_ge M L j (by omega)

omit [DecidableEq α] in
lemma pot_le (M : α → Finset β) :
    ∀ (L : List (α × Finset β)) (j : ℕ), pot M L j ≤ Fintype.card α + 1
  | [], _ => by simp [pot]
  | x :: L, j => by
    simp only [pot]
    rcases eq_or_ne j L.length with rfl | hj
    · rw [Function.update_self]; omega
    · rw [Function.update_of_ne hj]; exact pot_le M L j

omit [DecidableEq α] in
lemma pot_cons_of_lt (M : α → Finset β) (x : α × Finset β) (L : List (α × Finset β)) {j : ℕ}
    (hj : j < L.length) : pot M (x :: L) j = pot M L j := by
  simp only [pot]
  rw [Function.update_of_ne (by omega)]

omit [DecidableEq α] in
lemma pot_cons_self (M : α → Finset β) (x : α × Finset β) (L : List (α × Finset β)) :
    pot M (x :: L) L.length = Fintype.card α + 1 - (Y M x.2).card := by
  simp only [pot]
  rw [Function.update_self]

/-- Changing `M` at a vertex `a` outside the reached set, to an edge avoiding the tree, does not
affect the tree. -/
lemma congr_update (edges : α → Finset (Finset β)) (a₀ : α) (M : α → Finset β) (a : α)
    (e : Finset β) :
    ∀ L : List (α × Finset β), a ∉ reach a₀ M L → Disjoint e (used L) →
      reach a₀ (Function.update M a e) L = reach a₀ M L ∧
      pot (Function.update M a e) L = pot M L ∧
      (Valid edges a₀ M L → Valid edges a₀ (Function.update M a e) L)
  | [], _, _ => ⟨rfl, rfl, fun _ => trivial⟩
  | x :: L, ha, he => by
    simp only [reach, mem_union, not_or] at ha
    simp only [used, disjoint_union_right] at he
    obtain ⟨ih1, ih2, ih3⟩ := congr_update edges a₀ M a e L ha.1 he.1
    have hY : Y (Function.update M a e) x.2 = Y M x.2 := by
      ext v
      rw [mem_Y, mem_Y]
      rcases eq_or_ne v a with rfl | hv
      · rw [Function.update_self]
        exact ⟨fun h => absurd he.2 h, fun h => absurd (mem_Y.2 h) ha.2⟩
      · rw [Function.update_of_ne hv]
    refine ⟨?_, ?_, ?_⟩
    · simp only [reach, ih1, hY]
    · simp only [pot, ih2, hY]
    · rintro ⟨hV, hx1, hx2, hxu, hxr, hYne⟩
      refine ⟨ih3 hV, ih1 ▸ hx1, hx2, hxu, ?_, hY ▸ hYne⟩
      intro v hv
      rw [ih1] at hv
      have hva : v ≠ a := fun h => ha.1 (h ▸ hv)
      rw [Function.update_of_ne hva]
      exact hxr v hv

/-- The union of the tree edges and the `M`-edges of reached vertices is small. -/
lemma cover_bound (edges : α → Finset (Finset β)) (r : ℕ) (hr : 2 ≤ r)
    (hsize : ∀ a, ∀ e ∈ edges a, e.card ≤ r - 1) (D : Finset α) (a₀ : α) (ha₀ : a₀ ∉ D)
    (M : α → Finset β) (hM : IsMatchingOn edges D M) :
    ∀ L : List (α × Finset β), Valid edges a₀ M L →
      (used L ∪ (reach a₀ M L).biUnion M).card ≤ (2 * r - 3) * ((reach a₀ M L).card - 1)
  | [] => by simp [used, reach, hM.2.1 a₀ ha₀]
  | x :: L => by
    intro hV
    obtain ⟨hV', hx1, hx2, hxu, hxr, hYne⟩ := hV
    have ih := cover_bound edges r hr hsize D a₀ ha₀ M hM L hV'
    obtain ⟨y, hy⟩ := hYne
    have hMle : ∀ v, (M v).card ≤ r - 1 := fun v => by
      by_cases hv : v ∈ D
      · exact hsize v _ (hM.1 v hv)
      · simp [hM.2.1 v hv]
    have hdisj : Disjoint (reach a₀ M L) (Y M x.2) := by
      rw [disjoint_left]
      intro v hv hvY
      exact mem_Y.1 hvY (hxr v hv).symm
    have hcard_reach : (reach a₀ M (x :: L)).card = (reach a₀ M L).card + (Y M x.2).card := by
      simp only [reach]
      exact card_union_of_disjoint hdisj
    have hpos : 1 ≤ (reach a₀ M L).card := card_pos.mpr ⟨a₀, mem_reach_self a₀ M L⟩
    have hc : 1 ≤ (Y M x.2).card := card_pos.mpr ⟨y, hy⟩
    have key : (x.2 ∪ (Y M x.2).biUnion M).card ≤ (2 * r - 3) * (Y M x.2).card := by
      have h1 : (Y M x.2).biUnion M = M y ∪ ((Y M x.2).erase y).biUnion M := by
        rw [← biUnion_insert, insert_erase hy]
      have h2 : (((Y M x.2).erase y).biUnion M).card ≤ ((Y M x.2).card - 1) * (r - 1) := by
        calc _ ≤ ∑ v ∈ (Y M x.2).erase y, (M v).card := card_biUnion_le
          _ ≤ ∑ _v ∈ (Y M x.2).erase y, (r - 1) := sum_le_sum fun v _ => hMle v
          _ = _ := by simp [card_erase_of_mem hy]
      have h3 : (x.2 ∪ M y).card ≤ 2 * r - 3 := by
        have hu := card_union_add_card_inter x.2 (M y)
        have hi : (x.2 ∩ M y).Nonempty := by
          rw [← not_disjoint_iff_nonempty_inter]
          exact fun h => mem_Y.1 hy h.symm
        have := hi.card_pos
        have := hsize _ _ hx2
        have := hMle y
        omega
      have h4 : (2 * r - 3) + ((Y M x.2).card - 1) * (r - 1) ≤ (2 * r - 3) * (Y M x.2).card := by
        obtain ⟨c, hc'⟩ : ∃ c, (Y M x.2).card = c + 1 := ⟨_, (Nat.sub_add_cancel hc).symm⟩
        rw [hc', Nat.add_sub_cancel, mul_add, mul_one, add_comm (2 * r - 3), mul_comm c]
        exact Nat.add_le_add_right (Nat.mul_le_mul_right c (by omega)) _
      calc (x.2 ∪ (Y M x.2).biUnion M).card
          = ((x.2 ∪ M y) ∪ ((Y M x.2).erase y).biUnion M).card := by rw [h1, union_assoc]
        _ ≤ (x.2 ∪ M y).card + (((Y M x.2).erase y).biUnion M).card := card_union_le _ _
        _ ≤ (2 * r - 3) + ((Y M x.2).card - 1) * (r - 1) := add_le_add h3 h2
        _ ≤ _ := h4
    have hset : used (x :: L) ∪ (reach a₀ M (x :: L)).biUnion M ⊆
        (used L ∪ (reach a₀ M L).biUnion M) ∪ (x.2 ∪ (Y M x.2).biUnion M) := by
      rw [show reach a₀ M (x :: L) = reach a₀ M L ∪ Y M x.2 from rfl, union_biUnion]
      intro z hz
      simp only [used, mem_union] at hz ⊢
      tauto
    calc _ ≤ ((used L ∪ (reach a₀ M L).biUnion M) ∪ (x.2 ∪ (Y M x.2).biUnion M)).card :=
          card_le_card hset
      _ ≤ (used L ∪ (reach a₀ M L).biUnion M).card + (x.2 ∪ (Y M x.2).biUnion M).card :=
          card_union_le _ _
      _ ≤ (2 * r - 3) * ((reach a₀ M L).card - 1) + (2 * r - 3) * (Y M x.2).card :=
          add_le_add ih key
      _ = (2 * r - 3) * ((reach a₀ M (x :: L)).card - 1) := by
          rw [hcard_reach, ← mul_add]
          congr 1
          omega

/-- Augmentation along the tree: an edge at a reached vertex avoiding the tree and all `M`-edges
either completes the matching or yields a lexicographically better tree. -/
lemma aug (edges : α → Finset (Finset β)) (D : Finset α) (a₀ : α) :
    ∀ (L : List (α × Finset β)) (M : α → Finset β), IsMatchingOn edges D M →
      Valid edges a₀ M L → ∀ (a : α) (e : Finset β), a ∈ reach a₀ M L → e ∈ edges a →
      Disjoint e (used L) → (∀ v, Disjoint (M v) e) →
      (∃ M', IsMatchingOn edges (insert a₀ D) M') ∨
      ∃ (M' : α → Finset β) (L' : List (α × Finset β)) (i : ℕ), IsMatchingOn edges D M' ∧
        Valid edges a₀ M' L' ∧ i < L.length ∧ (∀ j < i, pot M' L' j = pot M L j) ∧
        pot M L i < pot M' L' i
  | [], M, hM, _, a, e, ha, he, _, hMe => by
    left
    simp only [reach, mem_singleton] at ha
    subst ha
    refine ⟨Function.update M a e, ?_, ?_, ?_⟩
    · intro v hv
      rcases eq_or_ne v a with rfl | hva
      · rw [Function.update_self]; exact he
      · rw [Function.update_of_ne hva]
        exact hM.1 v ((mem_insert.1 hv).resolve_left hva)
    · intro v hv
      have hva : v ≠ a := fun h => hv (h ▸ mem_insert_self _ _)
      rw [Function.update_of_ne hva]
      exact hM.2.1 v fun h => hv (mem_insert_of_mem h)
    · intro v w hvw
      rcases eq_or_ne v a with rfl | hva
      · rw [Function.update_self, Function.update_of_ne hvw.symm]; exact (hMe w).symm
      · rcases eq_or_ne w a with rfl | hwa
        · rw [Function.update_self, Function.update_of_ne hva]; exact hMe v
        · rw [Function.update_of_ne hva, Function.update_of_ne hwa]; exact hM.2.2 v w hvw
  | x :: L, M, hM, hV, a, e, ha, he, hu, hMe => by
    have hV0 := hV
    obtain ⟨hV', hx1, hx2, hxu, hxr, hYne⟩ := hV
    simp only [used, disjoint_union_right] at hu
    by_cases haL : a ∈ reach a₀ M L
    · rcases aug edges D a₀ L M hM hV' a e haL he hu.1 hMe with h | ⟨M', L', i, h1, h2, h3, h4, h5⟩
      · exact Or.inl h
      · right
        refine ⟨M', L', i, h1, h2, by simp only [List.length_cons]; omega, fun j hj => ?_, ?_⟩
        · rw [h4 j hj, pot_cons_of_lt M x L (by omega)]
        · rwa [pot_cons_of_lt M x L h3]
    · have haY : a ∈ Y M x.2 := by
        simp only [reach, mem_union] at ha
        exact ha.resolve_left haL
      have haD : a ∈ D := by
        by_contra hD
        exact mem_Y.1 haY (by rw [hM.2.1 a hD]; exact disjoint_empty_left _)
      obtain ⟨hc1, hc2, hc3⟩ := congr_update edges a₀ M a e L haL hu.1
      set M' := Function.update M a e with hM'def
      have hM' : IsMatchingOn edges D M' := by
        refine ⟨?_, ?_, ?_⟩
        · intro v hv
          rcases eq_or_ne v a with rfl | hva
          · rw [hM'def, Function.update_self]; exact he
          · rw [hM'def, Function.update_of_ne hva]; exact hM.1 v hv
        · intro v hv
          have hva : v ≠ a := fun h => hv (h ▸ haD)
          rw [hM'def, Function.update_of_ne hva]
          exact hM.2.1 v hv
        · intro v w hvw
          rcases eq_or_ne v a with rfl | hva
          · rw [hM'def, Function.update_self, Function.update_of_ne hvw.symm]
            exact (hMe w).symm
          · rcases eq_or_ne w a with rfl | hwa
            · rw [hM'def, Function.update_self, Function.update_of_ne hva]; exact hMe v
            · rw [hM'def, Function.update_of_ne hva, Function.update_of_ne hwa]
              exact hM.2.2 v w hvw
      have hYx : Y M' x.2 = (Y M x.2).erase a := by
        ext v
        rw [mem_erase, mem_Y, mem_Y]
        rcases eq_or_ne v a with rfl | hva
        · rw [hM'def, Function.update_self]
          simp only [ne_eq, not_true_eq_false, false_and, iff_false, not_not]
          exact hu.2
        · rw [hM'def, Function.update_of_ne hva]
          exact ⟨fun h => ⟨hva, h⟩, fun h => h.2⟩
      by_cases hne : (Y M' x.2).Nonempty
      · right
        refine ⟨M', x :: L, L.length, hM', ⟨hc3 hV', hc1 ▸ hx1, hx2, hxu, ?_, hne⟩,
          by simp, ?_, ?_⟩
        · intro v hv
          rw [hc1] at hv
          have hva : v ≠ a := fun h => haL (h ▸ hv)
          rw [hM'def, Function.update_of_ne hva]
          exact hxr v hv
        · intro j hj
          rw [pot_cons_of_lt _ x L hj, pot_cons_of_lt _ x L hj, hc2]
        · rw [pot_cons_self, pot_cons_self, hYx, card_erase_of_mem haY]
          have : (Y M x.2).card ≤ Fintype.card α := card_le_univ _
          have : 1 ≤ (Y M x.2).card := card_pos.2 ⟨a, haY⟩
          omega
      · have hdis : ∀ v, Disjoint (M' v) x.2 := fun v => by
          by_contra h
          exact hne ⟨v, mem_Y.2 h⟩
        rcases aug edges D a₀ L M' hM' (hc3 hV') x.1 x.2 (hc1 ▸ hx1) hx2 hxu hdis with
          h | ⟨M'', L', i, h1, h2, h3, h4, h5⟩
        · exact Or.inl h
        · right
          refine ⟨M'', L', i, h1, h2, by simp only [List.length_cons]; omega,
            fun j hj => ?_, ?_⟩
          · rw [h4 j hj, hc2, pot_cons_of_lt M x L (by omega)]
          · rw [pot_cons_of_lt M x L h3, ← hc2]; exact h5

/-- Bounded potential as an element of a finite lexicographically ordered type. -/
def potF (M : α → Finset β) (L : List (α × Finset β)) :
    Lex (Fin (Fintype.card α) → Fin (Fintype.card α + 2)) :=
  toLex fun i => ⟨pot M L i, Nat.lt_succ_of_le (pot_le M L i)⟩

omit [DecidableEq α] in
lemma potF_lt {M M' : α → Finset β} {L L' : List (α × Finset β)} {i : ℕ}
    (hi : i < Fintype.card α) (h1 : ∀ j < i, pot M' L' j = pot M L j)
    (h2 : pot M L i < pot M' L' i) : potF M L < potF M' L' :=
  ⟨⟨i, hi⟩, fun j hj => Fin.ext (h1 j hj).symm, h2⟩

/-- Extending a matching of `D` to `insert a₀ D`. -/
lemma extend (edges : α → Finset (Finset β)) (r : ℕ) (hr : 2 ≤ r)
    (hsize : ∀ a, ∀ e ∈ edges a, e.card ≤ r - 1)
    (hcover : ∀ I : Finset α, I.Nonempty → ∀ C : Finset β,
      C.card ≤ (2 * r - 3) * (I.card - 1) → ∃ a ∈ I, ∃ e ∈ edges a, Disjoint e C)
    (D : Finset α) (a₀ : α) (ha₀ : a₀ ∉ D) (M : α → Finset β) (L : List (α × Finset β))
    (hM : IsMatchingOn edges D M) (hV : Valid edges a₀ M L) :
    ∃ M', IsMatchingOn edges (insert a₀ D) M' := by
  suffices H : ∀ p, ∀ (M : α → Finset β) (L : List (α × Finset β)), IsMatchingOn edges D M →
      Valid edges a₀ M L → potF M L = p → ∃ M', IsMatchingOn edges (insert a₀ D) M' from
    H _ M L hM hV rfl
  intro p
  induction p using WellFoundedGT.induction with
  | ind p ih =>
  intro M L hM hV hp
  subst hp
  obtain ⟨a, ha, e, he, hdisj⟩ := hcover (reach a₀ M L) ⟨a₀, mem_reach_self a₀ M L⟩
    (used L ∪ (reach a₀ M L).biUnion M) (cover_bound edges r hr hsize D a₀ ha₀ M hM L hV)
  rw [disjoint_union_right] at hdisj
  have hu := hdisj.1
  have hr' : ∀ v ∈ reach a₀ M L, Disjoint e (M v) := fun v hv =>
    disjoint_of_subset_right (subset_biUnion_of_mem M hv) hdisj.2
  have hlen := length_lt_card edges a₀ M L hV
  by_cases hne : (Y M e).Nonempty
  · have hV' : Valid edges a₀ M ((a, e) :: L) := ⟨hV, ha, he, hu, hr', hne⟩
    refine ih _ (potF_lt (i := L.length) hlen (fun j hj => ?_) ?_) M _ hM hV' rfl
    · exact pot_cons_of_lt M _ L hj
    · rw [pot_cons_self, pot_of_ge M L _ le_rfl]
      have : (Y M e).card ≤ Fintype.card α := card_le_univ _
      dsimp only
      omega
  · have hMe : ∀ v, Disjoint (M v) e := fun v => by
      by_contra h
      exact hne ⟨v, mem_Y.2 h⟩
    rcases aug edges D a₀ L M hM hV a e ha he hu hMe with h | ⟨M', L', i, h1, h2, h3, h4, h5⟩
    · exact h
    · exact ih _ (potF_lt (by omega) h4 h5) M' L' h1 h2 rfl

lemma exists_matchingOn (edges : α → Finset (Finset β)) (r : ℕ) (hr : 2 ≤ r)
    (hsize : ∀ a, ∀ e ∈ edges a, e.card ≤ r - 1)
    (hcover : ∀ I : Finset α, I.Nonempty → ∀ C : Finset β,
      C.card ≤ (2 * r - 3) * (I.card - 1) → ∃ a ∈ I, ∃ e ∈ edges a, Disjoint e C)
    (D : Finset α) : ∃ M, IsMatchingOn edges D M := by
  induction D using Finset.induction_on with
  | empty => exact ⟨fun _ => ∅, by simp, fun _ _ => rfl, by simp⟩
  | insert a₀ D ha₀ ih =>
    obtain ⟨M, hM⟩ := ih
    exact extend edges r hr hsize hcover D a₀ ha₀ M [] hM trivial

end Haxell

/-- **Haxell's theorem.** A hypergraph on `A ∪ B` in which every edge meets `A` in one vertex
`a` and `B` in at most `r - 1` vertices (the `B`-parts of the edges at `a` are `edges a`).
If for every nonempty `I ⊆ A` the family of `B`-parts of edges meeting `I` has vertex-cover
number greater than `(2r - 3)(|I| - 1)`, then there is a matching saturating `A`. -/
theorem haxell {α β : Type*} [Finite α] (r : ℕ) (hr : 2 ≤ r)
    (edges : α → Finset (Finset β)) (hsize : ∀ a, ∀ e ∈ edges a, e.card ≤ r - 1)
    (hcover : ∀ I : Finset α, I.Nonempty → ∀ C : Finset β,
      C.card ≤ (2 * r - 3) * (I.card - 1) → ∃ a ∈ I, ∃ e ∈ edges a, Disjoint e C) :
    ∃ f : α → Finset β, (∀ a, f a ∈ edges a) ∧ ∀ a a', a ≠ a' → Disjoint (f a) (f a') := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨M, hM⟩ := Haxell.exists_matchingOn edges r hr hsize hcover univ
  exact ⟨M, fun a => hM.1 a (mem_univ a), hM.2.2⟩

end Lovasz
