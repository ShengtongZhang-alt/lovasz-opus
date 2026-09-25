/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 3.6: linear-size Hamilton routers

DAG node `L3.6` of `docs/BLUEPRINT.md`.

For a setting `σ` of the comparators (`σ j = true`: comparator `j` crossed), the union of `Q`
and the chosen path systems of the comparators is a spanning path system whose paths join the
inputs to the outputs; the input leaving at output `i < w - 1` is
`if σ i then i + 1 else routerCarry σ i`, and output `w - 1` receives `routerCarry σ (w - 1)`.
Given the outside matching, the settings are chosen greedily (`greedySigma`) so that each
output edge merges two classes of wires, which makes the union with the matching connected.
-/

namespace Lovasz

open Set

namespace Router

section Aux

variable {V : Type*}


variable {V : Type*}

lemma reachable_mem_of_adj_mem {P : SimpleGraph V} {A : Set V}
    (h : ∀ x y, P.Adj x y → x ∈ A ∧ y ∈ A) {u v : V} (hr : P.Reachable u v) (hu : u ∈ A) :
    v ∈ A := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact hu
  | cons hadj p ih => exact ih (h _ _ hadj).2

/-- A component of a path system contains at most two endpoints. -/
lemma pathSystem_false_of_three [Fintype V] {P : SimpleGraph V} {A T : Set V}
    (hP : IsPathSystem P A T) {t a b : V} (ht : t ∈ T) (ha : a ∈ T) (hb : b ∈ T)
    (hta : t ≠ a) (htb : t ≠ b) (hab : a ≠ b) (hra : P.Reachable t a)
    (hrb : P.Reachable t b) : False := by
  classical
  set C := P.connectedComponentMk t with hC
  have hmem : ∀ v, v ∈ C.supp ↔ P.Reachable v t := fun v => by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, hC, SimpleGraph.ConnectedComponent.eq]
  have hA : ∀ v ∈ C.supp, v ∈ A := fun v hv =>
    reachable_mem_of_adj_mem hP.adj_mem ((hmem v).1 hv).symm (hP.subset ht)
  set H := C.toSimpleGraph with hH
  have hconn : H.Connected := C.connected_toSimpleGraph
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  have h2 := H.sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v : C, H.degree v + (if (v : V) ∈ T then 1 else 0) = 2 := by
    intro v
    have hv : H.degree v = (P.neighborSet v).ncard := by
      rw [← SimpleGraph.ncard_neighborSet, ← Set.ncard_image_of_injective _ Subtype.val_injective]
      congr 1
      ext u
      simp only [Set.mem_image, SimpleGraph.mem_neighborSet]
      constructor
      · rintro ⟨u', hu', rfl⟩
        exact hu'
      · intro hu
        have hu' : u ∈ C.supp := (hmem u).2 (hu.reachable.symm.trans ((hmem v).1 v.2))
        exact ⟨⟨u, hu'⟩, hu, rfl⟩
    rw [hv]
    split_ifs with hvT
    · rw [hP.deg_end _ hvT]
    · rw [hP.deg_inner _ (hA _ v.2) hvT]
  have hsum : ∑ v : C, (H.degree v + (if (v : V) ∈ T then 1 else 0)) =
      2 * Fintype.card C := by
    rw [Finset.sum_congr rfl (fun v _ => hdeg v)]
    simp [mul_comm]
  rw [Finset.sum_add_distrib, h2, Finset.sum_boole] at hsum
  have h3 : 3 ≤ (Finset.univ.filter fun v : C => (v : V) ∈ T).card := by
    have htC : t ∈ C.supp := (hmem t).2 (SimpleGraph.Reachable.refl t)
    have haC : a ∈ C.supp := (hmem a).2 hra.symm
    have hbC : b ∈ C.supp := (hmem b).2 hrb.symm
    have hsub : ({⟨t, htC⟩, ⟨a, haC⟩, ⟨b, hbC⟩} : Finset C) ⊆
        Finset.univ.filter fun v : C => (v : V) ∈ T := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hv with rfl | rfl | rfl <;> assumption
    refine le_trans ?_ (Finset.card_le_card hsub)
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton, Subtype.mk.injEq]
      exact hab
    · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
      exact ⟨hta, htb⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at h1
  simp only [Nat.cast_id] at hsum
  omega


lemma induce_reachable_of_closed {G : SimpleGraph V} {s : Set V}
    (hs : ∀ x y, G.Adj x y → x ∈ s → y ∈ s) {u v : V} (h : G.Reachable u v) (hu : u ∈ s) :
    ∃ hv : v ∈ s, (G.induce s).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ⟨hu, SimpleGraph.Reachable.refl _⟩
  | cons hadj p ih =>
    obtain ⟨hv, h⟩ := ih (hs _ _ hadj hu)
    have h' : (G.induce s).Adj ⟨_, hu⟩ ⟨_, hs _ _ hadj hu⟩ := hadj
    exact ⟨hv, h'.reachable.trans h⟩

lemma induce_connected_of_reachable {G : SimpleGraph V} {s : Set V}
    (hs : ∀ x y, G.Adj x y → x ∈ s → y ∈ s) {r : V} (hr : r ∈ s)
    (h : ∀ v ∈ s, G.Reachable v r) : (G.induce s).Connected := by
  have key : ∀ v : s, (G.induce s).Reachable v ⟨r, hr⟩ := fun v => by
    obtain ⟨_, h'⟩ := induce_reachable_of_closed hs (h v v.2) v.2
    exact h'
  have : Nonempty s := ⟨⟨r, hr⟩⟩
  exact ⟨fun u v => (key u).trans (key v).symm⟩

end Aux

/-- The logical wire carried out of comparator `j - 1` into comparator `j` under the setting
`σ` (`σ j = true`: comparator `j` crossed). -/
def routerCarry (σ : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if σ j then routerCarry σ j else j + 1

lemma routerCarry_le (σ : ℕ → Bool) (j : ℕ) : routerCarry σ j ≤ j := by
  induction j with
  | zero => simp [routerCarry]
  | succ j ih =>
    simp only [routerCarry]
    split_ifs <;> omega

/-- Every input wire `k ≤ j` has left through some output `i < j` or is the current carry. -/
lemma routerCarry_surj (σ : ℕ → Bool) (j : ℕ) :
    ∀ k ≤ j, k = routerCarry σ j ∨
      ∃ i < j, (if σ i then i + 1 else routerCarry σ i) = k := by
  induction j with
  | zero => intro k hk; left; simp [routerCarry]; omega
  | succ j ih =>
    intro k hk
    rcases Nat.lt_or_ge k (j + 1) with hk' | hk'
    · rcases ih k (by omega) with h | ⟨i, hi, h⟩
      · by_cases hσ : σ j
        · left; simp [routerCarry, hσ, h]
        · right; exact ⟨j, by omega, by simp [hσ, h]⟩
      · right; exact ⟨i, by omega, h⟩
    · have hk'' : k = j + 1 := by omega
      subst hk''
      by_cases hσ : σ j
      · right; exact ⟨j, by omega, by simp [hσ]⟩
      · left; simp [routerCarry, hσ]

/-- The greedy choice of comparator settings: the state after `j` comparators is the current
carry and a map sending every wire to the open wire of its current class. -/
noncomputable def greedyState (τ : ℕ → ℕ) : ℕ → ℕ × (ℕ → ℕ)
  | 0 => (0, id)
  | j + 1 =>
    if (greedyState τ j).2 (τ j) = (greedyState τ j).1 then
      ((greedyState τ j).1, fun k => if (greedyState τ j).2 k = j + 1 then
        (greedyState τ j).2 (τ j) else (greedyState τ j).2 k)
    else
      (j + 1, fun k => if (greedyState τ j).2 k = (greedyState τ j).1 then
        (greedyState τ j).2 (τ j) else (greedyState τ j).2 k)

/-- The greedy setting of comparator `j`. -/
noncomputable def greedySigma (τ : ℕ → ℕ) (j : ℕ) : Bool :=
  decide ((greedyState τ j).2 (τ j) = (greedyState τ j).1)

lemma greedyState_fst (τ : ℕ → ℕ) (j : ℕ) :
    (greedyState τ j).1 = routerCarry (greedySigma τ) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [greedyState, routerCarry, greedySigma]
    split_ifs with h <;> simp_all

/-- The greedy settings make the graph of wire classes connected: if `R` is an equivalence
relation containing every edge `ρ i – τ i` (`i < w - 1`), where `ρ i` is the input wire leaving
at output `i`, then every wire is `R`-related to the final carry. -/
lemma greedy_connects (w : ℕ) (hw : 1 ≤ w) (τ : ℕ → ℕ) (hτ : ∀ i < w, τ i < w)
    (R : ℕ → ℕ → Prop) (hR : Equivalence R)
    (hedge : ∀ i, i + 1 < w →
      R (if greedySigma τ i then i + 1 else routerCarry (greedySigma τ) i) (τ i)) :
    ∀ k < w, R k (routerCarry (greedySigma τ) (w - 1)) := by
  have key : ∀ j, j + 1 ≤ w →
      (∀ k < w, (greedyState τ j).2 k = (greedyState τ j).1 ∨
        (j + 1 ≤ (greedyState τ j).2 k ∧ (greedyState τ j).2 k < w)) ∧
      (∀ u, (u = (greedyState τ j).1 ∨ (j + 1 ≤ u ∧ u < w)) → (greedyState τ j).2 u = u) ∧
      (∀ k < w, R k ((greedyState τ j).2 k)) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun k hk => ?_, fun u _ => rfl, fun k _ => hR.refl k⟩
      simp only [greedyState, id]
      omega
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      have hc : (greedyState τ j).1 ≤ j := by
        rw [greedyState_fst]; exact routerCarry_le _ _
      set c := (greedyState τ j).1 with hcdef
      set s := (greedyState τ j).2 with hsdef
      have he : R (if s (τ j) = c then j + 1 else c) (τ j) := by
        have := hedge j (by omega)
        rw [← greedyState_fst] at this
        simp only [greedySigma, decide_eq_true_eq] at this
        exact this
      have hτj := hτ j (by omega)
      have ha := h1 _ hτj
      have hra := h3 _ hτj
      by_cases hsc : s (τ j) = c
      · have hst : greedyState τ (j + 1) = (c, fun k => if s k = j + 1 then s (τ j) else s k) := by
          simp only [greedyState, ← hsdef, ← hcdef, hsc, ↓reduceIte]
        rw [hst]
        simp only [hsc, ↓reduceIte] at he
        refine ⟨fun k hk => ?_, fun u hu => ?_, fun k hk => ?_⟩
        · dsimp only
          split_ifs with hk'
          · left; exact hsc
          · rcases h1 k hk with h | h
            · left; exact h
            · right; omega
        · dsimp only at hu ⊢
          have hu' : s u = u := h2 u (by omega)
          simp only [hu']
          split_ifs <;> first | rfl | omega
        · dsimp only
          split_ifs with hk'
          · have := h3 k hk
            rw [hk'] at this
            exact hR.trans this (hR.trans he hra)
          · exact h3 k hk
      · have hst : greedyState τ (j + 1) =
            (j + 1, fun k => if s k = c then s (τ j) else s k) := by
          simp only [greedyState, ← hsdef, ← hcdef, hsc, ↓reduceIte]
        rw [hst]
        simp only [hsc, ↓reduceIte] at he
        have ha' : j + 1 ≤ s (τ j) ∧ s (τ j) < w := by
          rcases ha with h | h
          · exact absurd h hsc
          · exact h
        refine ⟨fun k hk => ?_, fun u hu => ?_, fun k hk => ?_⟩
        · dsimp only
          split_ifs with hk'
          · omega
          · rcases h1 k hk with h | h
            · exact absurd h hk'
            · omega
        · dsimp only at hu ⊢
          have hu' : s u = u := h2 u (by omega)
          simp only [hu']
          split_ifs <;> first | rfl | omega
        · dsimp only
          split_ifs with hk'
          · have := h3 k hk
            rw [hk'] at this
            exact hR.trans this (hR.trans he hra)
          · exact h3 k hk
  obtain ⟨h1, -, h3⟩ := key (w - 1) (by omega)
  intro k hk
  have := h3 k hk
  rcases h1 k hk with h | h
  · rw [h, greedyState_fst] at this; exact this
  · omega

end Router

open Router in
/-- **Lemma 3.6 (Linear-size router).** For `w ≥ 2`, place comparators `0, …, w-2` in
succession between logical wires `j` and `j+1`. The fixed connections of the template are
`I₀ – x₁(0)`, `I₁ – x₂(0)`, `y₂(j) – x₁(j+1)` and `I_{j+2} – x₂(j+1)` for `j + 2 < w`,
`y₁(j) – O_j` for `j < w - 1`, and `y₂(w-2) – O_{w-1}`. Replacing the comparators by arbitrary
comparators on disjoint vertex sets and the fixed connections by vertex-disjoint paths (a path
system `Q` on `B` meeting each comparator only in its terminals) gives an `I, O`-Hamilton
router. -/
theorem router_of_comparators {V : Type*} [Fintype V] [DecidableEq V] (w : ℕ) (hw : 2 ≤ w)
    (A : ℕ → Set V) (K : ℕ → SimpleGraph V) (x₁ x₂ y₁ y₂ : ℕ → V) (I O : ℕ → V)
    (hcomp : ∀ j < w - 1, IsComparator (K j) (A j) (x₁ j) (x₂ j) (y₁ j) (y₂ j))
    (hAdisj : ∀ j < w - 1, ∀ j' < w - 1, j ≠ j' → Disjoint (A j) (A j'))
    (hI : InjOn I (Iio w)) (hO : InjOn O (Iio w)) (hIO : ∀ k < w, ∀ k' < w, I k ≠ O k')
    (hIOA : ∀ k < w, ∀ j < w - 1, I k ∉ A j ∧ O k ∉ A j)
    (Q : SimpleGraph V) (B : Set V)
    (hQ : IsPathSystem Q B (I '' Iio w ∪ O '' Iio w ∪
      ⋃ j ∈ Iio (w - 1), ({x₁ j, x₂ j, y₁ j, y₂ j} : Set V)))
    (hB : ∀ j < w - 1, B ∩ A j = {x₁ j, x₂ j, y₁ j, y₂ j})
    (hc₁ : Q.Reachable (I 0) (x₁ 0)) (hc₂ : Q.Reachable (I 1) (x₂ 0))
    (hc₃ : ∀ j, j + 2 < w → Q.Reachable (y₂ j) (x₁ (j + 1)) ∧ Q.Reachable (I (j + 2)) (x₂ (j + 1)))
    (hc₄ : ∀ j < w - 1, Q.Reachable (y₁ j) (O j)) (hc₅ : Q.Reachable (y₂ (w - 2)) (O (w - 1))) :
    IsHamRouter (Q ⊔ ⨆ j ∈ Iio (w - 1), K j) (B ∪ ⋃ j ∈ Iio (w - 1), A j) (I '' Iio w)
      (O '' Iio w) := by
  classical
  set TQ : Set V := I '' Iio w ∪ O '' Iio w ∪
    ⋃ j ∈ Iio (w - 1), ({x₁ j, x₂ j, y₁ j, y₂ j} : Set V) with hTQ
  set AA : Set V := B ∪ ⋃ j ∈ Iio (w - 1), A j with hAA
  set TT : Set V := I '' Iio w ∪ O '' Iio w with hTT
  have hIT : ∀ k < w, I k ∈ TQ := fun k hk => Or.inl (Or.inl ⟨k, hk, rfl⟩)
  have hOT : ∀ k < w, O k ∈ TQ := fun k hk => Or.inl (Or.inr ⟨k, hk, rfl⟩)
  have hCT : ∀ j < w - 1, ∀ t ∈ ({x₁ j, x₂ j, y₁ j, y₂ j} : Set V), t ∈ TQ :=
    fun j hj t ht => Or.inr (Set.mem_biUnion (x := j) hj ht)
  have hCA : ∀ j < w - 1, ({x₁ j, x₂ j, y₁ j, y₂ j} : Set V) ⊆ A j := fun j hj => by
    rw [← hB j hj]; exact Set.inter_subset_right
  have hCB : ∀ j < w - 1, ({x₁ j, x₂ j, y₁ j, y₂ j} : Set V) ⊆ B := fun j hj => by
    rw [← hB j hj]; exact Set.inter_subset_left
  have hTTQ : TT ⊆ TQ := Set.subset_union_left
  have hmemAA : ∀ j < w - 1, A j ⊆ AA := fun j hj v hv =>
    Or.inr (Set.mem_biUnion (x := j) (Set.mem_Iio.2 hj) hv)
  have hTTA : ∀ t ∈ TT, ∀ j < w - 1, t ∉ A j := by
    rintro t (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) j hj
    · exact (hIOA k hk j hj).1
    · exact (hIOA k hk j hj).2
  -- the two path systems of each comparator
  have hstr : ∀ j, ∃ P : SimpleGraph V, j < w - 1 → P ≤ K j ∧
      IsPathSystem P (A j) {x₁ j, x₂ j, y₁ j, y₂ j} ∧ P.Reachable (x₁ j) (y₁ j) ∧
      P.Reachable (x₂ j) (y₂ j) := by
    intro j
    by_cases hj : j < w - 1
    · obtain ⟨P, h1, h2, h3, h4⟩ := (hcomp j hj).2.1
      exact ⟨P, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨⊥, fun h => absurd h hj⟩
  choose Ps hPs using hstr
  have hcr : ∀ j, ∃ P : SimpleGraph V, j < w - 1 → P ≤ K j ∧
      IsPathSystem P (A j) {x₁ j, x₂ j, y₁ j, y₂ j} ∧ P.Reachable (x₁ j) (y₂ j) ∧
      P.Reachable (x₂ j) (y₁ j) := by
    intro j
    by_cases hj : j < w - 1
    · obtain ⟨P, h1, h2, h3, h4⟩ := (hcomp j hj).2.2
      exact ⟨P, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨⊥, fun h => absurd h hj⟩
  choose Pc hPc using hcr
  set RR : (ℕ → Bool) → ℕ → SimpleGraph V := fun σ j => if σ j then Pc j else Ps j with hRRdef
  have hRR : ∀ σ : ℕ → Bool, ∀ j < w - 1, RR σ j ≤ K j ∧
      IsPathSystem (RR σ j) (A j) {x₁ j, x₂ j, y₁ j, y₂ j} ∧
      (RR σ j).Reachable (x₁ j) (if σ j then y₂ j else y₁ j) ∧
      (RR σ j).Reachable (x₂ j) (if σ j then y₁ j else y₂ j) := by
    intro σ j hj
    by_cases hσ : σ j
    · simp only [RR, hσ, ↓reduceIte]; exact hPc j hj
    · simp only [RR, hσ, Bool.false_eq_true, ↓reduceIte]; exact hPs j hj
  set GG : (ℕ → Bool) → SimpleGraph V := fun σ => Q ⊔ ⨆ j ∈ Iio (w - 1), RR σ j with hGGdef
  have hQG : ∀ σ, Q ≤ GG σ := fun σ => le_sup_left
  have hRG : ∀ σ, ∀ j < w - 1, RR σ j ≤ GG σ := fun σ j hj =>
    le_sup_of_le_right (le_iSup₂_of_le (f := fun j (_ : j ∈ Iio (w - 1)) => RR σ j) j
      (Set.mem_Iio.2 hj) le_rfl)
  have hRadj : ∀ σ, ∀ j < w - 1, ∀ x y, (RR σ j).Adj x y → x ∈ A j ∧ y ∈ A j :=
    fun σ j hj => (hRR σ j hj).2.1.adj_mem
  have hGadj : ∀ σ x y, (GG σ).Adj x y ↔ Q.Adj x y ∨ ∃ j < w - 1, (RR σ j).Adj x y := by
    intro σ x y
    simp only [GG, SimpleGraph.sup_adj, SimpleGraph.iSup_adj, Set.mem_Iio, exists_prop]
  -- the other endpoint of the `Q`-path at a comparator terminal lies outside the comparator
  have hpartner : ∀ j < w - 1, ∀ t ∈ ({x₁ j, x₂ j, y₁ j, y₂ j} : Set V),
      ∃ p ∈ TQ, p ∉ A j ∧ Q.Reachable t p := by
    intro j hj t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · rcases j with _ | j
      · exact ⟨I 0, hIT 0 (by omega), (hIOA 0 (by omega) 0 hj).1, hc₁.symm⟩
      · refine ⟨y₂ j, hCT j (by omega) _ (by simp), fun hmem => ?_, ((hc₃ j (by omega)).1).symm⟩
        exact Set.disjoint_left.1 (hAdisj j (by omega) (j + 1) hj (by omega))
          (hCA j (by omega) (by simp)) hmem
    · rcases j with _ | j
      · exact ⟨I 1, hIT 1 (by omega), (hIOA 1 (by omega) 0 hj).1, hc₂.symm⟩
      · exact ⟨I (j + 2), hIT _ (by omega), (hIOA _ (by omega) _ hj).1,
          ((hc₃ j (by omega)).2).symm⟩
    · exact ⟨O j, hOT j (by omega), (hIOA j (by omega) j hj).2, hc₄ j hj⟩
    · by_cases hj2 : j + 2 < w
      · refine ⟨x₁ (j + 1), hCT (j + 1) (by omega) _ (by simp), fun hmem => ?_, (hc₃ j hj2).1⟩
        exact Set.disjoint_left.1 (hAdisj (j + 1) (by omega) j hj (by omega))
          (hCA (j + 1) (by omega) (by simp)) hmem
      · have hj' : j = w - 2 := by omega
        subst hj'
        exact ⟨O (w - 1), hOT _ (by omega), (hIOA _ (by omega) _ hj).2, hc₅⟩
  have hQnbr : ∀ j < w - 1, ∀ t ∈ ({x₁ j, x₂ j, y₁ j, y₂ j} : Set V), ∀ u, Q.Adj t u →
      u ∉ A j := by
    intro j hj t ht u hu huA
    obtain ⟨p, hpT, hpA, hp⟩ := hpartner j hj t ht
    have huC : u ∈ ({x₁ j, x₂ j, y₁ j, y₂ j} : Set V) := by
      rw [← hB j hj]; exact ⟨(hQ.adj_mem _ _ hu).2, huA⟩
    exact pathSystem_false_of_three hQ (hCT j hj t ht) (hCT j hj u huC) hpT hu.ne
      (fun h => hpA (h ▸ hCA j hj ht)) (fun h => hpA (h ▸ huA)) hu.reachable hp
  -- neighbourhoods in `GG σ`
  have hnbr_in : ∀ σ, ∀ j < w - 1, ∀ v ∈ A j,
      (GG σ).neighborSet v = Q.neighborSet v ∪ (RR σ j).neighborSet v := by
    intro σ j hj v hv
    ext u
    simp only [SimpleGraph.mem_neighborSet, Set.mem_union, hGadj]
    constructor
    · rintro (h | ⟨j', hj', h⟩)
      · exact Or.inl h
      · right
        by_cases hjj : j' = j
        · subst hjj; exact h
        · exact absurd (hRadj σ j' hj' _ _ h).1
            (Set.disjoint_left.1 (hAdisj j hj j' hj' (Ne.symm hjj)) hv)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, h⟩
  have hnbr_out : ∀ σ, ∀ v, (∀ j < w - 1, v ∉ A j) → (GG σ).neighborSet v = Q.neighborSet v := by
    intro σ v hv
    ext u
    simp only [SimpleGraph.mem_neighborSet, hGadj]
    constructor
    · rintro (h | ⟨j', hj', h⟩)
      · exact h
      · exact absurd (hRadj σ j' hj' _ _ h).1 (hv j' hj')
    · exact Or.inl
  have hQempty : ∀ v ∉ B, Q.neighborSet v = ∅ := fun v hv =>
    Set.eq_empty_of_forall_notMem (fun u hu => hv (hQ.adj_mem _ _ hu).1)
  -- following the wires
  have W2 : ∀ σ, ∀ j < w - 1, (GG σ).Reachable (I (j + 1)) (x₂ j) := by
    intro σ j hj
    apply SimpleGraph.Reachable.mono (hQG σ)
    rcases j with _ | j
    · exact hc₂
    · exact (hc₃ j (by omega)).2
  have W1 : ∀ σ, ∀ j < w - 1, (GG σ).Reachable (I (routerCarry σ j)) (x₁ j) := by
    intro σ j
    induction j with
    | zero => intro _; exact hc₁.mono (hQG σ)
    | succ j ih =>
      intro hj
      have hy : (GG σ).Reachable (y₂ j) (x₁ (j + 1)) := (hc₃ j (by omega)).1.mono (hQG σ)
      obtain ⟨-, -, h1, h2⟩ := hRR σ j (by omega)
      by_cases hσ : σ j
      · simp only [routerCarry, hσ, ↓reduceIte] at h1 ⊢
        exact (ih (by omega)).trans ((h1.mono (hRG σ j (by omega))).trans hy)
      · simp only [routerCarry, hσ, Bool.false_eq_true, ↓reduceIte] at h2 ⊢
        exact (W2 σ j (by omega)).trans ((h2.mono (hRG σ j (by omega))).trans hy)
  have W3 : ∀ σ, ∀ i < w - 1,
      (GG σ).Reachable (I (if σ i then i + 1 else routerCarry σ i)) (O i) := by
    intro σ i hi
    have hy : (GG σ).Reachable (y₁ i) (O i) := (hc₄ i hi).mono (hQG σ)
    obtain ⟨-, -, h1, h2⟩ := hRR σ i hi
    by_cases hσ : σ i
    · simp only [hσ, ↓reduceIte] at h2 ⊢
      exact (W2 σ i hi).trans ((h2.mono (hRG σ i hi)).trans hy)
    · simp only [hσ, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
      exact (W1 σ i hi).trans ((h1.mono (hRG σ i hi)).trans hy)
  have W4 : ∀ σ, (GG σ).Reachable (I (routerCarry σ (w - 1))) (O (w - 1)) := by
    intro σ
    have hw1 : w - 1 = (w - 2) + 1 := by omega
    have hy : (GG σ).Reachable (y₂ (w - 2)) (O (w - 1)) := hc₅.mono (hQG σ)
    obtain ⟨-, -, h1, h2⟩ := hRR σ (w - 2) (by omega)
    rw [hw1] at hy ⊢
    by_cases hσ : σ (w - 2)
    · simp only [routerCarry, hσ, ↓reduceIte] at h1 ⊢
      exact (W1 σ (w - 2) (by omega)).trans ((h1.mono (hRG σ _ (by omega))).trans hy)
    · simp only [routerCarry, hσ, Bool.false_eq_true, ↓reduceIte] at h2 ⊢
      exact (W2 σ (w - 2) (by omega)).trans ((h2.mono (hRG σ _ (by omega))).trans hy)
  have W5 : ∀ σ, ∀ j < w - 1, ∀ t ∈ ({x₁ j, x₂ j, y₁ j, y₂ j} : Set V),
      ∃ k < w, (GG σ).Reachable t (I k) := by
    intro σ j hj t ht
    have hc := routerCarry_le σ j
    have e1 := (W1 σ j hj).symm
    have e2 := (W2 σ j hj).symm
    obtain ⟨-, -, h1, h2⟩ := hRR σ j hj
    have h1' := h1.mono (hRG σ j hj)
    have h2' := h2.mono (hRG σ j hj)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨_, by omega, e1⟩
    · exact ⟨_, by omega, e2⟩
    · by_cases hσ : σ j
      · simp only [hσ, ↓reduceIte] at h2'
        exact ⟨_, by omega, h2'.symm.trans e2⟩
      · simp only [hσ, Bool.false_eq_true, ↓reduceIte] at h1'
        exact ⟨_, by omega, h1'.symm.trans e1⟩
    · by_cases hσ : σ j
      · simp only [hσ, ↓reduceIte] at h1'
        exact ⟨_, by omega, h1'.symm.trans e1⟩
      · simp only [hσ, Bool.false_eq_true, ↓reduceIte] at h2'
        exact ⟨_, by omega, h2'.symm.trans e2⟩
  -- every setting gives a spanning path system with endpoints `I ∪ O`
  have P1 : ∀ σ, IsPathSystem (GG σ) AA TT := by
    intro σ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x y h
      rcases (hGadj σ x y).1 h with h | ⟨j, hj, h⟩
      · exact ⟨Or.inl (hQ.adj_mem _ _ h).1, Or.inl (hQ.adj_mem _ _ h).2⟩
      · exact ⟨hmemAA j hj (hRadj σ j hj _ _ h).1, hmemAA j hj (hRadj σ j hj _ _ h).2⟩
    · exact fun t ht => Or.inl (hQ.subset (hTTQ ht))
    · intro t ht
      rw [hnbr_out σ t (hTTA t ht)]
      exact hQ.deg_end t (hTTQ ht)
    · intro v hv hvT
      by_cases hvA : ∃ j < w - 1, v ∈ A j
      · obtain ⟨j, hj, hvj⟩ := hvA
        rw [hnbr_in σ j hj v hvj]
        have hRsys := (hRR σ j hj).2.1
        by_cases hvB : v ∈ B
        · have hvC : v ∈ ({x₁ j, x₂ j, y₁ j, y₂ j} : Set V) := by
            rw [← hB j hj]; exact ⟨hvB, hvj⟩
          have hdisj : Disjoint (Q.neighborSet v) ((RR σ j).neighborSet v) := by
            rw [Set.disjoint_left]
            intro u hu hu'
            exact hQnbr j hj v hvC u hu (hRadj σ j hj _ _ hu').2
          rw [Set.ncard_union_eq hdisj, hQ.deg_end v (hCT j hj v hvC), hRsys.deg_end v hvC]
        · rw [hQempty v hvB, Set.empty_union]
          exact hRsys.deg_inner v hvj (fun h => hvB (hCB j hj h))
      · push Not at hvA
        rw [hnbr_out σ v hvA]
        have hvB : v ∈ B := by
          rcases hv with hv | hv
          · exact hv
          · simp only [Set.mem_iUnion, Set.mem_Iio] at hv
            obtain ⟨j, hj, hvj⟩ := hv
            exact absurd hvj (hvA j hj)
        apply hQ.deg_inner v hvB
        rintro ((h | h) | h)
        · exact hvT (Or.inl h)
        · exact hvT (Or.inr h)
        · simp only [Set.mem_iUnion, Set.mem_Iio] at h
          obtain ⟨j, hj, hvj⟩ := h
          exact hvA j hj (hCA j hj hvj)
    · intro v hv
      have fin : ∀ t ∈ TQ, ∃ t' ∈ TT, (GG σ).Reachable t t' := by
        rintro t (ht | ht)
        · exact ⟨t, ht, SimpleGraph.Reachable.refl _⟩
        · simp only [Set.mem_iUnion, Set.mem_Iio] at ht
          obtain ⟨j, hj, htj⟩ := ht
          obtain ⟨k, hk, h⟩ := W5 σ j hj t htj
          exact ⟨I k, Or.inl ⟨k, hk, rfl⟩, h⟩
      rcases hv with hv | hv
      · obtain ⟨t, ht, h⟩ := hQ.reach_end v hv
        obtain ⟨t', ht', h'⟩ := fin t ht
        exact ⟨t', ht', (h.mono (hQG σ)).trans h'⟩
      · simp only [Set.mem_iUnion, Set.mem_Iio] at hv
        obtain ⟨j, hj, hvj⟩ := hv
        obtain ⟨t, ht, h⟩ := (hRR σ j hj).2.1.reach_end v hvj
        obtain ⟨k, hk, h'⟩ := W5 σ j hj t ht
        exact ⟨I k, Or.inl ⟨k, hk, rfl⟩, (h.mono (hRG σ j hj)).trans h'⟩
  -- every input is joined to some output, hence to no other input
  have hIO_reach : ∀ σ, ∀ k < w, ∃ i < w, (GG σ).Reachable (I k) (O i) := by
    intro σ k hk
    rcases routerCarry_surj σ (w - 1) k (by omega) with h | ⟨i, hi, h⟩
    · exact ⟨w - 1, by omega, by rw [h]; exact W4 σ⟩
    · exact ⟨i, by omega, by rw [← h]; exact W3 σ i hi⟩
  have P2 : ∀ σ, ∀ x ∈ I '' Iio w, ∀ y ∈ I '' Iio w, (GG σ).Reachable x y → x = y := by
    rintro σ _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩ hr
    by_contra hne
    obtain ⟨i, hi, hri⟩ := hIO_reach σ k hk
    exact pathSystem_false_of_three (P1 σ) (Or.inl ⟨k, hk, rfl⟩) (Or.inr ⟨i, hi, rfl⟩)
      (Or.inl ⟨k', hk', rfl⟩) (hIO k hk i hi) hne (fun h => hIO k' hk' i hi h.symm) hri hr
  refine ⟨?_, ?_, fun t ht => Or.inl (hQ.subset (hTTQ ht)), ?_⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨k, hk, rfl⟩ ⟨k', hk', h⟩
    exact hIO k hk k' hk' h.symm
  · rw [hI.ncard_image, hO.ncard_image]
  intro β
  have hτ : ∀ i, ∃ k, ∀ hi : i < w, k < w ∧ I k = (β ⟨O i, ⟨i, hi, rfl⟩⟩ : V) := by
    intro i
    by_cases hi : i < w
    · obtain ⟨k, hk, e⟩ := (β ⟨O i, ⟨i, hi, rfl⟩⟩).2
      exact ⟨k, fun _ => ⟨hk, e⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose τ hτ using hτ
  set σ := greedySigma τ with hσdef
  set M := bijMatching β with hMdef
  have hM : ∀ i < w, M.Adj (O i) (I (τ i)) := by
    intro i hi
    rw [hMdef, bijMatching, SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨⟨O i, ⟨i, hi, rfl⟩⟩, ?_⟩, (hIO (τ i) (hτ i hi).1 i hi).symm⟩
    rw [(hτ i hi).2]
  have hMmem : ∀ x y, M.Adj x y → y ∈ TT := by
    intro x y h
    rw [hMdef, bijMatching, SimpleGraph.fromEdgeSet_adj] at h
    obtain ⟨⟨o, e⟩, -⟩ := h
    rcases Sym2.eq_iff.1 e with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inl (β o).2
    · exact Or.inr o.2
  refine ⟨GG σ, sup_le_sup_left (iSup₂_mono fun j hj => (hRR σ j hj).1) _, P1 σ, P2 σ, ?_⟩
  set c := routerCarry σ (w - 1) with hcdef
  have hcw : c < w := by have := routerCarry_le σ (w - 1); omega
  have hall : ∀ k < w, (GG σ ⊔ M).Reachable (I k) (I c) :=
    greedy_connects w (by omega) τ (fun i hi => (hτ i hi).1)
      (fun a b => (GG σ ⊔ M).Reachable (I a) (I b))
      ⟨fun _ => SimpleGraph.Reachable.refl _, fun h => h.symm, fun h h' => h.trans h'⟩
      (fun i hi => ((W3 σ i (by omega)).mono le_sup_left).trans
        ((hM i (by omega)).reachable.mono le_sup_right))
  refine induce_connected_of_reachable (r := I c) ?_ (Or.inl (hQ.subset (hIT c hcw))) ?_
  · intro x y h _
    rcases h with h | h
    · exact ((P1 σ).adj_mem _ _ h).2
    · exact Or.inl (hQ.subset (hTTQ (hMmem _ _ h)))
  · intro v hv
    obtain ⟨t, ht, hvt⟩ := (P1 σ).reach_end v hv
    refine (hvt.mono le_sup_left).trans ?_
    rcases ht with ⟨k, hk, rfl⟩ | ⟨i, hi, rfl⟩
    · exact hall k hk
    · exact ((hM i hi).reachable.mono le_sup_right).trans (hall _ (hτ i hi).1)

end Lovasz
