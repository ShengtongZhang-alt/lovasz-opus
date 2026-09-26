/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent)
-/
import Lovasz.Absorption.Basic

/-!
# `T3.2b`: the initial random partition of Section 3.3

DAG node `T3.2b` of `docs/BLUEPRINT.md`.

The probability space is the group `permG col E` of colour-preserving permutations of the
vertices fixing `E` pointwise, acting on a fixed labeling of `V \ E` with prescribed cell sizes.
For a fixed set `X` of one colour class, `π ↦ π '' X` is uniform on the subsets of that class of
size `|X|`, and for sets `X₁, X₂` of the two classes the pair `(π '' X₁, π '' X₂)` is uniform on
pairs of subsets (`fibre_count`). Thus Lemmas 2.2, 2.3 and the hypergeometric tail bounds,
which count subsets, bound the number of bad permutations, and a union bound gives a good one.

The labeling uses sub-cells `SC`: the cells of `Cell`, with `U` split into the new ports of the
tails, the dummy `dA` and the filler, and `V` split likewise. The events (`exists_good_perm`) are
the sampling events of Lemma 2.3 for `R₁, Q, Z` and for the two filler pairs of the special
transition (`PB`), degree concentration into nine unions of cells for all vertices of the
opposite colour (`DB`), and the norm part of (2.9) for the colour blocks of `I, O, U, V` (`NB`).
The deterministic part (`build`) derives every field of `InitPartition`; the numerical
conditions (3.1)–(3.2) enter through `NumCtx`. Deviations from the text, all harmless: the sets
`Q` and `C` are sampled directly as disjoint uniform sets (so `Q` is uniform and Lemma 2.1 is not
needed for its gap), the degree bound (3.9) on the new ports is replaced by the degree bound into
all of `C ∪ I ∪ O ∪ U ∪ V`, and the column-norm part of (2.9) is deduced deterministically from
the degree part.
-/

universe u

namespace Lovasz

open Finset

namespace LocalAbsorption

namespace InitPart

/-! ### Transfer along weight-preserving equivalences -/

section Transfer

variable {α β : Type*} [Fintype α] [Fintype β]

lemma deg_equiv (H₁ : WGraph α) (H₂ : WGraph β) (e : α ≃ β)
    (h : ∀ a a', H₂.w (e a) (e a') = H₁.w a a') (a : α) : H₂.deg (e a) = H₁.deg a := by
  unfold WGraph.deg
  rw [← e.sum_comp]
  exact sum_congr rfl fun a' _ => h a a'

lemma degNear_equiv (H₁ : WGraph α) (H₂ : WGraph β) (e : α ≃ β)
    (h : ∀ a a', H₂.w (e a) (e a') = H₁.w a a') {P η : ℝ} (hd : H₁.DegNear P η) :
    H₂.DegNear P η := by
  intro x
  obtain ⟨a, rfl⟩ := e.surjective x
  rw [deg_equiv H₁ H₂ e h a]
  exact hd a

lemma hasGap_equiv (H₁ : WGraph α) (H₂ : WGraph β) (e : α ≃ β)
    (h : ∀ a a', H₂.w (e a) (e a') = H₁.w a a') {s : ℝ} (hg : H₁.HasGap s) : H₂.HasGap s := by
  intro f
  obtain ⟨z, hz⟩ := hg (f ∘ e)
  refine ⟨z, ?_⟩
  have e1 : ∑ x, H₂.deg x * (f x - z) ^ 2 = ∑ a, H₁.deg a * ((f ∘ e) a - z) ^ 2 := by
    rw [← e.sum_comp]
    exact sum_congr rfl fun a _ => by rw [deg_equiv H₁ H₂ e h a]; rfl
  have e2 : H₂.dirichlet f = H₁.dirichlet (f ∘ e) := by
    unfold WGraph.dirichlet
    congr 1
    rw [← e.sum_comp]
    refine sum_congr rfl fun a _ => ?_
    rw [← e.sum_comp]
    exact sum_congr rfl fun a' _ => by rw [h]; rfl
  rw [e1, e2]
  exact hz

end Transfer

section Subtype

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The equivalence between a finset `S'` of the subtype `univ \ E` and its image in `V`. -/
noncomputable def mapEquiv (E : Finset V) (S' : Finset ↥(univ \ E)) :
    ↥S' ≃ ↥(S'.map (Function.Embedding.subtype _)) :=
  Equiv.ofBijective (fun x => ⟨x.1.1, mem_map_of_mem _ x.2⟩)
    ⟨fun x y h => by
      have h' := congrArg Subtype.val h
      dsimp only at h'
      exact Subtype.ext (Subtype.ext h'),
     fun y => by
      obtain ⟨x, hx, hxy⟩ := mem_map.1 y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

lemma mapEquiv_w (H : WGraph V) (E : Finset V) (S' : Finset ↥(univ \ E)) (a a' : ↥S') :
    (H.induce (S'.map (Function.Embedding.subtype _))).w (mapEquiv E S' a) (mapEquiv E S' a') =
      ((H.induce (univ \ E)).induce S').w a a' := rfl

end Subtype

/-! ### Lemma 2.3 in the ambient type -/

open Classical in
/-- The conclusion of Lemma 2.3 (`bipartite_sampling`) for fixed constants. -/
def BSProp (ω c₂ a c₁ c C : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (A B : Finset V) (N k : ℕ)
    (η D σ L : ℝ),
    Disjoint A B → A ∪ B = univ → A.card = N → B.card = N →
    (∀ x ∈ A, ∀ y ∈ A, H.w x y = 0) → (∀ x ∈ B, ∀ y ∈ B, H.w x y = 0) →
    H.WeightsIn ω → H.DegNear D η → H.HasGap σ → 0 < σ → σ ≤ 1 → η ≤ c * σ →
    Real.log (2 * N) ≤ L → k ≤ N → C * σ ^ (-2 : ℝ) * L ≤ (k : ℝ) / N * D →
    (((A.powersetCard k ×ˢ B.powersetCard k).filter fun UW =>
        ¬ ((H.induce (UW.1 ∪ UW.2)).DegNear ((k : ℝ) / N * D) (c₁ * σ) ∧
          (H.induce (UW.1 ∪ UW.2)).HasGap (c₂ * σ))).card : ℝ) ≤
      Real.exp (-(a * L)) * ((N.choose k : ℕ) : ℝ) ^ 2

lemma exists_BSProp (ω : ℝ) (hω : 0 < ω) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ a c₁ : ℝ, 0 < a → 0 < c₁ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      BSProp.{u} ω c₂ a c₁ c C :=
  bipartite_sampling.{u} ω hω

variable {V : Type u} [Fintype V] [DecidableEq V]

lemma classOf_disjoint (E : Finset V) (col : V → Bool) (b : Bool) :
    Disjoint (classOf E col b) (classOf E col (!b)) := by
  refine disjoint_left.2 fun x h1 h2 => ?_
  simp only [classOf, mem_filter] at h1 h2
  rw [h1.2] at h2
  cases b <;> simp at h2

lemma classOf_subset (E : Finset V) (col : V → Bool) (b : Bool) :
    classOf E col b ⊆ univ \ E := filter_subset _ _

lemma mem_classOf {E : Finset V} {col : V → Bool} {b : Bool} {x : V} :
    x ∈ classOf E col b ↔ x ∉ E ∧ col x = b := by
  simp [classOf]

omit [Fintype V] [DecidableEq V] in
lemma w_eq_zero_of_col (H : WGraph V) (col : V → Bool) (hbip : H.IsBipartiteWith col) {x y : V}
    (h : col x = col y) : H.w x y = 0 := by
  rcases (H.nonneg x y).lt_or_eq with h' | h'
  · exact absurd h (hbip x y h')
  · exact h'.symm

open Classical in
/-- **Lemma 2.3 for `H₀ = H - E`, in the ambient type.** -/
lemma bs_V {ω c₂ a c₁ c C : ℝ} (hbs : BSProp.{u} ω c₂ a c₁ c C)
    (H : WGraph V) (col : V → Bool) (E : Finset V) (b : Bool) (N₀ k : ℕ) (η₀ D σ₀ L : ℝ)
    (hbip : H.IsBipartiteWith col) (hw : H.WeightsIn ω)
    (hA : (classOf E col b).card = N₀) (hB : (classOf E col (!b)).card = N₀)
    (hdeg : (H.induce (univ \ E)).DegNear D η₀) (hgap : (H.induce (univ \ E)).HasGap σ₀)
    (hσ0 : 0 < σ₀) (hσ1 : σ₀ ≤ 1) (hη : η₀ ≤ c * σ₀) (hL : Real.log (2 * N₀) ≤ L)
    (hk : k ≤ N₀) (hkD : C * σ₀ ^ (-2 : ℝ) * L ≤ (k : ℝ) / N₀ * D) :
    ((((classOf E col b).powersetCard k ×ˢ (classOf E col (!b)).powersetCard k).filter
        fun UW => ¬ ((H.induce (UW.1 ∪ UW.2)).DegNear ((k : ℝ) / N₀ * D) (c₁ * σ₀) ∧
          (H.induce (UW.1 ∪ UW.2)).HasGap (c₂ * σ₀))).card : ℝ) ≤
      Real.exp (-(a * L)) * ((N₀.choose k : ℕ) : ℝ) ^ 2 := by
  set H' := H.induce (univ \ E) with hH'
  set ι : ↥(univ \ E) ↪ V := Function.Embedding.subtype _ with hι
  set A' : Finset ↥(univ \ E) := univ.filter fun x => col x.1 = b with hA'
  set B' : Finset ↥(univ \ E) := univ.filter fun x => col x.1 = !b with hB'
  have hAmap : A'.map ι = classOf E col b := by
    ext x
    simp only [hA', hι, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype,
      mem_classOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(mem_sdiff.1 y.2).2, hy⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, mem_sdiff.2 ⟨mem_univ x, h1⟩⟩, h2, rfl⟩
  have hBmap : B'.map ι = classOf E col (!b) := by
    ext x
    simp only [hB', hι, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype,
      mem_classOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(mem_sdiff.1 y.2).2, hy⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, mem_sdiff.2 ⟨mem_univ x, h1⟩⟩, h2, rfl⟩
  have hAB' : Disjoint A' B' := by
    refine disjoint_left.2 fun x h1 h2 => ?_
    simp only [hA', hB', mem_filter, mem_univ, true_and] at h1 h2
    rw [h1] at h2
    cases b <;> simp at h2
  have hABu : A' ∪ B' = univ := by
    ext x
    simp only [hA', hB', mem_union, mem_filter, mem_univ, true_and, iff_true]
    cases h : col x.1 <;> cases b <;> simp
  have hA'card : A'.card = N₀ := by rw [← card_map ι, hAmap, hA]
  have hB'card : B'.card = N₀ := by rw [← card_map ι, hBmap, hB]
  have hA'0 : ∀ x ∈ A', ∀ y ∈ A', H'.w x y = 0 := by
    intro x hx y hy
    simp only [hA', mem_filter, mem_univ, true_and] at hx hy
    exact w_eq_zero_of_col H col hbip (hx.trans hy.symm)
  have hB'0 : ∀ x ∈ B', ∀ y ∈ B', H'.w x y = 0 := by
    intro x hx y hy
    simp only [hB', mem_filter, mem_univ, true_and] at hx hy
    exact w_eq_zero_of_col H col hbip (hx.trans hy.symm)
  have hw' : H'.WeightsIn ω := fun x y h => hw x y h
  have key := hbs H' A' B' N₀ k η₀ D σ₀ L hAB' hABu hA'card hB'card hA'0 hB'0 hw' hdeg hgap
    hσ0 hσ1 hη hL hk hkD
  refine le_trans (Nat.cast_le.2 (card_le_card_of_injOn
    (fun UW => (UW.1.subtype (· ∈ univ \ E), UW.2.subtype (· ∈ univ \ E))) ?_ ?_)) key
  · intro UW hUW
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_powersetCard] at hUW ⊢
    obtain ⟨⟨⟨hU, hUk⟩, ⟨hW, hWk⟩⟩, hbad⟩ := hUW
    have hUE : ∀ x ∈ UW.1, x ∈ univ \ E := fun x hx => classOf_subset E col b (hU hx)
    have hWE : ∀ x ∈ UW.2, x ∈ univ \ E := fun x hx => classOf_subset E col (!b) (hW hx)
    have hUm : (UW.1.subtype (· ∈ univ \ E)).map ι = UW.1 := by
      rw [hι, subtype_map, filter_true_of_mem hUE]
    have hWm : (UW.2.subtype (· ∈ univ \ E)).map ι = UW.2 := by
      rw [hι, subtype_map, filter_true_of_mem hWE]
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
    · intro x hx
      have : ι x ∈ classOf E col b := hU (by rw [← hUm]; exact mem_map_of_mem _ hx)
      rw [← hAmap] at this
      exact (mem_map' ι).1 this
    · rw [← card_map ι, hUm, hUk]
    · intro x hx
      have : ι x ∈ classOf E col (!b) := hW (by rw [← hWm]; exact mem_map_of_mem _ hx)
      rw [← hBmap] at this
      exact (mem_map' ι).1 this
    · rw [← card_map ι, hWm, hWk]
    · intro hgood
      apply hbad
      set S' := UW.1.subtype (· ∈ univ \ E) ∪ UW.2.subtype (· ∈ univ \ E) with hS'
      have hSm : S'.map ι = UW.1 ∪ UW.2 := by rw [hS', map_union, hUm, hWm]
      rw [← hSm]
      exact ⟨degNear_equiv _ _ (mapEquiv E S') (mapEquiv_w H E S') hgood.1,
        hasGap_equiv _ _ (mapEquiv E S') (mapEquiv_w H E S') hgood.2⟩
  · intro UW₁ h₁ UW₂ h₂ heq
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_powersetCard] at h₁ h₂
    simp only [Prod.mk.injEq] at heq
    have hE1 : ∀ (X : Finset V), X ⊆ univ \ E → (X.subtype (· ∈ univ \ E)).map ι = X :=
      fun X hX => by rw [hι, subtype_map, filter_true_of_mem fun x hx => hX hx]
    have hU1 := hE1 _ (h₁.1.1.1.trans (classOf_subset E col b))
    have hU2 := hE1 _ (h₂.1.1.1.trans (classOf_subset E col b))
    have hW1 := hE1 _ (h₁.1.2.1.trans (classOf_subset E col (!b)))
    have hW2 := hE1 _ (h₂.1.2.1.trans (classOf_subset E col (!b)))
    refine Prod.ext ?_ ?_
    · rw [← hU1, ← hU2, heq.1]
    · rw [← hW1, ← hW2, heq.2]

omit [Fintype V] [DecidableEq V] in
lemma degOn_eq_zero_of_col (H : WGraph V) (col : V → Bool) (hbip : H.IsBipartiteWith col)
    [Fintype V] {x : V} {S : Finset V} (h : ∀ y ∈ S, col y = col x) : H.degOn x S = 0 :=
  sum_eq_zero fun y hy => w_eq_zero_of_col H col hbip (h y hy).symm

lemma sdiff_eq_classOf_union (E : Finset V) (col : V → Bool) (b : Bool) :
    univ \ E = classOf E col b ∪ classOf E col (!b) := by
  ext y
  simp only [mem_sdiff, mem_univ, true_and, mem_union, mem_classOf]
  cases h : col y <;> cases b <;> simp

lemma degOn_sdiff_eq (H : WGraph V) (col : V → Bool) (E : Finset V)
    (hbip : H.IsBipartiteWith col) (b : Bool) {x : V} (hx : col x = b) :
    H.degOn x (univ \ E) = H.degOn x (classOf E col (!b)) := by
  rw [sdiff_eq_classOf_union E col b]
  unfold WGraph.degOn
  rw [sum_union (classOf_disjoint E col b)]
  have : ∑ y ∈ classOf E col b, H.w x y = 0 :=
    degOn_eq_zero_of_col H col hbip fun y hy => (mem_classOf.1 hy).2.trans hx.symm
  rw [this, zero_add]

/-- **The spectral bound (2.7) for `H₀ = H - E`, in the ambient type.** -/
lemma spectral_V (H : WGraph V) (col : V → Bool) (E : Finset V) (b : Bool)
    (hbip : H.IsBipartiteWith col) (σ₀ Δ : ℝ) (hgap : (H.induce (univ \ E)).HasGap σ₀)
    (hσ0 : 0 ≤ σ₀) (hσ1 : σ₀ ≤ 1) (hΔ : ∀ x, x ∉ E → H.degOn x (univ \ E) ≤ Δ)
    (hepos : 0 < H.edgeWeight (classOf E col b) (classOf E col (!b))) (x y : V → ℝ) :
    2 * ∑ i ∈ classOf E col b, ∑ j ∈ classOf E col (!b),
        x i * centred H (classOf E col b) (classOf E col (!b)) i j * y j ≤
      (1 - σ₀) * Δ * (∑ i ∈ classOf E col b, x i ^ 2 + ∑ j ∈ classOf E col (!b), y j ^ 2) := by
  set H' := H.induce (univ \ E) with hH'
  set ι : ↥(univ \ E) ↪ V := Function.Embedding.subtype _ with hι
  set A' : Finset ↥(univ \ E) := univ.filter fun x => col x.1 = b with hA'
  set B' : Finset ↥(univ \ E) := univ.filter fun x => col x.1 = !b with hB'
  have hAmap : A'.map ι = classOf E col b := by
    ext x
    simp only [hA', hι, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype,
      mem_classOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(mem_sdiff.1 y.2).2, hy⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, mem_sdiff.2 ⟨mem_univ x, h1⟩⟩, h2, rfl⟩
  have hBmap : B'.map ι = classOf E col (!b) := by
    ext x
    simp only [hB', hι, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype,
      mem_classOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(mem_sdiff.1 y.2).2, hy⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, mem_sdiff.2 ⟨mem_univ x, h1⟩⟩, h2, rfl⟩
  have hAB' : Disjoint A' B' := by
    refine disjoint_left.2 fun x h1 h2 => ?_
    simp only [hA', hB', mem_filter, mem_univ, true_and] at h1 h2
    rw [h1] at h2
    cases b <;> simp at h2
  have hABu : A' ∪ B' = univ := by
    ext x
    simp only [hA', hB', mem_union, mem_filter, mem_univ, true_and, iff_true]
    cases h : col x.1 <;> cases b <;> simp
  have hA'0 : ∀ x ∈ A', ∀ y ∈ A', H'.w x y = 0 := by
    intro x hx y hy
    simp only [hA', mem_filter, mem_univ, true_and] at hx hy
    exact w_eq_zero_of_col H col hbip (hx.trans hy.symm)
  have hB'0 : ∀ x ∈ B', ∀ y ∈ B', H'.w x y = 0 := by
    intro x hx y hy
    simp only [hB', mem_filter, mem_univ, true_and] at hx hy
    exact w_eq_zero_of_col H col hbip (hx.trans hy.symm)
  have hdeg' : ∀ v : ↥(univ \ E), H'.deg v = H.degOn v (univ \ E) := fun v =>
    sum_coe_sort (univ \ E) (fun y => H.w v y)
  have hdA : ∀ i ∈ A', H'.deg i = ∑ j ∈ B', H'.w i j := fun i hi => by
    unfold WGraph.deg
    rw [← hABu, BipSampling.sum_union_left_zero A' B' hAB' H'.w i (fun y hy => hA'0 i hi y hy)]
  have hdB : ∀ j ∈ B', H'.deg j = ∑ i ∈ A', H'.w i j := fun j hj => by
    unfold WGraph.deg
    rw [← hABu, BipSampling.sum_union_right_zero A' B' hAB' H'.w j (fun y hy => hB'0 j hj y hy)]
    exact sum_congr rfl fun i _ => H'.symm _ _
  have hdegA : ∀ i ∈ A', H'.deg i = H.degOn i.1 (classOf E col (!b)) := fun i hi => by
    rw [hdeg']
    exact degOn_sdiff_eq H col E hbip b (by simpa [hA'] using hi)
  have hdegB : ∀ j ∈ B', H'.deg j = H.degOn j.1 (classOf E col b) := fun j hj => by
    rw [hdeg', degOn_sdiff_eq H col E hbip (!b) (by simpa [hB'] using hj), Bool.not_not]
  have sA : ∀ f : V → ℝ, ∑ i ∈ classOf E col b, f i = ∑ i ∈ A', f i.1 := fun f => by
    rw [← hAmap, sum_map]; rfl
  have sB : ∀ f : V → ℝ, ∑ i ∈ classOf E col (!b), f i = ∑ i ∈ B', f i.1 := fun f => by
    rw [← hBmap, sum_map]; rfl
  have he' : ∑ l ∈ A', H'.deg l = H.edgeWeight (classOf E col b) (classOf E col (!b)) := by
    rw [sum_congr rfl hdegA, ← sA (fun l => H.degOn l (classOf E col (!b)))]
    rfl
  have hΔ' : ∀ v, H'.deg v ≤ Δ := fun v => by
    rw [hdeg']; exact hΔ v.1 (mem_sdiff.1 v.2).2
  have key := BipSampling.spectral_bound H' A' B' hAB' hABu hA'0 hB'0 σ₀ Δ hgap hσ0 hσ1 hΔ' hdA
    hdB (by rw [he']; exact hepos) (fun v => x v.1) (fun v => y v.1)
  have hL : ∑ i ∈ classOf E col b, ∑ j ∈ classOf E col (!b),
        x i * centred H (classOf E col b) (classOf E col (!b)) i j * y j =
      ∑ i ∈ A', ∑ j ∈ B', x i.1 * (H'.w i j - H'.deg i * H'.deg j / ∑ l ∈ A', H'.deg l) *
        y j.1 := by
    rw [sA]
    refine sum_congr rfl fun i hi => ?_
    rw [sB]
    refine sum_congr rfl fun j hj => ?_
    rw [hdegA i hi, hdegB j hj, he']
    rfl
  rw [hL, sA, sB]
  exact key

/-! ### The probability space: colour-preserving permutations -/

/-- Colour-preserving permutations fixing `E` pointwise. -/
def permG (col : V → Bool) (E : Finset V) : Finset (Equiv.Perm V) :=
  univ.filter fun π => ∀ x, col (π x) = col x ∧ (x ∈ E → π x = x)

lemma mem_permG {col : V → Bool} {E : Finset V} {π : Equiv.Perm V} :
    π ∈ permG col E ↔ ∀ x, col (π x) = col x ∧ (x ∈ E → π x = x) := by
  simp [permG]

lemma one_mem_permG (col : V → Bool) (E : Finset V) : (1 : Equiv.Perm V) ∈ permG col E :=
  mem_permG.2 fun _ => ⟨rfl, fun _ => rfl⟩

lemma mul_mem_permG {col : V → Bool} {E : Finset V} {π ρ : Equiv.Perm V}
    (hρ : ρ ∈ permG col E) (hπ : π ∈ permG col E) : ρ * π ∈ permG col E := by
  rw [mem_permG] at *
  intro x
  refine ⟨?_, fun hx => ?_⟩
  · rw [Equiv.Perm.mul_apply, (hρ _).1, (hπ x).1]
  · rw [Equiv.Perm.mul_apply, (hπ x).2 hx, (hρ x).2 hx]

lemma inv_mem_permG {col : V → Bool} {E : Finset V} {ρ : Equiv.Perm V}
    (hρ : ρ ∈ permG col E) : ρ⁻¹ ∈ permG col E := by
  rw [mem_permG] at *
  intro x
  refine ⟨?_, fun hx => ?_⟩
  · have := (hρ (ρ⁻¹ x)).1
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at this ⊢
    exact this.symm
  · have := (hρ x).2 hx
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact this.symm

lemma permG_classOf {col : V → Bool} {E : Finset V} {π : Equiv.Perm V}
    (hπ : π ∈ permG col E) (b : Bool) (x : V) :
    π x ∈ classOf E col b ↔ x ∈ classOf E col b := by
  rw [mem_permG] at hπ
  rw [mem_classOf, mem_classOf, (hπ x).1]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun hx => h1 ?_, h2⟩
    rw [(hπ x).2 hx]; exact hx
  · rintro ⟨h1, h2⟩
    refine ⟨fun hx => h1 ?_, h2⟩
    have hinv := (mem_permG.1 (inv_mem_permG (mem_permG.2 hπ)) (π x)).2 hx
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at hinv
    rw [hinv]; exact hx

omit [Fintype V] in
/-- A permutation supported in `X` mapping `T ⊆ X` onto `T' ⊆ X`, when `|T| = |T'|`. -/
lemma exists_perm_image [Finite V] (X T T' : Finset V) (hT : T ⊆ X) (hT' : T' ⊆ X)
    (h : T.card = T'.card) :
    ∃ ρ : Equiv.Perm V, (∀ x, x ∉ X → ρ x = x) ∧ (∀ x ∈ X, ρ x ∈ X) ∧ T.image ρ = T' := by
  have h2 : (X \ T).card = (X \ T').card := by
    rw [card_sdiff_of_subset hT, card_sdiff_of_subset hT', h]
  set f := Finset.equivOfCardEq h
  set g := Finset.equivOfCardEq h2
  set ρ₀ : V → V := fun x => if hx : x ∈ T then (f ⟨x, hx⟩ : V) else
    if hx' : x ∈ X \ T then (g ⟨x, hx'⟩ : V) else x with hρ₀
  have hT'X : ∀ x, x ∉ X → x ∉ T' := fun x hx h => hx (hT' h)
  have hval : ∀ x, (x ∈ T ∧ ρ₀ x ∈ T') ∨ (x ∈ X \ T ∧ ρ₀ x ∈ X \ T') ∨ (x ∉ X ∧ ρ₀ x = x) := by
    intro x
    by_cases hx : x ∈ T
    · left; refine ⟨hx, ?_⟩
      simp only [hρ₀, hx, ↓reduceDIte]; exact (f ⟨x, hx⟩).2
    by_cases hx' : x ∈ X \ T
    · right; left; refine ⟨hx', ?_⟩
      simp only [hρ₀, hx, hx', ↓reduceDIte]; exact (g ⟨x, hx'⟩).2
    · right; right
      refine ⟨fun hX => hx' (mem_sdiff.2 ⟨hX, hx⟩), ?_⟩
      simp only [hρ₀, hx, hx', ↓reduceDIte]
  have hinj : Function.Injective ρ₀ := by
    intro x y hxy
    have hTx : ∀ z (hz : z ∈ T), ρ₀ z = (f ⟨z, hz⟩ : V) := fun z hz => by
      simp only [hρ₀, hz, ↓reduceDIte]
    have hXx : ∀ z (hz : z ∈ X \ T), ρ₀ z = (g ⟨z, hz⟩ : V) := fun z hz => by
      simp only [hρ₀, (mem_sdiff.1 hz).2, hz, ↓reduceDIte]
    rcases hval x with ⟨hx, hx2⟩ | ⟨hx, hx2⟩ | ⟨hx, hx2⟩ <;>
      rcases hval y with ⟨hy, hy2⟩ | ⟨hy, hy2⟩ | ⟨hy, hy2⟩
    · rw [hTx x hx, hTx y hy] at hxy
      exact congrArg Subtype.val (f.injective (Subtype.ext hxy))
    · rw [hxy] at hx2; exact absurd hx2 (mem_sdiff.1 hy2).2
    · rw [hxy, hy2] at hx2; exact absurd hx2 (hT'X y hy)
    · rw [← hxy] at hy2; exact absurd hy2 (mem_sdiff.1 hx2).2
    · rw [hXx x hx, hXx y hy] at hxy
      exact congrArg Subtype.val (g.injective (Subtype.ext hxy))
    · rw [hxy, hy2] at hx2; exact absurd (mem_sdiff.1 hx2).1 hy
    · rw [← hxy, hx2] at hy2; exact absurd hy2 (hT'X x hx)
    · rw [← hxy, hx2] at hy2; exact absurd (mem_sdiff.1 hy2).1 hx
    · rw [hx2, hy2] at hxy; exact hxy
  set ρ := Equiv.ofBijective ρ₀ (Finite.injective_iff_bijective.mp hinj)
  refine ⟨ρ, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · rcases hval x with ⟨hx', -⟩ | ⟨hx', -⟩ | ⟨-, h⟩
    · exact absurd (hT hx') hx
    · exact absurd (mem_sdiff.1 hx').1 hx
    · exact h
  · rcases hval x with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · exact hT' h
    · exact (mem_sdiff.1 h).1
    · exact absurd hx h
  · ext z
    simp only [mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hval x with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd hx (mem_sdiff.1 h).2
      · exact absurd (hT hx) h
    · intro hz
      refine ⟨(f.symm ⟨z, hz⟩ : V), (f.symm ⟨z, hz⟩).2, ?_⟩
      show ρ₀ _ = z
      simp only [hρ₀, (f.symm ⟨z, hz⟩).2, ↓reduceDIte, Subtype.coe_eta, Equiv.apply_symm_apply]

omit [Fintype V] in
lemma image_eq_self_of_fix (T : Finset V) (ρ : Equiv.Perm V) (h : ∀ x ∈ T, ρ x = x) :
    T.image ρ = T := by
  ext z
  simp only [mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; rw [h x hx]; exact hx
  · intro hz; exact ⟨z, hz, h z hz⟩

/-- **Transitivity.** `permG` acts transitively on pairs of subsets of the two colour classes
with prescribed sizes. -/
lemma permG_trans (col : V → Bool) (E : Finset V) (b : Bool) (T₁ T₁' T₂ T₂' : Finset V)
    (h₁ : T₁ ⊆ classOf E col b) (h₁' : T₁' ⊆ classOf E col b)
    (h₂ : T₂ ⊆ classOf E col (!b)) (h₂' : T₂' ⊆ classOf E col (!b))
    (hc₁ : T₁.card = T₁'.card) (hc₂ : T₂.card = T₂'.card) :
    ∃ ρ ∈ permG col E, T₁.image ρ = T₁' ∧ T₂.image ρ = T₂' := by
  obtain ⟨ρ₁, hρ₁o, hρ₁i, hρ₁T⟩ := exists_perm_image _ T₁ T₁' h₁ h₁' hc₁
  obtain ⟨ρ₂, hρ₂o, hρ₂i, hρ₂T⟩ := exists_perm_image _ T₂ T₂' h₂ h₂' hc₂
  have hd := classOf_disjoint E col b
  have hcol : ∀ (ρ : Equiv.Perm V) (c : Bool), (∀ x, x ∉ classOf E col c → ρ x = x) →
      (∀ x ∈ classOf E col c, ρ x ∈ classOf E col c) → ρ ∈ permG col E := by
    intro ρ c ho hi
    refine mem_permG.2 fun x => ⟨?_, fun hx => ho x fun h => (mem_classOf.1 h).1 hx⟩
    by_cases hx : x ∈ classOf E col c
    · rw [(mem_classOf.1 (hi x hx)).2, (mem_classOf.1 hx).2]
    · rw [ho x hx]
  refine ⟨ρ₁ * ρ₂, mul_mem_permG (hcol ρ₁ b hρ₁o hρ₁i) (hcol ρ₂ (!b) hρ₂o hρ₂i), ?_, ?_⟩
  · have : T₁.image (ρ₁ * ρ₂) = (T₁.image ρ₂).image ρ₁ := by
      rw [image_image]; rfl
    rw [this, image_eq_self_of_fix T₁ ρ₂ fun x hx => hρ₂o x
      (disjoint_left.1 hd (h₁ hx)), hρ₁T]
  · have : T₂.image (ρ₁ * ρ₂) = (T₂.image ρ₂).image ρ₁ := by
      rw [image_image]; rfl
    rw [this, hρ₂T, image_eq_self_of_fix T₂' ρ₁ fun x hx => hρ₁o x
      (disjoint_right.1 hd (h₂' hx))]

lemma image_subset_classOf {col : V → Bool} {E : Finset V} {π : Equiv.Perm V}
    (hπ : π ∈ permG col E) {b : Bool} {X : Finset V} (hX : X ⊆ classOf E col b) :
    X.image π ⊆ classOf E col b := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hz
  exact (permG_classOf hπ b x).2 (hX hx)

open Classical in
/-- **Uniformity of the random blocks.** For `X₁, X₂` in the two colour classes, the pair
`(π '' X₁, π '' X₂)` is uniform on pairs of subsets of the classes of sizes `|X₁|, |X₂|`. -/
lemma fibre_count (col : V → Bool) (E : Finset V) (b : Bool) (X₁ X₂ : Finset V)
    (hX₁ : X₁ ⊆ classOf E col b) (hX₂ : X₂ ⊆ classOf E col (!b))
    (P : Finset V × Finset V → Prop) [DecidablePred P] :
    ((permG col E).filter fun π : Equiv.Perm V => P (X₁.image π, X₂.image π)).card *
        ((classOf E col b).card.choose X₁.card * (classOf E col (!b)).card.choose X₂.card) =
      ((((classOf E col b).powersetCard X₁.card) ×ˢ
          ((classOf E col (!b)).powersetCard X₂.card)).filter P).card * (permG col E).card := by
  set G := permG col E with hG
  set Y := ((classOf E col b).powersetCard X₁.card) ×ˢ
    ((classOf E col (!b)).powersetCard X₂.card) with hY
  set Φ : Equiv.Perm V → Finset V × Finset V := fun π => (X₁.image π, X₂.image π) with hΦ
  have hmaps : ∀ π ∈ G, Φ π ∈ Y := by
    intro π hπ
    simp only [hY, hΦ, mem_product, mem_powersetCard]
    exact ⟨⟨image_subset_classOf hπ hX₁, card_image_of_injective _ π.injective⟩,
      ⟨image_subset_classOf hπ hX₂, card_image_of_injective _ π.injective⟩⟩
  set M := (G.filter fun π => Φ π = (X₁, X₂)).card with hM
  have hfib : ∀ y ∈ Y, (G.filter fun π => Φ π = y).card = M := by
    rintro ⟨y₁, y₂⟩ hy
    simp only [hY, mem_product, mem_powersetCard] at hy
    obtain ⟨ρ, hρ, h1, h2⟩ := permG_trans col E b X₁ y₁ X₂ y₂ hX₁ hy.1.1 hX₂ hy.2.1
      hy.1.2.symm hy.2.2.symm
    have hρi := inv_mem_permG hρ
    have himg : ∀ (π : Equiv.Perm V) (σ : Equiv.Perm V) (X : Finset V),
        X.image (σ * π) = (X.image π).image σ := fun π σ X => by rw [image_image]; rfl
    symm
    refine card_nbij' (fun π => ρ * π) (fun π => ρ⁻¹ * π) ?_ ?_ ?_ ?_
    · intro π hπ
      simp only [coe_filter, Set.mem_ofPred_eq, hΦ, Prod.mk.injEq] at hπ ⊢
      refine ⟨mul_mem_permG hρ hπ.1, ?_, ?_⟩
      · rw [himg, hπ.2.1, h1]
      · rw [himg, hπ.2.2, h2]
    · intro π hπ
      simp only [coe_filter, Set.mem_ofPred_eq, hΦ, Prod.mk.injEq] at hπ ⊢
      refine ⟨mul_mem_permG hρi hπ.1, ?_, ?_⟩
      · rw [himg, hπ.2.1, ← h1, ← himg, inv_mul_cancel, Equiv.Perm.coe_one, image_id]
      · rw [himg, hπ.2.2, ← h2, ← himg, inv_mul_cancel, Equiv.Perm.coe_one, image_id]
    · intro π _
      simp only [inv_mul_cancel_left]
    · intro π _
      simp only [mul_inv_cancel_left]
  have hsum1 : (G.filter fun π => P (Φ π)).card = (Y.filter P).card * M := by
    rw [card_eq_sum_card_fiberwise (f := Φ) (t := Y.filter P)]
    · rw [sum_congr rfl fun y hy => ?_]
      · rw [sum_const, smul_eq_mul]
      · rw [filter_filter]
        rw [← hfib y (mem_filter.1 hy).1]
        congr 1
        ext π
        simp only [mem_filter]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨h1, by rw [h3]; exact (mem_filter.1 hy).2, h3⟩
    · intro π hπ
      simp only [coe_filter, Set.mem_ofPred_eq] at hπ ⊢
      exact ⟨hmaps π hπ.1, hπ.2⟩
  have hsum2 : G.card = Y.card * M := by
    rw [card_eq_sum_card_fiberwise (f := Φ) (t := Y) (fun π hπ => hmaps π hπ)]
    rw [sum_congr rfl fun y hy => hfib y hy, sum_const, smul_eq_mul]
  have hYc : Y.card = (classOf E col b).card.choose X₁.card *
      (classOf E col (!b)).card.choose X₂.card := by
    rw [hY, card_product, card_powersetCard, card_powersetCard]
  show (G.filter fun π => P (Φ π)).card * _ = _
  rw [hsum1, hsum2, ← hYc]
  ring

/-- Bound on the permutations for which a property of the random blocks fails. -/
lemma fibre_bound (col : V → Bool) (E : Finset V) (b : Bool) (X₁ X₂ : Finset V)
    (hX₁ : X₁ ⊆ classOf E col b) (hX₂ : X₂ ⊆ classOf E col (!b))
    (P : Finset V × Finset V → Prop) [DecidablePred P] (ε : ℝ)
    (hP : (((((classOf E col b).powersetCard X₁.card) ×ˢ
        ((classOf E col (!b)).powersetCard X₂.card)).filter P).card : ℝ) ≤
      ε * ((classOf E col b).card.choose X₁.card * (classOf E col (!b)).card.choose X₂.card : ℕ)) :
    (((permG col E).filter fun π : Equiv.Perm V => P (X₁.image π, X₂.image π)).card : ℝ) ≤
      ε * (permG col E).card := by
  have h := fibre_count col E b X₁ X₂ hX₁ hX₂ P
  set C := (classOf E col b).card.choose X₁.card * (classOf E col (!b)).card.choose X₂.card
  have hpos : (0 : ℝ) < (C : ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.choose_pos (card_le_card hX₁))
      (Nat.choose_pos (card_le_card hX₂))
  have h' : (((permG col E).filter fun π : Equiv.Perm V => P (X₁.image π, X₂.image π)).card : ℝ) *
      (C : ℕ) = (((((classOf E col b).powersetCard X₁.card) ×ˢ
        ((classOf E col (!b)).powersetCard X₂.card)).filter P).card : ℝ) *
          (permG col E).card := by
    exact_mod_cast h
  have hG0 : (0 : ℝ) ≤ (permG col E).card := Nat.cast_nonneg _
  have : (((permG col E).filter fun π : Equiv.Perm V => P (X₁.image π, X₂.image π)).card : ℝ) *
      (C : ℕ) ≤ ε * (permG col E).card * (C : ℕ) := by
    rw [h']
    calc _ ≤ ε * (C : ℕ) * (permG col E).card := mul_le_mul_of_nonneg_right hP hG0
      _ = _ := by ring
  exact le_of_mul_le_mul_right this hpos

omit [Fintype V] [DecidableEq V] in
/-- The Chernoff bound for a uniform `k`-subset, both tails, in the form used below. -/
lemma count_dev (S : Finset V) (k : ℕ) (g : V → ℝ) (hg : ∀ j ∈ S, 0 ≤ g j ∧ g j ≤ 1)
    (P t τ : ℝ) (hμ : (k : ℝ) / S.card * ∑ j ∈ S, g j ≤ P) (ht : 0 < t) (hτ0 : 0 ≤ τ)
    (hτ : 2 * τ * (P + t) ≤ t ^ 2) :
    (((S.powersetCard k).filter fun T =>
        t ≤ |∑ j ∈ T, g j - (k : ℝ) / S.card * ∑ j ∈ S, g j|).card : ℝ) ≤
      2 * Real.exp (-τ) * S.card.choose k := by
  classical
  set μ := (k : ℝ) / S.card * ∑ j ∈ S, g j with hμdef
  have hμ0 : 0 ≤ μ := mul_nonneg (by positivity) (sum_nonneg fun j hj => (hg j hj).1)
  have hsub : ((S.powersetCard k).filter fun T => t ≤ |∑ j ∈ T, g j - μ|) ⊆
      ((S.powersetCard k).filter fun T => μ + t ≤ ∑ j ∈ T, g j) ∪
        ((S.powersetCard k).filter fun T => ∑ j ∈ T, g j ≤ μ - t) := by
    intro T hT
    rw [mem_filter] at hT
    rw [mem_union, mem_filter, mem_filter]
    rcases le_abs'.1 hT.2 with h | h
    · right; exact ⟨hT.1, by linarith⟩
    · left; exact ⟨hT.1, by linarith⟩
  have hup := BipSampling.hyp_upper_finset S g hg k t ht.le
  have hlo := BipSampling.hyp_lower_finset S g hg k t ht.le
  rw [← hμdef] at hup hlo
  have hC0 : (0 : ℝ) ≤ S.card.choose k := Nat.cast_nonneg _
  have e1 : Real.exp (-(t ^ 2) / (2 * (μ + t / 3))) ≤ Real.exp (-τ) := by
    apply Real.exp_le_exp.2
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hμ hτ0]
  have e2 : (((S.powersetCard k).filter fun T => ∑ j ∈ T, g j ≤ μ - t).card : ℝ) ≤
      Real.exp (-τ) * S.card.choose k := by
    rcases hμ0.eq_or_lt with h0 | h0
    · rw [filter_false_of_mem]
      · simp only [card_empty, Nat.cast_zero]; positivity
      · intro T hT h
        have := sum_nonneg fun j hj => (hg j ((mem_powersetCard.1 hT).1 hj)).1
        linarith
    · refine hlo.trans (mul_le_mul_of_nonneg_right ?_ hC0)
      apply Real.exp_le_exp.2
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hμ hτ0]
  calc (((S.powersetCard k).filter fun T => t ≤ |∑ j ∈ T, g j - μ|).card : ℝ)
      ≤ ((((S.powersetCard k).filter fun T => μ + t ≤ ∑ j ∈ T, g j) ∪
        ((S.powersetCard k).filter fun T => ∑ j ∈ T, g j ≤ μ - t)).card : ℝ) :=
        Nat.cast_le.2 (card_le_card hsub)
    _ ≤ (((S.powersetCard k).filter fun T => μ + t ≤ ∑ j ∈ T, g j).card : ℝ) +
        (((S.powersetCard k).filter fun T => ∑ j ∈ T, g j ≤ μ - t).card : ℝ) := by
        exact_mod_cast card_union_le _ _
    _ ≤ Real.exp (-τ) * S.card.choose k + Real.exp (-τ) * S.card.choose k :=
        add_le_add (hup.trans (mul_le_mul_of_nonneg_right e1 hC0)) e2
    _ = 2 * Real.exp (-τ) * S.card.choose k := by ring

omit [Fintype V] [DecidableEq V] in
lemma card_filter_prod_empty (A : Finset (Finset V)) (P : Finset V × Finset V → Prop)
    [DecidablePred P] :
    ((A ×ˢ ({∅} : Finset (Finset V))).filter P).card ≤
      (A.filter fun T => P (T, ∅)).card := by
  classical
  refine card_le_card_of_injOn Prod.fst ?_ ?_
  · intro TT hTT
    simp only [coe_filter, mem_product, mem_singleton, Set.mem_ofPred_eq] at hTT ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hTT
    refine ⟨h1, ?_⟩
    have : TT = (TT.1, ∅) := Prod.ext rfl h2
    rw [← this]; exact h3
  · intro TT₁ h₁ TT₂ h₂ heq
    simp only [coe_filter, mem_product, mem_singleton, Set.mem_ofPred_eq] at h₁ h₂
    exact Prod.ext heq (h₁.1.2.trans h₂.1.2.symm)

open Classical in
/-- **Degree concentration into a random block**, for all vertices of the opposite colour. -/
lemma ev_dev (H : WGraph V) (col : V → Bool) (E : Finset V) (b : Bool)
    (hw : ∀ x y, H.w x y ≤ 1) (X : Finset V) (hX : X ⊆ classOf E col b) (P t τ : ℝ)
    (hμ : ∀ v, col v = !b →
      (X.card : ℝ) / (classOf E col b).card * H.degOn v (classOf E col b) ≤ P)
    (ht : 0 < t) (hτ0 : 0 ≤ τ) (hτ : 2 * τ * (P + t) ≤ t ^ 2) :
    (((permG col E).filter fun π : Equiv.Perm V => ∃ v, col v = !b ∧
        t ≤ |H.degOn v (X.image π) -
          (X.card : ℝ) / (classOf E col b).card * H.degOn v (classOf E col b)|).card : ℝ) ≤
      ((univ.filter fun v => col v = !b).card * (2 * Real.exp (-τ))) * (permG col E).card := by
  set W := univ.filter fun v => col v = !b with hW
  set S := classOf E col b with hS
  refine fibre_bound col E b X ∅ hX (empty_subset _) (fun TT => ∃ v, col v = !b ∧
      t ≤ |H.degOn v TT.1 - (X.card : ℝ) / S.card * H.degOn v S|) _ ?_
  rw [card_empty, Nat.choose_zero_right, mul_one, powersetCard_zero]
  refine le_trans (Nat.cast_le.2 (card_filter_prod_empty _ _)) ?_
  have hsub : ((S.powersetCard X.card).filter fun T => ∃ v, col v = !b ∧
      t ≤ |H.degOn v T - (X.card : ℝ) / S.card * H.degOn v S|) ⊆
      W.biUnion fun v => (S.powersetCard X.card).filter fun T =>
        t ≤ |∑ j ∈ T, H.w v j - (X.card : ℝ) / S.card * ∑ j ∈ S, H.w v j| := by
    intro T hT
    simp only [mem_filter] at hT
    obtain ⟨hT1, v, hv, hvT⟩ := hT
    exact mem_biUnion.2 ⟨v, by simp [hW, hv], mem_filter.2 ⟨hT1, hvT⟩⟩
  refine le_trans (Nat.cast_le.2 (card_le_card hsub)) ?_
  refine le_trans (BipSampling.card_biUnion_le_real W _ (2 * Real.exp (-τ) * S.card.choose X.card)
    fun v hv => ?_) (le_of_eq (by ring))
  have hv' : col v = !b := by simpa [hW] using hv
  exact count_dev S X.card (fun j => H.w v j) (fun j _ => ⟨H.nonneg v j, hw v j⟩) P t τ
    (hμ v hv') ht hτ0 hτ

open Classical in
/-- **The one-sided norm event** (Lemma 2.2 applied to the rows of a random block). -/
lemma ev_norm {C₀ : ℝ} (hC₀ : BipSampling.ColSampProp C₀) (H : WGraph V) (col : V → Bool)
    (E : Finset V) (b : Bool) (N₀ : ℕ) (hA : (classOf E col b).card = N₀)
    (hB : (classOf E col (!b)).card = N₀) (X : Finset V) (hX : X ⊆ classOf E col b)
    (M c τ : ℝ) (hM0 : 0 ≤ M) (hc0 : 0 ≤ c) (hτ : 0 < τ)
    (hop : ∀ v : V → ℝ, ∑ i ∈ classOf E col (!b), (∑ j ∈ classOf E col b,
      centred H (classOf E col b) (classOf E col (!b)) j i * v j) ^ 2 ≤
        M ^ 2 * ∑ j ∈ classOf E col b, v j ^ 2)
    (hrow : ∀ j ∈ classOf E col b, ∑ i ∈ classOf E col (!b),
      centred H (classOf E col b) (classOf E col (!b)) j i ^ 2 ≤ c ^ 2) :
    (((permG col E).filter fun π : Equiv.Perm V => ∃ v : V → ℝ,
        (Real.sqrt ((X.card : ℝ) / N₀) * M + C₀ * c * Real.sqrt τ) ^ 2 *
            ∑ j ∈ X.image π, v j ^ 2 <
          ∑ i ∈ classOf E col (!b), (∑ j ∈ X.image π,
            centred H (classOf E col b) (classOf E col (!b)) j i * v j) ^ 2).card : ℝ) ≤
      (N₀ * (N₀ + 1) * Real.exp (-τ)) * (permG col E).card := by
  refine fibre_bound col E b X ∅ hX (empty_subset _) (fun TT => ∃ v : V → ℝ,
      (Real.sqrt ((X.card : ℝ) / N₀) * M + C₀ * c * Real.sqrt τ) ^ 2 *
            ∑ j ∈ TT.1, v j ^ 2 <
          ∑ i ∈ classOf E col (!b), (∑ j ∈ TT.1,
            centred H (classOf E col b) (classOf E col (!b)) j i * v j) ^ 2) _ ?_
  rw [card_empty, Nat.choose_zero_right, mul_one, powersetCard_zero]
  refine le_trans (Nat.cast_le.2 (card_filter_prod_empty _ _)) ?_
  have h := BipSampling.column_sampling_finset hC₀ (classOf E col (!b)) (classOf E col b)
    (fun i j => centred H (classOf E col b) (classOf E col (!b)) j i) M c hop hrow hM0 hc0
    X.card (card_le_card hX) τ hτ
  rw [hA, hB] at h
  rw [hA]
  refine le_trans (le_of_eq ?_) h
  congr 2

open Classical in
/-- **The sampling events of Lemma 2.3** for a pair of random blocks. -/
lemma ev_pair {ω c₂ a c₁ c C : ℝ} (hbs : BSProp.{u} ω c₂ a c₁ c C)
    (H : WGraph V) (col : V → Bool) (E : Finset V) (b : Bool) (N₀ : ℕ) (η₀ D σ₀ L : ℝ)
    (hbip : H.IsBipartiteWith col) (hw : H.WeightsIn ω)
    (hA : (classOf E col b).card = N₀) (hB : (classOf E col (!b)).card = N₀)
    (hdeg : (H.induce (univ \ E)).DegNear D η₀) (hgap : (H.induce (univ \ E)).HasGap σ₀)
    (hσ0 : 0 < σ₀) (hσ1 : σ₀ ≤ 1) (hη : η₀ ≤ c * σ₀) (hL : Real.log (2 * N₀) ≤ L)
    (X₁ X₂ : Finset V) (hX₁ : X₁ ⊆ classOf E col b) (hX₂ : X₂ ⊆ classOf E col (!b))
    (hk : X₁.card = X₂.card) (hkD : C * σ₀ ^ (-2 : ℝ) * L ≤ (X₁.card : ℝ) / N₀ * D) :
    (((permG col E).filter fun π : Equiv.Perm V =>
        ¬ ((H.induce (X₁.image π ∪ X₂.image π)).DegNear ((X₁.card : ℝ) / N₀ * D) (c₁ * σ₀) ∧
          (H.induce (X₁.image π ∪ X₂.image π)).HasGap (c₂ * σ₀))).card : ℝ) ≤
      Real.exp (-(a * L)) * (permG col E).card := by
  refine fibre_bound col E b X₁ X₂ hX₁ hX₂ (fun TT =>
      ¬ ((H.induce (TT.1 ∪ TT.2)).DegNear ((X₁.card : ℝ) / N₀ * D) (c₁ * σ₀) ∧
          (H.induce (TT.1 ∪ TT.2)).HasGap (c₂ * σ₀))) _ ?_
  have h := bs_V hbs H col E b N₀ X₁.card η₀ D σ₀ L hbip hw hA hB hdeg hgap hσ0 hσ1 hη hL
    (hA ▸ card_le_card hX₁) hkD
  rw [← hk, hA, hB]
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
  · rfl
  · push_cast; ring

/-! ### Labelings with prescribed cell sizes -/

omit [Fintype V] in
/-- A labeling of a finset with prescribed fibre sizes. -/
lemma exists_labeling {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (S : Finset V) :
    ∀ sz : ι → ℕ, ∑ i, sz i = S.card →
      ∃ f : V → ι, ∀ i, (S.filter fun x => f x = i).card = sz i := by
  induction S using Finset.induction_on with
  | empty =>
    intro sz h
    refine ⟨fun _ => Classical.arbitrary ι, fun i => ?_⟩
    simp only [filter_empty, card_empty]
    have h' : ∑ i, sz i = 0 := by simpa using h
    exact ((Finset.sum_eq_zero_iff.1 h') i (mem_univ i)).symm
  | insert a s ha ih =>
    intro sz h
    rw [card_insert_of_notMem ha] at h
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, 0 < sz i₀ := by
      by_contra hne
      push Not at hne
      have : ∑ i, sz i = 0 := sum_eq_zero fun i _ => Nat.le_zero.1 (hne i)
      omega
    set sz' := Function.update sz i₀ (sz i₀ - 1) with hsz'
    have hsum : ∑ i, sz' i = s.card := by
      have h1 := Finset.sum_update_of_mem (mem_univ i₀) sz (sz i₀ - 1)
      have h2 := Finset.add_sum_erase univ sz (mem_univ i₀)
      rw [← sdiff_singleton_eq_erase] at h2
      rw [hsz', h1]
      omega
    obtain ⟨f, hf⟩ := ih sz' hsum
    refine ⟨Function.update f a i₀, fun i => ?_⟩
    rw [filter_insert]
    have hcongr : (s.filter fun x => Function.update f a i₀ x = i) = s.filter fun x => f x = i :=
      filter_congr fun x hx => by
        have hxa : x ≠ a := fun h => ha (h ▸ hx)
        rw [Function.update_of_ne hxa]
    rw [hcongr, Function.update_self]
    by_cases hi : i₀ = i
    · subst hi
      simp only [↓reduceIte]
      rw [card_insert_of_notMem (fun h => ha (mem_filter.1 h).1), hf,
        hsz', Function.update_self]
      omega
    · simp only [hi, ↓reduceIte]
      rw [hf, hsz', Function.update_of_ne (Ne.symm hi)]

/-- The sub-cells of the initial partition: the cells of `Cell`, with the special layers `U`
(`lu`) and `V` (`lv`) split into new ports, dummy and filler. -/
inductive SC
  | ends | att | rtr | cyc | div | inp | out | uP | uD | uF | vP | vD | vF | pool
  deriving DecidableEq

instance : Fintype SC :=
  ⟨{.ends, .att, .rtr, .cyc, .div, .inp, .out, .uP, .uD, .uF, .vP, .vD, .vF, .pool},
    fun x => by cases x <;> simp⟩

instance : Nonempty SC := ⟨SC.pool⟩

/-- The cell of a sub-cell. -/
def SC.toCell : SC → Cell
  | .ends => .ends | .att => .att | .rtr => .rtr | .cyc => .cyc | .div => .div
  | .inp => .inp | .out => .out | .uP => .lu | .uD => .lu | .uF => .lu
  | .vP => .lv | .vD => .lv | .vF => .lv | .pool => .pool

/-- The pairs of blocks for the sampling events of Lemma 2.3. -/
inductive PB | att | rtr | div | fill
  deriving DecidableEq

instance : Fintype PB := ⟨{.att, .rtr, .div, .fill}, fun x => by cases x <;> simp⟩

/-- The blocks for the degree-concentration events. -/
inductive DB | att | rtr | cyc | inp | out | lu | lv | wide | env
  deriving DecidableEq

instance : Fintype DB :=
  ⟨{.att, .rtr, .cyc, .inp, .out, .lu, .lv, .wide, .env}, fun x => by cases x <;> simp⟩

/-- The blocks for the one-sided norm events. -/
inductive NB | inp | out | lu | lv
  deriving DecidableEq

instance : Fintype NB := ⟨{.inp, .out, .lu, .lv}, fun x => by cases x <;> simp⟩

/-- First sub-cell set of a pair event. -/
def PB.c₁ : PB → Finset SC
  | .att => {.att} | .rtr => {.rtr} | .div => {.div} | .fill => {.uF}

/-- Second sub-cell set of a pair event. -/
def PB.c₂ : PB → Finset SC
  | .att => {.att} | .rtr => {.rtr} | .div => {.div} | .fill => {.vF}

/-- Sub-cell set of a degree event. -/
def DB.cells : DB → Finset SC
  | .att => {.att} | .rtr => {.rtr} | .cyc => {.cyc} | .inp => {.inp} | .out => {.out}
  | .lu => {.uP, .uD, .uF} | .lv => {.vP, .vD, .vF}
  | .wide => {.cyc, .inp, .out, .uP, .uD, .uF, .vP, .vD, .vF}
  | .env => {.att, .rtr, .cyc, .div, .inp, .out, .uP, .uD, .uF, .vP, .vD, .vF}

/-- Sub-cell set of a norm event. -/
def NB.cells : NB → Finset SC
  | .inp => {.inp} | .out => {.out} | .lu => {.uP, .uD, .uF} | .lv => {.vP, .vD, .vF}

/-- The block of colour `b` and sub-cells `S` of a labeling. -/
def blk (col : V → Bool) (κ : V → SC) (b : Bool) (S : Finset SC) : Finset V :=
  univ.filter fun x => col x = b ∧ κ x ∈ S

omit [DecidableEq V] in
lemma mem_blk {col : V → Bool} {κ : V → SC} {b : Bool} {S : Finset SC} {x : V} :
    x ∈ blk col κ b S ↔ col x = b ∧ κ x ∈ S := by
  simp [blk]

/-- The block of a permuted labeling is the image of the block. -/
lemma blk_perm {col : V → Bool} {E : Finset V} {π : Equiv.Perm V} (hπ : π ∈ permG col E)
    (κ : V → SC) (b : Bool) (S : Finset SC) :
    blk col (fun x => κ (π⁻¹ x)) b S = (blk col κ b S).image π := by
  ext x
  simp only [mem_blk, mem_image]
  have hc : col (π⁻¹ x) = col x := (mem_permG.1 (inv_mem_permG hπ) x).1
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨π⁻¹ x, ⟨hc.trans h1, h2⟩, by simp⟩
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    have : π⁻¹ (π y) = y := by simp
    rw [this]
    exact ⟨((mem_permG.1 hπ y).1).trans h1, h2⟩

lemma blk_subset_classOf {col : V → Bool} {E : Finset V} {κ : V → SC}
    (hκ : ∀ x, κ x = SC.ends ↔ x ∈ E) (b : Bool) {S : Finset SC} (hS : SC.ends ∉ S) :
    blk col κ b S ⊆ classOf E col b := by
  intro x hx
  rw [mem_blk] at hx
  rw [mem_classOf]
  exact ⟨fun h => hS ((hκ x).2 h ▸ hx.2), hx.1⟩

omit [DecidableEq V] in
lemma card_blk {col : V → Bool} {κ : V → SC} (sz : Bool → SC → ℕ)
    (hsz : ∀ b c, c ≠ SC.ends → (blk col κ b {c}).card = sz b c) (b : Bool) {S : Finset SC}
    (hS : SC.ends ∉ S) : (blk col κ b S).card = ∑ c ∈ S, sz b c := by
  rw [card_eq_sum_card_fiberwise (f := κ) (t := S)]
  · refine sum_congr rfl fun c hc => ?_
    rw [← hsz b c (fun h => hS (h ▸ hc))]
    congr 1
    ext x
    simp only [mem_filter, mem_blk, mem_singleton]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hc⟩, h3⟩
  · intro x hx
    exact (mem_blk.1 hx).2

/-- A base labeling with prescribed sizes of every sub-cell in both colour classes. -/
lemma exists_base_labeling (col : V → Bool) (E : Finset V) (sz : Bool → SC → ℕ)
    (hends : ∀ b, sz b SC.ends = 0)
    (hsum : ∀ b, ∑ c, sz b c = (classOf E col b).card) :
    ∃ κ : V → SC, (∀ x, κ x = SC.ends ↔ x ∈ E) ∧
      ∀ b c, c ≠ SC.ends → (blk col κ b {c}).card = sz b c := by
  have hf : ∀ b, ∃ f : V → SC, ∀ c, ((classOf E col b).filter fun x => f x = c).card = sz b c :=
    fun b => exists_labeling (classOf E col b) (sz b) (hsum b)
  choose f hf using hf
  refine ⟨fun x => if x ∈ E then SC.ends else f (col x) x, fun x => ?_, fun b c hc => ?_⟩
  · by_cases hx : x ∈ E
    · simp [hx]
    · simp only [hx, ↓reduceIte, iff_false]
      intro h
      have h0 := hf (col x) SC.ends
      rw [hends] at h0
      have : x ∈ (classOf E col (col x)).filter fun y => f (col x) y = SC.ends :=
        mem_filter.2 ⟨mem_classOf.2 ⟨hx, rfl⟩, h⟩
      rw [card_eq_zero.1 h0] at this
      exact absurd this (notMem_empty x)
  · rw [← hf b c]
    congr 1
    ext x
    simp only [mem_blk, mem_singleton, mem_filter, mem_classOf]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hx : x ∈ E
      · simp [hx] at h2; exact absurd h2.symm hc
      · simp only [hx, ↓reduceIte, h1] at h2
        exact ⟨⟨hx, h1⟩, h2⟩
    · rintro ⟨⟨hx, h1⟩, h2⟩
      simp only [hx, ↓reduceIte, h1]
      exact ⟨trivial, h2⟩

/-! ### Ports and matchings -/

omit [Fintype V] in
/-- A bijection between finsets of equal size. -/
lemma exists_bijOn_finset (A B : Finset V) (h : A.card = B.card) :
    ∃ g : V → V, Set.BijOn g A B := by
  set e := Finset.equivOfCardEq h
  refine ⟨fun x => if hx : x ∈ A then (e ⟨x, hx⟩ : V) else x, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_coe] at hx
    simp only [hx, ↓reduceDIte, Finset.mem_coe]
    exact (e ⟨x, hx⟩).2
  · intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    simp only [hx, hy, ↓reduceDIte] at hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext hxy))
  · intro z hz
    simp only [Finset.mem_coe] at hz
    refine ⟨(e.symm ⟨z, hz⟩ : V), (e.symm ⟨z, hz⟩).2, ?_⟩
    simp only [(e.symm ⟨z, hz⟩).2, ↓reduceDIte, Subtype.coe_eta, Equiv.apply_symm_apply]

omit [Fintype V] in
/-- **The new ports**: an injection of `E` sending the vertices of each role `r` onto a
prescribed set `P r` of the same size. -/
lemma exists_port {β : Type*} [DecidableEq β] (E : Finset V) (role : V → β)
    (P : β → Finset V) (hP : ∀ r r', r ≠ r' → Disjoint (P r) (P r'))
    (hc : ∀ r, (E.filter fun x => role x = r).card = (P r).card) :
    ∃ port : V → V, (∀ x ∈ E, port x ∈ P (role x)) ∧ Set.InjOn port E ∧
      ∀ r, ∀ z ∈ P r, ∃ x ∈ E, port x = z := by
  have hg : ∀ r, ∃ g : V → V, Set.BijOn g (E.filter fun x => role x = r) (P r) :=
    fun r => exists_bijOn_finset _ _ (hc r)
  choose g hg using hg
  have hmem : ∀ x ∈ E, x ∈ ((E.filter fun y => role y = role x : Finset V) : Set V) :=
    fun x hx => by simp [hx]
  refine ⟨fun x => g (role x) x, fun x hx => (hg (role x)).mapsTo (hmem x hx),
    fun x hx y hy hxy => ?_, ?_⟩
  · simp only at hxy
    have hx' := (hg (role x)).mapsTo (hmem x hx)
    have hy' := (hg (role y)).mapsTo (hmem y hy)
    have hr : role x = role y := by
      by_contra hne
      rw [hxy] at hx'
      exact disjoint_left.1 (hP _ _ hne) hx' hy'
    have hy'' : y ∈ ((E.filter fun z => role z = role x : Finset V) : Set V) := by
      simp [Finset.mem_coe.1 hy, hr]
    refine (hg (role x)).injOn (hmem x hx) hy'' ?_
    rw [hxy, hr]
  · intro r z hz
    obtain ⟨x, hx, rfl⟩ := (hg r).surjOn (Finset.mem_coe.2 hz)
    have hx' := mem_filter.1 (Finset.mem_coe.1 hx)
    exact ⟨x, hx'.1, by simp only [hx'.2]⟩

omit [Fintype V] in
lemma bijOn_piecewise (f₁ f₂ : V → V) (U₁ W₁ U₂ W₂ : Finset V)
    (h₁ : Set.BijOn f₁ U₁ W₁) (h₂ : Set.BijOn f₂ U₂ W₂) (hU : Disjoint U₁ U₂)
    (hW : Disjoint W₁ W₂) :
    Set.BijOn (fun u => if u ∈ U₁ then f₁ u else f₂ u) ↑(U₁ ∪ U₂) ↑(W₁ ∪ W₂) := by
  have hv1 : ∀ u ∈ U₁, (if u ∈ U₁ then f₁ u else f₂ u) = f₁ u := fun u hu => by simp [hu]
  have hv2 : ∀ u ∈ U₂, (if u ∈ U₁ then f₁ u else f₂ u) = f₂ u := fun u hu => by
    simp [disjoint_right.1 hU hu]
  refine ⟨fun u hu => ?_, fun u hu v hv huv => ?_, fun w hw => ?_⟩
  · simp only [coe_union, Set.mem_union, Finset.mem_coe] at hu ⊢
    rcases hu with hu | hu
    · rw [hv1 u hu]; exact Or.inl (h₁.mapsTo hu)
    · rw [hv2 u hu]; exact Or.inr (h₂.mapsTo hu)
  · simp only [coe_union, Set.mem_union, Finset.mem_coe] at hu hv
    simp only at huv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · rw [hv1 u hu, hv1 v hv] at huv; exact h₁.injOn hu hv huv
    · rw [hv1 u hu, hv2 v hv] at huv
      exact absurd (huv ▸ h₁.mapsTo hu) (disjoint_right.1 hW (h₂.mapsTo hv))
    · rw [hv2 u hu, hv1 v hv] at huv
      exact absurd (huv ▸ h₂.mapsTo hu) (disjoint_left.1 hW (h₁.mapsTo hv))
    · rw [hv2 u hu, hv2 v hv] at huv; exact h₂.injOn hu hv huv
  · simp only [coe_union, Set.mem_union, Finset.mem_coe] at hw
    rcases hw with hw | hw
    · obtain ⟨u, hu, rfl⟩ := h₁.surjOn hw
      exact ⟨u, by simp [Finset.mem_coe.1 hu], hv1 u hu⟩
    · obtain ⟨u, hu, rfl⟩ := h₂.surjOn hw
      exact ⟨u, by simp [Finset.mem_coe.1 hu], hv2 u hu⟩

omit [Fintype V] in
/-- **A perfect matching of a sampled bipartite graph** (Lemma 2.5 without enlargement, with
cut density from the gap). -/
lemma exists_matching (H : WGraph V) (col : V → Bool) (hbip : H.IsBipartiteWith col)
    (b : Bool) (U W : Finset V) (hU : ∀ x ∈ U, col x = b) (hW : ∀ x ∈ W, col x = !b)
    (hcard : U.card = W.card) (hne : U.Nonempty) (P η' s : ℝ) (hP : 0 < P) (hs : 0 < s)
    (hs1 : s ≤ 1) (hη0 : 0 ≤ η') (hη : η' ≤ s / 40)
    (hdeg : (H.induce (U ∪ W)).DegNear P η') (hgap : (H.induce (U ∪ W)).HasGap s) :
    ∃ f : V → V, Set.BijOn f U W ∧ ∀ u ∈ U, 0 < H.w u (f u) := by
  classical
  set S := U ∪ W with hS
  set H' := H.induce S with hH'
  have hUW : Disjoint U W := disjoint_left.2 fun x h1 h2 => by
    have e1 := hU x h1
    have e2 := hW x h2
    rw [e1] at e2
    cases b <;> simp at e2
  set L₀ : Finset ↥S := univ.filter fun x => x.1 ∈ U with hL₀
  set R₀ : Finset ↥S := univ.filter fun x => x.1 ∈ W with hR₀
  have hLR : Disjoint L₀ R₀ := by
    refine disjoint_left.2 fun x h1 h2 => ?_
    simp only [hL₀, hR₀, mem_filter, mem_univ, true_and] at h1 h2
    exact disjoint_left.1 hUW h1 h2
  have hLRu : L₀ ∪ R₀ = univ := by
    ext x
    simp only [hL₀, hR₀, mem_union, mem_filter, mem_univ, true_and, iff_true]
    exact mem_union.1 x.2
  have hLmap : L₀.map (Function.Embedding.subtype _) = U := by
    ext x
    simp only [hL₀, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, mem_union_left _ hx⟩, hx, rfl⟩
  have hRmap : R₀.map (Function.Embedding.subtype _) = W := by
    ext x
    simp only [hR₀, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, mem_union_right _ hx⟩, hx, rfl⟩
  set m := U.card with hm
  have hLc : L₀.card = m := by rw [← card_map, hLmap]
  have hRc : R₀.card = m := by rw [← card_map, hRmap, hcard]
  have hbL : ∀ x ∈ L₀, ∀ y ∈ L₀, H'.w x y = 0 := by
    intro x hx y hy
    simp only [hL₀, mem_filter, mem_univ, true_and] at hx hy
    exact w_eq_zero_of_col H col hbip ((hU _ hx).trans (hU _ hy).symm)
  have hbR : ∀ x ∈ R₀, ∀ y ∈ R₀, H'.w x y = 0 := by
    intro x hx y hy
    simp only [hR₀, mem_filter, mem_univ, true_and] at hx hy
    exact w_eq_zero_of_col H col hbip ((hW _ hx).trans (hW _ hy).symm)
  have hdegL : ∀ v ∈ L₀, |H'.degOn v R₀ - P| ≤ η' * P := by
    intro v hv
    have : H'.degOn v R₀ = H'.deg v := by
      unfold WGraph.deg WGraph.degOn
      rw [← hLRu, BipSampling.sum_union_left_zero L₀ R₀ hLR H'.w v (fun y hy => hbL v hv y hy)]
    rw [this]; exact hdeg v
  have hdegR : ∀ v ∈ R₀, |H'.degOn v L₀ - P| ≤ η' * P := by
    intro v hv
    have : H'.degOn v L₀ = H'.deg v := by
      unfold WGraph.deg WGraph.degOn
      rw [← hLRu, BipSampling.sum_union_right_zero L₀ R₀ hLR H'.w v (fun y hy => hbR v hv y hy)]
    rw [this]; exact hdeg v
  have hDB : H'.DegBetween ((1 - η') * P) ((1 + η') * P) := fun x => by
    have := abs_le.1 (hdeg x)
    constructor <;> nlinarith
  have hcd := WGraph.isCutDense_of_hasGap H' hgap hs.le (by linarith) hP hDB
  have hcardS : (Fintype.card ↥S : ℝ) = 2 * m := by
    rw [Fintype.card_coe, hS, card_union_of_disjoint hUW, ← hcard]
    push_cast; ring
  set ξ := s * (1 - η') ^ 2 * P / ((1 + η') * Fintype.card ↥S) with hξ
  have hm0 : (0 : ℝ) < m := by exact_mod_cast card_pos.2 hne
  have hα : ξ * m / P = s * (1 - η') ^ 2 / (2 * (1 + η')) := by
    rw [hξ, hcardS]; field_simp
  have hη1 : η' ≤ 1 / 40 := by linarith
  have hαpos : 0 < ξ * m / P := by
    rw [hα]; exact div_pos (mul_pos hs (pow_pos (by linarith) 2)) (by linarith)
  have hαle : ξ * m / P ≤ 1 / 2 := by
    rw [hα, div_le_iff₀ (by linarith)]
    nlinarith
  have hηα : η' ≤ ξ * m / P / 10 := by
    rw [hα, le_div_iff₀ (by norm_num), le_div_iff₀ (by linarith)]
    have h1 : η' * (1 + η') ≤ s / 40 * (41 / 40) :=
      mul_le_mul hη (by linarith) (by linarith) (by positivity)
    have h2 : (39 / 40 : ℝ) ^ 2 ≤ (1 - η') ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have h3 := mul_le_mul_of_nonneg_left h2 hs.le
    nlinarith
  have hcut : ∀ A ⊆ L₀ ∪ R₀, ξ * A.card * ((L₀ ∪ R₀) \ A).card ≤
      H'.edgeWeight A ((L₀ ∪ R₀) \ A) := by
    intro A _
    rw [hLRu]
    exact hcd A
  have hzero : ∀ v : ↥S, H'.degOn v ∅ ≤ ξ * m / P * P / 20 := fun v => by
    simp only [WGraph.degOn, sum_empty]
    positivity
  obtain ⟨f, hfinj, hfR, hfw⟩ := robust_hall H' L₀ R₀ ∅ ∅ m P η' ξ hLR
    (disjoint_empty_right _) (disjoint_empty_right _) (disjoint_empty_right _)
    (disjoint_empty_right _) (disjoint_empty_right _) hLc hRc rfl hbL hbR hP hdegL hdegR hcut
    hαpos hαle hηα (fun x hx => absurd hx (notMem_empty x))
    (fun x hx => absurd hx (notMem_empty x)) (fun v _ => hzero v) (fun v _ => hzero v)
  have hmemL : ∀ u (hu : u ∈ U), (⟨u, mem_union_left _ hu⟩ : ↥S) ∈ L₀ ∪ ∅ := fun u hu =>
    mem_union_left _ (by simp [hL₀, hu])
  set g : V → V := fun u => if hu : u ∈ U then (f ⟨⟨u, mem_union_left _ hu⟩, hmemL u hu⟩ : V)
    else u with hg
  have hgU : ∀ u (hu : u ∈ U), g u = (f ⟨⟨u, mem_union_left _ hu⟩, hmemL u hu⟩ : V) :=
    fun u hu => by simp only [hg, hu, ↓reduceDIte]
  have hmaps : ∀ u ∈ U, g u ∈ W := by
    intro u hu
    rw [hgU u hu]
    have := hfR ⟨⟨u, mem_union_left _ hu⟩, hmemL u hu⟩
    rw [union_empty] at this
    simpa [hR₀] using this
  have hinj : Set.InjOn g U := by
    intro u hu v hv huv
    simp only [Finset.mem_coe] at hu hv
    rw [hgU u hu, hgU v hv] at huv
    have := hfinj (Subtype.ext huv)
    simpa using this
  have himg : U.image g = W := by
    refine eq_of_subset_of_card_le (fun z hz => ?_) ?_
    · obtain ⟨u, hu, rfl⟩ := mem_image.1 hz; exact hmaps u hu
    · rw [card_image_of_injOn hinj]; omega
  refine ⟨g, ⟨fun u hu => hmaps u hu, hinj, fun w hw => ?_⟩, fun u hu => ?_⟩
  · have : w ∈ U.image g := by rw [himg]; exact hw
    obtain ⟨u, hu, rfl⟩ := mem_image.1 this
    exact ⟨u, hu, rfl⟩
  · rw [hgU u hu]
    exact hfw ⟨⟨u, mem_union_left _ hu⟩, hmemL u hu⟩

/-! ### Cells of a sub-cell labeling -/

/-- The sub-cells of a cell. -/
def cellSub : Cell → Finset SC
  | .ends => {.ends} | .att => {.att} | .rtr => {.rtr} | .cyc => {.cyc} | .div => {.div}
  | .inp => {.inp} | .out => {.out} | .lu => {.uP, .uD, .uF} | .lv => {.vP, .vD, .vF}
  | .pool => {.pool}

lemma toCell_eq_iff (y : SC) (c : Cell) : y.toCell = c ↔ y ∈ cellSub c := by
  cases y <;> cases c <;> simp [SC.toCell, cellSub]

/-- The cell labeling induced by a sub-cell labeling. -/
def labOf (κ : V → SC) : V → Cell := fun x => (κ x).toCell

omit [DecidableEq V] in
lemma cellSet_filter_col (col : V → Bool) (κ : V → SC) (c : Cell) (b : Bool) :
    (cellSet (labOf κ) c).filter (fun x => col x = b) = blk col κ b (cellSub c) := by
  ext x
  simp [labOf, mem_blk, toCell_eq_iff, and_comm]

lemma cellSet_eq_union (col : V → Bool) (κ : V → SC) (c : Cell) (b : Bool) :
    cellSet (labOf κ) c = blk col κ b (cellSub c) ∪ blk col κ (!b) (cellSub c) := by
  ext x
  simp only [mem_cellSet, labOf, toCell_eq_iff, mem_union, mem_blk]
  cases col x <;> cases b <;> simp

lemma card_blk_union (col : V → Bool) (κ : V → SC) (b : Bool) (S : Finset SC) :
    (blk col κ b S ∪ blk col κ (!b) S).card = (blk col κ b S).card + (blk col κ (!b) S).card := by
  refine card_union_of_disjoint (disjoint_left.2 fun x h1 h2 => ?_)
  rw [mem_blk] at h1 h2
  rw [h1.1] at h2
  cases b <;> simp at h2

omit [Fintype V] [DecidableEq V] in
lemma degOn_filter_opp (H : WGraph V) (col : V → Bool) (hbip : H.IsBipartiteWith col) (v : V)
    (X : Finset V) : H.degOn v X = H.degOn v (X.filter fun x => col x = !col v) := by
  unfold WGraph.degOn
  rw [← sum_filter_add_sum_filter_not X (fun x => col x = !col v)]
  have : ∑ x ∈ X.filter (fun x => ¬ col x = !col v), H.w v x = 0 := sum_eq_zero fun x hx => by
    have h := (mem_filter.1 hx).2
    apply w_eq_zero_of_col H col hbip
    cases h1 : col v <;> cases h2 : col x <;> simp_all
  rw [this, add_zero]

omit [DecidableEq V] in
lemma degOn_cellSet (H : WGraph V) (col : V → Bool) (hbip : H.IsBipartiteWith col)
    (κ : V → SC) (c : Cell) (v : V) :
    H.degOn v (cellSet (labOf κ) c) = H.degOn v (blk col κ (!col v) (cellSub c)) := by
  rw [degOn_filter_opp H col hbip v, cellSet_filter_col]

omit [DecidableEq V] in
lemma degOn_le_blk (H : WGraph V) (col : V → Bool) (hbip : H.IsBipartiteWith col)
    (κ : V → SC) (S : Finset SC) (v : V) (X : Finset V) (hX : ∀ x ∈ X, κ x ∈ S) :
    H.degOn v X ≤ H.degOn v (blk col κ (!col v) S) := by
  rw [degOn_filter_opp H col hbip v X]
  refine degOn_mono H v fun x hx => ?_
  rw [mem_filter] at hx
  exact mem_blk.2 ⟨hx.2, hX x hx.1⟩

omit [Fintype V] [DecidableEq V] in
lemma dev_lo_hi {a f d t lo hi : ℝ} (h : |a - f * d| < t) (hf : 0 ≤ f) (hlo : lo ≤ d)
    (hhi : d ≤ hi) : f * lo - t < a ∧ a < f * hi + t := by
  have h1 := abs_lt.1 h
  have h2 := mul_le_mul_of_nonneg_left hlo hf
  have h3 := mul_le_mul_of_nonneg_left hhi hf
  constructor <;> linarith

/-- The prescribed sizes of the sub-cells (`a`, `b'`: the numbers of positive and negative
tails of `J`). -/
def szFun (N₀ s kC m a b' : ℕ) : Bool → SC → ℕ
  | _, .ends => 0
  | _, .att => s
  | _, .rtr => s
  | _, .cyc => kC
  | _, .div => s
  | _, .inp => m
  | _, .out => m
  | true, .uP => a
  | true, .uD => 1
  | true, .uF => m - 1 - a
  | true, .vP => b'
  | true, .vD => 0
  | true, .vF => m - b'
  | false, .uP => b'
  | false, .uD => 0
  | false, .uF => m - b'
  | false, .vP => a
  | false, .vD => 1
  | false, .vF => m - 1 - a
  | _, .pool => N₀ - (3 * s + kC + 4 * m)

lemma univ_SC : (univ : Finset SC) =
    {.ends, .att, .rtr, .cyc, .div, .inp, .out, .uP, .uD, .uF, .vP, .vD, .vF, .pool} := rfl

lemma sum_szFun (N₀ s kC m a b' : ℕ) (ha : a + 1 ≤ m) (hb : b' ≤ m)
    (hN : 3 * s + kC + 4 * m ≤ N₀) (b : Bool) : ∑ c, szFun N₀ s kC m a b' b c = N₀ := by
  rw [univ_SC]
  cases b <;> simp [szFun] <;> omega

/-- The thresholds of the degree events. -/
noncomputable def thrFun (S₁ DC PL tW tE : ℝ) : DB → ℝ
  | .att => S₁ / 4 | .rtr => S₁ / 4 | .cyc => DC / 4
  | .inp => PL | .out => PL | .lu => PL | .lv => PL
  | .wide => tW | .env => tE

/-! ### The one-sided events and the entries of `F` -/

lemma centred_sq_le (H : WGraph V) (col : V → Bool) (E : Finset V) (b : Bool) (N₀ : ℕ)
    (D η : ℝ) (hwle : ∀ x y, H.w x y ≤ 1) (hA : (classOf E col b).card = N₀)
    (hN : (0 : ℝ) < N₀) (hD : 0 < D) (hDN : D ≤ 2 * N₀) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 32)
    (hdA : ∀ x ∈ classOf E col b, (1 - η) * D ≤ H.degOn x (classOf E col (!b)) ∧
      H.degOn x (classOf E col (!b)) ≤ (1 + η) * D)
    (hdB : ∀ y ∈ classOf E col (!b), (1 - η) * D ≤ H.degOn y (classOf E col b) ∧
      H.degOn y (classOf E col b) ≤ (1 + η) * D)
    {x y : V} (hx : x ∈ classOf E col b) (hy : y ∈ classOf E col (!b)) :
    centred H (classOf E col b) (classOf E col (!b)) x y ^ 2 ≤ 2 * H.w x y + 16 * D / N₀ := by
  have he : N₀ * ((1 - η) * D) ≤ H.edgeWeight (classOf E col b) (classOf E col (!b)) := by
    have : ∑ l ∈ classOf E col b, (1 - η) * D ≤
        ∑ l ∈ classOf E col b, H.degOn l (classOf E col (!b)) :=
      sum_le_sum fun l hl => (hdA l hl).1
    rw [sum_const, hA, nsmul_eq_mul] at this
    exact this
  have hdi := hdA x hx
  have hdj := hdB y hy
  have h1η : 0 < (1 - η) * D := mul_pos (by linarith) hD
  have hdipos : 0 < H.degOn x (classOf E col (!b)) := lt_of_lt_of_le h1η hdi.1
  have hdjpos : 0 < H.degOn y (classOf E col b) := lt_of_lt_of_le h1η hdj.1
  have hepos : 0 < H.edgeWeight (classOf E col b) (classOf E col (!b)) :=
    lt_of_lt_of_le (mul_pos hN h1η) he
  unfold centred
  exact BipSampling.num_entry_sq (H.nonneg x y) (hwle x y)
    (div_nonneg (mul_nonneg hdipos.le hdjpos.le) hepos.le)
    (BipSampling.num_rank_one hdipos hdjpos hdi.2 hdj.2 he hN hD hη0 hη hepos) hD hN hDN

lemma cls_deg_bounds (H : WGraph V) (col : V → Bool) (E : Finset V) (D σ c : ℝ)
    (hc0 : 0 ≤ c) (hσ : 0 < σ)
    (hcls : ∀ v b, col v = !b → (1 - 2 * c * σ) * D ≤ H.degOn v (classOf E col b) ∧
      H.degOn v (classOf E col b) ≤ (1 + c * σ) * D) (b : Bool) (hD : 0 < D) :
    ∀ x ∈ classOf E col b, (1 - 2 * c * σ) * D ≤ H.degOn x (classOf E col (!b)) ∧
      H.degOn x (classOf E col (!b)) ≤ (1 + 2 * c * σ) * D := by
  intro x hx
  have h := hcls x (!b) (by rw [(mem_classOf.1 hx).2, Bool.not_not])
  refine ⟨h.1, h.2.trans ?_⟩
  have : 0 ≤ c * σ * D := mul_nonneg (mul_nonneg hc0 hσ.le) hD.le
  linarith

/-- **The one-sided events (2.9)** for a block, from the norm and degree events. -/
lemma oneSided_of (H : WGraph V) (col : V → Bool) (E : Finset V) (b : Bool) (N₀ m : ℕ)
    (D σ L K δ c C₀ δ' : ℝ) (X : Finset V) (hX : X ⊆ classOf E col b) (hXc : X.card = m)
    (hwle : ∀ x y, H.w x y ≤ 1)
    (hA : ∀ b, (classOf E col b).card = N₀) (hN : (0 : ℝ) < N₀) (hD : 0 < D)
    (hDN : D ≤ 2 * N₀) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c) (hcσ : c * σ ≤ 1 / 64)
    (hcls : ∀ v b, col v = !b → (1 - 2 * c * σ) * D ≤ H.degOn v (classOf E col b) ∧
      H.degOn v (classOf E col b) ≤ (1 + c * σ) * D)
    (hnormX : ∀ v : V → ℝ, ∑ i ∈ classOf E col (!b), (∑ j ∈ X,
        centred H (classOf E col b) (classOf E col (!b)) j i * v j) ^ 2 ≤
      (Real.sqrt ((m : ℝ) / N₀) * ((1 - σ / 2) * ((1 + 2 * c * σ) * D)) +
        C₀ * Real.sqrt (24 * D) * Real.sqrt (6 * L)) ^ 2 * ∑ j ∈ X, v j ^ 2)
    (hdevX : ∀ v, col v = !b → |H.degOn v X - (m : ℝ) / N₀ * H.degOn v (classOf E col b)| <
      δ' * σ * ((m : ℝ) / N₀ * D) / 4)
    (hC₀ : 0 ≤ C₀)
    (hnormK : C₀ * Real.sqrt (24 * D) * Real.sqrt (6 * L) ≤ K * Real.sqrt (D * L))
    (hK : 18 + 2 * δ ≤ K) (hδ' : 0 < δ') (hδ'δ : δ' ≤ δ) (hcδ : 16 * c ≤ δ') (hδ'1 : δ' ≤ 1) :
    OneSided H (classOf E col b) (classOf E col (!b)) X ((m : ℝ) / N₀) D (σ / 2) L K δ := by
  have hp0 : 0 ≤ (m : ℝ) / N₀ := by positivity
  have hc16 : c ≤ 1 / 16 := by linarith
  have hdeg : ∀ y ∈ classOf E col (!b),
      |H.degOn y X - (m : ℝ) / N₀ * D| ≤ δ * (σ / 2) * ((m : ℝ) / N₀) * D := by
    intro y hy
    have hyc : col y = !b := (mem_classOf.1 hy).2
    have h1 := abs_lt.1 (hdevX y hyc)
    have h2 := hcls y b hyc
    have h3 := mul_le_mul_of_nonneg_left h2.1 hp0
    have h4 := mul_le_mul_of_nonneg_left h2.2 hp0
    have hpD : 0 ≤ (m : ℝ) / N₀ * D := by positivity
    have h5 : 16 * c * σ * ((m : ℝ) / N₀ * D) ≤ δ' * σ * ((m : ℝ) / N₀ * D) := by
      have := mul_le_mul_of_nonneg_right hcδ (mul_nonneg hσ.le hpD)
      nlinarith
    have h6 : δ' * σ * ((m : ℝ) / N₀ * D) ≤ δ * σ * ((m : ℝ) / N₀ * D) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδ'δ hσ.le) hpD
    rw [abs_le]
    constructor <;> nlinarith
  refine ⟨fun v => ?_, fun y hy => ?_, hdeg⟩
  · set β := Real.sqrt ((m : ℝ) / N₀) * ((1 - σ / 2) * ((1 + 2 * c * σ) * D)) +
      C₀ * Real.sqrt (24 * D) * Real.sqrt (6 * L) with hβ
    have hβ0 : 0 ≤ β := by
      rw [hβ]
      have : 0 ≤ (1 - σ / 2) * ((1 + 2 * c * σ) * D) :=
        mul_nonneg (by linarith) (mul_nonneg (by positivity) hD.le)
      positivity
    have h := BipSampling.op_transpose (classOf E col (!b)) X
      (fun i j => centred H (classOf E col b) (classOf E col (!b)) j i) β hβ0 hnormX v
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sq_nonneg _))
    refine pow_le_pow_left₀ hβ0 ?_ 2
    rw [hβ]
    have hM : (1 - σ / 2) * ((1 + 2 * c * σ) * D) ≤ (1 - σ / 2 / 2) * D := by
      have h1 : 2 * c * σ ≤ σ / 8 := by nlinarith
      have h2 : 0 ≤ c * σ * σ := by positivity
      have : (1 - σ / 2) * (1 + 2 * c * σ) ≤ 1 - σ / 2 / 2 := by nlinarith
      nlinarith
    have := mul_le_mul_of_nonneg_left hM (Real.sqrt_nonneg ((m : ℝ) / N₀))
    nlinarith
  · have hyc : col y = !b := (mem_classOf.1 hy).2
    have hent : ∀ x ∈ X, centred H (classOf E col b) (classOf E col (!b)) x y ^ 2 ≤
        2 * H.w x y + 16 * D / N₀ := fun x hx =>
      centred_sq_le H col E b N₀ D (2 * c * σ) hwle (hA b) hN hD hDN (by positivity)
        (by linarith) (cls_deg_bounds H col E D σ c hc0 hσ hcls b hD)
        (fun y' hy' => by
          have h := hcls y' b (mem_classOf.1 hy').2
          exact ⟨h.1, h.2.trans (by nlinarith [mul_pos hσ hD])⟩) (hX hx) hy
    have hsum : ∑ x ∈ X, H.w x y = H.degOn y X :=
      sum_congr rfl fun x _ => H.symm x y
    have h1 := sum_le_sum hent
    rw [sum_add_distrib, ← mul_sum, sum_const, hXc, nsmul_eq_mul, hsum] at h1
    have h2 := abs_le.1 (hdeg y hy)
    have hpD : 0 ≤ (m : ℝ) / N₀ * D := by positivity
    have h3 : (m : ℝ) * (16 * D / N₀) = 16 * ((m : ℝ) / N₀ * D) := by ring
    have h4 : δ * (σ / 2) * ((m : ℝ) / N₀) * D ≤ δ * ((m : ℝ) / N₀ * D) := by
      have hδ0 : 0 ≤ δ := by linarith
      have := mul_le_mul_of_nonneg_left (show σ / 2 ≤ 1 by linarith) (mul_nonneg hδ0 hpD)
      nlinarith
    have h5 : (18 + 2 * δ) * ((m : ℝ) / N₀ * D) ≤ K * ((m : ℝ) / N₀ * D) :=
      mul_le_mul_of_nonneg_right hK hpD
    nlinarith

/-! ### Sizes of the event blocks -/

/-- Sizes of the degree-event blocks. -/
def dbSize (s kC m : ℕ) : DB → ℕ
  | .att => s | .rtr => s | .cyc => kC | .inp => m | .out => m | .lu => m | .lv => m
  | .wide => kC + 4 * m | .env => 3 * s + kC + 4 * m

/-- Sizes of the first blocks of the pair events. -/
def pbSize (s m a b' : ℕ) : Bool → PB → ℕ
  | _, .att => s | _, .rtr => s | _, .div => s | true, .fill => m - 1 - a
  | false, .fill => m - b'

omit [DecidableEq V] in
lemma card_DB {col : V → Bool} {κ : V → SC} {N₀ s kC m a b' : ℕ}
    (hsz : ∀ b c', c' ≠ SC.ends → (blk col κ b {c'}).card = szFun N₀ s kC m a b' b c')
    (ha : a + 1 ≤ m) (hb : b' ≤ m) (b : Bool) (d : DB) :
    (blk col κ b d.cells).card = dbSize s kC m d := by
  rw [card_blk (szFun N₀ s kC m a b') hsz b (by cases d <;> decide)]
  cases b <;> cases d <;> simp [DB.cells, szFun, dbSize] <;> omega

omit [DecidableEq V] in
lemma card_PB₁ {col : V → Bool} {κ : V → SC} {N₀ s kC m a b' : ℕ}
    (hsz : ∀ b c', c' ≠ SC.ends → (blk col κ b {c'}).card = szFun N₀ s kC m a b' b c')
    (b : Bool) (j : PB) : (blk col κ b j.c₁).card = pbSize s m a b' b j := by
  rw [card_blk (szFun N₀ s kC m a b') hsz b (by cases j <;> decide)]
  cases b <;> cases j <;> simp [PB.c₁, szFun, pbSize]

omit [DecidableEq V] in
lemma card_PB₂ {col : V → Bool} {κ : V → SC} {N₀ s kC m a b' : ℕ}
    (hsz : ∀ b c', c' ≠ SC.ends → (blk col κ b {c'}).card = szFun N₀ s kC m a b' b c')
    (b : Bool) (j : PB) : (blk col κ (!b) j.c₂).card = pbSize s m a b' b j := by
  rw [card_blk (szFun N₀ s kC m a b') hsz (!b) (by cases j <;> decide)]
  cases b <;> cases j <;> simp [PB.c₂, szFun, pbSize]

omit [DecidableEq V] in
lemma card_NB {col : V → Bool} {κ : V → SC} {N₀ s kC m a b' : ℕ}
    (hsz : ∀ b c', c' ≠ SC.ends → (blk col κ b {c'}).card = szFun N₀ s kC m a b' b c')
    (ha : a + 1 ≤ m) (hb : b' ≤ m) (b : Bool) (n : NB) : (blk col κ b n.cells).card = m := by
  rw [card_blk (szFun N₀ s kC m a b') hsz b (by cases n <;> decide)]
  cases b <;> cases n <;> simp [NB.cells, szFun] <;> omega

/-! ### The union bound -/

omit [Fintype V] [DecidableEq V] in
lemma exists_forall_of_count {α ι : Type*} [DecidableEq α] [Fintype ι] (G : Finset α)
    (hG : G.Nonempty) (P : ι → α → Prop) (ε : ℝ) (B : ι → Finset α)
    (hB : ∀ i, ∀ π ∈ G, ¬ P i π → π ∈ B i) (hcard : ∀ i, ((B i).card : ℝ) ≤ ε * G.card)
    (hε : (Fintype.card ι : ℝ) * ε < 1) : ∃ π ∈ G, ∀ i, P i π := by
  by_contra hne
  push Not at hne
  have hsub : G ⊆ univ.biUnion B := by
    intro π hπ
    obtain ⟨i, hi⟩ := hne π hπ
    exact mem_biUnion.2 ⟨i, mem_univ _, hB i π hπ hi⟩
  have h1 : (G.card : ℝ) ≤ ∑ i, ((B i).card : ℝ) := by
    have := (card_le_card hsub).trans card_biUnion_le
    exact_mod_cast this
  have h2 : ∑ i, ((B i).card : ℝ) ≤ Fintype.card ι * (ε * G.card) := by
    calc _ ≤ ∑ _i : ι, ε * (G.card : ℝ) := sum_le_sum fun i _ => hcard i
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hG0 : (0 : ℝ) < G.card := by exact_mod_cast card_pos.2 hG
  nlinarith

omit [Fintype V] [DecidableEq V] in
lemma num_tail (N N₀ : ℕ) (L : ℝ) (hL : 10 ≤ L) (hN : Real.log (2 * N) ≤ L) (hN1 : 1 ≤ N)
    (hNN : N₀ ≤ N) :
    (N : ℝ) * (2 * Real.exp (-(6 * L))) ≤ Real.exp (-(4 * L)) ∧
      (N₀ : ℝ) * (N₀ + 1) * Real.exp (-(6 * L)) ≤ Real.exp (-(4 * L)) ∧
      34 * Real.exp (-(4 * L)) < 1 := by
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNN' : (N₀ : ℝ) ≤ N := by exact_mod_cast hNN
  have hN₀0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
  have h2N : 2 * (N : ℝ) ≤ Real.exp L := by
    have := Real.exp_le_exp.2 hN
    rwa [Real.exp_log (by linarith)] at this
  have e6 : Real.exp (-(6 * L)) = Real.exp (-(4 * L)) * Real.exp (-L) * Real.exp (-L) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hEL : Real.exp L * Real.exp (-L) = 1 := by rw [← Real.exp_add]; simp
  have hE4 := Real.exp_pos (-(4 * L))
  have hEm := Real.exp_pos (-L)
  have hEm1 : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [e6]
    have : (N : ℝ) * 2 * Real.exp (-L) ≤ 1 := by nlinarith
    nlinarith [mul_pos hE4 hEm]
  · rw [e6]
    have h1 : (N₀ : ℝ) * (N₀ + 1) ≤ 2 * N * (2 * N) := by nlinarith
    have h2 : 2 * (N : ℝ) * Real.exp (-L) ≤ 1 := by nlinarith
    have h3 : (N₀ : ℝ) * (N₀ + 1) * (Real.exp (-L) * Real.exp (-L)) ≤ 1 := by
      calc _ ≤ 2 * N * (2 * N) * (Real.exp (-L) * Real.exp (-L)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (2 * N * Real.exp (-L)) * (2 * N * Real.exp (-L)) := by ring
        _ ≤ 1 * 1 := mul_le_mul h2 h2 (by positivity) (by norm_num)
        _ = 1 := by norm_num
    nlinarith
  · have h40 : (41 : ℝ) ≤ Real.exp 40 := by
      have := Real.add_one_le_exp (40 : ℝ); linarith
    have h4L : Real.exp (-(4 * L)) ≤ Real.exp (-40) := Real.exp_le_exp.2 (by linarith)
    have : Real.exp (-40) * Real.exp 40 = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-40)]

/-- The index type of all the events. -/
abbrev EvIdx := Bool × (PB ⊕ (DB ⊕ NB))

lemma card_EvIdx : Fintype.card EvIdx = 34 := rfl

/-! ### Assembly of the initial partition from a good labeling -/

/-- The new ports and the dummies of a labeling with the prescribed sizes. -/
lemma build_ports (col : V → Bool) (E : Finset V) (κ : V → SC) (tail : V → Bool)
    {N₀ s kC m a b' : ℕ}
    (hsz : ∀ b c', c' ≠ SC.ends → (blk col κ b {c'}).card = szFun N₀ s kC m a b' b c')
    (hrole : ∀ r : Bool × Bool, (E.filter fun x => (col x, tail x) = r).card =
      (blk col κ r.1 {if r.2 then SC.uP else SC.vP}).card) :
    ∃ port : V → V, ∃ dA dB : V,
      (∀ x ∈ E, col (port x) = col x ∧ κ (port x) = if tail x then SC.uP else SC.vP) ∧
      Set.InjOn port E ∧ (∀ z, z ∈ E.image port ↔ κ z = SC.uP ∨ κ z = SC.vP) ∧
      (∀ x, κ x = SC.uD ↔ x = dA) ∧ col dA = true ∧
      (∀ x, κ x = SC.vD ↔ x = dB) ∧ col dB = false := by
  have c_uDt : (blk col κ true {SC.uD}).card = 1 := by rw [hsz true _ (by decide)]; rfl
  have c_uDf : (blk col κ false {SC.uD}).card = 0 := by rw [hsz false _ (by decide)]; rfl
  have c_vDt : (blk col κ true {SC.vD}).card = 0 := by rw [hsz true _ (by decide)]; rfl
  have c_vDf : (blk col κ false {SC.vD}).card = 1 := by rw [hsz false _ (by decide)]; rfl
  obtain ⟨dA, hdA⟩ := card_eq_one.1 c_uDt
  obtain ⟨dB, hdB⟩ := card_eq_one.1 c_vDf
  have hdAmem : dA ∈ blk col κ true {SC.uD} := by rw [hdA]; exact mem_singleton_self _
  have hdBmem : dB ∈ blk col κ false {SC.vD} := by rw [hdB]; exact mem_singleton_self _
  have huD : ∀ x, κ x = SC.uD ↔ x = dA := by
    intro x
    constructor
    · intro hx
      cases hc : col x
      · have : x ∈ blk col κ false {SC.uD} := mem_blk.2 ⟨hc, by simp [hx]⟩
        rw [card_eq_zero.1 c_uDf] at this
        exact absurd this (notMem_empty _)
      · have : x ∈ blk col κ true {SC.uD} := mem_blk.2 ⟨hc, by simp [hx]⟩
        rw [hdA] at this
        exact mem_singleton.1 this
    · rintro rfl
      simpa using (mem_blk.1 hdAmem).2
  have hvD : ∀ x, κ x = SC.vD ↔ x = dB := by
    intro x
    constructor
    · intro hx
      cases hc : col x
      · have : x ∈ blk col κ false {SC.vD} := mem_blk.2 ⟨hc, by simp [hx]⟩
        rw [hdB] at this
        exact mem_singleton.1 this
      · have : x ∈ blk col κ true {SC.vD} := mem_blk.2 ⟨hc, by simp [hx]⟩
        rw [card_eq_zero.1 c_vDt] at this
        exact absurd this (notMem_empty _)
    · rintro rfl
      simpa using (mem_blk.1 hdBmem).2
  have hPdisj : ∀ r r' : Bool × Bool, r ≠ r' →
      Disjoint (blk col κ r.1 {if r.2 then SC.uP else SC.vP})
        (blk col κ r'.1 {if r'.2 then SC.uP else SC.vP}) := by
    rintro ⟨r1, r2⟩ ⟨r1', r2'⟩ hrr
    refine disjoint_left.2 fun x h1 h2 => hrr ?_
    rw [mem_blk, mem_singleton] at h1 h2
    refine Prod.ext (h1.1.symm.trans h2.1) ?_
    have := h1.2.symm.trans h2.2
    cases r2 <;> cases r2' <;> first | rfl | (simp at this)
  obtain ⟨port, hportP, hportinj, hportsurj⟩ := exists_port E (fun x => (col x, tail x))
    (fun r => blk col κ r.1 {if r.2 then SC.uP else SC.vP}) hPdisj hrole
  have hportκ : ∀ x ∈ E, col (port x) = col x ∧
      κ (port x) = if tail x then SC.uP else SC.vP := fun x hx => by
    have := mem_blk.1 (hportP x hx)
    simpa using this
  refine ⟨port, dA, dB, hportκ, hportinj, fun z => ?_, huD, (mem_blk.1 hdAmem).1, hvD,
    (mem_blk.1 hdBmem).1⟩
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hz
    rw [(hportκ x hx).2]
    cases tail x <;> simp
  · intro hz
    have hmem : z ∈ blk col κ (col z, decide (κ z = SC.uP)).1
        {if (col z, decide (κ z = SC.uP)).2 then SC.uP else SC.vP} := by
      rw [mem_blk, mem_singleton]
      refine ⟨rfl, ?_⟩
      rcases hz with hz | hz <;> simp [hz]
    obtain ⟨x, hx, rfl⟩ := hportsurj _ z hmem
    exact mem_image_of_mem _ hx

lemma filler_lu (col : V → Bool) (E : Finset V) (κ : V → SC) (port : V → V) (dA : V)
    (himg : ∀ z, z ∈ E.image port ↔ κ z = SC.uP ∨ κ z = SC.vP)
    (huD : ∀ x, κ x = SC.uD ↔ x = dA) :
    filler (labOf κ) Cell.lu dA E port = blk col κ true {SC.uF} ∪ blk col κ false {SC.uF} := by
  ext x
  have e1 : (x ≠ dA) ↔ κ x ≠ SC.uD := by rw [Ne, Ne, huD]
  simp only [filler, mem_sdiff, mem_erase, mem_cellSet, labOf, toCell_eq_iff, cellSub,
    himg, e1, mem_union, mem_blk, mem_singleton, mem_insert]
  cases col x <;> cases κ x <;> simp

lemma filler_lv (col : V → Bool) (E : Finset V) (κ : V → SC) (port : V → V) (dB : V)
    (himg : ∀ z, z ∈ E.image port ↔ κ z = SC.uP ∨ κ z = SC.vP)
    (hvD : ∀ x, κ x = SC.vD ↔ x = dB) :
    filler (labOf κ) Cell.lv dB E port = blk col κ false {SC.vF} ∪ blk col κ true {SC.vF} := by
  ext x
  have e1 : (x ≠ dB) ↔ κ x ≠ SC.vD := by rw [Ne, Ne, hvD]
  simp only [filler, mem_sdiff, mem_erase, mem_cellSet, labOf, toCell_eq_iff, cellSub,
    himg, e1, mem_union, mem_blk, mem_singleton, mem_insert]
  cases col x <;> cases κ x <;> simp

omit [DecidableEq V] in
lemma envelope_filter (col : V → Bool) (κ : V → SC) (b : Bool) :
    (envelope (labOf κ)).filter (fun x => col x = b) = blk col κ b DB.env.cells := by
  ext x
  have key : (labOf κ x ≠ Cell.pool ∧ labOf κ x ≠ Cell.ends) ↔ κ x ∈ DB.env.cells := by
    simp only [labOf]; cases κ x <;> simp [SC.toCell, DB.cells]
  simp only [envelope, mem_filter, mem_univ, true_and, mem_blk]
  rw [key, and_comm]

omit [Fintype V] [DecidableEq V] in
lemma arith_small {c₂' σ c₁' : ℝ} (hc₂ : 0 < c₂') (hc₂1 : c₂' ≤ 1) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 10) (hc₁' : c₁' = c₂' / 40) :
    c₁' * (σ / 2) ≤ 1 / 800 ∧ c₂' * (σ / 2) ≤ 1 := by
  subst hc₁'
  constructor <;> nlinarith

omit [Fintype V] [DecidableEq V] in
lemma degBetween_of_near {W : Type*} [Fintype W] (H : WGraph W) {P e : ℝ} (hP : 0 < P)
    (he : e ≤ 1 / 3) (h : H.DegNear P e) :
    H.DegBetween (1 / 2 * ((1 + e) * P)) ((1 + e) * P) := fun x => by
  have := abs_le.1 (h x)
  constructor <;> nlinarith

omit [Fintype V] [DecidableEq V] in
lemma degBetween_of_near' {W : Type*} [Fintype W] (H : WGraph W) {P e : ℝ} (hP : 0 < P)
    (he : e ≤ 1 / 2) (h : H.DegNear P e) : H.DegBetween (1 / 2 * P) (2 * P) := fun x => by
  have := abs_le.1 (h x)
  constructor <;> nlinarith

omit [Fintype V] [DecidableEq V] in
lemma arith_res {S c σ e d k N₀ D : ℝ} (hS : S = k / N₀ * D) (hS0 : 0 < S)
    (hcσ : c * σ ≤ 1 / 64) (he : e ≤ 1 / 800)
    (h : k / N₀ * ((1 - 2 * c * σ) * D) - S / 4 < d) : 1 / 4 * ((1 + e) * S) ≤ d := by
  have e1 : k / N₀ * ((1 - 2 * c * σ) * D) = S * (1 - 2 * (c * σ)) := by rw [hS]; ring
  rw [e1] at h
  nlinarith

omit [Fintype V] [DecidableEq V] in
lemma arith_cyc {S c σ d k N₀ D : ℝ} (hS : S = k / N₀ * D) (hS0 : 0 ≤ S)
    (hcσ : c * σ ≤ 1 / 64)
    (h : k / N₀ * ((1 - 2 * c * σ) * D) - S / 4 < d ∧ d < k / N₀ * ((1 + c * σ) * D) + S / 4) :
    1 / 2 * S ≤ d ∧ d ≤ 2 * S := by
  have e1 : k / N₀ * ((1 - 2 * c * σ) * D) = S * (1 - 2 * (c * σ)) := by rw [hS]; ring
  have e2 : k / N₀ * ((1 + c * σ) * D) = S * (1 + c * σ) := by rw [hS]; ring
  rw [e1, e2] at h
  obtain ⟨h1, h2⟩ := h
  constructor <;> nlinarith

/-- The perfect matching of the fillers of the special transition. -/
lemma build_mu (H : WGraph V) (col : V → Bool) (hbip : H.IsBipartiteWith col) (κ : V → SC)
    (N₀ : ℕ) (D σ c₁' c₂ c₂' : ℝ) (hN0 : (0 : ℝ) < N₀) (hD : 0 < D) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hc₂ : 0 < c₂') (hc₂1 : c₂' ≤ 1) (hc₂le : c₂' ≤ c₂) (hc₁' : c₁' = c₂' / 40)
    (hfill : ∀ b, (blk col κ b {SC.uF}).card = (blk col κ (!b) {SC.vF}).card)
    (hfpos : ∀ b, 1 ≤ (blk col κ b {SC.uF}).card)
    (hpair : ∀ b, (H.induce (blk col κ b PB.fill.c₁ ∪ blk col κ (!b) PB.fill.c₂)).DegNear
        (((blk col κ b PB.fill.c₁).card : ℝ) / N₀ * D) (c₁' * (σ / 2)) ∧
      (H.induce (blk col κ b PB.fill.c₁ ∪ blk col κ (!b) PB.fill.c₂)).HasGap (c₂ * (σ / 2))) :
    ∃ μ : V → V, Set.BijOn μ ↑(blk col κ true {SC.uF} ∪ blk col κ false {SC.uF})
        ↑(blk col κ false {SC.vF} ∪ blk col κ true {SC.vF}) ∧
      ∀ u ∈ blk col κ true {SC.uF} ∪ blk col κ false {SC.uF}, 0 < H.w u (μ u) := by
  have hσ₀ : 0 < σ / 2 := by positivity
  have hc₁'0 : 0 < c₁' := by rw [hc₁']; positivity
  simp only [PB.c₁, PB.c₂] at hpair
  have hmatch : ∀ b, ∃ f : V → V, Set.BijOn f (blk col κ b {SC.uF}) (blk col κ (!b) {SC.vF}) ∧
      ∀ u ∈ blk col κ b {SC.uF}, 0 < H.w u (f u) := by
    intro b
    have hk : (1 : ℝ) ≤ (blk col κ b {SC.uF}).card := by exact_mod_cast hfpos b
    have hc2s : c₂' * (σ / 2) ≤ 1 := by
      have := mul_le_mul hc₂1 (show σ / 2 ≤ 1 by linarith) hσ₀.le (by norm_num)
      linarith
    exact exists_matching H col hbip b (blk col κ b {SC.uF}) (blk col κ (!b) {SC.vF})
      (fun x hx => (mem_blk.1 hx).1) (fun x hx => (mem_blk.1 hx).1) (hfill b)
      (card_pos.1 (by have := hfpos b; omega))
      (((blk col κ b {SC.uF}).card : ℝ) / N₀ * D) (c₁' * (σ / 2)) (c₂' * (σ / 2))
      (mul_pos (div_pos (by linarith) hN0) hD) (mul_pos hc₂ hσ₀) hc2s
      (mul_pos hc₁'0 hσ₀).le (by rw [hc₁']; linarith) (hpair b).1
      (hasGap_mono _ (hpair b).2 (mul_le_mul_of_nonneg_right hc₂le hσ₀.le))
  obtain ⟨g₁, hg₁, hg₁w⟩ := hmatch true
  obtain ⟨g₂, hg₂, hg₂w⟩ := hmatch false
  have hdisjU : Disjoint (blk col κ true {SC.uF}) (blk col κ false {SC.uF}) :=
    disjoint_left.2 fun x h1 h2 => by
      rw [mem_blk] at h1 h2; rw [h1.1] at h2; simp at h2
  have hdisjV : Disjoint (blk col κ false {SC.vF}) (blk col κ true {SC.vF}) :=
    disjoint_left.2 fun x h1 h2 => by
      rw [mem_blk] at h1 h2; rw [h1.1] at h2; simp at h2
  refine ⟨fun u => if u ∈ blk col κ true {SC.uF} then g₁ u else g₂ u,
    bijOn_piecewise g₁ g₂ _ _ _ _ hg₁ hg₂ hdisjU hdisjV, fun u hu => ?_⟩
  rw [mem_union] at hu
  rcases hu with hu | hu
  · simp only [hu, ↓reduceIte]; exact hg₁w u hu
  · have : u ∉ blk col κ true {SC.uF} := disjoint_right.1 hdisjU hu
    simp only [this, ↓reduceIte]; exact hg₂w u hu

/-- Degree bounds from a degree event. -/
lemma dev_bounds (H : WGraph V) (col : V → Bool) (E : Finset V) (κ : V → SC) (N₀ k : ℕ)
    (D σ c t : ℝ) (hA : ∀ b, (classOf E col b).card = N₀)
    (hcls : ∀ v b, col v = !b → (1 - 2 * c * σ) * D ≤ H.degOn v (classOf E col b) ∧
      H.degOn v (classOf E col b) ≤ (1 + c * σ) * D)
    (b : Bool) (S : Finset SC) (hk : (blk col κ b S).card = k)
    (hdev : ∀ v, col v = !b → |H.degOn v (blk col κ b S) -
      ((blk col κ b S).card : ℝ) / (classOf E col b).card * H.degOn v (classOf E col b)| < t) :
    ∀ v, col v = !b → (k : ℝ) / N₀ * ((1 - 2 * c * σ) * D) - t < H.degOn v (blk col κ b S) ∧
      H.degOn v (blk col κ b S) < (k : ℝ) / N₀ * ((1 + c * σ) * D) + t := by
  intro v hv
  have h := hdev v hv
  rw [hk, hA b] at h
  exact dev_lo_hi h (by positivity) (hcls v b hv).1 (hcls v b hv).2

lemma degOn_cell_lower (H : WGraph V) (col : V → Bool) (hbip : H.IsBipartiteWith col)
    (E : Finset V) (κ : V → SC) (N₀ k : ℕ) (D σ c t : ℝ) (hA : ∀ b, (classOf E col b).card = N₀)
    (hcls : ∀ v b, col v = !b → (1 - 2 * c * σ) * D ≤ H.degOn v (classOf E col b) ∧
      H.degOn v (classOf E col b) ≤ (1 + c * σ) * D)
    (cc : Cell) (hk : ∀ b, (blk col κ b (cellSub cc)).card = k)
    (hdev : ∀ b, ∀ v, col v = !b → |H.degOn v (blk col κ b (cellSub cc)) -
      ((blk col κ b (cellSub cc)).card : ℝ) / (classOf E col b).card *
        H.degOn v (classOf E col b)| < t) (x : V) :
    (k : ℝ) / N₀ * ((1 - 2 * c * σ) * D) - t < H.degOn x (cellSet (labOf κ) cc) ∧
      H.degOn x (cellSet (labOf κ) cc) < (k : ℝ) / N₀ * ((1 + c * σ) * D) + t := by
  rw [degOn_cellSet H col hbip κ cc x]
  exact dev_bounds H col E κ N₀ k D σ c t hA hcls (!col x) (cellSub cc) (hk _) (hdev _) x
    (by simp)

lemma degOn_wide (H : WGraph V) (col : V → Bool) (hbip : H.IsBipartiteWith col)
    (E : Finset V) (κ : V → SC) (N₀ k : ℕ) (D σ c t : ℝ) (hA : ∀ b, (classOf E col b).card = N₀)
    (hcls : ∀ v b, col v = !b → (1 - 2 * c * σ) * D ≤ H.degOn v (classOf E col b) ∧
      H.degOn v (classOf E col b) ≤ (1 + c * σ) * D)
    (S : Finset SC) (hk : ∀ b, (blk col κ b S).card = k)
    (hdev : ∀ b, ∀ v, col v = !b → |H.degOn v (blk col κ b S) -
      ((blk col κ b S).card : ℝ) / (classOf E col b).card * H.degOn v (classOf E col b)| < t)
    (hP : (k : ℝ) / N₀ * ((1 + c * σ) * D) ≤ t) (v : V) (X : Finset V)
    (hX : ∀ x ∈ X, κ x ∈ S) : H.degOn v X ≤ t + t := by
  refine (degOn_le_blk H col hbip κ S v X hX).trans ?_
  have h := (dev_bounds H col E κ N₀ k D σ c t hA hcls (!col v) S (hk _) (hdev _) v
    (by simp)).2
  linarith

/-- **Assembly.** A sub-cell labeling with the prescribed sizes satisfying all the sampling
events, together with an orientation of `J`, yields the initial partition. -/
theorem build {εR c₇ C₇ εA cdfs δ κc K CF : ℝ} {c c₁' c₂ c₂' C₀ δ' tW tE : ℝ}
    (H : WGraph V) (col : V → Bool) (E : Finset V) (J : SimpleGraph V) (N₀ : ℕ) (D σ L g : ℝ)
    (s kC m a b' : ℕ) (κ : V → SC) (tail : V → Bool)
    (hbip : H.IsBipartiteWith col) (hwle : ∀ x y, H.w x y ≤ 1)
    (hA : ∀ b, (classOf E col b).card = N₀) (hN₀ : 1 ≤ N₀)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 10) (hD : 0 < D) (hDN : D ≤ 2 * N₀)
    (hc0 : 0 ≤ c) (hcσ : c * σ ≤ 1 / 64)
    (hcls : ∀ v b, col v = !b → (1 - 2 * c * σ) * D ≤ H.degOn v (classOf E col b) ∧
      H.degOn v (classOf E col b) ≤ (1 + c * σ) * D)
    (hEdeg : ∀ x, H.degOn x E ≤ c * σ ^ (5 / 2 : ℝ) * D / L)
    (hκE : ∀ x, κ x = SC.ends ↔ x ∈ E)
    (hsz : ∀ b c', c' ≠ SC.ends → (blk col κ b {c'}).card = szFun N₀ s kC m a b' b c')
    (htail : ∀ x y, J.Adj x y → tail x ≠ tail y)
    (hrole : ∀ r : Bool × Bool, (E.filter fun x => (col x, tail x) = r).card =
      (blk col κ r.1 {if r.2 then SC.uP else SC.vP}).card)
    (hpair : ∀ b (j : PB), (H.induce (blk col κ b j.c₁ ∪ blk col κ (!b) j.c₂)).DegNear
        (((blk col κ b j.c₁).card : ℝ) / N₀ * D) (c₁' * (σ / 2)) ∧
      (H.induce (blk col κ b j.c₁ ∪ blk col κ (!b) j.c₂)).HasGap (c₂ * (σ / 2)))
    (hdev : ∀ b (d : DB), ∀ v, col v = !b → |H.degOn v (blk col κ b d.cells) -
        ((blk col κ b d.cells).card : ℝ) / (classOf E col b).card *
          H.degOn v (classOf E col b)| <
        thrFun ((s : ℝ) / N₀ * D) ((kC : ℝ) / N₀ * D) (δ' * σ * ((m : ℝ) / N₀ * D) / 4) tW tE d)
    (hnorm : ∀ b (n : NB), ∀ v : V → ℝ, ∑ i ∈ classOf E col (!b), (∑ j ∈ blk col κ b n.cells,
        centred H (classOf E col b) (classOf E col (!b)) j i * v j) ^ 2 ≤
      (Real.sqrt (((blk col κ b n.cells).card : ℝ) / N₀) *
          ((1 - σ / 2) * ((1 + 2 * c * σ) * D)) +
        C₀ * Real.sqrt (24 * D) * Real.sqrt (6 * L)) ^ 2 * ∑ j ∈ blk col κ b n.cells, v j ^ 2)
    (hm : 8 ≤ m) (ha : 8 * a ≤ m) (hb : 8 * b' ≤ m) (hsize : 3 * s + kC + 9 * m ≤ N₀)
    (hs1 : 1 ≤ s)
    (hc₂ : 0 < c₂') (hc₂1 : c₂' ≤ 1) (hc₂le : c₂' ≤ c₂) (hc₁' : c₁' = c₂' / 40)
    (hcycDC : C₇ ≤ (kC : ℝ) / N₀ * D)
    (hgirth : C₇ * Real.log (2 * ((2 * kC : ℕ) : ℝ)) / Real.log (2 + (kC : ℝ) / N₀ * D) ≤ g)
    (hmany : (2 * m : ℝ) ≤ c₇ * ((2 * kC : ℕ) : ℝ) / g)
    (hrtrlog : Real.log (2 * ((2 * s : ℕ) : ℝ)) ≤ L)
    (hwideP : ((kC + 4 * m : ℕ) : ℝ) / N₀ * ((1 + c * σ) * D) ≤ tW)
    (hrtrsp : tW + tW ≤ εR * (c₂' * (σ / 2)) ^ (3 / 2 : ℝ) *
      ((1 + c₁' * (σ / 2)) * ((s : ℝ) / N₀ * D)) / L)
    (hattsp : c * σ ^ (5 / 2 : ℝ) * D / L + (tW + tW) ≤ εA * (c₂' * (σ / 2)) ^ (3 / 2 : ℝ) *
      ((1 + c₁' * (σ / 2)) * ((s : ℝ) / N₀ * D)) / L)
    (hdiv : (2 * m + 2 : ℝ) ≤ cdfs * (c₂' * (σ / 2)) * ((2 * s : ℕ) : ℝ))
    (hC₀ : 0 ≤ C₀)
    (hnormK : C₀ * Real.sqrt (24 * D) * Real.sqrt (6 * L) ≤ K * Real.sqrt (D * L))
    (hK : 18 + 2 * δ ≤ K) (hδ' : 0 < δ') (hδ'1 : δ' ≤ 1) (hδ'δ : δ' ≤ δ) (hcδ : 16 * c ≤ δ')
    (hlayer : CF * (σ / 2) ^ (-(2 : ℝ)) * L ≤ (m : ℝ) / N₀ * D)
    (henvP : ((3 * s + kC + 4 * m : ℕ) : ℝ) / N₀ * ((1 + c * σ) * D) ≤ tE)
    (henv : tE + tE ≤ κc * (σ / 2) * D)
    (henvc : ((3 * s + kC + 4 * m : ℕ) : ℝ) ≤ κc * (σ / 2) * N₀) :
    Nonempty (InitPartition εR c₇ C₇ εA cdfs δ κc K CF H col E J N₀ D σ L g) := by
  have hN0 : (0 : ℝ) < N₀ := by exact_mod_cast hN₀
  have hσ₀ : 0 < σ / 2 := by positivity
  have hs1' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hS₁pos : 0 < (s : ℝ) / N₀ * D := by positivity
  have hc₁'0 : 0 < c₁' := by rw [hc₁']; positivity
  obtain ⟨hc₁σ, hc2s⟩ := arith_small hc₂ hc₂1 hσ hσ1 hc₁'
  have ha1 : a + 1 ≤ m := by omega
  have hb1 : b' ≤ m := by omega
  have cDB := card_DB (col := col) (κ := κ) hsz ha1 hb1
  have cNB := card_NB (col := col) (κ := κ) hsz ha1 hb1
  have cPB₁ := card_PB₁ (col := col) (κ := κ) hsz
  have hcc : ∀ (d : DB) (cc : Cell), d.cells = cellSub cc → ∀ b,
      (blk col κ b (cellSub cc)).card = dbSize s kC m d := fun d cc h b => by
    rw [← h]; exact cDB b d
  obtain ⟨port, dA, dB, hportκ, hportinj, himg, huD, hdAcol, hvD, hdBcol⟩ :=
    build_ports col E κ tail hsz hrole
  have hfill : ∀ b, (blk col κ b {SC.uF}).card = (blk col κ (!b) {SC.vF}).card := fun b => by
    have h1 := card_PB₁ (col := col) (κ := κ) hsz b PB.fill
    have h2 := card_PB₂ (col := col) (κ := κ) hsz b PB.fill
    simp only [PB.c₁, PB.c₂] at h1 h2
    rw [h1, h2]
  have hfpos : ∀ b, 1 ≤ (blk col κ b {SC.uF}).card := fun b => by
    have h1 := card_PB₁ (col := col) (κ := κ) hsz b PB.fill
    simp only [PB.c₁] at h1
    rw [h1]; cases b <;> simp [pbSize] <;> omega
  obtain ⟨μ, hμbij, hμw⟩ := build_mu H col hbip κ N₀ D σ c₁' c₂ c₂' hN0 hD hσ (by linarith)
    hc₂ hc₂1 hc₂le hc₁' hfill hfpos (fun b => hpair b PB.fill)
  have hfilU := filler_lu col E κ port dA himg huD
  have hfilV := filler_lv col E κ port dB himg hvD
  -- the reservoirs
  have hres_pair : ∀ (j : PB) (cc : Cell), j.c₁ = cellSub cc → j.c₂ = cellSub cc →
      (∀ b, (blk col κ b j.c₁).card = s) →
      (H.induce (cellSet (labOf κ) cc)).DegNear ((s : ℝ) / N₀ * D) (c₁' * (σ / 2)) ∧
        (H.induce (cellSet (labOf κ) cc)).HasGap (c₂' * (σ / 2)) := by
    intro j cc h1 h2 hk
    have h := hpair true j
    rw [hk true, h1, h2, ← cellSet_eq_union col κ cc true] at h
    exact ⟨h.1, hasGap_mono _ h.2 (mul_le_mul_of_nonneg_right hc₂le hσ₀.le)⟩
  have hR₁ := hres_pair PB.att Cell.att rfl rfl (fun b => by rw [cPB₁]; cases b <;> rfl)
  have hQ := hres_pair PB.rtr Cell.rtr rfl rfl (fun b => by rw [cPB₁]; cases b <;> rfl)
  have hZ := hres_pair PB.div Cell.div rfl rfl (fun b => by rw [cPB₁]; cases b <;> rfl)
  have hDB2 : ∀ (S : Finset V), (H.induce S).DegNear ((s : ℝ) / N₀ * D) (c₁' * (σ / 2)) →
      (H.induce S).DegBetween (1 / 2 * ((1 + c₁' * (σ / 2)) * ((s : ℝ) / N₀ * D)))
        ((1 + c₁' * (σ / 2)) * ((s : ℝ) / N₀ * D)) := fun S h =>
    degBetween_of_near _ hS₁pos (by linarith) h
  have hcardC : ∀ cc : Cell, (cellSet (labOf κ) cc).card =
      (blk col κ true (cellSub cc)).card + (blk col κ false (cellSub cc)).card := fun cc => by
    rw [cellSet_eq_union col κ cc true]; exact card_blk_union col κ true _
  have hσQ : 0 < c₂' * (σ / 2) ∧ c₂' * (σ / 2) ≤ 1 := ⟨by positivity, hc2s⟩
  -- degree events of the individual blocks
  have hdA_att : ∀ b, ∀ v, col v = !b → |H.degOn v (blk col κ b (cellSub Cell.att)) -
      ((blk col κ b (cellSub Cell.att)).card : ℝ) / (classOf E col b).card *
        H.degOn v (classOf E col b)| < (s : ℝ) / N₀ * D / 4 := fun b => hdev b DB.att
  have hdA_rtr : ∀ b, ∀ v, col v = !b → |H.degOn v (blk col κ b (cellSub Cell.rtr)) -
      ((blk col κ b (cellSub Cell.rtr)).card : ℝ) / (classOf E col b).card *
        H.degOn v (classOf E col b)| < (s : ℝ) / N₀ * D / 4 := fun b => hdev b DB.rtr
  have hdA_cyc : ∀ b, ∀ v, col v = !b → |H.degOn v (blk col κ b (cellSub Cell.cyc)) -
      ((blk col κ b (cellSub Cell.cyc)).card : ℝ) / (classOf E col b).card *
        H.degOn v (classOf E col b)| < (kC : ℝ) / N₀ * D / 4 := fun b => hdev b DB.cyc
  have hdA_wide : ∀ b, ∀ v, col v = !b → |H.degOn v (blk col κ b DB.wide.cells) -
      ((blk col κ b DB.wide.cells).card : ℝ) / (classOf E col b).card *
        H.degOn v (classOf E col b)| < tW := fun b => hdev b DB.wide
  have hdA_env : ∀ b, ∀ v, col v = !b → |H.degOn v (blk col κ b DB.env.cells) -
      ((blk col κ b DB.env.cells).card : ℝ) / (classOf E col b).card *
        H.degOn v (classOf E col b)| < tE := fun b => hdev b DB.env
  have hres_lo : ∀ cc : Cell, (∀ b, (blk col κ b (cellSub cc)).card = s) →
      (∀ b, ∀ v, col v = !b → |H.degOn v (blk col κ b (cellSub cc)) -
        ((blk col κ b (cellSub cc)).card : ℝ) / (classOf E col b).card *
          H.degOn v (classOf E col b)| < (s : ℝ) / N₀ * D / 4) → ∀ x,
      1 / 4 * ((1 + c₁' * (σ / 2)) * ((s : ℝ) / N₀ * D)) ≤
        H.degOn x (cellSet (labOf κ) cc) := by
    intro cc hk hdv x
    have h := (degOn_cell_lower H col hbip E κ N₀ s D σ c ((s : ℝ) / N₀ * D / 4) hA hcls cc hk
      hdv x).1
    exact arith_res rfl hS₁pos hcσ hc₁σ h
  have hwide : ∀ v (X : Finset V), (∀ x ∈ X, κ x ∈ DB.wide.cells) → H.degOn v X ≤ tW + tW :=
    fun v X hX => degOn_wide H col hbip E κ N₀ (kC + 4 * m) D σ c tW hA hcls DB.wide.cells
      (fun b => cDB b DB.wide) hdA_wide hwideP v X hX
  have hcyc : (H.induce (cellSet (labOf κ) Cell.cyc)).DegBetween
      (1 / 2 * ((kC : ℝ) / N₀ * D)) (2 * ((kC : ℝ) / N₀ * D)) := by
    intro x
    have hdeg : (H.induce (cellSet (labOf κ) Cell.cyc)).deg x =
        H.degOn x (cellSet (labOf κ) Cell.cyc) :=
      sum_coe_sort (cellSet (labOf κ) Cell.cyc) (fun y => H.w x y)
    rw [hdeg]
    have h := degOn_cell_lower H col hbip E κ N₀ kC D σ c ((kC : ℝ) / N₀ * D / 4) hA hcls
      Cell.cyc (hcc DB.cyc Cell.cyc rfl) hdA_cyc x
    exact arith_cyc rfl (by positivity) hcσ h
  have hattsp' : ∀ v, H.degOn v (E ∪ E.image port) ≤ εA * (c₂' * (σ / 2)) ^ (3 / 2 : ℝ) *
      ((1 + c₁' * (σ / 2)) * ((s : ℝ) / N₀ * D)) / L := by
    intro v
    have h1 : H.degOn v (E ∪ E.image port) ≤ H.degOn v E + H.degOn v (E.image port) := by
      unfold WGraph.degOn
      rw [← sum_union_inter]
      have : 0 ≤ ∑ x ∈ E ∩ E.image port, H.w v x := sum_nonneg fun x _ => H.nonneg v x
      linarith
    have h2 := hwide v (E.image port) (fun z hz => by
      rcases (himg z).1 hz with h | h <;> simp [h, DB.cells])
    have h3 := hEdeg v
    linarith
  have hrtrsp' : ∀ v, H.degOn v (cellSet (labOf κ) Cell.cyc ∪ cellSet (labOf κ) Cell.inp ∪
      cellSet (labOf κ) Cell.out) ≤ εR * (c₂' * (σ / 2)) ^ (3 / 2 : ℝ) *
        ((1 + c₁' * (σ / 2)) * ((s : ℝ) / N₀ * D)) / L := by
    intro v
    refine (hwide v _ fun x hx => ?_).trans hrtrsp
    simp only [mem_union, mem_cellSet, labOf, toCell_eq_iff] at hx
    rcases hx with (hx | hx) | hx <;> simp only [cellSub, mem_singleton] at hx <;>
      simp [hx, DB.cells]
  have henvdeg : ∀ v, H.degOn v (envelope (labOf κ)) ≤ κc * (σ / 2) * D := by
    intro v
    rw [degOn_filter_opp H col hbip v, envelope_filter]
    have h := (dev_bounds H col E κ N₀ (dbSize s kC m DB.env) D σ c tE hA hcls (!col v)
      DB.env.cells (cDB _ DB.env) (hdA_env _) v (by simp)).2
    have h2 : ((dbSize s kC m DB.env : ℕ) : ℝ) / N₀ * ((1 + c * σ) * D) ≤ tE := henvP
    linarith
  have hsided : ∀ cc b, (cc = Cell.inp ∨ cc = Cell.out ∨ cc = Cell.lu ∨ cc = Cell.lv) →
      OneSided H (classOf E col b) (classOf E col (!b))
        ((cellSet (labOf κ) cc).filter fun x => col x = b)
        ((m : ℝ) / N₀) D (σ / 2) L K δ := by
    intro cc b hcc
    rw [cellSet_filter_col]
    have hkey : ∀ (n : NB) (d : DB), n.cells = cellSub cc → d.cells = cellSub cc →
        thrFun ((s : ℝ) / N₀ * D) ((kC : ℝ) / N₀ * D) (δ' * σ * ((m : ℝ) / N₀ * D) / 4) tW tE d
          = δ' * σ * ((m : ℝ) / N₀ * D) / 4 →
        OneSided H (classOf E col b) (classOf E col (!b)) (blk col κ b (cellSub cc))
          ((m : ℝ) / N₀) D (σ / 2) L K δ := by
      intro n d hn hd ht
      have hk : (blk col κ b (cellSub cc)).card = m := by rw [← hn]; exact cNB b n
      refine oneSided_of H col E b N₀ m D σ L K δ c C₀ δ' _
        (blk_subset_classOf hκE b (by rcases hcc with rfl | rfl | rfl | rfl <;> decide)) hk
        hwle hA hN0 hD hDN hσ (by linarith) hc0 hcσ hcls ?_ ?_ hC₀ hnormK hK hδ' hδ'δ hcδ hδ'1
      · intro v
        have h := hnorm b n v
        rw [hn, hk] at h
        exact h
      · intro v hv
        have h := hdev b d v hv
        rw [hd, hk, hA b, ht] at h
        exact h
    rcases hcc with rfl | rfl | rfl | rfl
    · exact hkey NB.inp DB.inp rfl rfl rfl
    · exact hkey NB.out DB.out rfl rfl rfl
    · exact hkey NB.lu DB.lu rfl rfl rfl
    · exact hkey NB.lv DB.lv rfl rfl rfl
  refine ⟨{
    lab := labOf κ
    m := m
    tail := tail
    port := port
    dA := dA
    dB := dB
    μ := μ
    DC := (kC : ℝ) / N₀ * D
    ΔQ := (1 + c₁' * (σ / 2)) * ((s : ℝ) / N₀ * D)
    σQ := c₂' * (σ / 2)
    Δ₁ := (1 + c₁' * (σ / 2)) * ((s : ℝ) / N₀ * D)
    σ₁ := c₂' * (σ / 2)
    DZ := (s : ℝ) / N₀ * D
    σZ := c₂' * (σ / 2)
    lab_ends := fun x => by
      rw [← hκE x]; simp only [labOf]; cases κ x <;> simp [SC.toCell]
    one_le_m := by omega
    block_card := fun cc b hcc => by
      rw [cellSet_filter_col]
      rcases hcc with rfl | rfl | rfl | rfl
      · exact cNB b NB.inp
      · exact cNB b NB.out
      · exact cNB b NB.lu
      · exact cNB b NB.lv
    cyc_deg := hcyc
    cyc_DC := hcycDC
    cyc_girth := by
      rw [hcardC, hcc DB.cyc Cell.cyc rfl, hcc DB.cyc Cell.cyc rfl, ← two_mul]
      exact hgirth
    cyc_many := by
      rw [hcardC, hcc DB.cyc Cell.cyc rfl, hcc DB.cyc Cell.cyc rfl, ← two_mul]
      exact hmany
    rtr_pos := by positivity
    rtr_deg := hDB2 _ hQ.1
    rtr_gap := hQ.2
    rtr_σ := hσQ
    rtr_log := by
      rw [hcardC, hcc DB.rtr Cell.rtr rfl, hcc DB.rtr Cell.rtr rfl, ← two_mul]
      exact hrtrlog
    rtr_ends := fun x _ => hres_lo Cell.rtr (hcc DB.rtr Cell.rtr rfl) hdA_rtr x
    rtr_sparse := fun v _ => hrtrsp' v
    att_pos := by positivity
    att_deg := hDB2 _ hR₁.1
    att_gap := hR₁.2
    att_σ := hσQ
    att_log := by
      rw [hcardC, hcc DB.att Cell.att rfl, hcc DB.att Cell.att rfl, ← two_mul]
      exact hrtrlog
    att_ends := fun x _ => hres_lo Cell.att (hcc DB.att Cell.att rfl) hdA_att x
    att_sparse := fun v _ => hattsp' v
    tail_adj := htail
    port_col := fun x hx => (hportκ x hx).1
    port_inj := hportinj
    port_tail := fun x hx ht => by
      have h := hportκ x hx
      simp only [ht, ↓reduceIte] at h
      refine ⟨by simp [labOf, h.2, SC.toCell], fun he => ?_⟩
      have := (huD (port x)).2 he
      rw [h.2] at this
      exact absurd this (by decide)
    port_head := fun x hx ht => by
      have h := hportκ x hx
      simp only [ht, Bool.false_eq_true, ↓reduceIte] at h
      refine ⟨by simp [labOf, h.2, SC.toCell], fun he => ?_⟩
      have := (hvD (port x)).2 he
      rw [h.2] at this
      exact absurd this (by decide)
    dA_lab := by simp [labOf, (huD dA).2 rfl, SC.toCell]
    dA_col := hdAcol
    dB_lab := by simp [labOf, (hvD dB).2 rfl, SC.toCell]
    dB_col := hdBcol
    μ_bij := by rw [hfilU, hfilV]; exact hμbij
    μ_adj := fun u hu => by rw [hfilU] at hu; exact hμw u hu
    div_pos := hS₁pos
    div_deg := degBetween_of_near' _ hS₁pos (by linarith) hZ.1
    div_gap := hZ.2
    div_σ := hσQ
    div_long := by
      have hdv : ∀ b, (blk col κ b (cellSub Cell.div)).card = s := fun b => by
        rw [show cellSub Cell.div = {SC.div} from rfl, hsz b _ (by decide)]
        cases b <;> rfl
      rw [hcardC, hdv, hdv, ← two_mul]
      exact hdiv
    one_sided := hsided
    layer_large := hlayer
    env_deg := henvdeg
    env_card := fun b => by
      rw [envelope_filter, cDB b DB.env]
      exact henvc
    pool_large := fun b => by
      rw [cellSet_filter_col]
      have : (blk col κ b (cellSub Cell.pool)).card = N₀ - (3 * s + kC + 4 * m) := by
        rw [show cellSub Cell.pool = {SC.pool} from rfl, hsz b _ (by decide)]
        cases b <;> rfl
      rw [this]
      omega }⟩

/-! ### The good permutation -/

open Classical in
/-- **The union bound**: a permutation of the base labeling for which all the events hold. -/
lemma exists_good_perm {ω c₂ c₁' cb Cb C₀ : ℝ} (hbs : BSProp.{u} ω c₂ 4 c₁' cb Cb)
    (hC₀ : BipSampling.ColSampProp C₀)
    (H : WGraph V) (col : V → Bool) (E : Finset V) (N N₀ : ℕ) (D σ L c : ℝ) (thr : DB → ℝ)
    (κ₀ : V → SC) (hκ₀ : ∀ x, κ₀ x = SC.ends ↔ x ∈ E)
    (hbip : H.IsBipartiteWith col) (hw : H.WeightsIn ω) (hwle : ∀ x y, H.w x y ≤ 1)
    (hA : ∀ b, (classOf E col b).card = N₀) (hN₀ : 1 ≤ N₀) (hNN : N₀ ≤ N)
    (hcolN : ∀ b, (univ.filter fun v => col v = b).card = N)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hD : 0 < D) (hDN : D ≤ 2 * N₀) (hc0 : 0 ≤ c)
    (hcσ : c * σ ≤ 1 / 64) (hL : 10 ≤ L) (hlogL : Real.log (2 * N) ≤ L)
    (hcls : ∀ v b, col v = !b → (1 - 2 * c * σ) * D ≤ H.degOn v (classOf E col b) ∧
      H.degOn v (classOf E col b) ≤ (1 + c * σ) * D)
    (hgap₀ : (H.induce (univ \ E)).HasGap (σ / 2))
    (hdeg₀ : (H.induce (univ \ E)).DegNear D (2 * c * σ)) (hcb : 2 * c * σ ≤ cb * (σ / 2))
    (hpairC : ∀ b (j : PB), (blk col κ₀ b j.c₁).card = (blk col κ₀ (!b) j.c₂).card ∧
      Cb * (σ / 2) ^ (-2 : ℝ) * L ≤ ((blk col κ₀ b j.c₁).card : ℝ) / N₀ * D)
    (hthr : ∀ b (d : DB), 0 < thr d ∧ 12 * L * (((blk col κ₀ b d.cells).card : ℝ) / N₀ *
      ((1 + c * σ) * D) + thr d) ≤ thr d ^ 2) :
    ∃ π ∈ permG col E,
      (∀ b (j : PB), (H.induce (blk col (fun x => κ₀ (π⁻¹ x)) b j.c₁ ∪
          blk col (fun x => κ₀ (π⁻¹ x)) (!b) j.c₂)).DegNear
          (((blk col (fun x => κ₀ (π⁻¹ x)) b j.c₁).card : ℝ) / N₀ * D) (c₁' * (σ / 2)) ∧
        (H.induce (blk col (fun x => κ₀ (π⁻¹ x)) b j.c₁ ∪
          blk col (fun x => κ₀ (π⁻¹ x)) (!b) j.c₂)).HasGap (c₂ * (σ / 2))) ∧
      (∀ b (d : DB), ∀ v, col v = !b →
        |H.degOn v (blk col (fun x => κ₀ (π⁻¹ x)) b d.cells) -
          ((blk col (fun x => κ₀ (π⁻¹ x)) b d.cells).card : ℝ) / (classOf E col b).card *
            H.degOn v (classOf E col b)| < thr d) ∧
      (∀ b (n : NB), ∀ v : V → ℝ, ∑ i ∈ classOf E col (!b),
        (∑ j ∈ blk col (fun x => κ₀ (π⁻¹ x)) b n.cells,
          centred H (classOf E col b) (classOf E col (!b)) j i * v j) ^ 2 ≤
        (Real.sqrt (((blk col (fun x => κ₀ (π⁻¹ x)) b n.cells).card : ℝ) / N₀) *
            ((1 - σ / 2) * ((1 + 2 * c * σ) * D)) +
          C₀ * Real.sqrt (24 * D) * Real.sqrt (6 * L)) ^ 2 *
          ∑ j ∈ blk col (fun x => κ₀ (π⁻¹ x)) b n.cells, v j ^ 2) := by
  set G := permG col E with hG
  have hN0 : (0 : ℝ) < N₀ := by exact_mod_cast hN₀
  have hN1 : 1 ≤ N := le_trans hN₀ hNN
  obtain ⟨tl1, tl2, tl3⟩ := num_tail N N₀ L hL hlogL hN1 hNN
  have hlog₀ : Real.log (2 * N₀) ≤ L := by
    refine le_trans (Real.log_le_log (by positivity) ?_) hlogL
    have : (N₀ : ℝ) ≤ N := by exact_mod_cast hNN
    linarith
  have hS : ∀ b (S : Finset SC), SC.ends ∉ S → blk col κ₀ b S ⊆ classOf E col b :=
    fun b S h => blk_subset_classOf hκ₀ b h
  -- the spectral facts
  set M := (1 - σ / 2) * ((1 + 2 * c * σ) * D) with hM
  have hM0 : 0 ≤ M := mul_nonneg (by linarith) (mul_nonneg (by positivity) hD.le)
  have hΔ : ∀ x, x ∉ E → H.degOn x (univ \ E) ≤ (1 + 2 * c * σ) * D := by
    intro x _
    rw [degOn_sdiff_eq H col E hbip (col x) rfl]
    have := (hcls x (!col x) (by simp)).2
    nlinarith [mul_pos hσ hD]
  have hepos : ∀ b, 0 < H.edgeWeight (classOf E col b) (classOf E col (!b)) := by
    intro b
    have h1 : ∀ l ∈ classOf E col b, (1 - 2 * c * σ) * D ≤ H.degOn l (classOf E col (!b)) :=
      fun l hl => (cls_deg_bounds H col E D σ c hc0 hσ hcls b hD l hl).1
    have h2 := sum_le_sum h1
    rw [sum_const, hA b, nsmul_eq_mul] at h2
    have h3 : 0 < (N₀ : ℝ) * ((1 - 2 * c * σ) * D) :=
      mul_pos hN0 (mul_pos (by nlinarith) hD)
    exact lt_of_lt_of_le h3 h2
  have hop : ∀ b (v : V → ℝ), ∑ i ∈ classOf E col (!b), (∑ j ∈ classOf E col b,
      centred H (classOf E col b) (classOf E col (!b)) j i * v j) ^ 2 ≤
        M ^ 2 * ∑ j ∈ classOf E col b, v j ^ 2 := fun b v =>
    BipSampling.op_of_bil' (classOf E col b) (classOf E col (!b))
      (centred H (classOf E col b) (classOf E col (!b))) M hM0
      (fun x y => spectral_V H col E b hbip (σ / 2) ((1 + 2 * c * σ) * D) hgap₀ (by positivity)
        (by linarith) hΔ (hepos b) x y) v
  have hrow : ∀ b, ∀ j ∈ classOf E col b, ∑ i ∈ classOf E col (!b),
      centred H (classOf E col b) (classOf E col (!b)) j i ^ 2 ≤ Real.sqrt (24 * D) ^ 2 := by
    intro b j hj
    rw [Real.sq_sqrt (by positivity)]
    have hent : ∀ i ∈ classOf E col (!b),
        centred H (classOf E col b) (classOf E col (!b)) j i ^ 2 ≤
          2 * H.w j i + 16 * D / N₀ := fun i hi =>
      centred_sq_le H col E b N₀ D (2 * c * σ) hwle (hA b) hN0 hD hDN (by positivity)
        (by nlinarith) (cls_deg_bounds H col E D σ c hc0 hσ hcls b hD)
        (fun y' hy' => by
          have h := hcls y' b (mem_classOf.1 hy').2
          exact ⟨h.1, h.2.trans (by nlinarith [mul_pos hσ hD])⟩) hj hi
    have h1 := sum_le_sum hent
    rw [sum_add_distrib, ← mul_sum, sum_const, hA, nsmul_eq_mul] at h1
    have h2 := (cls_deg_bounds H col E D σ c hc0 hσ hcls b hD j hj).2
    have h3 : (N₀ : ℝ) * (16 * D / N₀) = 16 * D := by field_simp
    have h4 : ∑ i ∈ classOf E col (!b), H.w j i = H.degOn j (classOf E col (!b)) := rfl
    nlinarith
  -- the events
  let P : EvIdx → Equiv.Perm V → Prop := fun i π => match i with
    | (b, Sum.inl j) =>
        (H.induce ((blk col κ₀ b j.c₁).image π ∪ (blk col κ₀ (!b) j.c₂).image π)).DegNear
          (((blk col κ₀ b j.c₁).card : ℝ) / N₀ * D) (c₁' * (σ / 2)) ∧
        (H.induce ((blk col κ₀ b j.c₁).image π ∪ (blk col κ₀ (!b) j.c₂).image π)).HasGap
          (c₂ * (σ / 2))
    | (b, Sum.inr (Sum.inl d)) => ∀ v, col v = !b →
        |H.degOn v ((blk col κ₀ b d.cells).image π) -
          ((blk col κ₀ b d.cells).card : ℝ) / (classOf E col b).card *
            H.degOn v (classOf E col b)| < thr d
    | (b, Sum.inr (Sum.inr n)) => ∀ v : V → ℝ, ∑ i ∈ classOf E col (!b),
        (∑ j ∈ (blk col κ₀ b n.cells).image π,
          centred H (classOf E col b) (classOf E col (!b)) j i * v j) ^ 2 ≤
        (Real.sqrt (((blk col κ₀ b n.cells).card : ℝ) / N₀) * M +
          C₀ * Real.sqrt (24 * D) * Real.sqrt (6 * L)) ^ 2 *
          ∑ j ∈ (blk col κ₀ b n.cells).image π, v j ^ 2
  let B : EvIdx → Finset (Equiv.Perm V) := fun i => match i with
    | (b, Sum.inl j) => (permG col E).filter fun π : Equiv.Perm V =>
        ¬ ((H.induce ((blk col κ₀ b j.c₁).image π ∪ (blk col κ₀ (!b) j.c₂).image π)).DegNear
          (((blk col κ₀ b j.c₁).card : ℝ) / N₀ * D) (c₁' * (σ / 2)) ∧
          (H.induce ((blk col κ₀ b j.c₁).image π ∪ (blk col κ₀ (!b) j.c₂).image π)).HasGap
            (c₂ * (σ / 2)))
    | (b, Sum.inr (Sum.inl d)) => (permG col E).filter fun π : Equiv.Perm V => ∃ v, col v = !b ∧
        thr d ≤ |H.degOn v ((blk col κ₀ b d.cells).image π) -
          ((blk col κ₀ b d.cells).card : ℝ) / (classOf E col b).card *
            H.degOn v (classOf E col b)|
    | (b, Sum.inr (Sum.inr n)) => (permG col E).filter fun π : Equiv.Perm V => ∃ v : V → ℝ,
        (Real.sqrt (((blk col κ₀ b n.cells).card : ℝ) / N₀) * M +
          C₀ * Real.sqrt (24 * D) * Real.sqrt (6 * L)) ^ 2 *
            ∑ j ∈ (blk col κ₀ b n.cells).image π, v j ^ 2 <
          ∑ i ∈ classOf E col (!b), (∑ j ∈ (blk col κ₀ b n.cells).image π,
            centred H (classOf E col b) (classOf E col (!b)) j i * v j) ^ 2
  have hB : ∀ i, ∀ π ∈ G, ¬ P i π → π ∈ B i := by
    rintro ⟨b, j | d | n⟩ π hπ hn
    · exact mem_filter.2 ⟨hπ, hn⟩
    · refine mem_filter.2 ⟨hπ, ?_⟩
      have h2 : ¬ ∀ v, col v = !b → |H.degOn v ((blk col κ₀ b d.cells).image π) -
          ((blk col κ₀ b d.cells).card : ℝ) / (classOf E col b).card *
            H.degOn v (classOf E col b)| < thr d := hn
      push Not at h2
      exact h2
    · refine mem_filter.2 ⟨hπ, ?_⟩
      have h2 : ¬ ∀ v : V → ℝ, ∑ i ∈ classOf E col (!b),
          (∑ j ∈ (blk col κ₀ b n.cells).image π,
            centred H (classOf E col b) (classOf E col (!b)) j i * v j) ^ 2 ≤
          (Real.sqrt (((blk col κ₀ b n.cells).card : ℝ) / N₀) * M +
            C₀ * Real.sqrt (24 * D) * Real.sqrt (6 * L)) ^ 2 *
            ∑ j ∈ (blk col κ₀ b n.cells).image π, v j ^ 2 := hn
      push Not at h2
      exact h2
  have hcount : ∀ i, ((B i).card : ℝ) ≤ Real.exp (-(4 * L)) * G.card := by
    rintro ⟨b, j | d | n⟩
    · exact ev_pair hbs H col E b N₀ (2 * c * σ) D (σ / 2) L hbip hw (hA b) (hA (!b)) hdeg₀
        hgap₀ (by positivity) (by linarith) hcb hlog₀ (blk col κ₀ b j.c₁) (blk col κ₀ (!b) j.c₂)
        (hS b _ (by cases j <;> decide)) (hS (!b) _ (by cases j <;> decide)) (hpairC b j).1
        (hpairC b j).2
    · have h := ev_dev H col E b hwle (blk col κ₀ b d.cells) (hS b _ (by cases d <;> decide))
        (((blk col κ₀ b d.cells).card : ℝ) / N₀ * ((1 + c * σ) * D)) (thr d) (6 * L)
        (fun v hv => by
          rw [hA b]
          exact mul_le_mul_of_nonneg_left (hcls v b hv).2 (by positivity))
        (hthr b d).1 (by linarith) (by have := (hthr b d).2; linarith)
      rw [hcolN] at h
      exact h.trans (mul_le_mul_of_nonneg_right tl1 (Nat.cast_nonneg _))
    · have h := ev_norm hC₀ H col E b N₀ (hA b) (hA (!b)) (blk col κ₀ b n.cells)
        (hS b _ (by cases n <;> decide)) M (Real.sqrt (24 * D)) (6 * L) hM0 (Real.sqrt_nonneg _)
        (by linarith) (hop b) (hrow b)
      exact h.trans (mul_le_mul_of_nonneg_right tl2 (Nat.cast_nonneg _))
  obtain ⟨π, hπ, hgood⟩ := exists_forall_of_count G ⟨1, one_mem_permG col E⟩ P
    (Real.exp (-(4 * L))) B hB hcount (by rw [card_EvIdx]; push_cast; linarith)
  have hbp : ∀ b S, blk col (fun x => κ₀ (π⁻¹ x)) b S = (blk col κ₀ b S).image π :=
    fun b S => blk_perm hπ κ₀ b S
  have hcp : ∀ b S, (blk col (fun x => κ₀ (π⁻¹ x)) b S).card = (blk col κ₀ b S).card :=
    fun b S => by rw [hbp]; exact card_image_of_injective _ π.injective
  refine ⟨π, hπ, fun b j => ?_, fun b d v hv => ?_, fun b n v => ?_⟩
  · have h1 := hgood (b, Sum.inl j)
    rw [hcp, hbp, hbp]
    exact h1
  · have h1 := hgood (b, Sum.inr (Sum.inl d)) v hv
    rw [hcp, hbp]
    exact h1
  · have h1 := hgood (b, Sum.inr (Sum.inr n)) v
    rw [hcp, hbp]
    exact h1

/-! ### Orientation of `J` -/

omit [DecidableEq V] in
/-- An orientation of the perfect matching `J` of `E`; the positive heads are as many as the
negative tails, and the negative heads as many as the positive tails. -/
lemma exists_orientation (col : V → Bool) (E : Finset V) (J : SimpleGraph V)
    (hJ : IsPerfectMatchingOn J ↑E) (ℓ : ℕ)
    (hℓt : (E.filter fun x => col x = true).card = ℓ)
    (hℓf : (E.filter fun x => col x = false).card = ℓ) :
    ∃ tail : V → Bool, (∀ x y, J.Adj x y → tail x ≠ tail y) ∧
      (E.filter fun x => (col x, tail x) = (true, false)).card =
        (E.filter fun x => (col x, tail x) = (false, true)).card ∧
      (E.filter fun x => (col x, tail x) = (false, false)).card =
        (E.filter fun x => (col x, tail x) = (true, true)).card ∧
      (E.filter fun x => (col x, tail x) = (true, true)).card ≤ ℓ ∧
      (E.filter fun x => (col x, tail x) = (false, true)).card ≤ ℓ := by
  classical
  set e := Fintype.equivFin V
  set p : V → V := fun x => if h : ∃ y, J.Adj x y then h.choose else x with hp
  have hpadj : ∀ x ∈ E, J.Adj x (p x) := fun x hx => by
    have h := (hJ.2 x (Finset.mem_coe.2 hx)).exists
    simp only [hp, h, ↓reduceDIte]
    exact h.choose_spec
  have huniq : ∀ x y, J.Adj x y → p x = y := fun x y h => by
    have hx := Finset.mem_coe.1 (hJ.1 x y h).1
    exact (hJ.2 x (Finset.mem_coe.2 hx)).unique (hpadj x hx) h
  have hpE : ∀ x ∈ E, p x ∈ E := fun x hx => Finset.mem_coe.1 (hJ.1 x _ (hpadj x hx)).2
  have hpp : ∀ x ∈ E, p (p x) = x := fun x hx => huniq _ _ (hpadj x hx).symm
  set tail : V → Bool := fun x => decide (e x < e (p x)) with htail
  have hta : ∀ x y, J.Adj x y → tail x ≠ tail y := by
    intro x y h
    have h1 : p x = y := huniq x y h
    have h2 : p y = x := huniq y x h.symm
    have hne : e x ≠ e y := fun h' => J.ne_of_adj h (e.injective h')
    simp only [htail, h1, h2]
    rcases lt_or_gt_of_ne hne with h3 | h3
    · simp [h3, not_lt.2 h3.le]
    · simp [h3, not_lt.2 h3.le]
  have htp : ∀ x ∈ E, tail (p x) = !tail x := by
    intro x hx
    have h := hta x (p x) (hpadj x hx)
    revert h
    cases tail x <;> cases tail (p x) <;> simp
  -- tails and heads are in bijection
  have hTH : (E.filter fun x => tail x = true).card = (E.filter fun x => tail x = false).card := by
    refine card_nbij' p p ?_ ?_ ?_ ?_
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨hpE x hx.1, by rw [htp x hx.1, hx.2]; rfl⟩
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨hpE x hx.1, by rw [htp x hx.1, hx.2]; rfl⟩
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx
      exact hpp x hx.1
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx
      exact hpp x hx.1
  have hsplit : ∀ (P Q : V → Prop) [DecidablePred P] [DecidablePred Q],
      (E.filter P).card = ((E.filter P).filter Q).card + ((E.filter P).filter fun x => ¬ Q x).card :=
    fun P Q _ _ => (card_filter_add_card_filter_not _).symm
  have hrw : ∀ c t, (E.filter fun x => (col x, tail x) = (c, t)) =
      (E.filter fun x => col x = c).filter fun x => tail x = t := by
    intro c t
    rw [filter_filter]
    exact filter_congr fun x _ => by simp [Prod.ext_iff]
  have hrw' : ∀ c t, (E.filter fun x => (col x, tail x) = (c, t)) =
      (E.filter fun x => tail x = t).filter fun x => col x = c := by
    intro c t
    rw [filter_filter]
    exact filter_congr fun x _ => by simp [Prod.ext_iff, and_comm]
  have hb1 : ∀ c, (E.filter fun x => col x = c).card =
      (E.filter fun x => (col x, tail x) = (c, true)).card +
        (E.filter fun x => (col x, tail x) = (c, false)).card := by
    intro c
    rw [hrw, hrw, hsplit (fun x => col x = c) (fun x => tail x = true)]
    congr 2
  have hb2 : ∀ t, (E.filter fun x => tail x = t).card =
      (E.filter fun x => (col x, tail x) = (true, t)).card +
        (E.filter fun x => (col x, tail x) = (false, t)).card := by
    intro t
    rw [hrw', hrw', hsplit (fun x => tail x = t) (fun x => col x = true)]
    congr 2
  have e1 := hb1 true
  have e2 := hb1 false
  have e3 := hb2 true
  have e4 := hb2 false
  refine ⟨tail, hta, by omega, by omega, by omega, by omega⟩

/-! ### Numerics -/

/-- The numerical setting of the proof: the parameters of Theorem 3.2, the chosen constants,
and the sizes `s = |R₁ ∩ A|`, `kC = |C ∩ A|`, `m = w / 2` (`X = σ^{5/2}`). -/
structure NumCtx (εR c₇ C₇ εA cdfs κc CF Cb c₂' c₀ ρ c₃ c₁ c C δ' : ℝ)
    (σ X L g D N ℓ : ℝ) (N₀ s kC m : ℕ) : Prop where
  hσ : 0 < σ
  hσ1 : σ ≤ 1 / 10
  hX : 0 < X
  hXσ : X ≤ σ ^ 2
  hX32 : σ ^ (3 / 2 : ℝ) * σ = X
  hL : 10 ≤ L
  hg : 4 ≤ g
  hD : 0 < D
  hDN : D ≤ 2 * N₀
  hN₀ : 1 ≤ N₀
  hNN : (N₀ : ℝ) ≤ N
  hN2 : N ≤ 2 * N₀
  hℓ0 : 0 ≤ ℓ
  hdl : C * L ^ 2 * g ≤ D * X * σ ^ 2
  hgirth : C * L / Real.log (2 + X * D / L) ≤ g
  hℓ : ℓ ≤ c * X * N / (L * g)
  hlogN : Real.log (2 * N) ≤ L
  hs : s = ⌊c₀ * σ * N₀⌋₊
  hkC : kC = ⌊c₃ * X * N₀ / L⌋₊
  hm : m = ⌊c₁ * X * N₀ / (L * g)⌋₊
  hc₂' : 0 < c₂'
  hc₂'1 : c₂' ≤ 1
  hδ' : 0 < δ'
  hδ'1 : δ' ≤ 1
  hc₀ : 0 < c₀
  hc₀1 : c₀ ≤ 1 / 40
  hc₀κ : 48 * c₀ ≤ κc
  hρ : 0 < ρ
  hρc₀ : ρ ≤ c₀
  hρR : ρ ≤ εR * (c₂' / 2) ^ (3 / 2 : ℝ) * c₀ / 2
  hρA : ρ ≤ εA * (c₂' / 2) ^ (3 / 2 : ℝ) * c₀ / 2
  hc₃ : c₃ = ρ / 16
  hc₁ : 0 < c₁
  hc₁ρ : 16 * c₁ ≤ ρ
  hc₁7 : 2 * c₁ ≤ c₇ * c₃
  hc₁d : 4 * c₁ ≤ cdfs * c₂' * c₀
  hc : 0 < c
  hcδ : 16 * c ≤ δ'
  hcρ : 2 * c ≤ ρ
  hc₁c : 64 * c ≤ c₁
  hC₇ : 0 < C₇
  hεR : 0 < εR
  hεA : 0 < εA
  hc₇ : 0 < c₇
  hcdfs : 0 < cdfs
  hC1 : 8 * Cb ≤ c₀ * C
  hC2 : 16 * Cb ≤ c₁ * C
  hC3 : 8 * CF ≤ c₁ * C
  hC4 : 500 ≤ δ' ^ 2 * c₁ * C
  hC5 : 2 ≤ c₃ * C
  hC6 : 1 ≤ ρ * C
  hC7 : 1 ≤ κc * C
  hC8 : 1 ≤ c₀ * C
  hC9 : C₇ ≤ c₃ * C
  hC10 : C₇ * (1 + 4 / c₃) ≤ C
  hC11 : 16 ≤ c₁ * C
  hC : 0 < C

omit [Fintype V] [DecidableEq V] in
lemma floor_half {z : ℝ} (hz : 2 ≤ z) : z / 2 ≤ (⌊z⌋₊ : ℝ) ∧ (⌊z⌋₊ : ℝ) ≤ z :=
  ⟨by have := Nat.lt_floor_add_one z; linarith, Nat.floor_le (by linarith)⟩

omit [Fintype V] [DecidableEq V] in
lemma rpow_neg_two' {x : ℝ} (hx : 0 < x) : x ^ (-(2 : ℝ)) = 1 / x ^ 2 := by
  rw [Real.rpow_neg hx.le, Real.rpow_two, one_div]

section Num

variable {εR c₇ C₇ εA cdfs κc CF Cb c₂' c₀ ρ c₃ c₁ c C δ' σ X L g D N ℓ : ℝ} {N₀ s kC m : ℕ}
  (h : NumCtx εR c₇ C₇ εA cdfs κc CF Cb c₂' c₀ ρ c₃ c₁ c C δ' σ X L g D N ℓ N₀ s kC m)
include h

omit [Fintype V] [DecidableEq V]

lemma NumCtx.N₀pos : (0 : ℝ) < N₀ := by have := h.hN₀; exact_mod_cast this

lemma NumCtx.Lpos : 0 < L := by linarith [h.hL]

lemma NumCtx.gpos : 0 < g := by linarith [h.hg]

lemma NumCtx.Lg : 40 ≤ L * g := by nlinarith [h.hL, h.hg]

lemma NumCtx.Lgpos : 0 < L * g := by linarith [h.Lg]

lemma NumCtx.σ2 : σ ^ 2 ≤ 1 / 100 := by nlinarith [h.hσ, h.hσ1]

lemma NumCtx.σ2le : σ ^ 2 ≤ σ / 10 := by nlinarith [h.hσ, h.hσ1]

lemma NumCtx.Xle : X ≤ σ / 10 := h.hXσ.trans h.σ2le

lemma NumCtx.c₃pos : 0 < c₃ := by rw [h.hc₃]; linarith [h.hρ]

lemma NumCtx.c₁c₃ : c₁ ≤ c₃ := by rw [h.hc₃]; linarith [h.hc₁ρ]

lemma NumCtx.c₁c₀ : c₁ ≤ c₀ := by linarith [h.hc₁ρ, h.hρc₀, h.hc₁]

lemma NumCtx.c₃small : c₃ ≤ 1 / 640 := by
  rw [h.hc₃]; linarith [h.hρc₀, h.hc₀1]

lemma NumCtx.c16 : c ≤ 1 / 16 := by linarith [h.hcδ, h.hδ'1]

lemma NumCtx.cσ : c * σ ≤ 1 / 160 := by nlinarith [h.c16, h.hσ, h.hσ1, h.hc]

lemma NumCtx.cσ0 : 0 ≤ c * σ := mul_nonneg h.hc.le h.hσ.le

lemma NumCtx.Ypos : 0 < X * N₀ / (L * g) := div_pos (mul_pos h.hX h.N₀pos) h.Lgpos

lemma NumCtx.Zpos : 0 < X * D / (L * g) := div_pos (mul_pos h.hX h.hD) h.Lgpos

/-- `Z = σ^{5/2} D / (L g)` is at least `C L / σ²`. -/
lemma NumCtx.Z_ge : C * L / σ ^ 2 ≤ X * D / (L * g) := by
  have hσ2 : 0 < σ ^ 2 := by have := h.hσ; positivity
  rw [div_le_div_iff₀ hσ2 h.Lgpos]
  have := h.hdl
  nlinarith

lemma NumCtx.CL100 : 100 * C * L ≤ C * L / σ ^ 2 := by
  have hσ2 : 0 < σ ^ 2 := by have := h.hσ; positivity
  rw [le_div_iff₀ hσ2]
  have hCL : 0 ≤ C * L := mul_nonneg h.hC.le h.Lpos.le
  nlinarith [mul_le_mul_of_nonneg_left h.σ2 hCL]

lemma NumCtx.Z_ge' : 100 * C * L ≤ X * D / (L * g) := h.CL100.trans h.Z_ge

lemma NumCtx.XLg : X / (L * g) ≤ σ ^ 2 / 40 := by
  rw [div_le_div_iff₀ h.Lgpos (by norm_num)]
  have hσ2 : 0 ≤ σ ^ 2 := sq_nonneg σ
  nlinarith [h.hXσ, h.hX, mul_le_mul_of_nonneg_left h.Lg hσ2]

lemma NumCtx.Y_le : X * N₀ / (L * g) ≤ σ ^ 2 * N₀ / 40 := by
  have := mul_le_mul_of_nonneg_right h.XLg h.N₀pos.le
  calc X * N₀ / (L * g) = X / (L * g) * N₀ := by ring
    _ ≤ σ ^ 2 / 40 * N₀ := this
    _ = σ ^ 2 * N₀ / 40 := by ring

lemma NumCtx.Y_le' : X * N₀ / (L * g) ≤ σ * N₀ / 400 := by
  refine h.Y_le.trans ?_
  have := mul_le_mul_of_nonneg_right h.σ2le h.N₀pos.le
  linarith

/-- `Y = σ^{5/2} N₀ / (L g)`, the scale of `m`, is at least `500 C`. -/
lemma NumCtx.Y_ge : 500 * C ≤ X * N₀ / (L * g) := by
  have hZ := h.Z_ge'
  have h1 : X * D / (L * g) ≤ 2 * (X * N₀ / (L * g)) := by
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right h.Lgpos]
    nlinarith [h.hDN, h.hX]
  have h2 : 1000 * C ≤ 100 * C * L := by nlinarith [h.hL, h.hC]
  linarith

lemma NumCtx.c₁Y : 16 ≤ c₁ * (X * N₀ / (L * g)) := by
  have := mul_le_mul_of_nonneg_left h.Y_ge h.hc₁.le
  nlinarith [h.hC11]

lemma NumCtx.m_bounds : c₁ * (X * N₀ / (L * g)) / 2 ≤ (m : ℝ) ∧
    (m : ℝ) ≤ c₁ * (X * N₀ / (L * g)) := by
  have e : c₁ * X * N₀ / (L * g) = c₁ * (X * N₀ / (L * g)) := by ring
  rw [h.hm, e]
  exact floor_half (by linarith [h.c₁Y])

lemma NumCtx.kCexpr : c₃ * X * N₀ / L = c₃ * (X * N₀ / (L * g)) * g := by
  have hg0 : g ≠ 0 := h.gpos.ne'
  have hL0 : L ≠ 0 := h.Lpos.ne'
  field_simp

lemma NumCtx.c₃Yg : 16 ≤ c₃ * X * N₀ / L := by
  rw [h.kCexpr]
  have h1 := mul_le_mul_of_nonneg_right h.c₁c₃ h.Ypos.le
  have h2 := h.c₁Y
  have hg := h.hg
  have h3 : 0 ≤ c₃ * (X * N₀ / (L * g)) := mul_nonneg h.c₃pos.le h.Ypos.le
  nlinarith

lemma NumCtx.kC_bounds : c₃ * X * N₀ / L / 2 ≤ (kC : ℝ) ∧ (kC : ℝ) ≤ c₃ * X * N₀ / L := by
  rw [h.hkC]
  exact floor_half (by linarith [h.c₃Yg])

lemma NumCtx.c₀σN : 16 ≤ c₀ * σ * N₀ := by
  have h1 : X * N₀ / (L * g) ≤ σ * N₀ := by
    have := h.Y_le'
    have : 0 ≤ σ * N₀ := mul_nonneg h.hσ.le h.N₀pos.le
    linarith
  have h3 := mul_le_mul h.c₁c₀ h1 h.Ypos.le h.hc₀.le
  have h4 := h.c₁Y
  linarith [show c₀ * (σ * N₀) = c₀ * σ * N₀ by ring]

lemma NumCtx.s_bounds : c₀ * σ * N₀ / 2 ≤ (s : ℝ) ∧ (s : ℝ) ≤ c₀ * σ * N₀ := by
  rw [h.hs]
  exact floor_half (by linarith [h.c₀σN])

lemma NumCtx.m8 : 8 ≤ m := by
  have h1 := h.m_bounds.1
  have h2 := h.c₁Y
  have : (8 : ℝ) ≤ m := by linarith
  exact_mod_cast this

lemma NumCtx.s1 : 1 ≤ s := by
  have h1 := h.s_bounds.1
  have h2 := h.c₀σN
  have : (1 : ℝ) ≤ s := by linarith
  exact_mod_cast this

lemma NumCtx.kC1 : (1 : ℝ) ≤ kC := by
  have h1 := h.kC_bounds.1
  have h2 := h.c₃Yg
  linarith

lemma NumCtx.ℓm : 8 * ℓ ≤ (m : ℝ) := by
  have h1 : ℓ ≤ 2 * c * (X * N₀ / (L * g)) := by
    refine h.hℓ.trans ?_
    rw [show 2 * c * (X * N₀ / (L * g)) = c * X * (2 * N₀) / (L * g) by ring]
    apply div_le_div_of_nonneg_right _ h.Lgpos.le
    exact mul_le_mul_of_nonneg_left h.hN2 (mul_nonneg h.hc.le h.hX.le)
  have h2 := h.m_bounds.1
  have h3 := mul_le_mul_of_nonneg_right h.hc₁c h.Ypos.le
  nlinarith

lemma NumCtx.size : (3 * s + kC + 9 * m : ℝ) ≤ N₀ := by
  have hN := h.N₀pos
  have hs := h.s_bounds.2
  have hk := h.kC_bounds.2
  have hm := h.m_bounds.2
  have h1 : c₀ * σ * N₀ ≤ N₀ / 400 := by
    have : c₀ * σ ≤ 1 / 400 := by nlinarith [h.hc₀1, h.hc₀, h.hσ, h.hσ1]
    have := mul_le_mul_of_nonneg_right this hN.le
    linarith
  have h2 : c₃ * X * N₀ / L ≤ N₀ / 1000 := by
    rw [div_le_div_iff₀ h.Lpos (by norm_num)]
    have hX1 : X ≤ 1 / 100 := by nlinarith [h.Xle, h.hσ1]
    have hc3X : c₃ * X ≤ 1 / 64000 := by nlinarith [h.c₃small, h.c₃pos, h.hX]
    have := mul_le_mul_of_nonneg_right hc3X hN.le
    nlinarith [h.hL]
  have h3 : c₁ * (X * N₀ / (L * g)) ≤ N₀ / 1000 := by
    have hY := h.Y_le'
    have : c₁ ≤ 1 / 640 := h.c₁c₃.trans h.c₃small
    have h4 : c₁ * (X * N₀ / (L * g)) ≤ 1 / 640 * (σ * N₀ / 400) :=
      mul_le_mul this hY h.Ypos.le (by norm_num)
    have : σ * N₀ ≤ N₀ / 10 := by nlinarith [h.hσ1]
    nlinarith
  linarith

/-- `σ D ≥ 40000 C L`. -/
lemma NumCtx.σD : 40000 * C * L ≤ σ * D := by
  have hσ := h.hσ
  have hX4 : X * σ ^ 2 ≤ σ ^ 4 := by
    have := mul_le_mul_of_nonneg_right h.hXσ (sq_nonneg σ)
    nlinarith
  have h1 : C * L ^ 2 * g ≤ D * σ ^ 4 := by
    have := mul_le_mul_of_nonneg_left hX4 h.hD.le
    nlinarith [h.hdl]
  have hσ3 : σ ^ 3 ≤ 1 / 1000 := by
    have := pow_le_pow_left₀ hσ.le h.hσ1 3
    norm_num at this; linarith
  have hCL : 0 ≤ C * L := mul_nonneg h.hC.le h.Lpos.le
  have h2 : 40000 * C * L * σ ^ 3 ≤ C * L ^ 2 * g := by
    have h5 := mul_le_mul_of_nonneg_left hσ3 hCL
    have h6 := mul_le_mul_of_nonneg_left h.Lg hCL
    nlinarith
  have h3 : 40000 * C * L * σ ^ 3 ≤ σ * D * σ ^ 3 := by nlinarith
  exact le_of_mul_le_mul_right h3 (by positivity)

end Num

omit [Fintype V] [DecidableEq V] in
lemma scale_le {a b N₀ D : ℝ} (hN : 0 < N₀) (hD : 0 ≤ D) (h : a ≤ b) : a / N₀ * D ≤ b / N₀ * D :=
  mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h hN.le) hD

section Num2

variable {εR c₇ C₇ εA cdfs κc CF Cb c₂' c₀ ρ c₃ c₁ c C δ' σ X L g D N ℓ : ℝ} {N₀ s kC m : ℕ}
  (h : NumCtx εR c₇ C₇ εA cdfs κc CF Cb c₂' c₀ ρ c₃ c₁ c C δ' σ X L g D N ℓ N₀ s kC m)
include h

omit [Fintype V] [DecidableEq V]

lemma NumCtx.PM_lo : c₁ * (X * D / (L * g)) / 2 ≤ (m : ℝ) / N₀ * D := by
  have hN := h.N₀pos
  have h1 := scale_le hN h.hD.le h.m_bounds.1
  refine le_trans (le_of_eq ?_) h1
  have := hN.ne'; have := h.Lgpos.ne'
  field_simp

lemma NumCtx.PM_hi : (m : ℝ) / N₀ * D ≤ c₁ * (X * D / (L * g)) := by
  have hN := h.N₀pos
  have h1 := scale_le hN h.hD.le h.m_bounds.2
  refine h1.trans (le_of_eq ?_)
  have := hN.ne'; have := h.Lgpos.ne'
  field_simp

lemma NumCtx.DC_lo : c₃ * (X * D / L) / 2 ≤ (kC : ℝ) / N₀ * D := by
  have hN := h.N₀pos
  have h1 := scale_le hN h.hD.le h.kC_bounds.1
  refine le_trans (le_of_eq ?_) h1
  have := hN.ne'; have := h.Lpos.ne'
  field_simp

lemma NumCtx.DC_hi : (kC : ℝ) / N₀ * D ≤ c₃ * (X * D / L) := by
  have hN := h.N₀pos
  have h1 := scale_le hN h.hD.le h.kC_bounds.2
  refine h1.trans (le_of_eq ?_)
  have := hN.ne'; have := h.Lpos.ne'
  field_simp

lemma NumCtx.S_lo : c₀ * σ * D / 2 ≤ (s : ℝ) / N₀ * D := by
  have hN := h.N₀pos
  have h1 := scale_le hN h.hD.le h.s_bounds.1
  refine le_trans (le_of_eq ?_) h1
  have := hN.ne'
  field_simp

lemma NumCtx.S_hi : (s : ℝ) / N₀ * D ≤ c₀ * σ * D := by
  have hN := h.N₀pos
  have h1 := scale_le hN h.hD.le h.s_bounds.2
  refine h1.trans (le_of_eq ?_)
  have := hN.ne'
  field_simp

lemma NumCtx.Zg : X * D / (L * g) * g = X * D / L := by
  have := h.Lpos.ne'; have := h.gpos.ne'
  field_simp

lemma NumCtx.W_ge : 400 * C * L ≤ X * D / L := by
  rw [← h.Zg]
  have := mul_le_mul h.Z_ge' h.hg (by norm_num) h.Zpos.le
  linarith

lemma NumCtx.Wpos : 0 < X * D / L := div_pos (mul_pos h.hX h.hD) h.Lpos

lemma NumCtx.XDL : X * D / L ≤ σ * D / 100 := by
  rw [div_le_div_iff₀ h.Lpos (by norm_num)]
  have h1 := mul_le_mul_of_nonneg_right h.Xle h.hD.le
  have h2 : 0 ≤ σ * D := mul_nonneg h.hσ.le h.hD.le
  nlinarith [mul_le_mul_of_nonneg_left h.hL h2]

lemma NumCtx.Z_le_σD : X * D / (L * g) ≤ σ * D := by
  rw [div_le_iff₀ h.Lgpos]
  have h1 : X ≤ σ := by linarith [h.Xle, h.hσ]
  have h2 := mul_le_mul_of_nonneg_right h1 h.hD.le
  have h3 : 0 ≤ σ * D := mul_nonneg h.hσ.le h.hD.le
  nlinarith [mul_le_mul_of_nonneg_left h.Lg h3]

lemma NumCtx.S_ge : 20000 * L ≤ (s : ℝ) / N₀ * D := by
  have h1 := h.S_lo
  have h2 := mul_le_mul_of_nonneg_left h.σD h.hc₀.le
  have h3 := mul_le_mul_of_nonneg_right h.hC8 h.Lpos.le
  nlinarith

lemma NumCtx.thr_att : 0 < (s : ℝ) / N₀ * D / 4 ∧ 12 * L * ((s : ℝ) / N₀ * ((1 + c * σ) * D) +
    (s : ℝ) / N₀ * D / 4) ≤ ((s : ℝ) / N₀ * D / 4) ^ 2 := by
  set S := (s : ℝ) / N₀ * D with hS
  have hSL := h.S_ge
  have hL := h.Lpos
  have hS0 : 0 ≤ S := by linarith
  have e : (s : ℝ) / N₀ * ((1 + c * σ) * D) = S * (1 + c * σ) := by rw [hS]; ring
  rw [e]
  refine ⟨by linarith, ?_⟩
  have hLS : 0 ≤ L * S := mul_nonneg hL.le hS0
  nlinarith [mul_le_mul_of_nonneg_left h.cσ hLS, mul_le_mul_of_nonneg_right hSL hS0]

lemma NumCtx.DC_ge2 : 200 * c₃ * C * L ≤ (kC : ℝ) / N₀ * D := by
  have h1 := h.DC_lo
  have h2 := mul_le_mul_of_nonneg_left h.W_ge h.c₃pos.le
  nlinarith

lemma NumCtx.DC_ge : 400 * L ≤ (kC : ℝ) / N₀ * D := by
  have h1 := h.DC_ge2
  have h2 := mul_le_mul_of_nonneg_right h.hC5 h.Lpos.le
  nlinarith

lemma NumCtx.thr_cyc : 0 < (kC : ℝ) / N₀ * D / 4 ∧ 12 * L * ((kC : ℝ) / N₀ * ((1 + c * σ) * D) +
    (kC : ℝ) / N₀ * D / 4) ≤ ((kC : ℝ) / N₀ * D / 4) ^ 2 := by
  set S := (kC : ℝ) / N₀ * D with hS
  have hSL := h.DC_ge
  have hL := h.Lpos
  have hS0 : 0 ≤ S := by linarith
  have e : (kC : ℝ) / N₀ * ((1 + c * σ) * D) = S * (1 + c * σ) := by rw [hS]; ring
  rw [e]
  refine ⟨by linarith, ?_⟩
  have hLS : 0 ≤ L * S := mul_nonneg hL.le hS0
  nlinarith [mul_le_mul_of_nonneg_left h.cσ hLS, mul_le_mul_of_nonneg_right hSL hS0]

lemma NumCtx.PM_ge : c₁ * C * L / (2 * σ ^ 2) ≤ (m : ℝ) / N₀ * D := by
  refine le_trans ?_ h.PM_lo
  have := mul_le_mul_of_nonneg_left h.Z_ge h.hc₁.le
  have e : c₁ * C * L / (2 * σ ^ 2) = c₁ * (C * L / σ ^ 2) / 2 := by ring
  rw [e]
  linarith

lemma NumCtx.thr_lay : 0 < δ' * σ * ((m : ℝ) / N₀ * D) / 4 ∧
    12 * L * ((m : ℝ) / N₀ * ((1 + c * σ) * D) + δ' * σ * ((m : ℝ) / N₀ * D) / 4) ≤
      (δ' * σ * ((m : ℝ) / N₀ * D) / 4) ^ 2 := by
  set P := (m : ℝ) / N₀ * D with hP
  have hL := h.Lpos
  have hσ := h.hσ
  have hδ := h.hδ'
  have hPg := h.PM_ge
  have hP0 : 0 < P := lt_of_lt_of_le
    (div_pos (mul_pos (mul_pos h.hc₁ h.hC) hL) (by positivity)) hPg
  have hT : 250 * L ≤ δ' ^ 2 * σ ^ 2 * P := by
    have h1 : δ' ^ 2 * σ ^ 2 * (c₁ * C * L / (2 * σ ^ 2)) = δ' ^ 2 * c₁ * C * L / 2 := by
      have := hσ.ne'
      field_simp
    have h2 := mul_le_mul_of_nonneg_left hPg (show 0 ≤ δ' ^ 2 * σ ^ 2 by positivity)
    have h3 := mul_le_mul_of_nonneg_right h.hC4 hL.le
    nlinarith
  have e : (m : ℝ) / N₀ * ((1 + c * σ) * D) = P * (1 + c * σ) := by rw [hP]; ring
  rw [e]
  have hδσ : δ' * σ ≤ 1 / 10 := by nlinarith [h.hδ'1, h.hσ1]
  refine ⟨by positivity, ?_⟩
  have e2 : (δ' * σ * P / 4) ^ 2 = δ' ^ 2 * σ ^ 2 * P * P / 16 := by ring
  rw [e2]
  have hLP : 0 ≤ L * P := mul_nonneg hL.le hP0.le
  nlinarith [mul_le_mul_of_nonneg_left h.cσ hLP, mul_le_mul_of_nonneg_left hδσ hLP,
    mul_le_mul_of_nonneg_right hT hP0.le]

lemma NumCtx.wideP : ((kC + 4 * m : ℕ) : ℝ) / N₀ * ((1 + c * σ) * D) ≤ ρ * X * D / (4 * L) := by
  have e : ((kC + 4 * m : ℕ) : ℝ) / N₀ * ((1 + c * σ) * D) =
      ((kC : ℝ) / N₀ * D + 4 * ((m : ℝ) / N₀ * D)) * (1 + c * σ) := by
    push_cast; ring
  rw [e]
  set W := X * D / L with hW
  have h1 := h.DC_hi
  have h2 := h.PM_hi
  have hZg := h.Zg
  have h3 : 4 * (c₁ * (X * D / (L * g))) ≤ c₁ * W := by
    rw [hW, ← hZg]
    have := mul_le_mul_of_nonneg_left h.hg (mul_nonneg h.hc₁.le h.Zpos.le)
    linarith
  have hW0 : 0 ≤ W := h.Wpos.le
  have hsum : (kC : ℝ) / N₀ * D + 4 * ((m : ℝ) / N₀ * D) ≤ ρ / 8 * W := by
    have h4 : c₃ + c₁ ≤ ρ / 8 := by rw [h.hc₃]; linarith [h.hc₁ρ]
    have := mul_le_mul_of_nonneg_right h4 hW0
    nlinarith
  have hS0 : 0 ≤ (kC : ℝ) / N₀ * D + 4 * ((m : ℝ) / N₀ * D) := by
    have := h.N₀pos; have := h.hD; positivity
  have e2 : ρ * X * D / (4 * L) = ρ / 4 * W := by rw [hW]; ring
  rw [e2]
  have hρW : 0 ≤ ρ / 8 * W := mul_nonneg (by linarith [h.hρ]) hW0
  nlinarith [mul_le_mul_of_nonneg_left h.cσ hS0, mul_le_mul_of_nonneg_right hsum h.cσ0]

lemma NumCtx.tW_ge : 100 * L ≤ ρ * X * D / (4 * L) := by
  have e2 : ρ * X * D / (4 * L) = ρ / 4 * (X * D / L) := by ring
  rw [e2]
  have h1 := mul_le_mul_of_nonneg_left h.W_ge (show 0 ≤ ρ / 4 by linarith [h.hρ])
  have h2 := mul_le_mul_of_nonneg_right h.hC6 h.Lpos.le
  nlinarith

lemma NumCtx.thr_wide : 0 < ρ * X * D / (4 * L) ∧
    12 * L * (((kC + 4 * m : ℕ) : ℝ) / N₀ * ((1 + c * σ) * D) + ρ * X * D / (4 * L)) ≤
      (ρ * X * D / (4 * L)) ^ 2 := by
  have h1 := h.wideP
  have h2 := h.tW_ge
  have hL := h.Lpos
  set t := ρ * X * D / (4 * L)
  have ht : 0 ≤ t := by linarith
  refine ⟨by linarith, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right h2 ht, mul_le_mul_of_nonneg_left h1 hL.le]

lemma NumCtx.envP : ((3 * s + kC + 4 * m : ℕ) : ℝ) / N₀ * ((1 + c * σ) * D) ≤ κc * σ * D / 4 := by
  have e : ((3 * s + kC + 4 * m : ℕ) : ℝ) / N₀ * ((1 + c * σ) * D) =
      (3 * ((s : ℝ) / N₀ * D) + (kC : ℝ) / N₀ * D + 4 * ((m : ℝ) / N₀ * D)) * (1 + c * σ) := by
    push_cast; ring
  rw [e]
  have h1 := h.S_hi
  have h2 := h.DC_hi
  have h3 := h.PM_hi
  have hZg := h.Zg
  have h4 : 4 * (c₁ * (X * D / (L * g))) ≤ c₁ * (X * D / L) := by
    rw [← hZg]
    have := mul_le_mul_of_nonneg_left h.hg (mul_nonneg h.hc₁.le h.Zpos.le)
    linarith
  have hσD : 0 ≤ σ * D := mul_nonneg h.hσ.le h.hD.le
  have h5 : (c₃ + c₁) * (X * D / L) ≤ (c₃ + c₁) * (σ * D / 100) :=
    mul_le_mul_of_nonneg_left h.XDL (by linarith [h.c₃pos, h.hc₁])
  have h6 : c₃ + c₁ ≤ c₀ / 8 := by rw [h.hc₃]; linarith [h.hc₁ρ, h.hρc₀]
  have hsum : 3 * ((s : ℝ) / N₀ * D) + (kC : ℝ) / N₀ * D + 4 * ((m : ℝ) / N₀ * D) ≤
      κc / 5 * (σ * D) := by
    have h7 := h.hc₀κ
    have h8 := mul_le_mul_of_nonneg_right h6 (show 0 ≤ σ * D / 100 by positivity)
    have h9 := mul_le_mul_of_nonneg_right h7 hσD
    have hκ : 0 ≤ κc := by linarith [h.hc₀κ, h.hc₀]
    have h10 := mul_nonneg hκ hσD
    nlinarith
  have hS0 : 0 ≤ 3 * ((s : ℝ) / N₀ * D) + (kC : ℝ) / N₀ * D + 4 * ((m : ℝ) / N₀ * D) := by
    have := h.N₀pos; have := h.hD; positivity
  have hκ : 0 ≤ κc := by linarith [h.hc₀κ, h.hc₀]
  have hK5 : 0 ≤ κc / 5 * (σ * D) := mul_nonneg (by linarith) hσD
  nlinarith [mul_le_mul_of_nonneg_left h.cσ hS0, mul_le_mul_of_nonneg_right hsum h.cσ0]

lemma NumCtx.thr_env : 0 < κc * σ * D / 4 ∧
    12 * L * (((3 * s + kC + 4 * m : ℕ) : ℝ) / N₀ * ((1 + c * σ) * D) + κc * σ * D / 4) ≤
      (κc * σ * D / 4) ^ 2 := by
  have h1 := h.envP
  have hL := h.Lpos
  have hκ : 0 < κc := by linarith [h.hc₀κ, h.hc₀]
  have h3 : 100 * L ≤ κc * σ * D / 4 := by
    have h4 := mul_le_mul_of_nonneg_left h.σD hκ.le
    have h5 := mul_le_mul_of_nonneg_right h.hC7 hL.le
    nlinarith
  set t := κc * σ * D / 4
  have ht : 0 ≤ t := by linarith
  refine ⟨by linarith, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right h3 ht, mul_le_mul_of_nonneg_left h1 hL.le]

lemma NumCtx.envc : ((3 * s + kC + 4 * m : ℕ) : ℝ) ≤ κc * (σ / 2) * N₀ := by
  have hN := h.N₀pos
  push_cast
  have h1 := h.s_bounds.2
  have h2 := h.kC_bounds.2
  have h3 := h.m_bounds.2
  have hσN : 0 ≤ σ * N₀ := mul_nonneg h.hσ.le hN.le
  have h4 : c₃ * X * N₀ / L ≤ c₃ * (σ * N₀) / 100 := by
    rw [div_le_div_iff₀ h.Lpos (by norm_num)]
    have h5 := mul_le_mul_of_nonneg_right h.Xle (mul_nonneg h.c₃pos.le hN.le)
    have h6 := mul_le_mul_of_nonneg_left h.hL (mul_nonneg h.c₃pos.le hσN)
    nlinarith
  have h6 : c₁ * (X * N₀ / (L * g)) ≤ c₁ * (σ * N₀ / 400) :=
    mul_le_mul_of_nonneg_left h.Y_le' h.hc₁.le
  have h7 : c₃ + c₁ ≤ c₀ / 8 := by rw [h.hc₃]; linarith [h.hc₁ρ, h.hρc₀]
  have h8 := mul_le_mul_of_nonneg_right h.hc₀κ hσN
  have h9 := mul_le_mul_of_nonneg_right h7 hσN
  have h10 : 0 ≤ c₃ * (σ * N₀) := mul_nonneg h.c₃pos.le hσN
  have h11 : 0 ≤ c₁ * (σ * N₀) := mul_nonneg h.hc₁.le hσN
  nlinarith

lemma NumCtx.pair_s : Cb * (σ / 2) ^ (-2 : ℝ) * L ≤ (s : ℝ) / N₀ * D := by
  have hσ := h.hσ
  rw [rpow_neg_two' (by positivity)]
  refine le_trans ?_ h.S_lo
  have hZ := h.Z_ge.trans h.Z_le_σD
  have hLσ : 0 ≤ L / σ ^ 2 := div_nonneg h.Lpos.le (by positivity)
  have e1 : Cb * (1 / (σ / 2) ^ 2) * L = (8 * Cb) * (L / σ ^ 2) / 2 := by
    have := hσ.ne'
    field_simp; ring
  have e2 : C * L / σ ^ 2 = C * (L / σ ^ 2) := by ring
  rw [e1]
  rw [e2] at hZ
  have h1 := mul_le_mul_of_nonneg_right h.hC1 hLσ
  have h2 := mul_le_mul_of_nonneg_left hZ h.hc₀.le
  nlinarith

lemma NumCtx.pair_fill (k : ℕ) (hk : (m : ℝ) / 2 ≤ k) :
    Cb * (σ / 2) ^ (-2 : ℝ) * L ≤ (k : ℝ) / N₀ * D := by
  have hσ := h.hσ
  have hN := h.N₀pos
  rw [rpow_neg_two' (by positivity)]
  have h1 : (m : ℝ) / N₀ * D / 2 ≤ (k : ℝ) / N₀ * D := by
    have := scale_le hN h.hD.le hk
    linarith [show (m : ℝ) / 2 / N₀ * D = (m : ℝ) / N₀ * D / 2 by ring]
  refine le_trans ?_ h1
  have h2 := h.PM_ge
  have hLσ : 0 ≤ L / σ ^ 2 := div_nonneg h.Lpos.le (by positivity)
  have e1 : Cb * (1 / (σ / 2) ^ 2) * L = (16 * Cb) * (L / σ ^ 2) / 4 := by
    have := hσ.ne'
    field_simp; ring
  have e2 : c₁ * C * L / (2 * σ ^ 2) = (c₁ * C) * (L / σ ^ 2) / 2 := by ring
  rw [e1]
  rw [e2] at h2
  have h3 := mul_le_mul_of_nonneg_right h.hC2 hLσ
  nlinarith

lemma NumCtx.layer : CF * (σ / 2) ^ (-(2 : ℝ)) * L ≤ (m : ℝ) / N₀ * D := by
  have hσ := h.hσ
  rw [rpow_neg_two' (by positivity)]
  have h2 := h.PM_ge
  have hLσ : 0 ≤ L / σ ^ 2 := div_nonneg h.Lpos.le (by positivity)
  have e1 : CF * (1 / (σ / 2) ^ 2) * L = (8 * CF) * (L / σ ^ 2) / 2 := by
    have := hσ.ne'
    field_simp; ring
  have e2 : c₁ * C * L / (2 * σ ^ 2) = (c₁ * C) * (L / σ ^ 2) / 2 := by ring
  rw [e1]
  rw [e2] at h2
  have h3 := mul_le_mul_of_nonneg_right h.hC3 hLσ
  nlinarith

lemma NumCtx.cycDC : C₇ ≤ (kC : ℝ) / N₀ * D := by
  have h1 := h.DC_ge2
  have h9 := h.hC9
  have hc3C : 0 ≤ c₃ * C := mul_nonneg h.c₃pos.le h.hC.le
  have := mul_le_mul_of_nonneg_left h.hL hc3C
  nlinarith

lemma NumCtx.many : (2 * m : ℝ) ≤ c₇ * ((2 * kC : ℕ) : ℝ) / g := by
  push_cast
  rw [le_div_iff₀ h.gpos]
  have h1 := h.m_bounds.2
  have h2 := h.kC_bounds.1
  rw [h.kCexpr] at h2
  set Y := X * N₀ / (L * g)
  have hY0 : 0 ≤ Y := h.Ypos.le
  have hg0 := h.gpos
  have h3 := mul_le_mul_of_nonneg_left h2 h.hc₇.le
  have h4 := mul_le_mul_of_nonneg_right h.hc₁7 (mul_nonneg hY0 hg0.le)
  have h5 := mul_le_mul_of_nonneg_right h1 hg0.le
  nlinarith

lemma NumCtx.rtrlog : Real.log (2 * ((2 * s : ℕ) : ℝ)) ≤ L := by
  have hs1 : (1 : ℝ) ≤ s := by have := h.s1; exact_mod_cast this
  refine le_trans (Real.log_le_log (by push_cast; positivity) ?_) h.hlogN
  push_cast
  have h1 := h.s_bounds.2
  have hN := h.N₀pos
  have h2 : c₀ * σ * N₀ ≤ N₀ / 400 := by
    have : c₀ * σ ≤ 1 / 400 := by nlinarith [h.hc₀1, h.hc₀, h.hσ, h.hσ1]
    have := mul_le_mul_of_nonneg_right this hN.le
    linarith
  have := h.hNN
  linarith

lemma NumCtx.div : (2 * m + 2 : ℝ) ≤ cdfs * (c₂' * (σ / 2)) * ((2 * s : ℕ) : ℝ) := by
  push_cast
  have h1 := h.s_bounds.1
  have h2 := h.m_bounds.2
  have hY := h.Y_le
  have hc1Y := h.c₁Y
  have hN := h.N₀pos
  have hσ := h.hσ
  have hσN : 0 ≤ σ ^ 2 * N₀ := by positivity
  have h3 : c₁ * (X * N₀ / (L * g)) ≤ c₁ * (σ ^ 2 * N₀ / 40) :=
    mul_le_mul_of_nonneg_left hY h.hc₁.le
  have h4 : 640 ≤ c₁ * (σ ^ 2 * N₀) := by
    have := mul_le_mul_of_nonneg_left hY h.hc₁.le
    nlinarith
  have hK : 0 ≤ cdfs * (c₂' * (σ / 2)) := by
    have := h.hcdfs; have := h.hc₂'; positivity
  have h5 : cdfs * (c₂' * (σ / 2)) * (2 * (c₀ * σ * N₀ / 2)) ≤
      cdfs * (c₂' * (σ / 2)) * (2 * (s : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hK
  have e : cdfs * (c₂' * (σ / 2)) * (2 * (c₀ * σ * N₀ / 2)) =
      (cdfs * c₂' * c₀) * (σ ^ 2 * N₀) / 2 := by ring
  rw [e] at h5
  have h6 : 4 * c₁ * (σ ^ 2 * N₀) ≤ (cdfs * c₂' * c₀) * (σ ^ 2 * N₀) :=
    mul_le_mul_of_nonneg_right h.hc₁d hσN
  nlinarith

lemma NumCtx.sparse (ε c' c₁' : ℝ) (hε : ρ ≤ ε * (c₂' / 2) ^ (3 / 2 : ℝ) * c₀ / 2)
    (hε0 : 0 < ε) (hc' : 2 * c' ≤ ρ) (hc₁' : 0 ≤ c₁') :
    c' * X * D / L + (ρ * X * D / (4 * L) + ρ * X * D / (4 * L)) ≤
      ε * (c₂' * (σ / 2)) ^ (3 / 2 : ℝ) * ((1 + c₁' * (σ / 2)) * ((s : ℝ) / N₀ * D)) / L := by
  have hσ := h.hσ
  have hL := h.Lpos
  set W := X * D / L with hW
  have hW0 : 0 ≤ W := h.Wpos.le
  set A := (c₂' / 2) ^ (3 / 2 : ℝ) with hA
  have hA0 : 0 ≤ A := Real.rpow_nonneg (by linarith [h.hc₂']) _
  have hsplit : (c₂' * (σ / 2)) ^ (3 / 2 : ℝ) = A * σ ^ (3 / 2 : ℝ) := by
    rw [hA, ← Real.mul_rpow (by linarith [h.hc₂']) hσ.le]
    congr 1; ring
  rw [hsplit]
  have hσ32 : 0 ≤ σ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hσ.le _
  have hS := h.S_lo
  have hS0 : 0 ≤ (s : ℝ) / N₀ * D := by have := h.N₀pos; have := h.hD; positivity
  have h1 : c₀ * σ * D / 2 ≤ (1 + c₁' * (σ / 2)) * ((s : ℝ) / N₀ * D) := by
    have : 0 ≤ c₁' * (σ / 2) * ((s : ℝ) / N₀ * D) := by positivity
    nlinarith
  have hK0 : 0 ≤ ε * (A * σ ^ (3 / 2 : ℝ)) := by positivity
  have h2 : ε * (A * σ ^ (3 / 2 : ℝ)) * (c₀ * σ * D / 2) / L ≤
      ε * (A * σ ^ (3 / 2 : ℝ)) * ((1 + c₁' * (σ / 2)) * ((s : ℝ) / N₀ * D)) / L :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hK0) hL.le
  have e : ε * (A * σ ^ (3 / 2 : ℝ)) * (c₀ * σ * D / 2) / L = (ε * A * c₀ / 2) * W := by
    rw [hW, ← h.hX32]; ring
  rw [e] at h2
  have h3 : ρ * W ≤ (ε * A * c₀ / 2) * W := mul_le_mul_of_nonneg_right (by linarith) hW0
  have e2 : c' * X * D / L + (ρ * X * D / (4 * L) + ρ * X * D / (4 * L)) = c' * W + ρ / 2 * W := by
    rw [hW]; ring
  rw [e2, show ε * (A * σ ^ (3 / 2 : ℝ)) * ((1 + c₁' * (σ / 2)) * ((s : ℝ) / N₀ * D)) / L =
    ε * (A * σ ^ (3 / 2 : ℝ)) * ((1 + c₁' * (σ / 2)) * ((s : ℝ) / N₀ * D)) / L from rfl]
  have h4 : c' * W ≤ ρ / 2 * W := mul_le_mul_of_nonneg_right (by linarith) hW0
  have e3 : ε * (c₂' * (σ / 2)) ^ (3 / 2 : ℝ) = ε * (A * σ ^ (3 / 2 : ℝ)) := by rw [hsplit]
  linarith

lemma NumCtx.girth :
    C₇ * Real.log (2 * ((2 * kC : ℕ) : ℝ)) / Real.log (2 + (kC : ℝ) / N₀ * D) ≤ g := by
  have hL := h.Lpos
  have hC₇ := h.hC₇
  have hc₃ := h.c₃pos
  have hN := h.N₀pos
  have hk1 := h.kC1
  have hlogk : Real.log (2 * ((2 * kC : ℕ) : ℝ)) ≤ L := by
    refine le_trans (Real.log_le_log (by push_cast; positivity) ?_) h.hlogN
    push_cast
    have h1 := h.kC_bounds.2
    have h2 : c₃ * X * N₀ / L ≤ N₀ / 1000 := by
      rw [div_le_div_iff₀ hL (by norm_num)]
      have hX1 : X ≤ 1 / 100 := by nlinarith [h.Xle, h.hσ1]
      have hc3X : c₃ * X ≤ 1 / 64000 := by nlinarith [h.c₃small, h.c₃pos, h.hX]
      have := mul_le_mul_of_nonneg_right hc3X hN.le
      nlinarith [h.hL]
    have := h.hNN
    linarith
  set y := X * D / L with hy
  set DC := (kC : ℝ) / N₀ * D with hDC
  have hDCy : c₃ * y / 2 ≤ DC := h.DC_lo
  have hy0 : 0 ≤ y := h.Wpos.le
  have hDC0 : 0 ≤ DC := mul_nonneg (div_nonneg (Nat.cast_nonneg _) hN.le) h.hD.le
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlogDC : Real.log 2 ≤ Real.log (2 + DC) := Real.log_le_log (by norm_num) (by linarith)
  have hlogDC0 : 0 < Real.log (2 + DC) := by linarith
  have hc₃1 : c₃ ≤ 1 := by linarith [h.c₃small]
  have hmul : 2 + y ≤ 2 / c₃ * (2 + DC) := by
    have e : 2 / c₃ * (2 + DC) = 4 / c₃ + 2 / c₃ * DC := by ring
    rw [e]
    have h4 : 2 ≤ 4 / c₃ := by rw [le_div_iff₀ hc₃]; linarith
    have h5 : y ≤ 2 / c₃ * DC := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc₃]; linarith
    linarith
  have hlogy : Real.log (2 + y) ≤ Real.log (2 / c₃) + Real.log (2 + DC) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) hmul
  have hlogc : Real.log (2 / c₃) ≤ 4 / c₃ * Real.log (2 + DC) := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < 2 / c₃ by positivity)
    have h2 : 4 / c₃ * (1 / 2) ≤ 4 / c₃ * Real.log (2 + DC) :=
      mul_le_mul_of_nonneg_left (hlog2.trans hlogDC) (by positivity)
    have e : 4 / c₃ * (1 / 2) = 2 / c₃ := by ring
    linarith
  have hkey : C₇ * Real.log (2 + y) ≤ C * Real.log (2 + DC) := by
    have h1 : Real.log (2 + y) ≤ (1 + 4 / c₃) * Real.log (2 + DC) := by
      have e : (1 + 4 / c₃) * Real.log (2 + DC) = Real.log (2 + DC) + 4 / c₃ * Real.log (2 + DC) := by
        ring
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hC₇.le
    have h3 := mul_le_mul_of_nonneg_right h.hC10 hlogDC0.le
    have e : C₇ * ((1 + 4 / c₃) * Real.log (2 + DC)) = C₇ * (1 + 4 / c₃) * Real.log (2 + DC) := by
      ring
    linarith
  have hlogy0 : 0 < Real.log (2 + y) := Real.log_pos (by linarith)
  have hstep : C₇ * L / Real.log (2 + DC) ≤ C * L / Real.log (2 + y) := by
    rw [div_le_div_iff₀ hlogDC0 hlogy0]
    have := mul_le_mul_of_nonneg_right hkey hL.le
    linarith [show C₇ * L * Real.log (2 + y) = C₇ * Real.log (2 + y) * L by ring,
      show C * L * Real.log (2 + DC) = C * Real.log (2 + DC) * L by ring]
  calc C₇ * Real.log (2 * ((2 * kC : ℕ) : ℝ)) / Real.log (2 + DC)
      ≤ C₇ * L / Real.log (2 + DC) := by
        apply div_le_div_of_nonneg_right _ hlogDC0.le
        exact mul_le_mul_of_nonneg_left hlogk hC₇.le
    _ ≤ C * L / Real.log (2 + y) := hstep
    _ ≤ g := h.hgirth

end Num2

/-! ### The main construction -/

/-- The statement of `T3.2a` (`deletion_step`) for a fixed constant. -/
def DelProp (cdel : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (E : Finset V)
    (c η D σ L : ℝ), 0 < c → c ≤ cdel → 0 < D → H.DegNear D η → η ≤ c * σ → H.HasGap σ →
    0 < σ → σ ≤ 1 → 10 ≤ L → (∀ x, H.degOn x E ≤ c * σ ^ (5 / 2 : ℝ) * D / L) →
    (H.induce (univ \ E)).DegNear D (2 * c * σ) ∧ (H.induce (univ \ E)).HasGap (σ / 2)

omit [Fintype V] [DecidableEq V] in
lemma exists_DelProp : ∃ c : ℝ, 0 < c ∧ DelProp.{u} c := deletion_step.{u}

/-- **The initial partition, for fixed constants.** -/
theorem core {ω εR c₇ C₇ εA cdfs δ κc K CF : ℝ}
    {C₀ c₂ c₂' c₁' cb Cb cdel c₀ ρ c₃ c₁ c C δ' : ℝ}
    (hC₀ : BipSampling.ColSampProp C₀) (hC₀0 : 0 ≤ C₀)
    (hbs : BSProp.{u} ω c₂ 4 c₁' cb Cb) (hdel : DelProp.{u} cdel)
    (hc₂le : c₂' ≤ c₂) (hc₁' : c₁' = c₂' / 40)
    (hK : 12 * C₀ ≤ K) (hK2 : 18 + 2 * δ ≤ K) (hδ'δ : δ' ≤ δ)
    (hcdel : c ≤ cdel) (hccb : 4 * c ≤ cb)
    (hc₂' : 0 < c₂') (hc₂'1 : c₂' ≤ 1) (hδ' : 0 < δ') (hδ'1 : δ' ≤ 1)
    (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1 / 40) (hc₀κ : 48 * c₀ ≤ κc)
    (hρ : 0 < ρ) (hρc₀ : ρ ≤ c₀) (hρR : ρ ≤ εR * (c₂' / 2) ^ (3 / 2 : ℝ) * c₀ / 2)
    (hρA : ρ ≤ εA * (c₂' / 2) ^ (3 / 2 : ℝ) * c₀ / 2) (hc₃ : c₃ = ρ / 16)
    (hc₁ : 0 < c₁) (hc₁ρ : 16 * c₁ ≤ ρ) (hc₁7 : 2 * c₁ ≤ c₇ * c₃)
    (hc₁d : 4 * c₁ ≤ cdfs * c₂' * c₀)
    (hc : 0 < c) (hcδ : 16 * c ≤ δ') (hcρ : 2 * c ≤ ρ) (hc₁c : 64 * c ≤ c₁)
    (hC₇ : 0 < C₇) (hεR : 0 < εR) (hεA : 0 < εA) (hc₇ : 0 < c₇) (hcdfs : 0 < cdfs)
    (hC1 : 8 * Cb ≤ c₀ * C) (hC2 : 16 * Cb ≤ c₁ * C) (hC3 : 8 * CF ≤ c₁ * C)
    (hC4 : 500 ≤ δ' ^ 2 * c₁ * C) (hC5 : 2 ≤ c₃ * C) (hC6 : 1 ≤ ρ * C) (hC7 : 1 ≤ κc * C)
    (hC8 : 1 ≤ c₀ * C) (hC9 : C₇ ≤ c₃ * C) (hC10 : C₇ * (1 + 4 / c₃) ≤ C)
    (hC11 : 16 ≤ c₁ * C) (hC : 0 < C)
    (H : WGraph V) (col : V → Bool) (N ℓ : ℕ) (η D σ L g : ℝ) (E : Finset V)
    (J : SimpleGraph V) (hyp : LocalAbsorptionHyp ω c C H col N ℓ η D σ L g E)
    (hJ : IsPerfectMatchingOn J ↑E) :
    Nonempty (InitPartition εR c₇ C₇ εA cdfs δ κc K CF H col E J (N - ℓ) D σ L g) := by
  classical
  have hbip := hyp.bipartite
  have hσ := hyp.sigma_pos
  have hσ1 : σ ≤ 1 / 10 := hyp.sigma_le
  have hL := hyp.ten_le
  have hg := hyp.four_le
  have hwle : ∀ x y, H.w x y ≤ 1 := fun x y => by
    rcases (H.nonneg x y).lt_or_eq with h | h
    · exact (hyp.weights x y h).2
    · rw [← h]; norm_num
  set X := σ ^ (5 / 2 : ℝ) with hXdef
  have hX : 0 < X := Real.rpow_pos_of_pos hσ _
  have hXσ : X ≤ σ ^ 2 := by
    rw [hXdef, ← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_ge hσ (by linarith) (by norm_num)
  have hX32 : σ ^ (3 / 2 : ℝ) * σ = X := by
    rw [hXdef, show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hσ, Real.rpow_one]
  have hdl : C * L ^ 2 * g ≤ D * X * σ ^ 2 := by
    have h1 := hyp.deg_large
    have e : σ ^ (-(9 / 2 : ℝ)) = 1 / (X * σ ^ 2) := by
      rw [hXdef, ← Real.rpow_two, ← Real.rpow_add hσ, Real.rpow_neg hσ.le, one_div]
      norm_num
    rw [e] at h1
    have hXσ2 : 0 < X * σ ^ 2 := by positivity
    rw [show C * (1 / (X * σ ^ 2)) * L ^ 2 * g = C * L ^ 2 * g / (X * σ ^ 2) by ring,
      div_le_iff₀ hXσ2] at h1
    linarith [show D * (X * σ ^ 2) = D * X * σ ^ 2 by ring]
  have hD : 0 < D := by
    have h1 : 0 < C * L ^ 2 * g := by
      have : 0 < L := by linarith
      have : 0 < g := by linarith
      positivity
    have h2 : 0 < D * (X * σ ^ 2) := by linarith [show D * (X * σ ^ 2) = D * X * σ ^ 2 by ring]
    exact (pos_iff_pos_of_mul_pos h2).2 (by positivity)
  -- the classes
  have hcolN : ∀ b, (univ.filter fun v => col v = b).card = N := by
    intro b; cases b
    · exact hyp.card_false
    · exact hyp.card_true
  have hEc : ∀ b, (E.filter fun x => col x = b).card = ℓ := by
    intro b; cases b
    · exact hyp.ends_false
    · exact hyp.ends_true
  have hℓN : ℓ ≤ N := by
    rw [← hEc true, ← hcolN true]
    exact card_le_card (filter_subset_filter _ (subset_univ E))
  have hA : ∀ b, (classOf E col b).card = N - ℓ := by
    intro b
    have h1 : univ.filter (fun v => col v = b) =
        classOf E col b ∪ E.filter (fun x => col x = b) := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_classOf]
      by_cases hx : x ∈ E <;> simp [hx]
    have h2 : Disjoint (classOf E col b) (E.filter fun x => col x = b) :=
      disjoint_left.2 fun x h1 h2 => (mem_classOf.1 h1).1 (mem_filter.1 h2).1
    have := card_union_of_disjoint h2
    rw [← h1, hcolN, hEc] at this
    omega
  -- `ℓ` is small
  have hℓ1 := hyp.one_le
  have hLg : 40 ≤ L * g := by
    have := mul_le_mul hL hg (by norm_num) (by linarith)
    linarith
  have hσ2 : σ ^ 2 ≤ 1 / 100 := by
    calc σ ^ 2 = σ * σ := sq σ
      _ ≤ (1 / 10) * (1 / 10) := mul_le_mul hσ1 hσ1 hσ.le (by norm_num)
      _ = 1 / 100 := by norm_num
  have hc16 : c ≤ 1 / 16 := by linarith
  have hℓf : (ℓ : ℝ) ≤ c * X * N / (L * g) := hyp.ends_few
  have h2ℓ : 2 * ℓ ≤ N := by
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast hℓ1.trans hℓN
    have hcX : c * X ≤ 1 / 16 := by
      have : X ≤ 1 := by linarith
      have := mul_le_mul hc16 this hX.le (by norm_num)
      linarith
    have : (ℓ : ℝ) ≤ N / 2 := by
      refine hℓf.trans ?_
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      have hN0 : (0 : ℝ) ≤ N := by linarith
      have h1 := mul_le_mul_of_nonneg_right hcX hN0
      have h2 := mul_le_mul_of_nonneg_left hLg hN0
      linarith
    have : (2 * ℓ : ℝ) ≤ N := by linarith
    exact_mod_cast this
  set N₀ := N - ℓ with hN₀def
  have hN₀ : 1 ≤ N₀ := by omega
  have hN₀r : (N₀ : ℝ) = N - ℓ := by rw [hN₀def, Nat.cast_sub hℓN]
  -- degrees into the classes
  have hEdeg := hyp.ends_sparse
  have hXL : X / L ≤ σ := by
    rw [div_le_iff₀ (by linarith)]
    have h1 : X ≤ σ := by
      have := mul_le_mul_of_nonneg_left hσ1 hσ.le
      linarith [sq σ]
    have := mul_le_mul_of_nonneg_left hL hσ.le
    linarith
  have hcσ1 : c * σ ≤ 1 / 160 := by
    have := mul_le_mul hc16 hσ1 hσ.le (by norm_num)
    linarith
  have hcls : ∀ v b, col v = !b → (1 - 2 * c * σ) * D ≤ H.degOn v (classOf E col b) ∧
      H.degOn v (classOf E col b) ≤ (1 + c * σ) * D := by
    intro v b hv
    have key : H.deg v = H.degOn v (univ \ E) + H.degOn v E := by
      unfold WGraph.deg WGraph.degOn
      rw [sum_sdiff (subset_univ E)]
    have e1 : H.degOn v (univ \ E) = H.degOn v (classOf E col b) := by
      rw [degOn_sdiff_eq H col E hbip (!b) hv, Bool.not_not]
    have hdv := abs_le.1 (hyp.degrees v)
    have hη : η * D ≤ c * σ * D := mul_le_mul_of_nonneg_right hyp.eta_le hD.le
    have hE1 := hEdeg v
    have hE0 : 0 ≤ H.degOn v E := sum_nonneg fun y _ => H.nonneg v y
    have hE2 : c * X * D / L ≤ c * σ * D := by
      have : c * X * D / L = c * D * (X / L) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hXL (mul_nonneg hc.le hD.le)
      linarith
    rw [e1] at key
    have hcσD : c * σ * D ≤ 1 / 160 * D := mul_le_mul_of_nonneg_right hcσ1 hD.le
    constructor <;> linarith
  have hDN : D ≤ 2 * N₀ := by
    obtain ⟨v, hv⟩ : (classOf E col true).Nonempty := card_pos.1 (by rw [hA]; omega)
    have h1 := (hcls v false (by rw [(mem_classOf.1 hv).2]; rfl)).1
    have h2 : H.degOn v (classOf E col false) ≤ N₀ := by
      have : H.degOn v (classOf E col false) ≤ ∑ y ∈ classOf E col false, (1 : ℝ) :=
        sum_le_sum fun y _ => hwle v y
      rw [sum_const, hA, nsmul_eq_mul, mul_one] at this
      exact this
    have := mul_le_mul_of_nonneg_right hcσ1 hD.le
    linarith
  have hcb : 2 * c * σ ≤ cb * (σ / 2) := by
    have := mul_le_mul_of_nonneg_right hccb hσ.le
    linarith
  -- deletion of `E`
  obtain ⟨hdeg₀, hgap₀⟩ := hdel H E c η D σ L hc hcdel hD hyp.degrees hyp.eta_le hyp.gap hσ
    (by linarith) hL hEdeg
  -- the orientation of `J`
  obtain ⟨tail, htail, hr1, hr2, ha, hb⟩ := exists_orientation col E J hJ ℓ (hEc true)
    (hEc false)
  set a := (E.filter fun x => (col x, tail x) = (true, true)).card with ha_def
  set b' := (E.filter fun x => (col x, tail x) = (false, true)).card with hb_def
  -- the sizes
  set s := ⌊c₀ * σ * (N₀ : ℝ)⌋₊ with hs
  set kC := ⌊c₃ * X * (N₀ : ℝ) / L⌋₊ with hkC
  set m := ⌊c₁ * X * (N₀ : ℝ) / (L * g)⌋₊ with hm
  have hnc : NumCtx εR c₇ C₇ εA cdfs κc CF Cb c₂' c₀ ρ c₃ c₁ c C δ' σ X L g D N ℓ N₀ s kC m :=
    { hσ := hσ, hσ1 := hσ1, hX := hX, hXσ := hXσ, hX32 := hX32, hL := hL, hg := hg, hD := hD
      hDN := hDN, hN₀ := hN₀
      hNN := by rw [hN₀r]; have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _; linarith
      hN2 := by
        rw [hN₀r]
        have : (2 * ℓ : ℝ) ≤ N := by exact_mod_cast h2ℓ
        linarith
      hℓ0 := Nat.cast_nonneg _, hdl := hdl, hgirth := hyp.girth_param, hℓ := hℓf
      hlogN := hyp.log_le, hs := hs, hkC := hkC, hm := hm, hc₂' := hc₂', hc₂'1 := hc₂'1
      hδ' := hδ', hδ'1 := hδ'1, hc₀ := hc₀, hc₀1 := hc₀1, hc₀κ := hc₀κ, hρ := hρ
      hρc₀ := hρc₀, hρR := hρR, hρA := hρA, hc₃ := hc₃, hc₁ := hc₁, hc₁ρ := hc₁ρ
      hc₁7 := hc₁7, hc₁d := hc₁d, hc := hc, hcδ := hcδ, hcρ := hcρ, hc₁c := hc₁c
      hC₇ := hC₇, hεR := hεR, hεA := hεA, hc₇ := hc₇, hcdfs := hcdfs, hC1 := hC1
      hC2 := hC2, hC3 := hC3, hC4 := hC4, hC5 := hC5, hC6 := hC6, hC7 := hC7, hC8 := hC8
      hC9 := hC9, hC10 := hC10, hC11 := hC11, hC := hC }
  have hm8 := hnc.m8
  have hℓm := hnc.ℓm
  have ha8 : 8 * a ≤ m := by
    have : (8 * a : ℝ) ≤ m := by
      have : (a : ℝ) ≤ ℓ := by exact_mod_cast ha
      linarith
    exact_mod_cast this
  have hb8 : 8 * b' ≤ m := by
    have : (8 * b' : ℝ) ≤ m := by
      have : (b' : ℝ) ≤ ℓ := by exact_mod_cast hb
      linarith
    exact_mod_cast this
  have hsize : 3 * s + kC + 9 * m ≤ N₀ := by exact_mod_cast hnc.size
  -- the base labeling
  obtain ⟨κ₀, hκ₀E, hsz₀⟩ := exists_base_labeling col E (szFun N₀ s kC m a b')
    (fun b => by cases b <;> rfl)
    (fun b => by rw [sum_szFun N₀ s kC m a b' (by omega) (by omega) (by omega), hA])
  -- the events
  set thr := thrFun ((s : ℝ) / N₀ * D) ((kC : ℝ) / N₀ * D) (δ' * σ * ((m : ℝ) / N₀ * D) / 4)
    (ρ * X * D / (4 * L)) (κc * σ * D / 4) with hthr
  have hpairC : ∀ b (j : PB), (blk col κ₀ b j.c₁).card = (blk col κ₀ (!b) j.c₂).card ∧
      Cb * (σ / 2) ^ (-2 : ℝ) * L ≤ ((blk col κ₀ b j.c₁).card : ℝ) / N₀ * D := by
    intro b j
    rw [card_PB₁ hsz₀, card_PB₂ hsz₀]
    refine ⟨rfl, ?_⟩
    cases j
    · cases b <;> exact hnc.pair_s
    · cases b <;> exact hnc.pair_s
    · cases b <;> exact hnc.pair_s
    · cases b
      · refine hnc.pair_fill _ ?_
        simp only [pbSize]
        have : (b' : ℝ) ≤ m / 8 := by
          have : (8 * b' : ℝ) ≤ m := by exact_mod_cast hb8
          linarith
        rw [Nat.cast_sub (by omega)]
        linarith
      · refine hnc.pair_fill _ ?_
        simp only [pbSize]
        have : (a : ℝ) ≤ m / 8 := by
          have : (8 * a : ℝ) ≤ m := by exact_mod_cast ha8
          linarith
        have hm8r : (8 : ℝ) ≤ m := by exact_mod_cast hm8
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast
        linarith
  have hthr' : ∀ b (d : DB), 0 < thr d ∧ 12 * L * (((blk col κ₀ b d.cells).card : ℝ) / N₀ *
      ((1 + c * σ) * D) + thr d) ≤ thr d ^ 2 := by
    intro b d
    rw [card_DB hsz₀ (by omega) (by omega)]
    cases d
    · exact hnc.thr_att
    · exact hnc.thr_att
    · exact hnc.thr_cyc
    · exact hnc.thr_lay
    · exact hnc.thr_lay
    · exact hnc.thr_lay
    · exact hnc.thr_lay
    · exact hnc.thr_wide
    · exact hnc.thr_env
  obtain ⟨π, hπ, hP1, hP2, hP3⟩ := exists_good_perm hbs hC₀ H col E N N₀ D σ L c thr κ₀ hκ₀E
    hbip hyp.weights hwle hA hN₀ (by omega) hcolN hσ (by linarith) hD hDN hc.le
    (by linarith) hL hyp.log_le hcls hgap₀ hdeg₀ hcb hpairC hthr'
  -- the permuted labeling
  set κ : V → SC := fun x => κ₀ (π⁻¹ x) with hκ
  have hκE : ∀ x, κ x = SC.ends ↔ x ∈ E := by
    intro x
    rw [hκ]
    simp only
    rw [hκ₀E]
    have := (mem_permG.1 (inv_mem_permG hπ) x).2
    constructor
    · intro h
      have h2 := (mem_permG.1 hπ (π⁻¹ x)).2 h
      simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at h2
      have h3 : π⁻¹ x = x := h2.symm
      rw [← h3]; exact h
    · intro h; rw [this h]; exact h
  have hsz : ∀ b c', c' ≠ SC.ends → (blk col κ b {c'}).card = szFun N₀ s kC m a b' b c' := by
    intro b c' hc'
    rw [hκ, blk_perm hπ, card_image_of_injective _ π.injective]
    exact hsz₀ b c' hc'
  have hrole : ∀ r : Bool × Bool, (E.filter fun x => (col x, tail x) = r).card =
      (blk col κ r.1 {if r.2 then SC.uP else SC.vP}).card := by
    rintro ⟨b, t⟩
    rw [hsz b _ (by cases t <;> simp)]
    cases b <;> cases t
    · simp only [↓reduceIte, Bool.false_eq_true]; rw [hr2]; rfl
    · simp only [↓reduceIte]; rfl
    · simp only [↓reduceIte, Bool.false_eq_true]; rw [hr1]; rfl
    · simp only [↓reduceIte]; rfl
  -- assembly
  have hsp := hnc.sparse εR 0 c₁' hρR hεR (by linarith) (by rw [hc₁']; positivity)
  simp only [zero_mul, zero_div, zero_add] at hsp
  have hnK : C₀ * Real.sqrt (24 * D) * Real.sqrt (6 * L) ≤ K * Real.sqrt (D * L) := by
    have e : Real.sqrt (24 * D) * Real.sqrt (6 * L) = 12 * Real.sqrt (D * L) := by
      rw [← Real.sqrt_mul (by positivity), show 24 * D * (6 * L) = 12 ^ 2 * (D * L) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rw [mul_assoc, e]
    have := mul_le_mul_of_nonneg_right hK (Real.sqrt_nonneg (D * L))
    linarith
  exact build (c₁' := c₁') (c₂ := c₂) (c₂' := c₂') (C₀ := C₀) (δ' := δ')
    (tW := ρ * X * D / (4 * L)) (tE := κc * σ * D / 4)
    H col E J N₀ D σ L g s kC m a b' κ tail hbip hwle hA hN₀ hσ hσ1 hD hDN hc.le
    (by linarith) hcls hEdeg hκE hsz htail hrole hP1 hP2 hP3 hm8 ha8 hb8 hsize hnc.s1
    hc₂' hc₂'1 hc₂le hc₁' hnc.cycDC hnc.girth hnc.many hnc.rtrlog hnc.wideP hsp
    (hnc.sparse εA c c₁' hρA hεA hcρ (by rw [hc₁']; positivity)) hnc.div hC₀0 hnK hK2 hδ'
    hδ'1 hδ'δ hcδ hnc.layer hnc.envP (by linarith) hnc.envc

omit [Fintype V] [DecidableEq V] in
/-- The choice of the constants of the proof. -/
lemma choose_consts (εR c₇ C₇ εA cdfs δ κ c₂' cdel cb Cb CF : ℝ) (hεR : 0 < εR) (hc₇ : 0 < c₇)
    (hC₇ : 0 < C₇) (hεA : 0 < εA) (hcdfs : 0 < cdfs) (hδ : 0 < δ) (hκ : 0 < κ) (hc₂' : 0 < c₂')
    (hcdel : 0 < cdel) (hcb : 0 < cb) (hCb : 0 < Cb) (hCF : 0 < CF) :
    ∃ δ' c₀ ρ c₃ c₁ c C : ℝ, δ' ≤ δ ∧ c ≤ cdel ∧ 4 * c ≤ cb ∧ 0 < δ' ∧ δ' ≤ 1 ∧ 0 < c₀ ∧
      c₀ ≤ 1 / 40 ∧ 48 * c₀ ≤ κ ∧ 0 < ρ ∧ ρ ≤ c₀ ∧
      ρ ≤ εR * (c₂' / 2) ^ (3 / 2 : ℝ) * c₀ / 2 ∧ ρ ≤ εA * (c₂' / 2) ^ (3 / 2 : ℝ) * c₀ / 2 ∧
      c₃ = ρ / 16 ∧ 0 < c₁ ∧ 16 * c₁ ≤ ρ ∧ 2 * c₁ ≤ c₇ * c₃ ∧ 4 * c₁ ≤ cdfs * c₂' * c₀ ∧
      0 < c ∧ 16 * c ≤ δ' ∧ 2 * c ≤ ρ ∧ 64 * c ≤ c₁ ∧ 8 * Cb ≤ c₀ * C ∧ 16 * Cb ≤ c₁ * C ∧
      8 * CF ≤ c₁ * C ∧ 500 ≤ δ' ^ 2 * c₁ * C ∧ 2 ≤ c₃ * C ∧ 1 ≤ ρ * C ∧ 1 ≤ κ * C ∧
      1 ≤ c₀ * C ∧ C₇ ≤ c₃ * C ∧ C₇ * (1 + 4 / c₃) ≤ C ∧ 16 ≤ c₁ * C ∧ 0 < C := by
  obtain ⟨δ', hδ'⟩ : ∃ x : ℝ, x = min δ 1 := ⟨_, rfl⟩
  have hδ'1 : δ' ≤ δ := by rw [hδ']; exact min_le_left _ _
  have hδ'2 : δ' ≤ 1 := by rw [hδ']; exact min_le_right _ _
  have hδ'0 : 0 < δ' := by rw [hδ']; exact lt_min hδ one_pos
  obtain ⟨c₀, hc₀⟩ : ∃ x : ℝ, x = min (κ / 48) (1 / 40) := ⟨_, rfl⟩
  have hc₀1 : c₀ ≤ κ / 48 := by rw [hc₀]; exact min_le_left _ _
  have hc₀2 : c₀ ≤ 1 / 40 := by rw [hc₀]; exact min_le_right _ _
  have hc₀0 : 0 < c₀ := by rw [hc₀]; exact lt_min (by positivity) (by norm_num)
  obtain ⟨A, hA⟩ : ∃ x : ℝ, x = (c₂' / 2) ^ (3 / 2 : ℝ) := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; exact Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨ρ, hρ⟩ : ∃ x : ℝ, x = min (min εR εA * A * c₀ / 2) c₀ := ⟨_, rfl⟩
  have hρ1 : ρ ≤ min εR εA * A * c₀ / 2 := by rw [hρ]; exact min_le_left _ _
  have hρ2 : ρ ≤ c₀ := by rw [hρ]; exact min_le_right _ _
  have hmin0 : 0 < min εR εA := lt_min hεR hεA
  have hρ0 : 0 < ρ := by rw [hρ]; exact lt_min (by positivity) hc₀0
  have hAc : 0 ≤ A * c₀ / 2 := by positivity
  have hρR : ρ ≤ εR * A * c₀ / 2 := by
    have := mul_le_mul_of_nonneg_right (min_le_left εR εA) hAc
    linarith [show min εR εA * A * c₀ / 2 = min εR εA * (A * c₀ / 2) by ring,
      show εR * A * c₀ / 2 = εR * (A * c₀ / 2) by ring]
  have hρA : ρ ≤ εA * A * c₀ / 2 := by
    have := mul_le_mul_of_nonneg_right (min_le_right εR εA) hAc
    linarith [show min εR εA * A * c₀ / 2 = min εR εA * (A * c₀ / 2) by ring,
      show εA * A * c₀ / 2 = εA * (A * c₀ / 2) by ring]
  obtain ⟨c₃, hc₃⟩ : ∃ x : ℝ, x = ρ / 16 := ⟨_, rfl⟩
  have hc₃0 : 0 < c₃ := by rw [hc₃]; positivity
  obtain ⟨c₁, hc₁⟩ : ∃ x : ℝ, x = min (min (ρ / 16) (c₇ * c₃ / 2)) (cdfs * c₂' * c₀ / 4) :=
    ⟨_, rfl⟩
  have hc₁1 : c₁ ≤ ρ / 16 := by rw [hc₁]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hc₁2 : c₁ ≤ c₇ * c₃ / 2 := by rw [hc₁]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hc₁3 : c₁ ≤ cdfs * c₂' * c₀ / 4 := by rw [hc₁]; exact min_le_right _ _
  have hc₁0 : 0 < c₁ := by
    rw [hc₁]; exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  obtain ⟨c, hc⟩ : ∃ x : ℝ, x = min (min cdel (cb / 4)) (min (δ' / 16) (min (ρ / 2) (c₁ / 64))) :=
    ⟨_, rfl⟩
  have hc1 : c ≤ cdel := by rw [hc]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ cb / 4 := by rw [hc]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ δ' / 16 := by rw [hc]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hc4 : c ≤ ρ / 2 := by
    rw [hc]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc5 : c ≤ c₁ / 64 := by
    rw [hc]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc0 : 0 < c := by
    rw [hc]
    exact lt_min (lt_min hcdel (by positivity))
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  obtain ⟨C, hC⟩ : ∃ x : ℝ, x = 8 * Cb / c₀ + 16 * Cb / c₁ + 8 * CF / c₁ + 500 / (δ' ^ 2 * c₁) +
      2 / c₃ + 1 / ρ + 1 / κ + 1 / c₀ + C₇ / c₃ + C₇ * (1 + 4 / c₃) + 16 / c₁ := ⟨_, rfl⟩
  have t1 : 0 ≤ 8 * Cb / c₀ := by positivity
  have t2 : 0 ≤ 16 * Cb / c₁ := by positivity
  have t3 : 0 ≤ 8 * CF / c₁ := by positivity
  have t4 : 0 ≤ 500 / (δ' ^ 2 * c₁) := by positivity
  have t5 : 0 ≤ 2 / c₃ := by positivity
  have t6 : 0 ≤ 1 / ρ := by positivity
  have t7 : 0 ≤ 1 / κ := by positivity
  have t8 : 0 ≤ 1 / c₀ := by positivity
  have t9 : 0 ≤ C₇ / c₃ := by positivity
  have t10 : 0 ≤ C₇ * (1 + 4 / c₃) := by positivity
  have t11 : 0 < 16 / c₁ := by positivity
  have mulb : ∀ {x y : ℝ}, 0 < y → x / y ≤ C → x ≤ y * C := fun {x y} hy h => by
    rw [div_le_iff₀ hy] at h; linarith
  refine ⟨δ', c₀, ρ, c₃, c₁, c, C, hδ'1, hc1, by linarith, hδ'0, hδ'2, hc₀0, hc₀2,
    by linarith, hρ0, hρ2, by rw [← hA]; exact hρR, by rw [← hA]; exact hρA, hc₃, hc₁0,
    by linarith, by linarith, by linarith, hc0, by linarith, by linarith, by linarith,
    mulb hc₀0 (by rw [hC]; linarith), mulb hc₁0 (by rw [hC]; linarith),
    mulb hc₁0 (by rw [hC]; linarith),
    by have := mulb (show 0 < δ' ^ 2 * c₁ by positivity)
         (show 500 / (δ' ^ 2 * c₁) ≤ C by rw [hC]; linarith)
       linarith,
    mulb hc₃0 (by rw [hC]; linarith),
    by have := mulb hρ0 (show 1 / ρ ≤ C by rw [hC]; linarith); linarith,
    by have := mulb hκ (show 1 / κ ≤ C by rw [hC]; linarith); linarith,
    by have := mulb hc₀0 (show 1 / c₀ ≤ C by rw [hC]; linarith); linarith,
    by have := mulb hc₃0 (show C₇ / c₃ ≤ C by rw [hC]; linarith); linarith,
    by rw [hC]; linarith, mulb hc₁0 (by rw [hC]; linarith), by rw [hC]; linarith⟩

end InitPart

/-- **`T3.2b` (the initial random partition).** For all constants of the later steps there are
`c, C` such that, under the hypotheses of Theorem 3.2 with `c, C`, for every perfect matching
`J` of `E` an initial partition with all the required events exists. (Paper: "Ordinary
concentration and a union bound establish all the events just listed", using Lemmas 2.2, 2.3
and the scalar Chernoff bounds.) -/
theorem initial_partition (ω : ℝ) (hω : 0 < ω) (εR c₇ C₇ εA cdfs δ κ : ℝ) (hεR : 0 < εR)
    (hc₇ : 0 < c₇) (hC₇ : 0 < C₇) (hεA : 0 < εA) (hcdfs : 0 < cdfs) (hδ : 0 < δ)
    (hκ : 0 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ CF : ℝ, 0 < CF → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (col : V → Bool) (N ℓ : ℕ)
        (η D σ L g : ℝ) (E : Finset V) (J : SimpleGraph V),
        LocalAbsorptionHyp ω c C H col N ℓ η D σ L g E → IsPerfectMatchingOn J ↑E →
        Nonempty (InitPartition εR c₇ C₇ εA cdfs δ κ K CF H col E J (N - ℓ) D σ L g) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := BipSampling.exists_colSampProp
  obtain ⟨c₂, hc₂, hbsall⟩ := InitPart.exists_BSProp.{u} ω hω
  have hc₂'pos : 0 < min c₂ 1 := lt_min hc₂ one_pos
  obtain ⟨cb, Cb, hcb, hCb, hbs⟩ := hbsall 4 (min c₂ 1 / 40) (by norm_num) (by positivity)
  obtain ⟨cdel, hcdel, hdel⟩ := InitPart.exists_DelProp.{u}
  refine ⟨12 * C₀ + (18 + 2 * δ), by positivity, fun CF hCF => ?_⟩
  obtain ⟨δ', c₀, ρ, c₃, c₁, c, C, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31,
    h32, h33⟩ := InitPart.choose_consts εR c₇ C₇ εA cdfs δ κ (min c₂ 1) cdel cb Cb CF hεR hc₇
      hC₇ hεA hcdfs hδ hκ hc₂'pos hcdel hcb hCb hCF
  refine ⟨c, C, h18, h33, ?_⟩
  intro V _ _ H col N ℓ η D σ L g E J hyp hJ
  exact InitPart.core hC₀ hC₀pos.le hbs hdel (min_le_left _ _) rfl (by linarith) (by linarith)
    h1 h2 h3 hc₂'pos (min_le_right _ _) h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
    h19 h20 h21 hC₇ hεR hεA hc₇ hcdfs h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 H col N ℓ
    η D σ L g E J hyp hJ

end LocalAbsorption

end Lovasz
