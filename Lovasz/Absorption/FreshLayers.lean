/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.Absorption.FixedBoundary

/-!
# `T3.2f`: fresh layers of Section 3.3

DAG node `T3.2f` of `docs/BLUEPRINT.md` (uses Lemma 2.4, `Lovasz/Absorption/FixedBoundary.lean`).

The proof follows paper p. 11. The pool is equipartitioned independently in the two colour
classes, through a uniform ordering of each class (`lay`); every layer, and every pair of layers
of opposite colours, is then a uniform `m`-subset, respectively a uniform pair of `m`-subsets
(`lay_fibre`, `count_pair`). Fixed–fresh transitions use Lemma 2.4 (`fixed_count`, after
weakening the one-sided constants to fixed values in `oneSided_weaken`), fresh–fresh transitions
use Lemma 2.3 on the pool graph `H[P]` (`fresh_count`, with the gap of `H[P]` from Lemma 2.1 in
`pool_gap`), and the swapped endpoints `zA, zB` use a hypergeometric tail (`z_count`). A union
bound over the `10 + 2(t - 2)` events (`layers_exist`) gives a good equipartition. The sampled
estimates give perfect matchings by Lemma 2.5 (`plain_match`, and `swap_match` for the
enlargement by the swapped endpoint), and the matchings of consecutive layers form the grid
(`assemble`).
-/

universe u

namespace Lovasz

open Finset

namespace LocalAbsorption

namespace FreshLayers

/-! ### Transport of degrees and gaps along isomorphisms -/

section Transport

variable {W₁ W₂ : Type*} [Fintype W₁] [Fintype W₂]

lemma deg_equiv (G₁ : WGraph W₁) (G₂ : WGraph W₂) (e : W₁ ≃ W₂)
    (h : ∀ x y, G₂.w (e x) (e y) = G₁.w x y) (x : W₁) : G₂.deg (e x) = G₁.deg x := by
  unfold WGraph.deg
  rw [← e.sum_comp]
  exact sum_congr rfl fun y _ => h x y

lemma degNear_equiv (G₁ : WGraph W₁) (G₂ : WGraph W₂) (e : W₁ ≃ W₂)
    (h : ∀ x y, G₂.w (e x) (e y) = G₁.w x y) {D η : ℝ} (hD : G₁.DegNear D η) :
    G₂.DegNear D η := by
  intro y
  rw [← e.apply_symm_apply y, deg_equiv G₁ G₂ e h]
  exact hD _

lemma hasGap_equiv (G₁ : WGraph W₁) (G₂ : WGraph W₂) (e : W₁ ≃ W₂)
    (h : ∀ x y, G₂.w (e x) (e y) = G₁.w x y) {σ : ℝ} (hg : G₁.HasGap σ) : G₂.HasGap σ := by
  intro f
  obtain ⟨z, hz⟩ := hg (fun x => f (e x))
  refine ⟨z, ?_⟩
  have h1 : ∑ y, G₂.deg y * (f y - z) ^ 2 = ∑ x, G₁.deg x * (f (e x) - z) ^ 2 := by
    rw [← e.sum_comp]
    exact sum_congr rfl fun x _ => by rw [deg_equiv G₁ G₂ e h]
  have h2 : G₂.dirichlet f = G₁.dirichlet (fun x => f (e x)) := by
    unfold WGraph.dirichlet
    congr 1
    rw [← e.sum_comp]
    refine sum_congr rfl fun x _ => ?_
    rw [← e.sum_comp]
    exact sum_congr rfl fun y _ => by rw [h]
  rw [h1, h2]
  exact hz

/-- `↥T ≃ ↥T'` when `T'` is the image of `T : Finset (Subtype p)` in the ambient type. -/
noncomputable def mapEquiv {α : Type*} {p : α → Prop} (T : Finset (Subtype p)) (T' : Finset α)
    (h : T.map (Function.Embedding.subtype p) = T') : ↥T ≃ ↥T' :=
  Equiv.ofBijective (fun x => ⟨x.1.1, by rw [← h]; exact mem_map_of_mem _ x.2⟩) (by
    constructor
    · intro x y hxy
      simp only [Subtype.mk.injEq] at hxy
      exact Subtype.ext (Subtype.ext hxy)
    · rintro ⟨y, hy⟩
      rw [← h] at hy
      obtain ⟨a, ha, rfl⟩ := mem_map.1 hy
      exact ⟨⟨a, ha⟩, rfl⟩)

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
lemma degNear_map (G : WGraph α) (S : Finset α) (T : Finset ↥S) (T' : Finset α)
    (h : T.map (Function.Embedding.subtype _) = T') {D η : ℝ}
    (hd : ((G.induce S).induce T).DegNear D η) : (G.induce T').DegNear D η :=
  degNear_equiv _ _ (mapEquiv T T' h) (fun _ _ => rfl) hd

omit [Fintype α] [DecidableEq α] in
lemma hasGap_map (G : WGraph α) (S : Finset α) (T : Finset ↥S) (T' : Finset α)
    (h : T.map (Function.Embedding.subtype _) = T') {σ : ℝ}
    (hd : ((G.induce S).induce T).HasGap σ) : (G.induce T').HasGap σ :=
  hasGap_equiv _ _ (mapEquiv T T' h) (fun _ _ => rfl) hd

omit [Fintype α] [DecidableEq α] in
lemma induce_deg_eq (G : WGraph α) (T : Finset α) (x : ↥T) :
    (G.induce T).deg x = G.degOn x T := by
  unfold WGraph.deg WGraph.degOn
  exact sum_coe_sort T (fun y => G.w x y)

omit [Fintype α] in
/-- Cut density of an induced graph, in ambient form. -/
lemma cut_ambient (G : WGraph α) (T : Finset α) {ξ : ℝ} (h : (G.induce T).IsCutDense ξ)
    (A : Finset α) (hA : A ⊆ T) :
    ξ * A.card * (T \ A).card ≤ G.edgeWeight A (T \ A) := by
  set A' : Finset ↥T := A.subtype (· ∈ T) with hA'
  have h1 : A'.map (Function.Embedding.subtype _) = A := by
    rw [hA', subtype_map]; exact filter_true_of_mem hA
  have h2 : (univ \ A').map (Function.Embedding.subtype _) = T \ A := by
    ext y
    simp only [mem_map, mem_sdiff, mem_univ, true_and, Function.Embedding.coe_subtype, hA',
      mem_subtype]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2, ha⟩
    · rintro ⟨hy, hy'⟩
      exact ⟨⟨y, hy⟩, hy', rfl⟩
  have hc := h A'
  have e1 : A'.card = A.card := by rw [← h1, card_map]
  have e2 : (univ \ A').card = (T \ A).card := by rw [← h2, card_map]
  have e3 : (G.induce T).edgeWeight A' (univ \ A') = G.edgeWeight A (T \ A) := by
    unfold WGraph.edgeWeight
    calc ∑ x ∈ A', ∑ y ∈ univ \ A', (G.induce T).w x y
        = ∑ x ∈ A', ∑ y ∈ T \ A, G.w x y := by
          refine sum_congr rfl fun x _ => ?_
          have := sum_map (univ \ A') (Function.Embedding.subtype _) (fun y => G.w x y)
          rw [h2] at this
          exact this.symm
      _ = ∑ x ∈ A, ∑ y ∈ T \ A, G.w x y := by
          have := sum_map A' (Function.Embedding.subtype _) (fun x => ∑ y ∈ T \ A, G.w x y)
          rw [h1] at this
          exact this.symm
  rw [e1, e2, e3] at hc
  exact hc

end Transport

/-! ### Perfect matchings from the sampled estimates (Lemma 2.5) -/

section Matching

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- Cut density survives the deletion of a few vertices: if every vertex of the core `C ⊆ T`
has weight at most `β` into `T \ C`, and `4 β ≤ ξ |T|`, then the core is `ξ/2`-cut-dense. -/
lemma cut_core (G : WGraph α) (T C : Finset α) (hC : C ⊆ T) {ξ β : ℝ} (hξ : 0 ≤ ξ)
    (hcut : ∀ A ⊆ T, ξ * A.card * (T \ A).card ≤ G.edgeWeight A (T \ A))
    (hβ : ∀ v ∈ C, G.degOn v (T \ C) ≤ β) (hTβ : 4 * β ≤ ξ * T.card) :
    ∀ A ⊆ C, ξ / 2 * A.card * (C \ A).card ≤ G.edgeWeight A (C \ A) := by
  have small : ∀ A ⊆ C, 2 * A.card ≤ C.card →
      ξ / 2 * A.card * (C \ A).card ≤ G.edgeWeight A (C \ A) := by
    intro A hA h2
    have hsplit : T \ A = (C \ A) ∪ (T \ C) := by
      ext x
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨hx, hxA⟩
        by_cases hxC : x ∈ C
        · exact Or.inl ⟨hxC, hxA⟩
        · exact Or.inr ⟨hx, hxC⟩
      · rintro (⟨hxC, hxA⟩ | ⟨hx, hxC⟩)
        · exact ⟨hC hxC, hxA⟩
        · exact ⟨hx, fun h => hxC (hA h)⟩
    have hdisj : Disjoint (C \ A) (T \ C) :=
      disjoint_left.2 fun x h1 h2 => (mem_sdiff.1 h2).2 (mem_sdiff.1 h1).1
    have he := hcut A (hA.trans hC)
    rw [hsplit, RobustHall.eW_union_right G A hdisj] at he
    have hle : G.edgeWeight A (T \ C) ≤ A.card * β :=
      RobustHall.eW_le_of_deg_le G fun a ha => hβ a (hA ha)
    have hcardTA : ((T \ A).card : ℝ) = T.card - A.card := by
      rw [card_sdiff_of_subset (hA.trans hC), Nat.cast_sub (card_le_card (hA.trans hC))]
    have hCT : (C.card : ℝ) ≤ T.card := by exact_mod_cast card_le_card hC
    have hCA : ((C \ A).card : ℝ) ≤ (T \ A).card := by
      exact_mod_cast card_le_card (sdiff_subset_sdiff hC le_rfl)
    have h2' : (2 * A.card : ℝ) ≤ C.card := by exact_mod_cast h2
    have hA0 : (0 : ℝ) ≤ A.card := by positivity
    have key : 2 * β ≤ ξ * (T \ A).card := by
      rw [hcardTA]; nlinarith
    have hsplit' : ((T \ A).card : ℝ) = (C \ A).card + (T \ C).card := by
      rw [hsplit, card_union_of_disjoint hdisj, Nat.cast_add]
    rw [card_union_of_disjoint hdisj, Nat.cast_add] at he
    have hk : (A.card : ℝ) * β ≤ A.card * (ξ * ((C \ A).card + (T \ C).card) / 2) :=
      mul_le_mul_of_nonneg_left (by rw [← hsplit']; linarith) hA0
    have hy : 0 ≤ ξ * A.card * (T \ C).card := by positivity
    nlinarith
  intro A hA
  by_cases h2 : 2 * A.card ≤ C.card
  · exact small A hA h2
  · have hA' : C \ A ⊆ C := sdiff_subset
    have hcard : (C \ A).card + A.card = C.card := card_sdiff_add_card_eq_card hA
    have := small (C \ A) hA' (by omega)
    rw [Finset.sdiff_sdiff_eq_self hA, RobustHall.eW_comm] at this
    linarith

omit [Fintype α] in
lemma degOn_union_of_zero (G : WGraph α) {X Y : Finset α} (hXY : Disjoint X Y) (v : α)
    (h : ∀ y ∈ X, G.w v y = 0) : G.degOn v (X ∪ Y) = G.degOn v Y := by
  unfold WGraph.degOn
  rw [sum_union hXY, sum_eq_zero h, zero_add]

omit [Fintype α] in
lemma degOn_erase_add (G : WGraph α) {X : Finset α} {a : α} (ha : a ∈ X) (v : α) :
    G.degOn v (X.erase a) + G.w v a = G.degOn v X := by
  unfold WGraph.degOn
  exact sum_erase_add X _ ha

omit [Fintype α] in
lemma bijOn_of_injOn_card {s t : Finset α} {g : α → α} (hmaps : ∀ x ∈ s, g x ∈ t)
    (hinj : Set.InjOn g ↑s) (hcard : t.card ≤ s.card) : Set.BijOn g ↑s ↑t := by
  have himg : s.image g ⊆ t := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    exact hmaps x hx
  have heq : s.image g = t :=
    eq_of_subset_of_card_le himg (by rw [card_image_of_injOn hinj]; exact hcard)
  refine ⟨fun x hx => hmaps x hx, hinj, fun y hy => ?_⟩
  rw [mem_coe, ← heq] at hy
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
  exact ⟨x, hx, rfl⟩

/-- **Transition with a swapped vertex** (the enlargement step of Lemma 2.5). Let
`H[U ∪ W]` (with `U, W` independent, `|U| = |W| = m ≥ 2`) have degrees `(1 ± η) D₀` and gap
`σ`, with `η ≤ σ/400` and `D₀ ≥ 400/σ`. Replace `d ∈ U` by a vertex `z` (possibly `z = d`)
with `d(z, W) ≥ D₀/2 + 1`. Then `insert z (U \ {d})` is perfectly matched onto `W`. -/
theorem swap_match (G : WGraph α) (hw1 : ∀ x y, G.w x y ≤ 1) (U W : Finset α) (m : ℕ)
    (d z : α) (D₀ η σ : ℝ) (hUW : Disjoint U W) (hU : U.card = m) (hW : W.card = m)
    (hm : 2 ≤ m) (hbU : ∀ x ∈ U, ∀ y ∈ U, G.w x y = 0) (hbW : ∀ x ∈ W, ∀ y ∈ W, G.w x y = 0)
    (hd : d ∈ U) (hzU : z ∉ U.erase d) (hzW : z ∉ W)
    (hdeg : (G.induce (U ∪ W)).DegNear D₀ η) (hgap : (G.induce (U ∪ W)).HasGap σ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hη0 : 0 ≤ η) (hη : η ≤ σ / 400) (hD₀ : 400 / σ ≤ D₀)
    (hz : D₀ / 2 + 1 ≤ G.degOn z W) :
    ∃ g : α → α, Set.BijOn g ↑(insert z (U.erase d)) ↑W ∧
      ∀ x ∈ insert z (U.erase d), G.supp.Adj x (g x) := by
  have hσD : 400 ≤ σ * D₀ := by
    rw [div_le_iff₀ hσ] at hD₀; linarith
  have hD₀ : 0 < D₀ := by nlinarith
  have hinv : 1 / D₀ ≤ σ / 400 := by
    rw [div_le_div_iff₀ hD₀ (by norm_num)]; linarith
  have hη1 : η ≤ 1 / 400 := by linarith [div_le_div_of_nonneg_right hσ1 (by norm_num : (0:ℝ) ≤ 400)]
  obtain ⟨f₀, hf₀⟩ : W.Nonempty := card_pos.1 (by omega)
  set T := U ∪ W with hT
  set L₀ := U.erase d with hL₀
  set R₀ := W.erase f₀ with hR₀
  have hTcard : T.card = 2 * m := by rw [hT, card_union_of_disjoint hUW, hU, hW]; ring
  -- degrees in `T`
  have hdegT : ∀ v ∈ T, |G.degOn v T - D₀| ≤ η * D₀ := fun v hv => by
    have := hdeg ⟨v, hv⟩
    rwa [induce_deg_eq] at this
  have hdU : ∀ v ∈ U, G.degOn v T = G.degOn v W := fun v hv =>
    degOn_union_of_zero G hUW v fun y hy => hbU v hv y hy
  have hdW : ∀ v ∈ W, G.degOn v T = G.degOn v U := fun v hv => by
    rw [hT, union_comm]; exact degOn_union_of_zero G hUW.symm v fun y hy => hbW v hv y hy
  have hwnn : ∀ x y, 0 ≤ G.w x y := G.nonneg
  -- cut density of `T`
  have hDB : (G.induce T).DegBetween ((1 - η) * D₀) ((1 + η) * D₀) := fun x => by
    have := abs_le.1 (hdeg x)
    constructor <;> nlinarith
  have hcd := WGraph.isCutDense_of_hasGap (G.induce T) hgap hσ.le (by linarith) hD₀ hDB
  rw [Fintype.card_coe, hTcard] at hcd
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  set ξ₁ : ℝ := σ * D₀ / (4 * m) with hξ₁
  have hξ₁le : ξ₁ ≤ σ * (1 - η) ^ 2 * D₀ / ((1 + η) * ((2 * m : ℕ) : ℝ)) := by
    rw [hξ₁, div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    have h1 : (1 + η) ≤ 2 * (1 - η) ^ 2 := by nlinarith
    have h2 : 0 ≤ σ * D₀ * m := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have hξ₁0 : 0 ≤ ξ₁ := by positivity
  have hcutT : ∀ A ⊆ T, ξ₁ * A.card * (T \ A).card ≤ G.edgeWeight A (T \ A) := by
    intro A hA
    refine le_trans ?_ (cut_ambient G T hcd A hA)
    have : (0 : ℝ) ≤ A.card * (T \ A).card := by positivity
    nlinarith
  -- the core
  have hdf : d ≠ f₀ := fun h => disjoint_left.1 hUW hd (h ▸ hf₀)
  have hCsub : L₀ ∪ R₀ ⊆ T := union_subset_union (erase_subset _ _) (erase_subset _ _)
  have hTC : T \ (L₀ ∪ R₀) ⊆ {d, f₀} := by
    intro x hx
    simp only [mem_sdiff, mem_union, hL₀, hR₀, mem_erase, not_or, not_and, hT] at hx
    simp only [mem_insert, mem_singleton]
    rcases hx.1 with h | h
    · left; by_contra hne; exact hx.2.1 hne h
    · right; by_contra hne; exact hx.2.2 hne h
  have hβ : ∀ v ∈ L₀ ∪ R₀, G.degOn v (T \ (L₀ ∪ R₀)) ≤ 1 := by
    intro v hv
    refine le_trans (degOn_mono G v hTC) ?_
    unfold WGraph.degOn
    rw [sum_pair hdf]
    rcases mem_union.1 hv with h | h
    · rw [hbU v (mem_of_mem_erase h) d hd, zero_add]; exact hw1 _ _
    · rw [hbW v (mem_of_mem_erase h) f₀ hf₀, add_zero]; exact hw1 _ _
  have hcore := cut_core G T (L₀ ∪ R₀) hCsub hξ₁0 hcutT hβ (by
    rw [hTcard, hξ₁]; push_cast
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith)
  -- the parameters of Lemma 2.5
  have hm1 : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hm2 : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm1pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by rw [hm1]; linarith
  set ξ : ℝ := σ * D₀ / (16 * ((m - 1 : ℕ) : ℝ)) with hξ
  have hα : ξ * ((m - 1 : ℕ) : ℝ) / D₀ = σ / 16 := by
    rw [hξ]; field_simp
  have hξle : ξ ≤ ξ₁ / 2 := by
    rw [hξ, hξ₁, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2:ℝ) ≤ m := by exact_mod_cast hm
    have h2 : (m : ℝ) ≤ 2 * ((m - 1 : ℕ) : ℝ) := by rw [hm1]; linarith
    have h3 : 0 ≤ σ * D₀ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  have hξ0 : 0 ≤ ξ := by positivity
  have hcut : ∀ A ⊆ L₀ ∪ R₀,
      ξ * A.card * ((L₀ ∪ R₀) \ A).card ≤ G.edgeWeight A ((L₀ ∪ R₀) \ A) := by
    intro A hA
    refine le_trans ?_ (hcore A hA)
    have : (0 : ℝ) ≤ A.card * ((L₀ ∪ R₀) \ A).card := by positivity
    nlinarith
  have hL₀card : L₀.card = m - 1 := by rw [hL₀, card_erase_of_mem hd, hU]
  have hR₀card : R₀.card = m - 1 := by rw [hR₀, card_erase_of_mem hf₀, hW]
  have hzf : z ≠ f₀ := fun h => hzW (h ▸ hf₀)
  obtain ⟨f, hfinj, hfR, hfpos⟩ := robust_hall G L₀ R₀ {z} {f₀} (m - 1) D₀ (η + 1 / D₀) ξ
    (disjoint_of_subset_left (erase_subset _ _) (disjoint_of_subset_right (erase_subset _ _) hUW))
    (disjoint_singleton_right.2 hzU)
    (disjoint_singleton_right.2 fun h => disjoint_left.1 hUW (mem_of_mem_erase h) hf₀)
    (disjoint_singleton_right.2 fun h => hzW (mem_of_mem_erase h))
    (disjoint_singleton_right.2 (notMem_erase f₀ W))
    (disjoint_singleton.2 hzf) hL₀card hR₀card (by simp)
    (fun x hx y hy => hbU x (mem_of_mem_erase hx) y (mem_of_mem_erase hy))
    (fun x hx y hy => hbW x (mem_of_mem_erase hx) y (mem_of_mem_erase hy)) hD₀
    (fun v hv => by
      have hvU := mem_of_mem_erase hv
      have h1 := abs_le.1 (hdegT v (mem_union_left _ hvU))
      have h2 := degOn_erase_add G hf₀ v
      rw [hdU v hvU] at h1
      have h3 := hw1 v f₀
      have h4 := hwnn v f₀
      have : (η + 1 / D₀) * D₀ = η * D₀ + 1 := by field_simp
      rw [this, abs_le]; constructor <;> linarith)
    (fun v hv => by
      have hvW := mem_of_mem_erase hv
      have h1 := abs_le.1 (hdegT v (mem_union_right _ hvW))
      have h2 := degOn_erase_add G hd v
      rw [hdW v hvW] at h1
      have h3 := hw1 v d
      have h4 := hwnn v d
      have : (η + 1 / D₀) * D₀ = η * D₀ + 1 := by field_simp
      rw [this, abs_le]; constructor <;> linarith)
    hcut (by rw [hα]; positivity) (by rw [hα]; linarith) (by rw [hα]; linarith)
    (fun x hx => by
      rw [mem_singleton] at hx; subst hx
      have h2 := degOn_erase_add G hf₀ x
      have h3 := hw1 x f₀
      linarith)
    (fun y hy => by
      rw [mem_singleton] at hy; subst hy
      have h1 := abs_le.1 (hdegT y (mem_union_right _ hf₀))
      rw [hdW y hf₀] at h1
      have h2 := degOn_erase_add G hd y
      have h3 := hw1 y d
      nlinarith)
    (fun v _ => by
      rw [hα]; unfold WGraph.degOn; rw [sum_singleton]
      have := hw1 v f₀
      nlinarith)
    (fun v _ => by
      rw [hα]; unfold WGraph.degOn; rw [sum_singleton]
      have := hw1 v z
      nlinarith)
  -- the bijection
  have hset : insert z (U.erase d) = L₀ ∪ {z} := by
    rw [hL₀, insert_eq, union_comm]
  have hRY : R₀ ∪ {f₀} = W := by
    rw [hR₀, union_comm, ← insert_eq, insert_erase hf₀]
  classical
  refine ⟨fun x => if h : x ∈ L₀ ∪ {z} then f ⟨x, h⟩ else x, ?_, ?_⟩
  · rw [hset]
    refine bijOn_of_injOn_card (fun x hx => ?_) (fun x hx y hy hxy => ?_) ?_
    · simp only [dite_eq_left hx]
      rw [← hRY]; exact hfR _
    · simp only [dite_eq_left (mem_coe.1 hx), dite_eq_left (mem_coe.1 hy)] at hxy
      exact congrArg Subtype.val (hfinj hxy)
    · rw [card_union_of_disjoint (disjoint_singleton_right.2 hzU), hL₀card, card_singleton, hW]
      omega
  · intro x hx
    rw [hset] at hx
    simp only [dite_eq_left hx]
    exact hfpos ⟨x, hx⟩

end Matching

/-! ### The grid of rows -/

section Grid

variable {α : Type*}

/-- A perfect matching of `X` onto `Y` along edges of `G`, as a bijection. -/
def Match (G : SimpleGraph α) (X Y : Finset α) : Prop :=
  ∃ g : α → α, Set.BijOn g ↑X ↑Y ∧ ∀ x ∈ X, G.Adj x (g x)

lemma Match.symm {G : SimpleGraph α} {X Y : Finset α} (h : Match G X Y) : Match G Y X := by
  obtain ⟨g, hg, hadj⟩ := h
  rcases isEmpty_or_nonempty α with hα | hα
  · have hX : (↑X : Set α) = ∅ := Set.eq_empty_of_forall_notMem fun x _ => hα.false x
    have hY : (↑Y : Set α) = ∅ := Set.eq_empty_of_forall_notMem fun x _ => hα.false x
    refine ⟨g, ?_, fun x _ => (hα.false x).elim⟩
    rw [hX, hY]; exact Set.bijOn_empty g
  · have hinv := hg.invOn_invFunOn
    have hb := hg.symm hinv.symm
    refine ⟨Function.invFunOn g ↑X, hb, fun y hy => ?_⟩
    have h1 : g (Function.invFunOn g ↑X y) = y := hinv.2 (mem_coe.2 hy)
    have h2 : Function.invFunOn g ↑X y ∈ X := hb.mapsTo (mem_coe.2 hy)
    have := hadj _ h2
    rw [h1] at this
    exact this.symm

/-- Two cross-colour matchings give a matching of the mixed layers. -/
lemma match_mixed (G : SimpleGraph α) (col : α → Bool) (X Y : Finset α)
    (h₁ : Match G (X.filter fun x => col x = true) (Y.filter fun x => col x = false))
    (h₂ : Match G (X.filter fun x => col x = false) (Y.filter fun x => col x = true)) :
    Match G X Y := by
  obtain ⟨g₁, hb₁, ha₁⟩ := h₁
  obtain ⟨g₂, hb₂, ha₂⟩ := h₂
  refine ⟨fun x => if col x = true then g₁ x else g₂ x, ⟨fun x hx => ?_, fun x hx x' hx' h => ?_,
    fun y hy => ?_⟩, fun x hx => ?_⟩
  · rw [mem_coe] at hx
    by_cases hc : col x = true
    · simp only [hc, ↓reduceIte]
      have := hb₁.mapsTo (mem_coe.2 (mem_filter.2 ⟨hx, hc⟩))
      exact mem_coe.2 (mem_filter.1 this).1
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      have := hb₂.mapsTo (mem_coe.2 (mem_filter.2 ⟨hx, by simpa using hc⟩))
      exact mem_coe.2 (mem_filter.1 this).1
  · rw [mem_coe] at hx hx'
    by_cases hc : col x = true <;> by_cases hc' : col x' = true <;>
      simp only [hc, hc', Bool.false_eq_true, ↓reduceIte] at h
    · exact hb₁.injOn (mem_coe.2 (mem_filter.2 ⟨hx, hc⟩)) (mem_coe.2 (mem_filter.2 ⟨hx', hc'⟩)) h
    · have e1 := mem_filter.1 (hb₁.mapsTo (mem_coe.2 (mem_filter.2 ⟨hx, hc⟩)))
      have e2 := mem_filter.1 (hb₂.mapsTo (mem_coe.2 (mem_filter.2 ⟨hx', by simpa using hc'⟩)))
      rw [h] at e1
      rw [e1.2] at e2; exact absurd e2.2 (by simp)
    · have e1 := mem_filter.1 (hb₂.mapsTo (mem_coe.2 (mem_filter.2 ⟨hx, by simpa using hc⟩)))
      have e2 := mem_filter.1 (hb₁.mapsTo (mem_coe.2 (mem_filter.2 ⟨hx', hc'⟩)))
      rw [h] at e1
      rw [e1.2] at e2; exact absurd e2.2 (by simp)
    · exact hb₂.injOn (mem_coe.2 (mem_filter.2 ⟨hx, by simpa using hc⟩))
        (mem_coe.2 (mem_filter.2 ⟨hx', by simpa using hc'⟩)) h
  · rw [mem_coe] at hy
    by_cases hc : col y = true
    · obtain ⟨x, hx, rfl⟩ := hb₂.surjOn (mem_coe.2 (mem_filter.2 ⟨hy, hc⟩))
      have hx' := mem_filter.1 (mem_coe.1 hx)
      refine ⟨x, mem_coe.2 hx'.1, ?_⟩
      simp [hx'.2]
    · obtain ⟨x, hx, rfl⟩ := hb₁.surjOn (mem_coe.2 (mem_filter.2 ⟨hy, by simpa using hc⟩))
      have hx' := mem_filter.1 (mem_coe.1 hx)
      exact ⟨x, mem_coe.2 hx'.1, by simp [hx'.2]⟩
  · by_cases hc : col x = true
    · simp only [hc, ↓reduceIte]; exact ha₁ x (mem_filter.2 ⟨hx, hc⟩)
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ha₂ x (mem_filter.2 ⟨hx, by simpa using hc⟩)

/-- The row through `x` of the grid defined by the column steps `g`. -/
def gridRow (g : ℕ → α → α) (x : α) : ℕ → α
  | 0 => x
  | j + 1 => g j (gridRow g x j)

/-- **The grid.** Bijective steps between pairwise disjoint columns `C 0, …, C k` give `w`
vertex-disjoint rows. -/
lemma grid (C : ℕ → Finset α) (k w : ℕ) (g : ℕ → α → α) (hcard : (C 0).card = w)
    (hbij : ∀ j < k, Set.BijOn (g j) ↑(C j) ↑(C (j + 1)))
    (hdisj : ∀ j j', j ≤ k → j' ≤ k → j ≠ j' → Disjoint (C j) (C j')) :
    ∃ φ : Fin w → ℕ → α, (∀ i j i' j', j ≤ k → j' ≤ k → φ i j = φ i' j' → i = i' ∧ j = j') ∧
      (∀ j ≤ k, ∀ v, v ∈ C j ↔ ∃ i, φ i j = v) ∧ (∀ i j, φ i (j + 1) = g j (φ i j)) := by
  set e : Fin w → α := fun i => BipSampling.enum (C 0) (Fin.cast hcard.symm i) with he
  have key : ∀ j ≤ k, (∀ i, gridRow g (e i) j ∈ C j) ∧
      Function.Injective (fun i => gridRow g (e i) j) ∧
      ∀ v ∈ C j, ∃ i, gridRow g (e i) j = v := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun i => BipSampling.enum_mem _ _, fun i i' h => ?_, fun v hv => ?_⟩
      · have h' : BipSampling.enum (C 0) (Fin.cast hcard.symm i) =
            BipSampling.enum (C 0) (Fin.cast hcard.symm i') := h
        exact Fin.cast_injective _ ((BipSampling.enum (C 0)).injective h')
      · have hv' : v ∈ (univ : Finset (Fin (C 0).card)).map (BipSampling.enum (C 0)) := by
          rw [BipSampling.univ_map_enum]; exact hv
        obtain ⟨j₀, -, rfl⟩ := mem_map.1 hv'
        exact ⟨Fin.cast hcard j₀, by simp [gridRow, he]⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      have hb := hbij j (by omega)
      refine ⟨fun i => hb.mapsTo (h1 i), fun i i' h => h2 (hb.injOn (h1 i) (h1 i') h),
        fun v hv => ?_⟩
      obtain ⟨x, hx, rfl⟩ := hb.surjOn (mem_coe.2 hv)
      obtain ⟨i, rfl⟩ := h3 x hx
      exact ⟨i, rfl⟩
  refine ⟨fun i j => gridRow g (e i) j, fun i j i' j' hj hj' h => ?_, fun j hj v => ?_,
    fun i j => rfl⟩
  · by_cases hjj : j = j'
    · subst hjj
      exact ⟨(key j hj).2.1 h, rfl⟩
    · exfalso
      have h1 := (key j hj).1 i
      have h2 := (key j' hj').1 i'
      simp only at h
      rw [h] at h1
      exact disjoint_left.1 (hdisj j j' hj hj' hjj) h1 h2
  · constructor
    · exact (key j hj).2.2 v
    · rintro ⟨i, rfl⟩; exact (key j hj).1 i

end Grid

/-! ### Uniform equipartitions -/

section Layers

variable {α : Type*}

/-- The `j`-th block `{i : i / m = j}` of `Fin n`. -/
def blk (n m j : ℕ) : Finset (Fin n) := univ.filter fun i => i.val / m = j

/-- The `j`-th layer of the equipartition of `S` given by the ordering `σ`. -/
noncomputable def lay (S : Finset α) (m : ℕ) (σ : Equiv.Perm (Fin S.card)) (j : ℕ) : Finset α :=
  (blk S.card m j).map (σ.toEmbedding.trans (BipSampling.enum S))

lemma card_blk (n m j : ℕ) (hm : 0 < m) (h : (j + 1) * m ≤ n) : (blk n m j).card = m := by
  have hmap : (blk n m j).map Fin.valEmbedding = Ico (j * m) (j * m + m) := by
    ext i
    simp only [blk, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩
      constructor
      · rw [← ha]; exact Nat.div_mul_le_self a m
      · have := Nat.lt_div_mul_add (a := a.val) hm
        rw [ha] at this; exact this
    · rintro ⟨h1, h2⟩
      refine ⟨⟨i, lt_of_lt_of_le h2 (by rwa [Nat.succ_mul] at h)⟩, ?_, rfl⟩
      exact Nat.div_eq_of_lt_le h1 (by show i < (j + 1) * m; rw [Nat.succ_mul]; exact h2)
  rw [← card_map Fin.valEmbedding, hmap, Nat.card_Ico]
  omega

lemma lay_sub (S : Finset α) (m : ℕ) (σ : Equiv.Perm (Fin S.card)) (j : ℕ) :
    lay S m σ j ⊆ S := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := mem_map.1 hx
  exact BipSampling.enum_mem S _

lemma card_lay (S : Finset α) {m : ℕ} (σ : Equiv.Perm (Fin S.card)) {j : ℕ} (hm : 0 < m)
    (h : (j + 1) * m ≤ S.card) : (lay S m σ j).card = m := by
  rw [lay, card_map, card_blk _ _ _ hm h]

lemma lay_disj (S : Finset α) (m : ℕ) (σ : Equiv.Perm (Fin S.card)) {j j' : ℕ} (hj : j ≠ j') :
    Disjoint (lay S m σ j) (lay S m σ j') := by
  rw [lay, lay, disjoint_map]
  exact disjoint_filter.2 fun i _ h1 h2 => hj (h1 ▸ h2)

lemma lay_cover (S : Finset α) {m t : ℕ} (σ : Equiv.Perm (Fin S.card)) (hm : 0 < m)
    (hS : S.card = t * m) {x : α} (hx : x ∈ S) : ∃ j < t, x ∈ lay S m σ j := by
  have hx' : x ∈ (univ : Finset (Fin S.card)).map (BipSampling.enum S) := by
    rw [BipSampling.univ_map_enum]; exact hx
  obtain ⟨i₀, -, rfl⟩ := mem_map.1 hx'
  refine ⟨(σ.symm i₀).val / m, ?_, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hm, ← hS]; exact (σ.symm i₀).2
  · refine mem_map.2 ⟨σ.symm i₀, by simp [blk], ?_⟩
    simp

lemma exists_perm_map {n m : ℕ} (A B : Finset (Fin n)) (hA : A.card = m) (hB : B.card = m) :
    ∃ g : Equiv.Perm (Fin n), A.map g.toEmbedding = B := by
  have := Set.powersetCard.isPretransitive (α := Fin n) (n := m)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin n))
    (⟨A, Set.powersetCard.mem_iff.2 hA⟩ : Set.powersetCard (Fin n) m)
    ⟨B, Set.powersetCard.mem_iff.2 hB⟩
  refine ⟨g, ?_⟩
  have h1 := congrArg (fun s : Set.powersetCard (Fin n) m => (s : Finset (Fin n))) hg
  simp only [Set.powersetCard.coe_smul] at h1
  rw [← h1, Finset.smul_finset_def, map_eq_image]
  rfl

lemma map_filter_enum [DecidableEq α] (S T : Finset α) (hT : T ⊆ S) :
    (univ.filter fun i => BipSampling.enum S i ∈ T).map (BipSampling.enum S) = T := by
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro hx
    have hx' : x ∈ (univ : Finset (Fin S.card)).map (BipSampling.enum S) := by
      rw [BipSampling.univ_map_enum]; exact hT hx
    obtain ⟨i, -, rfl⟩ := mem_map.1 hx'
    exact ⟨i, hx, rfl⟩

/-- All fibres of a layer map over sets of the same size have the same size. -/
lemma lay_fibre [DecidableEq α] (S : Finset α) (m j : ℕ) (T T' : Finset α) (hT : T ⊆ S)
    (hT' : T' ⊆ S) (hc : T.card = T'.card) :
    (univ.filter fun σ : Equiv.Perm (Fin S.card) => lay S m σ j = T).card =
      (univ.filter fun σ : Equiv.Perm (Fin S.card) => lay S m σ j = T').card := by
  set e := BipSampling.enum S
  set T₀ := univ.filter fun i => e i ∈ T with hT₀
  set T₀' := univ.filter fun i => e i ∈ T' with hT₀'
  have m₀ : T₀.map e = T := map_filter_enum S T hT
  have m₀' : T₀'.map e = T' := map_filter_enum S T' hT'
  have hc₀ : T₀.card = T₀'.card := by rw [← card_map e, m₀, ← card_map e, m₀', hc]
  obtain ⟨g, hg⟩ := exists_perm_map T₀ T₀' hc₀ rfl
  have hlay : ∀ σ : Equiv.Perm (Fin S.card),
      lay S m σ j = ((blk S.card m j).map σ.toEmbedding).map e := by
    intro σ; rw [lay, map_map]
  have hiff : ∀ σ : Equiv.Perm (Fin S.card) , ∀ X₀ : Finset (Fin S.card),
      (lay S m σ j = X₀.map e ↔ (blk S.card m j).map σ.toEmbedding = X₀) := by
    intro σ X₀; rw [hlay, map_inj]
  have htr : ∀ (σ τ : Equiv.Perm (Fin S.card)),
      (blk S.card m j).map (σ.trans τ).toEmbedding =
        ((blk S.card m j).map σ.toEmbedding).map τ.toEmbedding := by
    intro σ τ; rw [map_map, Equiv.trans_toEmbedding]
  have hg' : T₀'.map g.symm.toEmbedding = T₀ := by
    rw [← hg, map_map]
    ext x; simp
  refine card_nbij' (fun σ => σ.trans g) (fun σ => σ.trans g.symm) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hσ ⊢
    rw [← m₀'] ; rw [← m₀] at hσ
    rw [hiff] at hσ ⊢
    rw [htr, hσ, hg]
  · intro σ hσ
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hσ ⊢
    rw [← m₀] ; rw [← m₀'] at hσ
    rw [hiff] at hσ ⊢
    rw [htr, hσ, hg']
  · intro σ _; ext x; simp
  · intro σ _; ext x; simp

/-- Counting along a map with uniform fibres. -/
lemma card_filter_comp {Ω β : Type*} [Fintype Ω] [DecidableEq β] (f : Ω → β) (R : Finset β)
    (c : ℕ) (hf : ∀ ω, f ω ∈ R) (hc : ∀ r ∈ R, (univ.filter fun ω => f ω = r).card = c)
    (Q : β → Prop) [DecidablePred Q] :
    (univ.filter fun ω => Q (f ω)).card = (R.filter Q).card * c := by
  rw [card_eq_sum_card_fiberwise (f := f) (t := R.filter Q) (fun ω hω => by
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hω
    exact mem_coe.2 (mem_filter.2 ⟨hf ω, hω⟩))]
  rw [sum_congr rfl fun r hr => ?_, sum_const, smul_eq_mul]
  rw [filter_filter]
  have hr' := mem_filter.1 hr
  rw [← hc r hr'.1]
  congr 1
  refine filter_congr fun ω _ => ?_
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ hr'.2, h⟩

/-- **Uniformity of the layers.** For two independent uniform orderings of `S₁` and `S₂`, the
pair (layer `j₁` of `S₁`, layer `j₂` of `S₂`) is a uniform pair of `m`-subsets. -/
lemma count_pair [DecidableEq α] (S₁ S₂ : Finset α) (m j₁ j₂ : ℕ) (hm : 0 < m)
    (h₁ : (j₁ + 1) * m ≤ S₁.card) (h₂ : (j₂ + 1) * m ≤ S₂.card)
    (Q : Finset α × Finset α → Prop) [DecidablePred Q] (ε : ℝ)
    (hQ : ((((S₁.powersetCard m) ×ˢ (S₂.powersetCard m)).filter fun p => ¬ Q p).card : ℝ) ≤
      ε * ((S₁.card.choose m : ℕ) * (S₂.card.choose m : ℕ))) :
    ((univ.filter fun ω : Equiv.Perm (Fin S₁.card) × Equiv.Perm (Fin S₂.card) =>
        ¬ Q (lay S₁ m ω.1 j₁, lay S₂ m ω.2 j₂)).card : ℝ) ≤
      ε * Fintype.card (Equiv.Perm (Fin S₁.card) × Equiv.Perm (Fin S₂.card)) := by
  have hm₁ : m ≤ S₁.card := le_trans (by nlinarith) h₁
  have hm₂ : m ≤ S₂.card := le_trans (by nlinarith) h₂
  obtain ⟨T₁, hT₁⟩ := powersetCard_nonempty.2 hm₁
  obtain ⟨T₂, hT₂⟩ := powersetCard_nonempty.2 hm₂
  set c₁ := (univ.filter fun σ : Equiv.Perm (Fin S₁.card) => lay S₁ m σ j₁ = T₁).card
  set c₂ := (univ.filter fun σ : Equiv.Perm (Fin S₂.card) => lay S₂ m σ j₂ = T₂).card
  set R := (S₁.powersetCard m) ×ˢ (S₂.powersetCard m)
  set f : Equiv.Perm (Fin S₁.card) × Equiv.Perm (Fin S₂.card) → Finset α × Finset α :=
    fun ω => (lay S₁ m ω.1 j₁, lay S₂ m ω.2 j₂)
  have hf : ∀ ω, f ω ∈ R := fun ω => mem_product.2
    ⟨mem_powersetCard.2 ⟨lay_sub _ _ _ _, card_lay _ _ hm h₁⟩,
      mem_powersetCard.2 ⟨lay_sub _ _ _ _, card_lay _ _ hm h₂⟩⟩
  have hc : ∀ r ∈ R, (univ.filter fun ω => f ω = r).card = c₁ * c₂ := by
    rintro ⟨U₁, U₂⟩ hr
    obtain ⟨hU₁, hU₂⟩ := mem_product.1 hr
    have e1 := lay_fibre S₁ m j₁ U₁ T₁ (mem_powersetCard.1 hU₁).1 (mem_powersetCard.1 hT₁).1
      (by rw [(mem_powersetCard.1 hU₁).2, (mem_powersetCard.1 hT₁).2])
    have e2 := lay_fibre S₂ m j₂ U₂ T₂ (mem_powersetCard.1 hU₂).1 (mem_powersetCard.1 hT₂).1
      (by rw [(mem_powersetCard.1 hU₂).2, (mem_powersetCard.1 hT₂).2])
    have : (univ.filter fun ω => f ω = (U₁, U₂)) =
        (univ.filter fun σ : Equiv.Perm (Fin S₁.card) => lay S₁ m σ j₁ = U₁) ×ˢ
          (univ.filter fun σ : Equiv.Perm (Fin S₂.card) => lay S₂ m σ j₂ = U₂) := by
      ext ω; simp [f, Prod.ext_iff]
    rw [this, card_product, e1, e2]
  have hbad := card_filter_comp f R (c₁ * c₂) hf hc (fun p => ¬ Q p)
  have hall := card_filter_comp f R (c₁ * c₂) hf hc (fun _ => True)
  rw [filter_true_of_mem (fun _ _ => trivial), filter_true_of_mem (fun _ _ => trivial)] at hall
  have hR : (R.card : ℝ) = (S₁.card.choose m : ℕ) * (S₂.card.choose m : ℕ) := by
    simp [R, card_product, card_powersetCard]
  rw [Fintype.card, hall, hbad]
  push_cast
  rw [hR]
  have : (0 : ℝ) ≤ c₁ * c₂ := by positivity
  nlinarith

/-- The union bound. -/
lemma exists_good {Ω ι : Type*} [Fintype Ω] (s : Finset ι) (P : ι → Ω → Prop)
    [∀ e, DecidablePred (P e)] (ε : ℝ)
    (h : ∀ e ∈ s, ((univ.filter fun ω => ¬ P e ω).card : ℝ) ≤ ε * Fintype.card Ω)
    (hs : s.card * ε < 1) (hΩ : 0 < Fintype.card Ω) : ∃ ω, ∀ e ∈ s, P e ω := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : (univ : Finset Ω) ⊆ s.biUnion fun e => univ.filter fun ω => ¬ P e ω := by
    intro ω _
    obtain ⟨e, he, hne⟩ := hcon ω
    exact mem_biUnion.2 ⟨e, he, mem_filter.2 ⟨mem_univ _, hne⟩⟩
  have h1 : (Fintype.card Ω : ℝ) ≤ ∑ e ∈ s, ((univ.filter fun ω => ¬ P e ω).card : ℝ) := by
    have := (card_le_card hsub).trans card_biUnion_le
    rw [card_univ] at this
    exact_mod_cast this
  have h2 : ∑ e ∈ s, ((univ.filter fun ω => ¬ P e ω).card : ℝ) ≤ s.card * (ε * Fintype.card Ω) := by
    have := sum_le_sum h
    rwa [sum_const, nsmul_eq_mul] at this
  have hΩ' : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hΩ
  nlinarith

end Layers

/-! ### The transitions and the assembly of the grid -/

section Assembly

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Lemma 2.5 without enlargement, from the sampled estimates. -/
theorem plain_match (G : WGraph α) (hw1 : ∀ x y, G.w x y ≤ 1) (U W : Finset α) (m : ℕ)
    (D₀ η σ : ℝ) (hUW : Disjoint U W) (hU : U.card = m) (hW : W.card = m) (hm : 2 ≤ m)
    (hbU : ∀ x ∈ U, ∀ y ∈ U, G.w x y = 0) (hbW : ∀ x ∈ W, ∀ y ∈ W, G.w x y = 0)
    (hdeg : (G.induce (U ∪ W)).DegNear D₀ η) (hgap : (G.induce (U ∪ W)).HasGap σ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hη0 : 0 ≤ η) (hη : η ≤ σ / 400) (hD₀ : 400 / σ ≤ D₀) :
    Match G.supp U W := by
  obtain ⟨d, hd⟩ : U.Nonempty := card_pos.1 (by omega)
  have hσD : 400 ≤ σ * D₀ := by rw [div_le_iff₀ hσ] at hD₀; linarith
  have hD : 400 ≤ D₀ := by nlinarith
  have hη1 : η ≤ 1 / 400 := by
    linarith [div_le_div_of_nonneg_right hσ1 (by norm_num : (0:ℝ) ≤ 400)]
  have hdW : d ∉ W := disjoint_left.1 hUW hd
  have hz : D₀ / 2 + 1 ≤ G.degOn d W := by
    have h1 := abs_le.1 (hdeg ⟨d, mem_union_left _ hd⟩)
    rw [induce_deg_eq, degOn_union_of_zero G hUW d fun y hy => hbU d hd y hy] at h1
    nlinarith
  obtain ⟨g, hg, hadj⟩ := swap_match G hw1 U W m d d D₀ η σ hUW hU hW hm hbU hbW hd
    (notMem_erase d U) hdW hdeg hgap hσ hσ1 hη0 hη hD₀ hz
  rw [insert_erase hd] at hg hadj
  exact ⟨g, hg, hadj⟩

/-- The sampled estimates of Lemmas 2.3 and 2.4 on `H[X ∪ T]`. -/
def Good (H : WGraph α) (X T : Finset α) (D₀ η σ : ℝ) : Prop :=
  (H.induce (X ∪ T)).DegNear D₀ η ∧ (H.induce (X ∪ T)).HasGap σ

omit [Fintype α] [DecidableEq α] in
lemma bip_zero (H : WGraph α) (col : α → Bool) (hbip : H.IsBipartiteWith col) (X : Finset α)
    (b : Bool) (hX : ∀ x ∈ X, col x = b) : ∀ x ∈ X, ∀ y ∈ X, H.w x y = 0 := by
  intro x hx y hy
  refine le_antisymm (not_lt.1 fun h => hbip x y h ?_) (H.nonneg x y)
  rw [hX x hx, hX y hy]

omit [Fintype α] in
lemma filter_col_union (col : α → Bool) (A B : Finset α) (hA : ∀ x ∈ A, col x = true)
    (hB : ∀ x ∈ B, col x = false) :
    (A ∪ B).filter (fun x => col x = true) = A ∧ (A ∪ B).filter (fun x => col x = false) = B := by
  constructor
  · ext x
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hx | hx, hc⟩
      · exact hx
      · rw [hB x hx] at hc; exact absurd hc (by simp)
    · intro hx; exact ⟨Or.inl hx, hA x hx⟩
  · ext x
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hx | hx, hc⟩
      · rw [hA x hx] at hc; exact absurd hc (by simp)
      · exact hx
    · intro hx; exact ⟨Or.inr hx, hB x hx⟩

omit [Fintype α] in
lemma filter_swap (col : α → Bool) (X : Finset α) (d z : α) (b : Bool) (hd : col d = b)
    (hz : col z = b) :
    (insert z (X.erase d)).filter (fun x => col x = b) =
        insert z ((X.filter fun x => col x = b).erase d) ∧
      (insert z (X.erase d)).filter (fun x => col x = !b) = X.filter fun x => col x = !b := by
  constructor
  · rw [filter_insert, ite_eq_left hz, filter_erase]
  · rw [filter_insert, ite_eq_right (by rw [hz]; cases b <;> simp), filter_erase,
      erase_eq_of_notMem (by rw [mem_filter, hd]; cases b <;> simp)]

/-- **Assembly of the grid** from the sampled estimates of all transitions. -/
theorem assemble (H : WGraph α) (col : α → Bool) (hbip : H.IsBipartiteWith col)
    (hw1 : ∀ x y, H.w x y ≤ 1) (O I U W U' W' P : Finset α) (m t : ℕ) (hm : 2 ≤ m)
    (ht : 2 ≤ t) (dA dB zA zB : α) (τ : α → α)
    (hcard : ∀ X : Finset α, (X = O ∨ X = I ∨ X = U ∨ X = W) →
      ∀ b, (X.filter fun x => col x = b).card = m)
    (hOI : Disjoint O I) (hOU : Disjoint O U) (hOW : Disjoint O W) (hIU : Disjoint I U)
    (hIW : Disjoint I W) (hUW : Disjoint U W)
    (hdA : dA ∈ U) (hdAc : col dA = true) (hdB : dB ∈ W) (hdBc : col dB = false)
    (hzAc : col zA = true) (hzBc : col zB = false)
    (hzA : zA ∉ O ∪ I ∪ U ∪ W) (hzB : zB ∉ O ∪ I ∪ U ∪ W)
    (hU' : U' = insert zA (U.erase dA)) (hW' : W' = insert zB (W.erase dB))
    (hPd : Disjoint P (O ∪ I ∪ U' ∪ W')) (hτ : Set.BijOn τ ↑U' ↑W')
    (LT LF : ℕ → Finset α)
    (hLT : ∀ j, LT j ⊆ P.filter fun x => col x = true)
    (hLF : ∀ j, LF j ⊆ P.filter fun x => col x = false)
    (hLTc : ∀ j < t, (LT j).card = m) (hLFc : ∀ j < t, (LF j).card = m)
    (hLTd : ∀ j j', j ≠ j' → Disjoint (LT j) (LT j'))
    (hLFd : ∀ j j', j ≠ j' → Disjoint (LF j) (LF j'))
    (hcov : ∀ x ∈ P, ∃ j < t, x ∈ LT j ∪ LF j)
    (D₀ ηa σa D₁ ηb σb : ℝ) (hσa : 0 < σa) (hσa1 : σa ≤ 1) (hηa0 : 0 ≤ ηa)
    (hηa : ηa ≤ σa / 400) (hDa : 400 / σa ≤ D₀) (hσb : 0 < σb) (hσb1 : σb ≤ 1)
    (hηb0 : 0 ≤ ηb) (hηb : ηb ≤ σb / 400) (hDb : 400 / σb ≤ D₁)
    (gOt : Good H (O.filter fun x => col x = true) (LF 0) D₀ ηa σa)
    (gOf : Good H (O.filter fun x => col x = false) (LT 0) D₀ ηa σa)
    (gUt : Good H (U.filter fun x => col x = true) (LF 0) D₀ ηa σa)
    (gUf : Good H (U.filter fun x => col x = false) (LT 0) D₀ ηa σa)
    (gzA : D₀ / 2 + 1 ≤ H.degOn zA (LF 0))
    (gWt : Good H (W.filter fun x => col x = true) (LF 1) D₀ ηa σa)
    (gWf : Good H (W.filter fun x => col x = false) (LT 1) D₀ ηa σa)
    (gzB : D₀ / 2 + 1 ≤ H.degOn zB (LT 1))
    (gIt : Good H (I.filter fun x => col x = true) (LF (t - 1)) D₀ ηa σa)
    (gIf : Good H (I.filter fun x => col x = false) (LT (t - 1)) D₀ ηa σa)
    (gfr : ∀ i, 1 ≤ i → i + 1 < t → Good H (LT i) (LF (i + 1)) D₁ ηb σb ∧
      Good H (LT (i + 1)) (LF i) D₁ ηb σb) :
    ∃ k : ℕ, 4 ≤ k ∧ ∃ φ : Fin (2 * m) → ℕ → α,
      (∀ i j i' j', j ≤ k → j' ≤ k → φ i j = φ i' j' → i = i' ∧ j = j') ∧
      (∀ v, v ∈ O ↔ ∃ i, φ i 0 = v) ∧ (∀ v, v ∈ I ↔ ∃ i, φ i k = v) ∧
      (∀ v, v ∈ U' ↔ ∃ i, φ i 2 = v) ∧ (∀ v, v ∈ W' ↔ ∃ i, φ i 3 = v) ∧
      (∀ v, v ∈ P ↔ ∃ i j, (j = 1 ∨ (4 ≤ j ∧ j < k)) ∧ φ i j = v) ∧
      (∀ i, φ i 3 = τ (φ i 2)) ∧
      (∀ i j, j < k → j ≠ 2 → H.supp.Adj (φ i j) (φ i (j + 1))) := by
  -- colours
  have cT : ∀ j, ∀ x ∈ LT j, col x = true := fun j x hx => (mem_filter.1 (hLT j hx)).2
  have cF : ∀ j, ∀ x ∈ LF j, col x = false := fun j x hx => (mem_filter.1 (hLF j hx)).2
  have cb : ∀ (X : Finset α) (b : Bool), ∀ x ∈ X.filter (fun x => col x = b), col x = b :=
    fun X b x hx => (mem_filter.1 hx).2
  have dcol : ∀ (X Y : Finset α), (∀ x ∈ X, col x = true) → (∀ x ∈ Y, col x = false) →
      Disjoint X Y := fun X Y hX hY => disjoint_left.2 fun x h1 h2 => by
    have := hX x h1; rw [hY x h2] at this; exact absurd this (by simp)
  have zb : ∀ (X : Finset α) (b : Bool), (∀ x ∈ X, col x = b) →
      ∀ x ∈ X, ∀ y ∈ X, H.w x y = 0 := fun X b hX => bip_zero H col hbip X b hX
  have hmT : ∀ X, (X = O ∨ X = I ∨ X = U ∨ X = W) → (X.filter fun x => col x = true).card = m :=
    fun X hX => hcard X hX true
  have hmF : ∀ X, (X = O ∨ X = I ∨ X = U ∨ X = W) →
      (X.filter fun x => col x = false).card = m := fun X hX => hcard X hX false
  -- plain matchings
  have pm : ∀ (X T : Finset α), (∀ x ∈ X, col x = true) → (∀ x ∈ T, col x = false) →
      X.card = m → T.card = m → ∀ (D η σ : ℝ), 0 < σ → σ ≤ 1 → 0 ≤ η → η ≤ σ / 400 →
      400 / σ ≤ D → Good H X T D η σ → Match H.supp X T := by
    intro X T hX hT hXc hTc D η σ h1 h2 h3 h4 h5 hg
    exact plain_match H hw1 X T m D η σ (dcol X T hX hT) hXc hTc hm (zb X true hX)
      (zb T false hT) hg.1 hg.2 h1 h2 h3 h4 h5
  have pm' : ∀ (X T : Finset α), (∀ x ∈ X, col x = false) → (∀ x ∈ T, col x = true) →
      X.card = m → T.card = m → ∀ (D η σ : ℝ), 0 < σ → σ ≤ 1 → 0 ≤ η → η ≤ σ / 400 →
      400 / σ ≤ D → Good H X T D η σ → Match H.supp X T := by
    intro X T hX hT hXc hTc D η σ h1 h2 h3 h4 h5 hg
    exact plain_match H hw1 X T m D η σ (dcol T X hT hX).symm hXc hTc hm (zb X false hX)
      (zb T true hT) hg.1 hg.2 h1 h2 h3 h4 h5
  have ht1 : 1 < t := by omega
  have hLT0 := hLTc 0 (by omega)
  have hLF0 := hLFc 0 (by omega)
  have hLT1 := hLTc 1 ht1
  have hLF1 := hLFc 1 ht1
  have hLTt := hLTc (t - 1) (by omega)
  have hLFt := hLFc (t - 1) (by omega)
  have M1 := pm _ _ (cb O true) (cF 0) (hmT O (Or.inl rfl)) hLF0 D₀ ηa σa hσa hσa1 hηa0 hηa hDa gOt
  have M2 := pm' _ _ (cb O false) (cT 0) (hmF O (Or.inl rfl)) hLT0 D₀ ηa σa hσa hσa1 hηa0 hηa hDa gOf
  have M4 := pm' _ _ (cb U false) (cT 0) (hmF U (Or.inr (Or.inr (Or.inl rfl)))) hLT0 D₀ ηa σa
    hσa hσa1 hηa0 hηa hDa gUf
  have M5 := pm _ _ (cb W true) (cF 1) (hmT W (Or.inr (Or.inr (Or.inr rfl)))) hLF1 D₀ ηa σa
    hσa hσa1 hηa0 hηa hDa gWt
  have M7 := pm _ _ (cb I true) (cF (t - 1)) (hmT I (Or.inr (Or.inl rfl))) hLFt D₀ ηa σa
    hσa hσa1 hηa0 hηa hDa gIt
  have M8 := pm' _ _ (cb I false) (cT (t - 1)) (hmF I (Or.inr (Or.inl rfl))) hLTt D₀ ηa σa
    hσa hσa1 hηa0 hηa hDa gIf
  -- the swapped transitions
  have hzAU : zA ∉ U := fun h => hzA (mem_union_left _ (mem_union_right _ h))
  have hzBW : zB ∉ W := fun h => hzB (mem_union_right _ h)
  have hzAP : zA ∉ P := fun h => disjoint_left.1 hPd h
    (mem_union_left _ (mem_union_right _ (hU' ▸ mem_insert_self _ _)))
  have hzBP : zB ∉ P := fun h => disjoint_left.1 hPd h (mem_union_right _ (hW' ▸ mem_insert_self _ _))
  have hU't := (filter_swap col U dA zA true hdAc hzAc)
  have hW'f := (filter_swap col W dB zB false hdBc hzBc)
  have M3 : Match H.supp (U'.filter fun x => col x = true) (LF 0) := by
    rw [hU', hU't.1]
    obtain ⟨g, hg, hadj⟩ := swap_match H hw1 _ (LF 0) m dA zA D₀ ηa σa
      (dcol _ _ (cb U true) (cF 0)) (hmT U (Or.inr (Or.inr (Or.inl rfl)))) hLF0 hm
      (zb _ true (cb U true)) (zb _ false (cF 0)) (mem_filter.2 ⟨hdA, hdAc⟩)
      (fun h => hzAU (mem_filter.1 (mem_of_mem_erase h)).1)
      (fun h => hzAP (mem_filter.1 (hLF 0 h)).1) gUt.1 gUt.2 hσa hσa1 hηa0 hηa hDa gzA
    exact ⟨g, hg, hadj⟩
  have M6 : Match H.supp (W'.filter fun x => col x = false) (LT 1) := by
    rw [hW', hW'f.1]
    obtain ⟨g, hg, hadj⟩ := swap_match H hw1 _ (LT 1) m dB zB D₀ ηa σa
      (dcol _ _ (cT 1) (cb W false)).symm (hmF W (Or.inr (Or.inr (Or.inr rfl)))) hLT1 hm
      (zb _ false (cb W false)) (zb _ true (cT 1)) (mem_filter.2 ⟨hdB, hdBc⟩)
      (fun h => hzBW (mem_filter.1 (mem_of_mem_erase h)).1)
      (fun h => hzBP (mem_filter.1 (hLT 1 h)).1) gWf.1 gWf.2 hσa hσa1 hηa0 hηa hDa gzB
    exact ⟨g, hg, hadj⟩
  have hU'f : U'.filter (fun x => col x = false) = U.filter fun x => col x = false := by
    rw [hU']; exact hU't.2
  have hW't : W'.filter (fun x => col x = true) = W.filter fun x => col x = true := by
    rw [hW']; exact hW'f.2
  -- the columns
  set Lay : ℕ → Finset α := fun i => LT i ∪ LF i with hLay
  have hLayt : ∀ i, (Lay i).filter (fun x => col x = true) = LT i := fun i =>
    (filter_col_union col (LT i) (LF i) (cT i) (cF i)).1
  have hLayf : ∀ i, (Lay i).filter (fun x => col x = false) = LF i := fun i =>
    (filter_col_union col (LT i) (LF i) (cT i) (cF i)).2
  have hLayP : ∀ i, Lay i ⊆ P := fun i => union_subset
    ((hLT i).trans (filter_subset _ _)) ((hLF i).trans (filter_subset _ _))
  set C : ℕ → Finset α := fun j => if j = 0 then O else if j = 1 then Lay 0 else
    if j = 2 then U' else if j = 3 then W' else if j < t + 3 then Lay (j - 3) else I with hC
  have C0 : C 0 = O := by simp [hC]
  have C1 : C 1 = Lay 0 := by simp [hC]
  have C2 : C 2 = U' := by simp [hC]
  have C3 : C 3 = W' := by simp [hC]
  have Cmid : ∀ j, 4 ≤ j → j < t + 3 → C j = Lay (j - 3) := by
    intro j h1 h2
    simp only [hC]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]
  have Ck : C (t + 3) = I := by
    simp only [hC]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
  -- the steps
  have hstep : ∀ j, ∃ g : α → α, j < t + 3 → Set.BijOn g ↑(C j) ↑(C (j + 1)) ∧
      (j ≠ 2 → ∀ x ∈ C j, H.supp.Adj x (g x)) ∧ (j = 2 → g = τ) := by
    intro j
    by_cases hj2 : j = 2
    · subst hj2
      exact ⟨τ, fun _ => ⟨by rw [C2, C3]; exact hτ, fun h => absurd rfl h, fun _ => rfl⟩⟩
    have hM : j < t + 3 → Match H.supp (C j) (C (j + 1)) := by
      intro hjk
      rcases Nat.lt_or_ge j 4 with h4 | h4
      · interval_cases j
        · rw [C0, C1]
          refine match_mixed _ col _ _ ?_ ?_
          · rw [hLayf]; exact M1
          · rw [hLayt]; exact M2
        · rw [C1, C2]
          refine match_mixed _ col _ _ ?_ ?_
          · rw [hLayt, hU'f]; exact M4.symm
          · rw [hLayf]; exact M3.symm
        · exact absurd rfl hj2
        · rw [C3, Cmid 4 le_rfl (by omega)]
          refine match_mixed _ col _ _ ?_ ?_
          · rw [hLayf, hW't]; exact M5
          · rw [hLayt]; exact M6
      · rcases Nat.lt_or_ge (j + 1) (t + 3) with h5 | h5
        · rw [Cmid j h4 (by omega), Cmid (j + 1) (by omega) h5]
          obtain ⟨g1, g2⟩ := gfr (j - 3) (by omega) (by omega)
          have e1 : j + 1 - 3 = j - 3 + 1 := by omega
          rw [e1]
          refine match_mixed _ col _ _ ?_ ?_
          · rw [hLayt, hLayf]
            exact pm _ _ (cT _) (cF _) (hLTc _ (by omega)) (hLFc _ (by omega)) D₁ ηb σb hσb
              hσb1 hηb0 hηb hDb g1
          · rw [hLayt, hLayf]
            exact (pm _ _ (cT _) (cF _) (hLTc _ (by omega)) (hLFc _ (by omega)) D₁ ηb σb hσb
              hσb1 hηb0 hηb hDb g2).symm
        · have hjt : j = t + 2 := by omega
          rw [Cmid j h4 (by omega), hjt, Ck]
          have e1 : t + 2 - 3 = t - 1 := by omega
          rw [e1]
          refine match_mixed _ col _ _ ?_ ?_
          · rw [hLayt]; exact M8.symm
          · rw [hLayf]; exact M7.symm
    by_cases hjk : j < t + 3
    · obtain ⟨g, hg, hadj⟩ := hM hjk
      exact ⟨g, fun _ => ⟨hg, fun _ => hadj, fun h => absurd h hj2⟩⟩
    · exact ⟨id, fun h => absurd h hjk⟩
  choose g hg using hstep
  -- disjointness of the columns
  have hLL : ∀ i i', i ≠ i' → Disjoint (Lay i) (Lay i') := by
    intro i i' h
    refine disjoint_union_left.2 ⟨disjoint_union_right.2 ⟨hLTd i i' h, dcol _ _ (cT i) (cF i')⟩,
      disjoint_union_right.2 ⟨(dcol _ _ (cT i') (cF i)).symm, hLFd i i' h⟩⟩
  have hPO : Disjoint P O := disjoint_of_subset_right
    (subset_union_left.trans (subset_union_left.trans subset_union_left)) hPd
  have hPI : Disjoint P I := disjoint_of_subset_right
    (subset_union_right.trans (subset_union_left.trans subset_union_left)) hPd
  have hPU : Disjoint P U' := disjoint_of_subset_right
    (subset_union_right.trans subset_union_left) hPd
  have hPW : Disjoint P W' := disjoint_of_subset_right subset_union_right hPd
  have hLO : ∀ i, Disjoint (Lay i) O := fun i => disjoint_of_subset_left (hLayP i) hPO
  have hLI : ∀ i, Disjoint (Lay i) I := fun i => disjoint_of_subset_left (hLayP i) hPI
  have hLU : ∀ i, Disjoint (Lay i) U' := fun i => disjoint_of_subset_left (hLayP i) hPU
  have hLW : ∀ i, Disjoint (Lay i) W' := fun i => disjoint_of_subset_left (hLayP i) hPW
  have hzAO : zA ∉ O := fun h => hzA (mem_union_left _ (mem_union_left _ (mem_union_left _ h)))
  have hzAI : zA ∉ I := fun h => hzA (mem_union_left _ (mem_union_left _ (mem_union_right _ h)))
  have hzAW : zA ∉ W := fun h => hzA (mem_union_right _ h)
  have hzBO : zB ∉ O := fun h => hzB (mem_union_left _ (mem_union_left _ (mem_union_left _ h)))
  have hzBI : zB ∉ I := fun h => hzB (mem_union_left _ (mem_union_left _ (mem_union_right _ h)))
  have hzBU : zB ∉ U := fun h => hzB (mem_union_left _ (mem_union_right _ h))
  have hzAB : zA ≠ zB := fun h => by rw [h, hzBc] at hzAc; exact absurd hzAc (by simp)
  have hOU' : Disjoint O U' := by
    rw [hU', disjoint_insert_right]
    exact ⟨hzAO, disjoint_of_subset_right (erase_subset _ _) hOU⟩
  have hOW' : Disjoint O W' := by
    rw [hW', disjoint_insert_right]
    exact ⟨hzBO, disjoint_of_subset_right (erase_subset _ _) hOW⟩
  have hU'W' : Disjoint U' W' := by
    rw [hU', hW', disjoint_insert_left, disjoint_insert_right, mem_insert, not_or]
    refine ⟨⟨hzAB, fun h => hzAW (mem_of_mem_erase h)⟩, fun h => hzBU (mem_of_mem_erase h),
      disjoint_of_subset_left (erase_subset _ _) (disjoint_of_subset_right (erase_subset _ _) hUW)⟩
  have hU'I : Disjoint U' I := by
    rw [hU', disjoint_insert_left]
    exact ⟨hzAI, disjoint_of_subset_left (erase_subset _ _) hIU.symm⟩
  have hW'I : Disjoint W' I := by
    rw [hW', disjoint_insert_left]
    exact ⟨hzBI, disjoint_of_subset_left (erase_subset _ _) hIW.symm⟩
  have hdisj : ∀ j j', j ≤ t + 3 → j' ≤ t + 3 → j ≠ j' → Disjoint (C j) (C j') := by
    intro j j' hj hj' hne
    simp only [hC]
    split_ifs <;> first
      | (exfalso; omega)
      | exact hLL _ _ (by omega)
      | exact hLO _ | exact (hLO _).symm | exact hLI _ | exact (hLI _).symm
      | exact hLU _ | exact (hLU _).symm | exact hLW _ | exact (hLW _).symm
      | exact hOU' | exact hOU'.symm | exact hOW' | exact hOW'.symm | exact hOI | exact hOI.symm
      | exact hU'W' | exact hU'W'.symm | exact hU'I | exact hU'I.symm | exact hW'I
      | exact hW'I.symm
  -- the grid
  have hOcard : (C 0).card = 2 * m := by
    rw [C0, ← card_filter_add_card_filter_not (s := O) (fun x => col x = true)]
    have e : (O.filter fun x => ¬ col x = true) = O.filter fun x => col x = false := by
      congr 1; ext x; simp
    rw [e, hmT O (Or.inl rfl), hmF O (Or.inl rfl)]; ring
  obtain ⟨φ, hinj, hmem, hsucc⟩ := grid C (t + 3) (2 * m) g hOcard
    (fun j hj => (hg j hj).1) hdisj
  refine ⟨t + 3, by omega, φ, hinj, fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_,
    fun v => ?_, fun i => ?_, fun i j hj hj2 => ?_⟩
  · rw [← hmem 0 (by omega) v, C0]
  · rw [← hmem (t + 3) le_rfl v, Ck]
  · rw [← hmem 2 (by omega) v, C2]
  · rw [← hmem 3 (by omega) v, C3]
  · constructor
    · intro hv
      obtain ⟨l, hl, hvl⟩ := hcov v hv
      rcases Nat.eq_zero_or_pos l with rfl | hl0
      · obtain ⟨i, hi⟩ := (hmem 1 (by omega) v).1 (by rw [C1]; exact hvl)
        exact ⟨i, 1, Or.inl rfl, hi⟩
      · obtain ⟨i, hi⟩ := (hmem (l + 3) (by omega) v).1
          (by rw [Cmid (l + 3) (by omega) (by omega), Nat.add_sub_cancel]; exact hvl)
        exact ⟨i, l + 3, Or.inr ⟨by omega, by omega⟩, hi⟩
    · rintro ⟨i, j, hj, rfl⟩
      rcases hj with rfl | ⟨hj4, hjk⟩
      · have := (hmem 1 (by omega) (φ i 1)).2 ⟨i, rfl⟩
        rw [C1] at this; exact hLayP 0 this
      · have := (hmem j hjk.le (φ i j)).2 ⟨i, rfl⟩
        rw [Cmid j hj4 hjk] at this; exact hLayP _ this
  · rw [hsucc, (hg 2 (by omega)).2.2 rfl]
  · rw [hsucc]
    exact (hg j hj).2.1 hj2 _ ((hmem j hj.le _).2 ⟨i, rfl⟩)

end Assembly

/-! ### The sampling lemmas, transported to the ambient vertex type -/

section Sampling

open Classical in
/-- The conclusion of Lemma 2.4 (`fixed_boundary_fresh_layer`) for fixed constants. -/
def Spec24 (ω c₂ K δ c C a : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (A B U B' : Finset V)
    (N k : ℕ) (η D σ L : ℝ),
    Disjoint A B → A ∪ B = univ → A.card = N → B.card = N →
    (∀ x ∈ A, ∀ y ∈ A, H.w x y = 0) → (∀ x ∈ B, ∀ y ∈ B, H.w x y = 0) →
    H.WeightsIn ω → H.DegNear D η → H.HasGap σ → 0 < σ → σ ≤ 1 → η ≤ c * σ →
    Real.log (2 * N) ≤ L → U ⊆ A → U.card = k →
    OneSided H A B U ((k : ℝ) / N) D σ L K δ →
    B' ⊆ B → (1 - c * σ) * N ≤ B'.card → (∀ v, H.degOn v (B \ B') ≤ c * σ * D) →
    C * σ ^ (-2 : ℝ) * L ≤ (k : ℝ) / N * D →
    (((B'.powersetCard k).filter fun W =>
        ¬ ((H.induce (U ∪ W)).DegNear ((k : ℝ) / N * D) (δ * σ) ∧
          (H.induce (U ∪ W)).HasGap (c₂ * σ))).card : ℝ) ≤
      Real.exp (-(a * L)) * (B'.card.choose k : ℕ)

open Classical in
/-- The conclusion of Lemma 2.3 (`bipartite_sampling`) for fixed constants. -/
def Spec23 (ω c₂ c₁ c C a : ℝ) : Prop :=
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

/-- The conclusion of Lemma 2.1 (`hasGap_of_deletion`) for fixed constants. -/
def Spec21 (a b c' C' : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (A : Finset V) (H' : WGraph A)
    (D σ β : ℝ),
    0 < D → H.DegBetween (a * D) (b * D) → H.HasGap σ →
    (∀ x y : A, H'.w x y ≤ H.w x y) → (∀ x : A, H.deg x - H'.deg x ≤ β) →
    0 ≤ β → β ≤ c' * D →
    H'.HasGap (σ - C' * β / D)

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Pull back a finset of `α` to the subtype `↥S`. -/
def pb (S Y : Finset α) : Finset ↥S := Y.subtype (· ∈ S)

omit [Fintype α] in
lemma mem_pb {S Y : Finset α} {x : ↥S} : x ∈ pb S Y ↔ x.1 ∈ Y := mem_subtype

omit [Fintype α] in
lemma pb_map (S Y : Finset α) (h : Y ⊆ S) :
    (pb S Y).map (Function.Embedding.subtype _) = Y := by
  rw [pb, subtype_map]; exact filter_true_of_mem h

omit [Fintype α] in
lemma card_pb (S Y : Finset α) (h : Y ⊆ S) : (pb S Y).card = Y.card := by
  rw [← card_map (Function.Embedding.subtype _), pb_map S Y h]

omit [Fintype α] in
lemma sum_pb (S Y : Finset α) (h : Y ⊆ S) (g : α → ℝ) :
    ∑ y ∈ pb S Y, g y.1 = ∑ y ∈ Y, g y := by
  have := sum_map (pb S Y) (Function.Embedding.subtype _) g
  rw [pb_map S Y h] at this
  exact this.symm

omit [Fintype α] in
lemma degOn_pb (H : WGraph α) (S Y : Finset α) (h : Y ⊆ S) (x : ↥S) :
    (H.induce S).degOn x (pb S Y) = H.degOn x.1 Y :=
  sum_pb S Y h (fun y => H.w x.1 y)

omit [Fintype α] in
lemma edgeWeight_pb (H : WGraph α) (S X Y : Finset α) (hX : X ⊆ S) (hY : Y ⊆ S) :
    (H.induce S).edgeWeight (pb S X) (pb S Y) = H.edgeWeight X Y := by
  unfold WGraph.edgeWeight
  calc ∑ x ∈ pb S X, ∑ y ∈ pb S Y, (H.induce S).w x y = ∑ x ∈ pb S X, H.degOn x.1 Y :=
        sum_congr rfl fun x _ => degOn_pb H S Y hY x
    _ = ∑ x ∈ X, H.degOn x Y := sum_pb S X hX (fun x => H.degOn x Y)

lemma centred_pb (H : WGraph α) (S A B : Finset α) (hA : A ⊆ S) (hB : B ⊆ S) (x y : ↥S) :
    centred (H.induce S) (pb S A) (pb S B) x y = centred H A B x.1 y.1 := by
  unfold centred
  rw [degOn_pb H S B hB, degOn_pb H S A hA, edgeWeight_pb H S A B hA hB]
  rfl

lemma oneSided_pb (H : WGraph α) (S A B U : Finset α) (hA : A ⊆ S) (hB : B ⊆ S) (hU : U ⊆ S)
    {p D σ L K δ : ℝ} (h : OneSided H A B U p D σ L K δ) :
    OneSided (H.induce S) (pb S A) (pb S B) (pb S U) p D σ L K δ where
  norm_le := by
    intro v
    set v' : α → ℝ := fun z => if hz : z ∈ S then v ⟨z, hz⟩ else 0 with hv'
    have hv : ∀ y : ↥S, v' y.1 = v y := fun y => by simp [hv', y.2]
    have := h.norm_le v'
    calc ∑ x ∈ pb S U, (∑ y ∈ pb S B, centred (H.induce S) (pb S A) (pb S B) x y * v y) ^ 2
        = ∑ x ∈ pb S U, (∑ y ∈ B, centred H A B x.1 y * v' y) ^ 2 := by
          refine sum_congr rfl fun x _ => ?_
          congr 1
          rw [← sum_pb S B hB (fun y => centred H A B x.1 y * v' y)]
          exact sum_congr rfl fun y _ => by rw [centred_pb H S A B hA hB, hv]
      _ = ∑ x ∈ U, (∑ y ∈ B, centred H A B x y * v' y) ^ 2 :=
          sum_pb S U hU (fun x => (∑ y ∈ B, centred H A B x y * v' y) ^ 2)
      _ ≤ _ := this
      _ = _ := by
          congr 1
          rw [← sum_pb S B hB (fun y => v' y ^ 2)]
          exact sum_congr rfl fun y _ => by rw [hv]
  col_le := by
    intro y hy
    rw [mem_pb] at hy
    have := h.col_le y.1 hy
    calc ∑ x ∈ pb S U, centred (H.induce S) (pb S A) (pb S B) x y ^ 2
        = ∑ x ∈ pb S U, centred H A B x.1 y.1 ^ 2 :=
          sum_congr rfl fun x _ => by rw [centred_pb H S A B hA hB]
      _ = ∑ x ∈ U, centred H A B x y.1 ^ 2 := sum_pb S U hU (fun x => centred H A B x y.1 ^ 2)
      _ ≤ _ := this
  deg_near := by
    intro y hy
    rw [mem_pb] at hy
    rw [degOn_pb H S U hU]
    exact h.deg_near y.1 hy

lemma classOf_disj (E : Finset α) (col : α → Bool) (b : Bool) :
    Disjoint (classOf E col b) (classOf E col (!b)) :=
  disjoint_filter.2 fun x _ h1 h2 => by rw [h1] at h2; cases b <;> simp at h2

lemma classOf_union (E : Finset α) (col : α → Bool) (b : Bool) :
    classOf E col b ∪ classOf E col (!b) = univ \ E := by
  ext x
  simp only [classOf, mem_union, mem_filter]
  cases b <;> cases col x <;> simp

lemma degOn_class (H : WGraph α) (col : α → Bool) (hbip : H.IsBipartiteWith col)
    (E : Finset α) (b : Bool) (x : α) (hx : col x = b) :
    H.degOn x (univ \ E) = H.degOn x (classOf E col (!b)) := by
  rw [← classOf_union E col b, degOn_union_of_zero H (classOf_disj E col b) x]
  intro y hy
  refine le_antisymm (not_lt.1 fun h => hbip x y h ?_) (H.nonneg x y)
  rw [hx, (mem_filter.1 hy).2]

lemma deg0_near (H : WGraph α) (E : Finset α) {D η : ℝ}
    (hdeg : (H.induce (univ \ E)).DegNear D η) (x : α) (hx : x ∉ E) :
    |H.degOn x (univ \ E) - D| ≤ η * D := by
  have := hdeg ⟨x, mem_sdiff.2 ⟨mem_univ x, hx⟩⟩
  rwa [induce_deg_eq] at this

lemma class_deg (H : WGraph α) (col : α → Bool) (hbip : H.IsBipartiteWith col) (E : Finset α)
    {D η : ℝ} (hdeg : (H.induce (univ \ E)).DegNear D η) (b : Bool) (x : α)
    (hx : x ∈ classOf E col b) : |H.degOn x (classOf E col (!b)) - D| ≤ η * D := by
  have h := deg0_near H E hdeg x (mem_sdiff.1 (filter_subset _ _ hx)).2
  rwa [degOn_class H col hbip E b x (mem_filter.1 hx).2] at h

lemma class_deg' (H : WGraph α) (col : α → Bool) (hbip : H.IsBipartiteWith col) (E : Finset α)
    {D η : ℝ} (hdeg : (H.induce (univ \ E)).DegNear D η) (b : Bool) (x : α)
    (hx : x ∈ classOf E col (!b)) : |H.degOn x (classOf E col b) - D| ≤ η * D := by
  have h := class_deg H col hbip E hdeg (!b) x hx
  rwa [Bool.not_not] at h

/-- The one-sided events with constants `(σ₀, K, δ)` imply those with `(σ₀/2, 10, 2δ)` once
`p D ≥ 16 K² σ₀⁻² L`: the column bound follows from the degree bounds. -/
lemma oneSided_weaken (H : WGraph α) (col : α → Bool) (E : Finset α)
    (hbip : H.IsBipartiteWith col) (hw1 : ∀ x y, H.w x y ≤ 1) (b : Bool) (N₀ m : ℕ)
    (X : Finset α) (hX : X ⊆ classOf E col b) (hA : (classOf E col b).card = N₀)
    (hB : (classOf E col (!b)).card = N₀) (hXm : X.card = m) (hm : 1 ≤ m)
    (η₀ D σ₀ L K δ : ℝ) (hdeg : (H.induce (univ \ E)).DegNear D η₀) (hη0 : 0 ≤ η₀)
    (hη : η₀ ≤ 1 / 10) (hD : 0 < D) (hσ : 0 < σ₀) (hσ1 : σ₀ ≤ 1) (hδσ : δ * σ₀ ≤ 1)
    (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hKp : 16 * K ^ 2 * σ₀ ^ (-(2 : ℝ)) * L ≤ (m : ℝ) / N₀ * D)
    (h : OneSided H (classOf E col b) (classOf E col (!b)) X ((m : ℝ) / N₀) D σ₀ L K δ) :
    OneSided H (classOf E col b) (classOf E col (!b)) X ((m : ℝ) / N₀) D (σ₀ / 2) L 10
      (2 * δ) := by
  set A₀ := classOf E col b with hA₀
  set B₀ := classOf E col (!b) with hB₀
  set p : ℝ := (m : ℝ) / N₀ with hp
  obtain ⟨x₀, hx₀⟩ : X.Nonempty := card_pos.1 (by omega)
  have hN0 : (0 : ℝ) < N₀ := by
    have : 0 < A₀.card := card_pos.2 ⟨x₀, hX hx₀⟩
    rw [hA] at this; exact_mod_cast this
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hp0 : 0 < p := div_pos hm0 hN0
  have hdA := fun x hx => abs_le.1 (class_deg H col hbip E hdeg b x hx)
  have hdB := fun y hy => abs_le.1 (class_deg' H col hbip E hdeg b y hy)
  have hDN : D ≤ 10 / 9 * N₀ := by
    have h1 := hdA x₀ (hX hx₀)
    have h2 : H.degOn x₀ B₀ ≤ N₀ := by
      calc H.degOn x₀ B₀ ≤ ∑ y ∈ B₀, (1 : ℝ) := sum_le_sum fun y _ => hw1 _ _
        _ = N₀ := by rw [sum_const, hB]; simp
    nlinarith
  have he : (N₀ : ℝ) * ((1 - η₀) * D) ≤ H.edgeWeight A₀ B₀ := by
    have := RobustHall.le_eW_of_le_deg H (A := A₀) (B := B₀) (c := (1 - η₀) * D)
      (fun a ha => by have := hdA a ha; linarith)
    rwa [hA] at this
  have hepos : 0 < H.edgeWeight A₀ B₀ :=
    lt_of_lt_of_le (mul_pos hN0 (mul_pos (by linarith) hD)) he
  have hr : ∀ x ∈ A₀, ∀ y ∈ B₀, 0 ≤ H.degOn x B₀ * H.degOn y A₀ / H.edgeWeight A₀ B₀ ∧
      H.degOn x B₀ * H.degOn y A₀ / H.edgeWeight A₀ B₀ ≤ 2 * D / N₀ := by
    intro x hx y hy
    have h1 := hdA x hx
    have h2 := hdB y hy
    have hx0 : 0 ≤ H.degOn x B₀ := by nlinarith
    have hy0 : 0 ≤ H.degOn y A₀ := by nlinarith
    refine ⟨by positivity, ?_⟩
    rw [div_le_div_iff₀ hepos hN0]
    have h3 : H.degOn x B₀ * H.degOn y A₀ ≤ ((1 + η₀) * D) * ((1 + η₀) * D) :=
      mul_le_mul (by linarith) (by linarith) hy0 (by positivity)
    have h4 : 2 * D * (N₀ * ((1 - η₀) * D)) ≤ 2 * D * H.edgeWeight A₀ B₀ :=
      mul_le_mul_of_nonneg_left he (by positivity)
    have h5 : ((1 + η₀) * D) * ((1 + η₀) * D) * N₀ ≤ 2 * D * (N₀ * ((1 - η₀) * D)) := by
      have : (1 + η₀) * (1 + η₀) ≤ 2 * (1 - η₀) := by nlinarith
      have h6 : 0 ≤ D * D * N₀ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this h6]
    nlinarith
  have hsq : 16 * K ^ 2 * L ≤ σ₀ ^ 2 * (p * D) := by
    rw [Real.rpow_neg hσ.le, Real.rpow_two] at hKp
    have h1 := mul_le_mul_of_nonneg_left hKp (sq_nonneg σ₀)
    have h2 : σ₀ ^ 2 * (16 * K ^ 2 * (σ₀ ^ 2)⁻¹ * L) = 16 * K ^ 2 * L := by field_simp
    linarith
  refine ⟨fun v => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have h1 := h.norm_le v
    refine le_trans h1 (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun y _ => sq_nonneg _))
    have hDL : 0 ≤ D * L := by positivity
    have hsqrt : K * Real.sqrt (D * L) ≤ Real.sqrt p * σ₀ * D / 4 := by
      have ha : 0 ≤ K * Real.sqrt (D * L) := by positivity
      have hb : 0 ≤ Real.sqrt p * σ₀ * D / 4 := by positivity
      have hsq' : (K * Real.sqrt (D * L)) ^ 2 ≤ (Real.sqrt p * σ₀ * D / 4) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hDL, div_pow, mul_pow, mul_pow, Real.sq_sqrt hp0.le]
        have := mul_le_mul_of_nonneg_left hsq (show 0 ≤ D / 16 by positivity)
        nlinarith
      nlinarith
    have h0 : 0 ≤ Real.sqrt p * (1 - σ₀ / 2) * D + K * Real.sqrt (D * L) := by
      have : 0 ≤ 1 - σ₀ / 2 := by linarith
      positivity
    have hle : Real.sqrt p * (1 - σ₀ / 2) * D + K * Real.sqrt (D * L) ≤
        Real.sqrt p * (1 - σ₀ / 2 / 2) * D + 10 * Real.sqrt (D * L) := by
      have : 0 ≤ 10 * Real.sqrt (D * L) := by positivity
      nlinarith
    exact pow_le_pow_left₀ h0 hle 2
  · have hdn := abs_le.1 (h.deg_near y hy)
    have hsum : ∑ x ∈ X, centred H A₀ B₀ x y ^ 2 ≤ ∑ x ∈ X, (H.w y x + (2 * D / N₀) ^ 2) := by
      refine sum_le_sum fun x hx => ?_
      obtain ⟨r0, r1⟩ := hr x (hX hx) y hy
      unfold centred
      rw [H.symm x y]
      have hw0 := H.nonneg y x
      have hw1' := hw1 y x
      set r := H.degOn x B₀ * H.degOn y A₀ / H.edgeWeight A₀ B₀
      have : r ^ 2 ≤ (2 * D / N₀) ^ 2 := pow_le_pow_left₀ r0 r1 2
      nlinarith
    rw [sum_add_distrib, sum_const, hXm, nsmul_eq_mul] at hsum
    have hdegX : ∑ x ∈ X, H.w y x = H.degOn y X := rfl
    rw [hdegX] at hsum
    have hmD : (m : ℝ) * (2 * D / N₀) ^ 2 ≤ 40 / 9 * (p * D) := by
      have e : (m : ℝ) * (2 * D / N₀) ^ 2 = 4 * (p * D) * (D / N₀) := by
        rw [hp]; field_simp; ring
      rw [e]
      have : D / N₀ ≤ 10 / 9 := by rw [div_le_iff₀ hN0]; linarith
      have hpD0 : 0 ≤ p * D := by positivity
      have := mul_le_mul_of_nonneg_left this (show 0 ≤ 4 * (p * D) by positivity)
      linarith
    have hpD0 : 0 ≤ p * D := by positivity
    have : δ * σ₀ * p * D ≤ p * D := by
      calc δ * σ₀ * p * D = (δ * σ₀) * (p * D) := by ring
        _ ≤ 1 * (p * D) := mul_le_mul_of_nonneg_right hδσ hpD0
        _ = p * D := one_mul _
    linarith [hdn.2]
  · have := h.deg_near y hy
    calc |H.degOn y X - p * D| ≤ δ * σ₀ * p * D := this
      _ = 2 * δ * (σ₀ / 2) * p * D := by ring

lemma card_filter_powersetCard_map {β γ : Type*} [DecidableEq γ] (ι : β ↪ γ) (S : Finset β)
    (k : ℕ) (P : Finset γ → Prop) [DecidablePred P] (Q : Finset β → Prop) [DecidablePred Q]
    (hPQ : ∀ I, P (I.map ι) → Q I) :
    (((S.map ι).powersetCard k).filter P).card ≤ ((S.powersetCard k).filter Q).card := by
  rw [powersetCard_map, filter_map, card_map]
  refine card_le_card fun I => ?_
  simp only [mem_filter, Function.comp_apply]
  exact fun hI => ⟨hI.1, hPQ I hI.2⟩

lemma card_filter_prod_map {β γ : Type*} [DecidableEq β] [DecidableEq γ] (ι : β ↪ γ)
    (S₁ S₂ : Finset β) (k : ℕ) (P : Finset γ × Finset γ → Prop) [DecidablePred P]
    (Q : Finset β × Finset β → Prop) [DecidablePred Q]
    (hPQ : ∀ I J, P (I.map ι, J.map ι) → Q (I, J)) :
    ((((S₁.map ι).powersetCard k) ×ˢ ((S₂.map ι).powersetCard k)).filter P).card ≤
      (((S₁.powersetCard k) ×ˢ (S₂.powersetCard k)).filter Q).card := by
  refine le_trans (card_le_card ?_) (card_image_le
    (s := ((S₁.powersetCard k) ×ˢ (S₂.powersetCard k)).filter Q)
    (f := fun p : Finset β × Finset β => (p.1.map ι, p.2.map ι)))
  rintro ⟨T₁, T₂⟩ hT
  rw [mem_filter, mem_product, powersetCard_map, powersetCard_map] at hT
  obtain ⟨⟨h1, h2⟩, hP⟩ := hT
  obtain ⟨I, hI, rfl⟩ := mem_map.1 h1
  obtain ⟨J, hJ, rfl⟩ := mem_map.1 h2
  exact mem_image.2 ⟨(I, J), mem_filter.2 ⟨mem_product.2 ⟨hI, hJ⟩, hPQ I J hP⟩, rfl⟩

end Sampling

section Sampling'

open Classical in
/-- Lemma 2.4 for a fixed block of `H` (not of `H - E`), in ambient form. -/
lemma fixed_count {ω c₂ K δ c C a : ℝ} (h24 : Spec24.{u} ω c₂ K δ c C a)
    {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (col : V → Bool) (E : Finset V)
    (hbip : H.IsBipartiteWith col) (hwt : H.WeightsIn ω) (N₀ m : ℕ) (b : Bool)
    (hA : (classOf E col b).card = N₀) (hB : (classOf E col (!b)).card = N₀)
    (η D σ L : ℝ) (hdeg : (H.induce (univ \ E)).DegNear D η)
    (hgap : (H.induce (univ \ E)).HasGap σ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hη : η ≤ c * σ)
    (hL : Real.log (2 * N₀) ≤ L) (X : Finset V) (hX : X ⊆ classOf E col b) (hXc : X.card = m)
    (hos : OneSided H (classOf E col b) (classOf E col (!b)) X ((m : ℝ) / N₀) D σ L K δ)
    (Pb : Finset V) (hPb : Pb ⊆ classOf E col (!b)) (hPc : (1 - c * σ) * N₀ ≤ Pb.card)
    (hloss : ∀ v, H.degOn v (classOf E col (!b) \ Pb) ≤ c * σ * D)
    (hpD : C * σ ^ (-2 : ℝ) * L ≤ (m : ℝ) / N₀ * D) (σ' : ℝ) (hσ' : σ' ≤ c₂ * σ) :
    (((Pb.powersetCard m).filter fun T =>
        ¬ Good H X T ((m : ℝ) / N₀ * D) (δ * σ) σ').card : ℝ) ≤
      Real.exp (-(a * L)) * (Pb.card.choose m : ℕ) := by
  set S₀ : Finset V := univ \ E with hS₀
  have hAS : classOf E col b ⊆ S₀ := filter_subset _ _
  have hBS : classOf E col (!b) ⊆ S₀ := filter_subset _ _
  have hXS : X ⊆ S₀ := hX.trans hAS
  have hPS : Pb ⊆ S₀ := hPb.trans hBS
  have hdisj : Disjoint (pb S₀ (classOf E col b)) (pb S₀ (classOf E col (!b))) := by
    rw [← disjoint_map (Function.Embedding.subtype _), pb_map _ _ hAS, pb_map _ _ hBS]
    exact classOf_disj E col b
  have hunion : pb S₀ (classOf E col b) ∪ pb S₀ (classOf E col (!b)) = univ := by
    ext x
    simp only [mem_union, mem_pb, mem_univ, iff_true]
    rw [← mem_union, classOf_union]
    exact x.2
  have hzero : ∀ b' : Bool, ∀ x ∈ pb S₀ (classOf E col b'), ∀ y ∈ pb S₀ (classOf E col b'),
      (H.induce S₀).w x y = 0 := by
    intro b' x hx y hy
    rw [mem_pb] at hx hy
    exact bip_zero H col hbip _ b' (fun z hz => (mem_filter.1 hz).2) x.1 hx y.1 hy
  have hwt₀ : (H.induce S₀).WeightsIn ω := fun x y h => hwt x.1 y.1 h
  have hsub : pb S₀ X ⊆ pb S₀ (classOf E col b) := fun x hx => mem_pb.2 (hX (mem_pb.1 hx))
  have hsub' : pb S₀ Pb ⊆ pb S₀ (classOf E col (!b)) :=
    fun x hx => mem_pb.2 (hPb (mem_pb.1 hx))
  have hloss₀ : ∀ v : ↥S₀, (H.induce S₀).degOn v (pb S₀ (classOf E col (!b)) \ pb S₀ Pb) ≤
      c * σ * D := by
    intro v
    have e : pb S₀ (classOf E col (!b)) \ pb S₀ Pb = pb S₀ (classOf E col (!b) \ Pb) := by
      ext x; simp [mem_pb]
    rw [e, degOn_pb H S₀ _ (sdiff_subset.trans hBS)]
    exact hloss v.1
  have key := h24 (H.induce S₀) (pb S₀ (classOf E col b)) (pb S₀ (classOf E col (!b)))
    (pb S₀ X) (pb S₀ Pb) N₀ m η D σ L hdisj hunion (by rw [card_pb _ _ hAS, hA])
    (by rw [card_pb _ _ hBS, hB]) (hzero b) (hzero (!b)) hwt₀ hdeg hgap hσ hσ1 hη hL hsub
    (by rw [card_pb _ _ hXS, hXc]) (oneSided_pb H S₀ _ _ _ hAS hBS hXS hos) hsub'
    (by rw [card_pb _ _ hPS]; exact hPc) hloss₀ hpD
  rw [card_pb _ _ hPS] at key
  refine le_trans ?_ key
  have hle : ((Pb.powersetCard m).filter fun T =>
      ¬ Good H X T ((m : ℝ) / N₀ * D) (δ * σ) σ').card ≤
      (((pb S₀ Pb).powersetCard m).filter fun W =>
        ¬ (((H.induce S₀).induce (pb S₀ X ∪ W)).DegNear ((m : ℝ) / N₀ * D) (δ * σ) ∧
          ((H.induce S₀).induce (pb S₀ X ∪ W)).HasGap (c₂ * σ))).card := by
    have e := pb_map S₀ Pb hPS
    conv_lhs => rw [← e]
    refine card_filter_powersetCard_map (Function.Embedding.subtype _) (pb S₀ Pb) m _ _ ?_
    intro W hW hgood
    apply hW
    have hmap : (pb S₀ X ∪ W).map (Function.Embedding.subtype _) =
        X ∪ W.map (Function.Embedding.subtype _) := by rw [map_union, pb_map S₀ X hXS]
    exact ⟨degNear_map H S₀ _ _ hmap hgood.1, hasGap_mono _ (hasGap_map H S₀ _ _ hmap hgood.2) hσ'⟩
  exact_mod_cast hle

open Classical in
/-- Lemma 2.3 for the pool, in ambient form. -/
lemma fresh_count {ω c₂ c₁ c C a : ℝ} (h23 : Spec23.{u} ω c₂ c₁ c C a)
    {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (col : V → Bool)
    (hbip : H.IsBipartiteWith col) (hwt : H.WeightsIn ω) (P : Finset V) (n m : ℕ)
    (hPt : (P.filter fun x => col x = true).card = n)
    (hPf : (P.filter fun x => col x = false).card = n)
    (η D σ L : ℝ) (hdeg : (H.induce P).DegNear D η) (hgap : (H.induce P).HasGap σ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hη : η ≤ c * σ) (hL : Real.log (2 * n) ≤ L) (hmn : m ≤ n)
    (hpD : C * σ ^ (-2 : ℝ) * L ≤ (m : ℝ) / n * D) (σ' : ℝ) (hσ' : σ' ≤ c₂ * σ) :
    (((((P.filter fun x => col x = true).powersetCard m) ×ˢ
        ((P.filter fun x => col x = false).powersetCard m)).filter fun p =>
        ¬ Good H p.1 p.2 ((m : ℝ) / n * D) (c₁ * σ) σ').card : ℝ) ≤
      Real.exp (-(a * L)) * ((n.choose m : ℕ) : ℝ) ^ 2 := by
  set PT := P.filter fun x => col x = true with hPT
  set PF := P.filter fun x => col x = false with hPF
  have hTS : PT ⊆ P := filter_subset _ _
  have hFS : PF ⊆ P := filter_subset _ _
  have hdisj : Disjoint (pb P PT) (pb P PF) := by
    rw [← disjoint_map (Function.Embedding.subtype _), pb_map _ _ hTS, pb_map _ _ hFS]
    exact disjoint_filter.2 fun x _ h1 h2 => by rw [h1] at h2; exact absurd h2 (by simp)
  have hunion : pb P PT ∪ pb P PF = univ := by
    ext x
    simp only [mem_union, mem_pb, mem_univ, iff_true, hPT, hPF, mem_filter]
    cases col x.1 <;> simp [x.2]
  have hzero : ∀ b' : Bool, ∀ x ∈ pb P (P.filter fun x => col x = b'),
      ∀ y ∈ pb P (P.filter fun x => col x = b'), (H.induce P).w x y = 0 := by
    intro b' x hx y hy
    rw [mem_pb] at hx hy
    exact bip_zero H col hbip _ b' (fun z hz => (mem_filter.1 hz).2) x.1 hx y.1 hy
  have hwtP : (H.induce P).WeightsIn ω := fun x y h => hwt x.1 y.1 h
  have key := h23 (H.induce P) (pb P PT) (pb P PF) n m η D σ L hdisj hunion
    (by rw [card_pb _ _ hTS, hPt]) (by rw [card_pb _ _ hFS, hPf]) (hzero true) (hzero false)
    hwtP hdeg hgap hσ hσ1 hη hL hmn hpD
  refine le_trans ?_ key
  have hle : ((((PT.powersetCard m) ×ˢ (PF.powersetCard m)).filter fun p =>
        ¬ Good H p.1 p.2 ((m : ℝ) / n * D) (c₁ * σ) σ').card) ≤
      ((((pb P PT).powersetCard m ×ˢ (pb P PF).powersetCard m).filter fun UW =>
        ¬ (((H.induce P).induce (UW.1 ∪ UW.2)).DegNear ((m : ℝ) / n * D) (c₁ * σ) ∧
          ((H.induce P).induce (UW.1 ∪ UW.2)).HasGap (c₂ * σ)))).card := by
    have e1 := pb_map P PT hTS
    have e2 := pb_map P PF hFS
    conv_lhs => rw [← e1, ← e2]
    refine card_filter_prod_map (Function.Embedding.subtype _) (pb P PT) (pb P PF) m _ _ ?_
    intro I J hIJ hgood
    apply hIJ
    have hmap : (I ∪ J).map (Function.Embedding.subtype _) =
        I.map (Function.Embedding.subtype _) ∪ J.map (Function.Embedding.subtype _) :=
      map_union _ _
    exact ⟨degNear_map H P _ _ hmap hgood.1, hasGap_mono _ (hasGap_map H P _ _ hmap hgood.2) hσ'⟩
  exact_mod_cast hle

/-- Degrees in the pool graph `H[P]`. -/
lemma pool_degNear {V : Type*} [Fintype V] [DecidableEq V] (H : WGraph V) (E P S : Finset V)
    {D η₀ ε : ℝ} (hdeg : (H.induce (univ \ E)).DegNear D η₀) (hPE : Disjoint P E)
    (hS : (univ \ E) \ P ⊆ S) (hSdeg : ∀ v, H.degOn v S ≤ ε * D) :
    (H.induce P).DegNear D (η₀ + ε) := by
  intro x
  rw [induce_deg_eq]
  have hxE : x.1 ∉ E := disjoint_left.1 hPE x.2
  have h1 := abs_le.1 (deg0_near H E hdeg x.1 hxE)
  have hPsub : P ⊆ univ \ E := fun y hy => mem_sdiff.2 ⟨mem_univ y, disjoint_left.1 hPE hy⟩
  have h2 : H.degOn x.1 ((univ \ E) \ P) + H.degOn x.1 P = H.degOn x.1 (univ \ E) :=
    sum_sdiff hPsub
  have h3 : 0 ≤ H.degOn x.1 ((univ \ E) \ P) := sum_nonneg fun y _ => H.nonneg _ _
  have h4 : H.degOn x.1 ((univ \ E) \ P) ≤ ε * D :=
    (degOn_mono H x.1 hS).trans (hSdeg x.1)
  rw [abs_le]
  constructor <;> nlinarith

/-- The gap of the pool graph `H[P]` (Lemma 2.1). -/
lemma pool_gap {c' C' : ℝ} (h21 : Spec21.{u} (1 / 2) 2 c' C') {V : Type u} [Fintype V]
    [DecidableEq V] (H : WGraph V) (E P S : Finset V) {D η₀ σ₀ ε : ℝ} (hD : 0 < D)
    (hdeg : (H.induce (univ \ E)).DegNear D η₀) (hη : η₀ ≤ 1 / 2)
    (hgap : (H.induce (univ \ E)).HasGap σ₀) (hPE : Disjoint P E)
    (hS : (univ \ E) \ P ⊆ S) (hSdeg : ∀ v, H.degOn v S ≤ ε * D) (hε0 : 0 ≤ ε)
    (hεc : ε ≤ c') : (H.induce P).HasGap (σ₀ - C' * ε) := by
  set S₀ : Finset V := univ \ E with hS₀
  have hPsub : P ⊆ S₀ := fun y hy => mem_sdiff.2 ⟨mem_univ y, disjoint_left.1 hPE hy⟩
  have hDB : (H.induce S₀).DegBetween (1 / 2 * D) (2 * D) := fun x => by
    have := abs_le.1 (hdeg x)
    constructor <;> nlinarith
  have hloss : ∀ x : ↥(pb S₀ P), (H.induce S₀).deg x - ((H.induce S₀).induce (pb S₀ P)).deg x ≤
      ε * D := by
    intro x
    rw [induce_deg_eq, induce_deg_eq, degOn_pb H S₀ P hPsub]
    have h2 : H.degOn x.1.1 (S₀ \ P) + H.degOn x.1.1 P = H.degOn x.1.1 S₀ := sum_sdiff hPsub
    have h4 : H.degOn x.1.1 (S₀ \ P) ≤ ε * D := (degOn_mono H _ hS).trans (hSdeg _)
    linarith
  have hg := h21 (H.induce S₀) (pb S₀ P) ((H.induce S₀).induce (pb S₀ P)) D σ₀ (ε * D) hD hDB
    hgap (fun _ _ => le_rfl) hloss (by positivity) (mul_le_mul_of_nonneg_right hεc hD.le)
  have e : C' * (ε * D) / D = C' * ε := by field_simp
  rw [e] at hg
  exact hasGap_map H S₀ _ P (pb_map S₀ P hPsub) hg

open Classical in
/-- Concentration of the degree of a fixed vertex into a uniform layer (hypergeometric lower
tail). -/
lemma z_count {V : Type*} [Fintype V] [DecidableEq V] (H : WGraph V)
    (hw1 : ∀ x y, H.w x y ≤ 1) (z : V) (Pb : Finset V) (m : ℕ) (D₀ L : ℝ)
    (hμlo : 9 / 10 * D₀ ≤ (m : ℝ) / Pb.card * H.degOn z Pb)
    (hμhi : (m : ℝ) / Pb.card * H.degOn z Pb ≤ 6 / 5 * D₀) (hD₀ : 54 * L ≤ D₀)
    (hD10 : 10 ≤ D₀) :
    (((Pb.powersetCard m).filter fun T => ¬ (D₀ / 2 + 1 ≤ H.degOn z T)).card : ℝ) ≤
      Real.exp (-(2 * L)) * (Pb.card.choose m : ℕ) := by
  set μ := (m : ℝ) / Pb.card * H.degOn z Pb with hμ
  have hμ0 : 0 < μ := by linarith
  have h := BipSampling.hyp_lower_finset Pb (fun y => H.w z y)
    (fun y _ => ⟨H.nonneg _ _, hw1 _ _⟩) m (3 / 10 * D₀) (by linarith)
  have hsub : ((Pb.powersetCard m).filter fun T => ¬ (D₀ / 2 + 1 ≤ H.degOn z T)) ⊆
      ((Pb.powersetCard m).filter fun W =>
        ∑ j ∈ W, H.w z j ≤ (m : ℝ) / Pb.card * ∑ j ∈ Pb, H.w z j - 3 / 10 * D₀) := by
    intro T hT
    rw [mem_filter] at hT ⊢
    refine ⟨hT.1, ?_⟩
    have : H.degOn z T < D₀ / 2 + 1 := not_le.1 hT.2
    change H.degOn z T ≤ μ - 3 / 10 * D₀
    linarith
  refine le_trans (Nat.cast_le.2 (card_le_card hsub)) (le_trans h ?_)
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Nat.cast_nonneg _)
  change -((3 / 10 * D₀) ^ 2) / (2 * μ) ≤ -(2 * L)
  rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
  nlinarith

end Sampling'

/-! ### The fresh equipartition -/

section Main

open Classical in
lemma exists_good_list {Ω : Type*} [Fintype Ω] (l : List (Ω → Prop)) (ε : ℝ)
    (h : ∀ P ∈ l, ((univ.filter fun ω => ¬ P ω).card : ℝ) ≤ ε * Fintype.card Ω)
    (hs : l.length * ε < 1) (hε : 0 ≤ ε) (hΩ : 0 < Fintype.card Ω) :
    ∃ ω, ∀ P ∈ l, P ω := by
  obtain ⟨ω, hω⟩ := exists_good l.toFinset (fun P ω => P ω) ε
    (fun P hP => h P (List.mem_toFinset.1 hP))
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast List.toFinset_card_le l) hε)
      hs) hΩ
  exact ⟨ω, fun P hP => hω P (List.mem_toFinset.2 hP)⟩

lemma length_flatMap_pair {β : Type*} (l : List ℕ) (f g : ℕ → β) :
    (l.flatMap fun i => [f i, g i]).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [List.length_cons, List.length_nil]
    ring

lemma count_right {α : Type*} [DecidableEq α] (S₁ S₂ : Finset α) (m j : ℕ) (hm : 0 < m)
    (h₁ : m ≤ S₁.card) (h₂ : (j + 1) * m ≤ S₂.card) (Q : Finset α → Prop) [DecidablePred Q]
    (ε : ℝ)
    (hQ : (((S₂.powersetCard m).filter fun T => ¬ Q T).card : ℝ) ≤ ε * (S₂.card.choose m : ℕ)) :
    ((univ.filter fun ω : Equiv.Perm (Fin S₁.card) × Equiv.Perm (Fin S₂.card) =>
        ¬ Q (lay S₂ m ω.2 j)).card : ℝ) ≤
      ε * Fintype.card (Equiv.Perm (Fin S₁.card) × Equiv.Perm (Fin S₂.card)) := by
  have e : ((S₁.powersetCard m) ×ˢ (S₂.powersetCard m)).filter (fun p => ¬ Q p.2) =
      (S₁.powersetCard m) ×ˢ ((S₂.powersetCard m).filter fun T => ¬ Q T) := by
    ext ⟨a, b⟩; simp [mem_product, mem_filter, and_assoc]
  have hQ' : ((((S₁.powersetCard m) ×ˢ (S₂.powersetCard m)).filter fun p => ¬ Q p.2).card : ℝ) ≤
      ε * ((S₁.card.choose m : ℕ) * (S₂.card.choose m : ℕ)) := by
    rw [e, card_product, card_powersetCard, Nat.cast_mul]
    have h0 : (0 : ℝ) ≤ (S₁.card.choose m : ℕ) := Nat.cast_nonneg _
    calc ((S₁.card.choose m : ℕ) : ℝ) * (((S₂.powersetCard m).filter fun T => ¬ Q T).card : ℝ)
        ≤ (S₁.card.choose m : ℕ) * (ε * (S₂.card.choose m : ℕ)) :=
          mul_le_mul_of_nonneg_left hQ h0
      _ = _ := by ring
  exact count_pair S₁ S₂ m 0 j hm (by simpa using h₁) h₂ (fun p => Q p.2) ε hQ'

lemma count_left {α : Type*} [DecidableEq α] (S₁ S₂ : Finset α) (m j : ℕ) (hm : 0 < m)
    (h₁ : (j + 1) * m ≤ S₁.card) (h₂ : m ≤ S₂.card) (Q : Finset α → Prop) [DecidablePred Q]
    (ε : ℝ)
    (hQ : (((S₁.powersetCard m).filter fun T => ¬ Q T).card : ℝ) ≤ ε * (S₁.card.choose m : ℕ)) :
    ((univ.filter fun ω : Equiv.Perm (Fin S₁.card) × Equiv.Perm (Fin S₂.card) =>
        ¬ Q (lay S₁ m ω.1 j)).card : ℝ) ≤
      ε * Fintype.card (Equiv.Perm (Fin S₁.card) × Equiv.Perm (Fin S₂.card)) := by
  have e : ((S₁.powersetCard m) ×ˢ (S₂.powersetCard m)).filter (fun p => ¬ Q p.1) =
      ((S₁.powersetCard m).filter fun T => ¬ Q T) ×ˢ (S₂.powersetCard m) := by
    ext ⟨a, b⟩; simp [mem_product, mem_filter]; tauto
  have hQ' : ((((S₁.powersetCard m) ×ˢ (S₂.powersetCard m)).filter fun p => ¬ Q p.1).card : ℝ) ≤
      ε * ((S₁.card.choose m : ℕ) * (S₂.card.choose m : ℕ)) := by
    rw [e, card_product, card_powersetCard, Nat.cast_mul]
    have h0 : (0 : ℝ) ≤ (S₂.card.choose m : ℕ) := Nat.cast_nonneg _
    calc (((S₁.powersetCard m).filter fun T => ¬ Q T).card : ℝ) * ((S₂.card.choose m : ℕ) : ℝ)
        ≤ (ε * (S₁.card.choose m : ℕ)) * (S₂.card.choose m : ℕ) :=
          mul_le_mul_of_nonneg_right hQ h0
      _ = _ := by ring
  exact count_pair S₁ S₂ m j 0 hm h₁ (by simpa using h₂) (fun p => Q p.1) ε hQ'

open Classical in
/-- Lemma 2.4 for one fixed colour block, with the constants of `fresh_main`. -/
lemma block_count {ω c₂₄ δ c₄ C₄ κ K : ℝ} (h24 : Spec24.{u} ω c₂₄ 10 (2 * δ) c₄ C₄ 2)
    {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (col : V → Bool) (E : Finset V)
    (hbip : H.IsBipartiteWith col) (hwt : H.WeightsIn ω) (hw1 : ∀ x y, H.w x y ≤ 1)
    (N₀ m : ℕ) (hm1 : 1 ≤ m) (hNb : ∀ b, (classOf E col b).card = N₀)
    (η₀ D σ₀ L : ℝ) (hdeg : (H.induce (univ \ E)).DegNear D η₀)
    (hgap : (H.induce (univ \ E)).HasGap σ₀) (hσ : 0 < σ₀) (hσ1 : σ₀ ≤ 1) (hη0 : 0 ≤ η₀)
    (hηs : η₀ ≤ 1 / 40) (hη' : η₀ ≤ c₄ * (σ₀ / 2)) (hD : 0 < D)
    (hL : Real.log (2 * N₀) ≤ L) (hL0 : 0 < L) (hK : 0 < K) (hδσ : δ * σ₀ ≤ 1)
    (hκ' : κ * σ₀ ≤ c₄ * (σ₀ / 2))
    (hKp : 16 * K ^ 2 * σ₀ ^ (-(2 : ℝ)) * L ≤ (m : ℝ) / N₀ * D)
    (hpD : C₄ * (σ₀ / 2) ^ (-2 : ℝ) * L ≤ (m : ℝ) / N₀ * D)
    (b : Bool) (X : Finset V) (hX : X ⊆ classOf E col b) (hXc : X.card = m)
    (hos : OneSided H (classOf E col b) (classOf E col (!b)) X ((m : ℝ) / N₀) D σ₀ L K δ)
    (Pb : Finset V) (hPsub : Pb ⊆ classOf E col (!b)) (hPc : (1 - κ * σ₀) * N₀ ≤ Pb.card)
    (hPl : ∀ v, H.degOn v (classOf E col (!b) \ Pb) ≤ κ * σ₀ * D) :
    (((Pb.powersetCard m).filter fun T =>
        ¬ Good H X T ((m : ℝ) / N₀ * D) (2 * δ * (σ₀ / 2)) (min c₂₄ 1 * (σ₀ / 2))).card : ℝ) ≤
      Real.exp (-(2 * L)) * (Pb.card.choose m : ℕ) := by
  have hN0r : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
  have hos' := oneSided_weaken H col E hbip hw1 b N₀ m X hX (hNb b) (hNb _) hXc hm1 η₀ D σ₀ L K δ
    hdeg hη0 (by linarith) hD hσ hσ1 hδσ hL0.le hK.le hKp hos
  have hPc' : (1 - c₄ * (σ₀ / 2)) * N₀ ≤ Pb.card := by
    have := mul_le_mul_of_nonneg_right hκ' hN0r
    linarith
  have hPl' : ∀ v, H.degOn v (classOf E col (!b) \ Pb) ≤ c₄ * (σ₀ / 2) * D := fun v =>
    (hPl v).trans (mul_le_mul_of_nonneg_right hκ' hD.le)
  exact fixed_count h24 H col E hbip hwt N₀ m b (hNb b) (hNb _) η₀ D (σ₀ / 2) L hdeg
    (hasGap_mono _ hgap (by linarith)) (by positivity) (by linarith) hη' hL X hX hXc hos' Pb
    hPsub hPc' hPl' hpD (min c₂₄ 1 * (σ₀ / 2))
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))

open Classical in
/-- The degree of a swapped endpoint into its fresh layer. -/
lemma zblock_count {V : Type*} [Fintype V] [DecidableEq V] (H : WGraph V) (col : V → Bool)
    (E : Finset V) (hbip : H.IsBipartiteWith col) (hw1 : ∀ x y, H.w x y ≤ 1) (N₀ m : ℕ)
    (hN0r : (0 : ℝ) < N₀) (η₀ D σ₀ L κ D₀ : ℝ) (hdeg : (H.induce (univ \ E)).DegNear D η₀)
    (hD : 0 < D) (hηs : η₀ ≤ 1 / 40) (hκσ : κ * σ₀ ≤ 1 / 40)
    (hD₀ : D₀ = (m : ℝ) / N₀ * D) (hD₀54 : 54 * L ≤ D₀) (hD₀10 : 10 ≤ D₀)
    (z : V) (b : Bool) (hzcl : z ∈ classOf E col b)
    (Pb : Finset V) (hPsub : Pb ⊆ classOf E col (!b)) (hPc : (1 - κ * σ₀) * N₀ ≤ Pb.card)
    (hPN : Pb.card ≤ N₀) (hPl : ∀ v, H.degOn v (classOf E col (!b) \ Pb) ≤ κ * σ₀ * D) :
    (((Pb.powersetCard m).filter fun T => ¬ (D₀ / 2 + 1 ≤ H.degOn z T)).card : ℝ) ≤
      Real.exp (-(2 * L)) * (Pb.card.choose m : ℕ) := by
  have h1 := abs_le.1 (class_deg H col hbip E hdeg b z hzcl)
  have h2 : H.degOn z (classOf E col (!b) \ Pb) + H.degOn z Pb =
      H.degOn z (classOf E col (!b)) := sum_sdiff hPsub
  have h3 := hPl z
  have h4 : 0 ≤ H.degOn z (classOf E col (!b) \ Pb) := sum_nonneg fun _ _ => H.nonneg _ _
  have hlow : (39 / 40 : ℝ) * N₀ ≤ Pb.card := by
    have := mul_le_mul_of_nonneg_right hκσ hN0r.le
    linarith
  have hPbpos : (0 : ℝ) < Pb.card := by linarith
  have hPbN : (Pb.card : ℝ) ≤ N₀ := by exact_mod_cast hPN
  have e1 : η₀ * D ≤ 1 / 40 * D := mul_le_mul_of_nonneg_right hηs hD.le
  have e2 : κ * σ₀ * D ≤ 1 / 40 * D := mul_le_mul_of_nonneg_right hκσ hD.le
  have hXlo : 19 / 20 * D ≤ H.degOn z Pb := by linarith [h1.1]
  have hXhi : H.degOn z Pb ≤ 41 / 40 * D := by linarith [h1.2]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  refine z_count H hw1 z Pb m D₀ L ?_ ?_ hD₀54 hD₀10
  · have : (m : ℝ) / N₀ ≤ m / Pb.card := div_le_div_of_nonneg_left hm0 hPbpos hPbN
    calc 9 / 10 * D₀ = ((m : ℝ) / N₀) * (9 / 10 * D) := by rw [hD₀]; ring
      _ ≤ (m / Pb.card) * H.degOn z Pb :=
        mul_le_mul this (by linarith) (by positivity) (div_nonneg hm0 hPbpos.le)
  · have : (m : ℝ) / Pb.card ≤ m / (39 / 40 * N₀) :=
      div_le_div_of_nonneg_left hm0 (by positivity) hlow
    calc (m : ℝ) / Pb.card * H.degOn z Pb ≤ m / (39 / 40 * N₀) * (41 / 40 * D) :=
          mul_le_mul this hXhi (by linarith) (div_nonneg hm0 (by positivity))
      _ = 41 / 39 * D₀ := by rw [hD₀]; field_simp
      _ ≤ 6 / 5 * D₀ := by linarith

lemma union_numeric (N₀ t : ℕ) (L : ℝ) (hN0 : 1 ≤ N₀) (htN : t ≤ N₀)
    (hL : Real.log (2 * N₀) ≤ L) (hL10 : 10 ≤ L) :
    ((10 + 2 * (t - 2) : ℕ) : ℝ) * Real.exp (-(2 * L)) < 1 := by
  have hN0r : (0 : ℝ) < N₀ := by exact_mod_cast hN0
  have h1 : ((10 + 2 * (t - 2) : ℕ) : ℝ) ≤ 12 * N₀ := by
    have : 10 + 2 * (t - 2) ≤ 12 * N₀ := by omega
    exact_mod_cast this
  have h2 : Real.exp (-L) ≤ (2 * (N₀ : ℝ))⁻¹ := by
    rw [← Real.exp_log (show (0 : ℝ) < 2 * N₀ by positivity), ← Real.exp_neg]
    exact Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (-L) ≤ 1 / 11 := by
    have h4 : Real.exp (-L) ≤ Real.exp (-10) := Real.exp_le_exp.2 (by linarith)
    have h5 : (11 : ℝ) ≤ Real.exp 10 := by linarith [Real.add_one_le_exp (10 : ℝ)]
    have h6 : Real.exp (-10) = (Real.exp 10)⁻¹ := Real.exp_neg 10
    rw [h6] at h4
    refine h4.trans ?_
    rw [inv_le_comm₀ (Real.exp_pos 10) (by norm_num)]
    linarith
  have hεe : Real.exp (-(2 * L)) = Real.exp (-L) * Real.exp (-L) := by
    rw [← Real.exp_add]; ring_nf
  have h7 : Real.exp (-(2 * L)) ≤ (2 * (N₀ : ℝ))⁻¹ * (1 / 11) := by
    rw [hεe]; exact mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)
  have h8 : (12 * N₀ : ℝ) * ((2 * (N₀ : ℝ))⁻¹ * (1 / 11)) = 6 / 11 := by field_simp; ring
  calc ((10 + 2 * (t - 2) : ℕ) : ℝ) * Real.exp (-(2 * L))
      ≤ 12 * N₀ * ((2 * (N₀ : ℝ))⁻¹ * (1 / 11)) :=
        mul_le_mul h1 h7 (Real.exp_pos _).le (by positivity)
    _ < 1 := by rw [h8]; norm_num

open Classical in
/-- **The union bound over the transitions.** If each of the ten fixed-boundary events and the
fresh–fresh event fails for at most an `ε` fraction of the uniform layers, and
`(10 + 2(t - 2)) ε < 1`, then some pair of orderings of the two colour classes of the pool makes
all the events hold. -/
lemma layers_exist {α : Type*} [DecidableEq α] (PT PF : Finset α) (m t : ℕ) (hm0 : 0 < m)
    (ht2 : 2 ≤ t) (hT : PT.card = t * m) (hF : PF.card = t * m) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hlen : ((10 + 2 * (t - 2) : ℕ) : ℝ) * ε < 1)
    (A1 A3 A5 A6 A9 A2 A4 A7 A8 A10 : Finset α → Prop) (G : Finset α → Finset α → Prop)
    (h1 : (((PF.powersetCard m).filter fun T => ¬ A1 T).card : ℝ) ≤ ε * (PF.card.choose m : ℕ))
    (h3 : (((PF.powersetCard m).filter fun T => ¬ A3 T).card : ℝ) ≤ ε * (PF.card.choose m : ℕ))
    (h5 : (((PF.powersetCard m).filter fun T => ¬ A5 T).card : ℝ) ≤ ε * (PF.card.choose m : ℕ))
    (h6 : (((PF.powersetCard m).filter fun T => ¬ A6 T).card : ℝ) ≤ ε * (PF.card.choose m : ℕ))
    (h9 : (((PF.powersetCard m).filter fun T => ¬ A9 T).card : ℝ) ≤ ε * (PF.card.choose m : ℕ))
    (h2 : (((PT.powersetCard m).filter fun T => ¬ A2 T).card : ℝ) ≤ ε * (PT.card.choose m : ℕ))
    (h4 : (((PT.powersetCard m).filter fun T => ¬ A4 T).card : ℝ) ≤ ε * (PT.card.choose m : ℕ))
    (h7 : (((PT.powersetCard m).filter fun T => ¬ A7 T).card : ℝ) ≤ ε * (PT.card.choose m : ℕ))
    (h8 : (((PT.powersetCard m).filter fun T => ¬ A8 T).card : ℝ) ≤ ε * (PT.card.choose m : ℕ))
    (h10 : (((PT.powersetCard m).filter fun T => ¬ A10 T).card : ℝ) ≤
      ε * (PT.card.choose m : ℕ))
    (hG : ((((PT.powersetCard m) ×ˢ (PF.powersetCard m)).filter fun p => ¬ G p.1 p.2).card : ℝ)
      ≤ ε * ((PT.card.choose m : ℕ) * (PF.card.choose m : ℕ))) :
    ∃ σT : Equiv.Perm (Fin PT.card), ∃ σF : Equiv.Perm (Fin PF.card),
      A1 (lay PF m σF 0) ∧ A3 (lay PF m σF 0) ∧ A5 (lay PF m σF 0) ∧ A6 (lay PF m σF 1) ∧
      A9 (lay PF m σF (t - 1)) ∧ A2 (lay PT m σT 0) ∧ A4 (lay PT m σT 0) ∧
      A7 (lay PT m σT 1) ∧ A8 (lay PT m σT 1) ∧ A10 (lay PT m σT (t - 1)) ∧
      ∀ i, 1 ≤ i → i + 1 < t → G (lay PT m σT i) (lay PF m σF (i + 1)) ∧
        G (lay PT m σT (i + 1)) (lay PF m σF i) := by
  have hlt : ∀ j < t, (j + 1) * m ≤ PT.card := fun j hj => by
    rw [hT]; exact Nat.mul_le_mul_right m hj
  have hltF : ∀ j < t, (j + 1) * m ≤ PF.card := fun j hj => by
    rw [hF]; exact Nat.mul_le_mul_right m hj
  have hmT : m ≤ PT.card := by simpa using hlt 0 (by omega)
  have hmF : m ≤ PF.card := by simpa using hltF 0 (by omega)
  let Ω := Equiv.Perm (Fin PT.card) × Equiv.Perm (Fin PF.card)
  let fa : ℕ → Ω → Prop := fun i ω => G (lay PT m ω.1 i) (lay PF m ω.2 (i + 1))
  let fb : ℕ → Ω → Prop := fun i ω => G (lay PT m ω.1 (i + 1)) (lay PF m ω.2 i)
  let l₁ : List (Ω → Prop) :=
    [fun ω => A1 (lay PF m ω.2 0), fun ω => A3 (lay PF m ω.2 0), fun ω => A5 (lay PF m ω.2 0),
      fun ω => A6 (lay PF m ω.2 1), fun ω => A9 (lay PF m ω.2 (t - 1)),
      fun ω => A2 (lay PT m ω.1 0), fun ω => A4 (lay PT m ω.1 0), fun ω => A7 (lay PT m ω.1 1),
      fun ω => A8 (lay PT m ω.1 1), fun ω => A10 (lay PT m ω.1 (t - 1))]
  let evs : List (Ω → Prop) := l₁ ++ (List.range' 1 (t - 2)).flatMap fun i => [fa i, fb i]
  have hevs : ∀ Pr ∈ evs, ((univ.filter fun ω => ¬ Pr ω).card : ℝ) ≤ ε * Fintype.card Ω := by
    intro Pr hPr
    simp only [evs, l₁, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range'_1,
      List.not_mem_nil, or_false] at hPr
    rcases hPr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      ⟨i, ⟨hi1, hi2⟩, rfl | rfl⟩
    · exact count_right PT PF m 0 hm0 hmT (hltF 0 (by omega)) A1 ε h1
    · exact count_right PT PF m 0 hm0 hmT (hltF 0 (by omega)) A3 ε h3
    · exact count_right PT PF m 0 hm0 hmT (hltF 0 (by omega)) A5 ε h5
    · exact count_right PT PF m 1 hm0 hmT (hltF 1 (by omega)) A6 ε h6
    · exact count_right PT PF m (t - 1) hm0 hmT (hltF (t - 1) (by omega)) A9 ε h9
    · exact count_left PT PF m 0 hm0 (hlt 0 (by omega)) hmF A2 ε h2
    · exact count_left PT PF m 0 hm0 (hlt 0 (by omega)) hmF A4 ε h4
    · exact count_left PT PF m 1 hm0 (hlt 1 (by omega)) hmF A7 ε h7
    · exact count_left PT PF m 1 hm0 (hlt 1 (by omega)) hmF A8 ε h8
    · exact count_left PT PF m (t - 1) hm0 (hlt (t - 1) (by omega)) hmF A10 ε h10
    · exact count_pair PT PF m i (i + 1) hm0 (hlt i (by omega)) (hltF (i + 1) (by omega))
        (fun p => G p.1 p.2) ε hG
    · exact count_pair PT PF m (i + 1) i hm0 (hlt (i + 1) (by omega)) (hltF i (by omega))
        (fun p => G p.1 p.2) ε hG
  have hlenE : evs.length = 10 + 2 * (t - 2) := by
    simp only [evs, l₁, List.length_append, length_flatMap_pair, List.length_range',
      List.length_cons, List.length_nil]
  have hΩ : 0 < Fintype.card Ω := Fintype.card_pos_iff.2 ⟨(1, 1)⟩
  obtain ⟨ω₀, hω₀⟩ := exists_good_list evs ε hevs (by rw [hlenE]; exact hlen) hε0 hΩ
  have g : ∀ e ∈ l₁, e ω₀ := fun e he => hω₀ e (List.mem_append_left _ he)
  refine ⟨ω₀.1, ω₀.2, g (fun ω => A1 (lay PF m ω.2 0)) (by simp [l₁]),
    g (fun ω => A3 (lay PF m ω.2 0)) (by simp [l₁]),
    g (fun ω => A5 (lay PF m ω.2 0)) (by simp [l₁]),
    g (fun ω => A6 (lay PF m ω.2 1)) (by simp [l₁]),
    g (fun ω => A9 (lay PF m ω.2 (t - 1))) (by simp [l₁]),
    g (fun ω => A2 (lay PT m ω.1 0)) (by simp [l₁]),
    g (fun ω => A4 (lay PT m ω.1 0)) (by simp [l₁]),
    g (fun ω => A7 (lay PT m ω.1 1)) (by simp [l₁]),
    g (fun ω => A8 (lay PT m ω.1 1)) (by simp [l₁]),
    g (fun ω => A10 (lay PT m ω.1 (t - 1))) (by simp [l₁]), fun i hi1 hi2 => ?_⟩
  have hmem : i ∈ List.range' 1 (t - 2) := List.mem_range'_1.2 ⟨hi1, by omega⟩
  exact ⟨hω₀ (fa i) (List.mem_append_right _ (List.mem_flatMap.2 ⟨i, hmem, by simp⟩)),
    hω₀ (fb i) (List.mem_append_right _ (List.mem_flatMap.2 ⟨i, hmem, by simp⟩))⟩

/-- **`T3.2f` for fixed constants.** -/
theorem fresh_main {ω c₂₄ δ c₄ C₄ c₂₃ c₁ c₃ C₃ c' C' cF κ K CF : ℝ}
    (h24 : Spec24.{u} ω c₂₄ 10 (2 * δ) c₄ C₄ 2) (h23 : Spec23.{u} ω c₂₃ c₁ c₃ C₃ 2)
    (h21 : Spec21.{u} (1 / 2) 2 c' C')
    (hc₂₄ : 0 < c₂₄) (hδ : 0 < δ) (hc₂₃ : 0 < c₂₃) (hK : 0 < K) (hc₁0 : 0 ≤ c₁) (hc₁ : c₁ ≤ min c₂₃ 1 / 400)
    (hδc : δ ≤ min c₂₄ 1 / 800)
    (hcF1 : cF ≤ c₄ / 2) (hcF2 : cF ≤ c₃ / 4) (hcF3 : cF ≤ 1 / 40)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ c₄ / 2) (hκ2 : κ ≤ c₃ / 4) (hκ3 : κ ≤ c') (hκ4 : C' * κ ≤ 1 / 2)
    (hκ5 : κ ≤ 1 / 40)
    (hCF1 : 16 * K ^ 2 ≤ CF) (hCF2 : 4 * C₄ ≤ CF) (hCF3 : 4 * C₃ ≤ CF)
    (hCF4 : 80 / min c₂₄ 1 ≤ CF) (hCF5 : 80 / min c₂₃ 1 ≤ CF) (hCF6 : 54 ≤ CF) :
    FreshSpec.{u} ω cF δ κ K CF := by
  intro V _ _ H col E O I U W U' W' P S N₀ m η₀ D σ₀ L dA dB zA zB τ hbip hwt hNt hNf hdeg
    hgap hσ hσ1 hη0 hη hD hL hL10 hm1 hfix hOI hOU hOW hIU hIW hUW hCF hdA hdAc hdB hdBc
    hzAE hzAc hzBE hzBc hzA hzB hU' hW' hPE hPd hPbal hdvd hP2 hS hSdeg hScard hτ
  classical
  -- basic numerics
  have hw1 : ∀ x y, H.w x y ≤ 1 := fun x y => by
    rcases (H.nonneg x y).lt_or_eq with h | h
    · exact (hwt x y h).2
    · rw [← h]; norm_num
  have hL0 : 0 < L := by linarith
  have hσ2 : σ₀ ^ 2 ≤ σ₀ := by nlinarith
  have hs2 : σ₀ ^ (-(2 : ℝ)) = (σ₀ ^ 2)⁻¹ := by rw [Real.rpow_neg hσ.le, Real.rpow_two]
  have hs2' : (σ₀ / 2) ^ (-(2 : ℝ)) = 4 * (σ₀ ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]; field_simp; ring
  have hinv : σ₀⁻¹ ≤ (σ₀ ^ 2)⁻¹ := inv_anti₀ (by positivity) hσ2
  have hinv1 : 1 ≤ σ₀⁻¹ := (one_le_inv₀ hσ).2 hσ1
  set Q₀ : ℝ := (σ₀ ^ 2)⁻¹ * L with hQ₀
  have hQ₀10 : 10 / σ₀ ≤ Q₀ := by
    rw [hQ₀, div_eq_mul_inv]
    have := mul_le_mul hL10 hinv (by positivity) hL0.le
    linarith
  have hQ₀L : L ≤ Q₀ := by
    rw [hQ₀]
    have := mul_le_mul_of_nonneg_right (hinv1.trans hinv) hL0.le
    linarith
  have hQ₀0 : 0 ≤ Q₀ := by linarith
  have hCFQ : CF * Q₀ ≤ (m : ℝ) / N₀ * D := by
    have e : CF * Q₀ = CF * σ₀ ^ (-(2 : ℝ)) * L := by rw [hQ₀, hs2]; ring
    rw [e]; exact hCF
  set D₀ : ℝ := (m : ℝ) / N₀ * D with hD₀
  have hD₀54 : 54 * L ≤ D₀ := by
    have := mul_le_mul_of_nonneg_right hCF6 hQ₀0
    have := mul_le_mul_of_nonneg_left hQ₀L (show (0 : ℝ) ≤ 54 by norm_num)
    linarith
  have hD₀10 : 540 ≤ D₀ := by linarith
  have hηs : η₀ ≤ 1 / 40 := le_trans hη (by
    calc cF * σ₀ ≤ 1 / 40 * 1 := mul_le_mul hcF3 hσ1 hσ.le (by norm_num)
      _ = 1 / 40 := by norm_num)
  have hκσ : κ * σ₀ ≤ 1 / 40 := by
    calc κ * σ₀ ≤ κ * 1 := mul_le_mul_of_nonneg_left hσ1 hκ0.le
      _ ≤ 1 / 40 := by linarith
  have hδ1 : δ ≤ 1 / 800 := hδc.trans (by have := min_le_right c₂₄ 1; linarith)
  have hδσ : δ * σ₀ ≤ 1 := by
    calc δ * σ₀ ≤ δ * 1 := mul_le_mul_of_nonneg_left hσ1 hδ.le
      _ ≤ 1 := by linarith
  -- colour blocks
  have hXsub : ∀ X, (X = O ∨ X = I ∨ X = U ∨ X = W) → ∀ b,
      X.filter (fun x => col x = b) ⊆ classOf E col b := fun X hX b x hx =>
    mem_filter.2 ⟨mem_sdiff.2 ⟨mem_univ _, disjoint_left.1 (hfix X hX).1 (mem_filter.1 hx).1⟩,
      (mem_filter.1 hx).2⟩
  have hNb : ∀ b, (classOf E col b).card = N₀ := fun b => by cases b; exacts [hNf, hNt]
  have hOt := ((hfix O (Or.inl rfl)).2 true).1
  have hN0 : 1 ≤ N₀ := by
    have := card_le_card (hXsub O (Or.inl rfl) true)
    rw [hOt, hNt] at this; omega
  have hN0r : (0 : ℝ) < N₀ := by exact_mod_cast hN0
  have hDN : D ≤ 40 / 39 * N₀ := by
    obtain ⟨x₀, hx₀⟩ : (O.filter fun x => col x = true).Nonempty := card_pos.1 (by omega)
    have h1 := abs_le.1 (class_deg H col hbip E hdeg true x₀ (hXsub O (Or.inl rfl) true hx₀))
    have h2 : H.degOn x₀ (classOf E col (!true)) ≤ N₀ := by
      calc H.degOn x₀ (classOf E col (!true)) ≤ ∑ y ∈ classOf E col (!true), (1 : ℝ) :=
            sum_le_sum fun y _ => hw1 _ _
        _ = N₀ := by rw [sum_const, hNb]; simp
    have : η₀ * D ≤ 1 / 40 * D := mul_le_mul_of_nonneg_right hηs hD.le
    linarith [h1.1]
  have hm2 : 2 ≤ m := by
    have h1 : D₀ ≤ 40 / 39 * m := by
      rw [hD₀, div_mul_eq_mul_div, div_le_iff₀ hN0r]
      have := mul_le_mul_of_nonneg_left hDN (show (0 : ℝ) ≤ m by positivity)
      linarith
    have : (2 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hm0 : 0 < m := by omega
  -- the pool
  set PT := P.filter fun x => col x = true with hPT
  set PF := P.filter fun x => col x = false with hPF
  set n := PT.card with hn
  have hPFn : PF.card = n := hPbal.symm
  obtain ⟨t, ht⟩ := hdvd
  have hnt : n = t * m := by rw [ht, mul_comm]
  have ht2 : 2 ≤ t := by
    have : m * 2 ≤ m * t := by rw [← ht]; linarith
    exact Nat.le_of_mul_le_mul_left this hm0
  have hpool : ∀ b, (P.filter fun x => col x = b) ⊆ classOf E col b ∧
      (1 - κ * σ₀) * N₀ ≤ (P.filter fun x => col x = b).card ∧
      (∀ v, H.degOn v (classOf E col b \ P.filter fun x => col x = b) ≤ κ * σ₀ * D) ∧
      (P.filter fun x => col x = b).card ≤ N₀ := by
    intro b
    have hsub : (P.filter fun x => col x = b) ⊆ classOf E col b := fun x hx =>
      mem_filter.2 ⟨mem_sdiff.2 ⟨mem_univ _, disjoint_left.1 hPE (mem_filter.1 hx).1⟩,
        (mem_filter.1 hx).2⟩
    have hdiff : classOf E col b \ (P.filter fun x => col x = b) ⊆
        S.filter fun x => col x = b := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := mem_sdiff.1 hx
      have hc := (mem_filter.1 hx1).2
      have hxP : x ∉ P := fun h => hx2 (mem_filter.2 ⟨h, hc⟩)
      exact mem_filter.2 ⟨hS (mem_sdiff.2 ⟨(mem_filter.1 hx1).1, hxP⟩), hc⟩
    have hc1 := card_le_card hdiff
    have hc2 := card_sdiff_add_card_eq_card hsub
    rw [hNb b] at hc2
    have hc3 := hScard b
    refine ⟨hsub, ?_, fun v => (degOn_mono H v (hdiff.trans (filter_subset _ _))).trans
      (hSdeg v), by omega⟩
    have h4 : ((classOf E col b \ P.filter fun x => col x = b).card : ℝ) ≤ κ * σ₀ * N₀ :=
      le_trans (by exact_mod_cast hc1) hc3
    have e : ((classOf E col b \ P.filter fun x => col x = b).card : ℝ) +
        (P.filter fun x => col x = b).card = N₀ := by exact_mod_cast hc2
    linarith
  have hnN : n ≤ N₀ := (hpool true).2.2.2
  have hnpos : 0 < n := by rw [hnt]; positivity
  have hmn : m ≤ n := by
    rw [hnt]
    calc m = 1 * m := (one_mul m).symm
      _ ≤ t * m := Nat.mul_le_mul_right m (by omega)
  -- the parameters
  have hmin₄ : 0 < min c₂₄ 1 := lt_min hc₂₄ one_pos
  have hmin₃ : 0 < min c₂₃ 1 := lt_min hc₂₃ one_pos
  set σa : ℝ := min c₂₄ 1 * (σ₀ / 2) with hσa
  set ηa : ℝ := 2 * δ * (σ₀ / 2) with hηa
  set σb : ℝ := min c₂₃ 1 * (σ₀ / 2) with hσb
  set ηb : ℝ := c₁ * (σ₀ / 2) with hηb
  set D₁ : ℝ := (m : ℝ) / n * D with hD₁
  have hD₀₁ : D₀ ≤ D₁ := by
    rw [hD₀, hD₁]
    refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity)
      (by exact_mod_cast hnpos) (by exact_mod_cast hnN)) hD.le
  have hσa0 : 0 < σa := by positivity
  have hσa1 : σa ≤ 1 := by
    calc σa = min c₂₄ 1 * (σ₀ / 2) := rfl
      _ ≤ 1 * 1 := mul_le_mul (min_le_right _ _) (by linarith) (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hσb0 : 0 < σb := by positivity
  have hσb1 : σb ≤ 1 := by
    calc σb = min c₂₃ 1 * (σ₀ / 2) := rfl
      _ ≤ 1 * 1 := mul_le_mul (min_le_right _ _) (by linarith) (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hηa0 : 0 ≤ ηa := by positivity
  have hηb0 : 0 ≤ ηb := by positivity
  have hηa' : ηa ≤ σa / 400 := by
    have := mul_le_mul_of_nonneg_right hδc hσ.le
    rw [hηa, hσa]
    have e1 : 2 * δ * (σ₀ / 2) = δ * σ₀ := by ring
    have e2 : min c₂₄ 1 * (σ₀ / 2) / 400 = min c₂₄ 1 / 800 * σ₀ := by ring
    rw [e1, e2]; exact this
  have hηb' : ηb ≤ σb / 400 := by
    have := mul_le_mul_of_nonneg_right hc₁ (show 0 ≤ σ₀ / 2 by positivity)
    rw [hηb, hσb]
    have e2 : min c₂₃ 1 * (σ₀ / 2) / 400 = min c₂₃ 1 / 400 * (σ₀ / 2) := by ring
    rw [e2]; exact this
  have hDa : 400 / σa ≤ D₀ := by
    have e : 400 / σa = 80 / min c₂₄ 1 * (10 / σ₀) := by rw [hσa]; field_simp; ring
    rw [e]
    have h1 : 80 / min c₂₄ 1 * (10 / σ₀) ≤ CF * (10 / σ₀) :=
      mul_le_mul_of_nonneg_right hCF4 (by positivity)
    have h2 : CF * (10 / σ₀) ≤ CF * Q₀ := mul_le_mul_of_nonneg_left hQ₀10 (by linarith)
    linarith
  have hDb : 400 / σb ≤ D₁ := by
    have e : 400 / σb = 80 / min c₂₃ 1 * (10 / σ₀) := by rw [hσb]; field_simp; ring
    rw [e]
    have h1 : 80 / min c₂₃ 1 * (10 / σ₀) ≤ CF * (10 / σ₀) :=
      mul_le_mul_of_nonneg_right hCF5 (by positivity)
    have h2 : CF * (10 / σ₀) ≤ CF * Q₀ := mul_le_mul_of_nonneg_left hQ₀10 (by linarith)
    linarith
  -- the failure probabilities
  set ε : ℝ := Real.exp (-(2 * L)) with hε
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le
  have hKp : 16 * K ^ 2 * σ₀ ^ (-(2 : ℝ)) * L ≤ (m : ℝ) / N₀ * D := by
    have e : 16 * K ^ 2 * σ₀ ^ (-(2 : ℝ)) * L = 16 * K ^ 2 * Q₀ := by rw [hQ₀, hs2]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hCF1 hQ₀0
    linarith
  have hη' : η₀ ≤ c₄ * (σ₀ / 2) := by
    calc η₀ ≤ cF * σ₀ := hη
      _ ≤ c₄ / 2 * σ₀ := mul_le_mul_of_nonneg_right hcF1 hσ.le
      _ = c₄ * (σ₀ / 2) := by ring
  have hκ' : κ * σ₀ ≤ c₄ * (σ₀ / 2) := by
    calc κ * σ₀ ≤ c₄ / 2 * σ₀ := mul_le_mul_of_nonneg_right hκ1 hσ.le
      _ = c₄ * (σ₀ / 2) := by ring
  have hpD : C₄ * (σ₀ / 2) ^ (-2 : ℝ) * L ≤ (m : ℝ) / N₀ * D := by
    rw [hs2']
    have e : C₄ * (4 * (σ₀ ^ 2)⁻¹) * L = 4 * C₄ * Q₀ := by rw [hQ₀]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hCF2 hQ₀0
    linarith
  have hfixF : ∀ X, (X = O ∨ X = I ∨ X = U ∨ X = W) →
      (((PF.powersetCard m).filter fun T =>
        ¬ Good H (X.filter fun x => col x = true) T D₀ ηa σa).card : ℝ) ≤
        ε * (PF.card.choose m : ℕ) := fun X hX =>
    block_count h24 H col E hbip hwt hw1 N₀ m hm1 hNb η₀ D σ₀ L hdeg hgap hσ hσ1 hη0 hηs
      hη' hD hL hL0 hK hδσ hκ' hKp hpD true _ (hXsub X hX true) ((hfix X hX).2 true).1
      ((hfix X hX).2 true).2 PF (hpool false).1 (hpool false).2.1 (hpool false).2.2.1
  have hfixT : ∀ X, (X = O ∨ X = I ∨ X = U ∨ X = W) →
      (((PT.powersetCard m).filter fun T =>
        ¬ Good H (X.filter fun x => col x = false) T D₀ ηa σa).card : ℝ) ≤
        ε * (PT.card.choose m : ℕ) := fun X hX =>
    block_count h24 H col E hbip hwt hw1 N₀ m hm1 hNb η₀ D σ₀ L hdeg hgap hσ hσ1 hη0 hηs
      hη' hD hL hL0 hK hδσ hκ' hKp hpD false _ (hXsub X hX false) ((hfix X hX).2 false).1
      ((hfix X hX).2 false).2 PT (hpool true).1 (hpool true).2.1 (hpool true).2.2.1
  have hzF : (((PF.powersetCard m).filter fun T => ¬ (D₀ / 2 + 1 ≤ H.degOn zA T)).card : ℝ) ≤
      ε * (PF.card.choose m : ℕ) :=
    zblock_count H col E hbip hw1 N₀ m hN0r η₀ D σ₀ L κ D₀ hdeg hD hηs hκσ rfl hD₀54
      (by linarith) zA true (mem_filter.2 ⟨mem_sdiff.2 ⟨mem_univ _, hzAE⟩, hzAc⟩) PF
      (hpool false).1 (hpool false).2.1 (hpool false).2.2.2 (hpool false).2.2.1
  have hzT : (((PT.powersetCard m).filter fun T => ¬ (D₀ / 2 + 1 ≤ H.degOn zB T)).card : ℝ) ≤
      ε * (PT.card.choose m : ℕ) :=
    zblock_count H col E hbip hw1 N₀ m hN0r η₀ D σ₀ L κ D₀ hdeg hD hηs hκσ rfl hD₀54
      (by linarith) zB false (mem_filter.2 ⟨mem_sdiff.2 ⟨mem_univ _, hzBE⟩, hzBc⟩) PT
      (hpool true).1 (hpool true).2.1 (hpool true).2.2.2 (hpool true).2.2.1
  have hPdeg := pool_degNear H E P S (ε := κ * σ₀) hdeg hPE hS hSdeg
  have hκc : κ * σ₀ ≤ c' := by
    calc κ * σ₀ ≤ κ * 1 := mul_le_mul_of_nonneg_left hσ1 hκ0.le
      _ ≤ c' := by linarith
  have hPgap := pool_gap h21 H E P S hD hdeg (by linarith) hgap hPE hS hSdeg (by positivity) hκc
  have hPgap' : (H.induce P).HasGap (σ₀ / 2) := hasGap_mono _ hPgap (by
    have := mul_le_mul_of_nonneg_right hκ4 hσ.le
    linarith)
  have hLn : Real.log (2 * n) ≤ L := by
    refine le_trans (Real.log_le_log (by positivity) ?_) hL
    have : (n : ℝ) ≤ N₀ := by exact_mod_cast hnN
    linarith
  have hηP : η₀ + κ * σ₀ ≤ c₃ * (σ₀ / 2) := by
    have h1 : cF * σ₀ ≤ c₃ / 4 * σ₀ := mul_le_mul_of_nonneg_right hcF2 hσ.le
    have h2 : κ * σ₀ ≤ c₃ / 4 * σ₀ := mul_le_mul_of_nonneg_right hκ2 hσ.le
    linarith
  have hpD₁ : C₃ * (σ₀ / 2) ^ (-2 : ℝ) * L ≤ (m : ℝ) / n * D := by
    rw [hs2']
    have e : C₃ * (4 * (σ₀ ^ 2)⁻¹) * L = 4 * C₃ * Q₀ := by rw [hQ₀]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hCF3 hQ₀0
    linarith
  have hfr := fresh_count h23 H col hbip hwt P n m rfl hPFn (η₀ + κ * σ₀) D (σ₀ / 2) L hPdeg
    hPgap' (by positivity) (by linarith) hηP hLn hmn hpD₁ σb
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hfr' : ((((PT.powersetCard m) ×ˢ (PF.powersetCard m)).filter fun p =>
      ¬ Good H p.1 p.2 D₁ ηb σb).card : ℝ) ≤
      ε * ((PT.card.choose m : ℕ) * (PF.card.choose m : ℕ)) := by
    rw [hPFn, ← sq]; exact hfr
  have hO : O = O ∨ O = I ∨ O = U ∨ O = W := Or.inl rfl
  have hIq : I = O ∨ I = I ∨ I = U ∨ I = W := Or.inr (Or.inl rfl)
  have hUq : U = O ∨ U = I ∨ U = U ∨ U = W := Or.inr (Or.inr (Or.inl rfl))
  have hWq : W = O ∨ W = I ∨ W = U ∨ W = W := Or.inr (Or.inr (Or.inr rfl))
  -- the union bound
  have htN : t ≤ N₀ := le_trans (Nat.le_mul_of_pos_right t hm0) (hnt ▸ hnN)
  obtain ⟨σT, σF, g1, g3, g5, g6, g9, g2, g4, g7, g8, g10, gfr⟩ := layers_exist PT PF m t hm0
    ht2 hnt (by rw [hPFn, hnt]) ε hε0 (union_numeric N₀ t L hN0 htN hL hL10)
    (fun T => Good H (O.filter fun x => col x = true) T D₀ ηa σa)
    (fun T => Good H (U.filter fun x => col x = true) T D₀ ηa σa)
    (fun T => D₀ / 2 + 1 ≤ H.degOn zA T)
    (fun T => Good H (W.filter fun x => col x = true) T D₀ ηa σa)
    (fun T => Good H (I.filter fun x => col x = true) T D₀ ηa σa)
    (fun T => Good H (O.filter fun x => col x = false) T D₀ ηa σa)
    (fun T => Good H (U.filter fun x => col x = false) T D₀ ηa σa)
    (fun T => Good H (W.filter fun x => col x = false) T D₀ ηa σa)
    (fun T => D₀ / 2 + 1 ≤ H.degOn zB T)
    (fun T => Good H (I.filter fun x => col x = false) T D₀ ηa σa)
    (fun T₁ T₂ => Good H T₁ T₂ D₁ ηb σb)
    (hfixF O hO) (hfixF U hUq) hzF (hfixF W hWq) (hfixF I hIq)
    (hfixT O hO) (hfixT U hUq) (hfixT W hWq) hzT (hfixT I hIq) hfr'
  have hcov : ∀ x ∈ P, ∃ j < t, x ∈ lay PT m σT j ∪ lay PF m σF j := by
    intro x hx
    cases hc : col x
    · obtain ⟨j, hj, hxj⟩ := lay_cover PF σF hm0 (by rw [hPFn, hnt])
        (mem_filter.2 ⟨hx, hc⟩)
      exact ⟨j, hj, mem_union_right _ hxj⟩
    · obtain ⟨j, hj, hxj⟩ := lay_cover PT σT hm0 hnt (mem_filter.2 ⟨hx, hc⟩)
      exact ⟨j, hj, mem_union_left _ hxj⟩
  have hlt : ∀ j < t, (j + 1) * m ≤ PT.card := fun j hj => by
    rw [← hn, hnt]; exact Nat.mul_le_mul_right m hj
  have hltF : ∀ j < t, (j + 1) * m ≤ PF.card := fun j hj => by rw [hPFn]; exact hlt j hj
  exact assemble H col hbip hw1 O I U W U' W' P m t hm2 ht2 dA dB zA zB τ
    (fun X hX b => ((hfix X hX).2 b).1) hOI hOU hOW hIU hIW hUW hdA hdAc hdB hdBc hzAc hzBc
    hzA hzB hU' hW' hPd hτ (fun j => lay PT m σT j) (fun j => lay PF m σF j)
    (fun j => lay_sub PT m σT j) (fun j => lay_sub PF m σF j)
    (fun j hj => card_lay PT σT hm0 (hlt j hj)) (fun j hj => card_lay PF σF hm0 (hltF j hj))
    (fun j j' h => lay_disj PT m σT h) (fun j j' h => lay_disj PF m σF h) hcov
    D₀ ηa σa D₁ ηb σb hσa0 hσa1 hηa0 hηa' hDa hσb0 hσb1 hηb0 hηb' hDb
    g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 gfr

end Main

end FreshLayers

/-- **`T3.2f` (fresh layers).** Let `H₀ = H - E` be balanced (classes of size `N₀`) with
degrees `(1 ± η₀) D` and gap `σ₀`, `η₀ ≤ cF σ₀`. Let `O, I, U, W` be disjoint fixed layers with
`m` vertices of each colour satisfying the one-sided events (2.9) and (3.8). In `U` and `W`
the dummies `dA, dB` are replaced by the endpoints `zA, zB` of the divisibility path
(`U', W'`). Let the pool `P` be balanced with a multiple `tm` (`t ≥ 2`) of vertices of each
colour, such that everything outside it lies in an envelope `S` of small size into which every
vertex has small degree (3.10). Let `τ : U' → W'` be the special transition. Then a uniform
equipartition of `P` into layers `F₁, …, F_t` has perfect matchings between consecutive layers
of `O, F₁, U', W', F₂, …, F_t, I` (Lemmas 2.3, 2.4, 2.5, a union bound, and the robust Hall
enlargement for the swapped vertices). The union of these matchings, with `τ`, is recorded as
a grid `φ` of `w = 2m` vertex-disjoint rows: column `0` is `O`, column `2` is `U'`, column `3`
is `W'`, column `k` is `I`, and the other interior columns partition `P`. -/
theorem fresh_layers (ω : ℝ) (hω : 0 < ω) :
    ∃ cF δ κ : ℝ, 0 < cF ∧ 0 < δ ∧ 0 < κ ∧ ∀ K : ℝ, 0 < K → ∃ CF : ℝ, 0 < CF ∧
      FreshSpec.{u} ω cF δ κ K CF := by
  obtain ⟨c₂₄, δ₀, hc₂₄, hδ₀, h24⟩ := fixed_boundary_fresh_layer.{u} ω hω
  obtain ⟨c₂₃, hc₂₃, h23⟩ := bipartite_sampling.{u} ω hω
  obtain ⟨c', C', hc', hC', h21⟩ := hasGap_of_deletion.{u} (1 / 2) 2 (by norm_num) (by norm_num)
  have hmin₄ : 0 < min c₂₄ 1 := lt_min hc₂₄ one_pos
  have hmin₃ : 0 < min c₂₃ 1 := lt_min hc₂₃ one_pos
  set δ : ℝ := min (δ₀ / 2) (min c₂₄ 1 / 800) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ₀' : 2 * δ ≤ δ₀ := by have := min_le_left (δ₀ / 2) (min c₂₄ 1 / 800); linarith
  obtain ⟨c₄, C₄, hc₄, hC₄, h24'⟩ := h24 2 10 (2 * δ) (by norm_num) (by norm_num)
    (by positivity) hδ₀'
  obtain ⟨c₃, C₃, hc₃, hC₃, h23'⟩ := h23 2 (min c₂₃ 1 / 400) (by norm_num) (by positivity)
  set κ : ℝ := min (min (c₄ / 2) (c₃ / 4)) (min (min c' (1 / (2 * C'))) (1 / 40)) with hκdef
  have hκ0 : 0 < κ :=
    lt_min (lt_min (by positivity) (by positivity)) (lt_min (lt_min hc' (by positivity))
      (by norm_num))
  have hκ1 : κ ≤ c₄ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hκ2 : κ ≤ c₃ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hκ3 : κ ≤ c' := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hκ5 : κ ≤ 1 / 40 := (min_le_right _ _).trans (min_le_right _ _)
  have hκ4 : C' * κ ≤ 1 / 2 := by
    have h : κ ≤ 1 / (2 * C') :=
      (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    calc C' * κ ≤ C' * (1 / (2 * C')) := mul_le_mul_of_nonneg_left h hC'.le
      _ = 1 / 2 := by field_simp
  refine ⟨min (min (c₄ / 2) (c₃ / 4)) (1 / 40), δ, κ,
    lt_min (lt_min (by positivity) (by positivity)) (by norm_num), hδ, hκ0, fun K hK => ?_⟩
  have p1 : 0 ≤ 16 * K ^ 2 := by positivity
  have p2 : 0 ≤ 4 * C₄ := by positivity
  have p3 : 0 ≤ 4 * C₃ := by positivity
  have p4 : 0 ≤ 80 / min c₂₄ 1 := by positivity
  have p5 : 0 ≤ 80 / min c₂₃ 1 := by positivity
  refine ⟨16 * K ^ 2 + 4 * C₄ + 4 * C₃ + 80 / min c₂₄ 1 + 80 / min c₂₃ 1 + 54, by positivity, ?_⟩
  exact FreshLayers.fresh_main h24' h23' h21 hc₂₄ hδ hc₂₃ hK (by positivity) le_rfl
    (min_le_right _ _) ((min_le_left _ _).trans (min_le_left _ _))
    ((min_le_left _ _).trans (min_le_right _ _)) (min_le_right _ _) hκ0 hκ1 hκ2 hκ3 hκ4 hκ5
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)

end LocalAbsorption

end Lovasz
