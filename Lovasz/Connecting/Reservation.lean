/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.Connecting.Basic

/-!
# Reservation estimates (6.5)–(6.6)

DAG node `E6.5` of `docs/BLUEPRINT.md` (Section 6.1 of the paper).

A uniformly random transversal of the left `U`-cosets is the same as independent uniform choices
in the cosets (the sections of `G → G ⧸ U`), so exponential moments of sums `∑_{w ∈ W} ψ w`
factor over the cosets (`transv_tail`). The estimate (6.5) combines this with Lemma 6.2 and cut
counting (6.4) on the coset quotient multigraph; (6.6) uses a union bound over the cosets.
-/

universe u

noncomputable section

namespace Lovasz

open Finset Classical

namespace Connector

/-! ### Uniform transversals as sections -/

section Transversal

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

/-- The left coset `K` as a finset. -/
def fib (U : Subgroup G) (K : G ⧸ U) : Finset G := univ.filter fun g : G => (g : G ⧸ U) = K

omit [DecidableEq G] in
lemma mem_fib {U : Subgroup G} {K : G ⧸ U} {g : G} : g ∈ fib U K ↔ (g : G ⧸ U) = K := by
  simp [fib]

omit [DecidableEq G] in
lemma card_fib (U : Subgroup G) (K : G ⧸ U) : (fib U K).card = Nat.card U := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective K
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun h _ => x * (h : G)) ?_ ?_ ?_
  · intro h _
    rw [mem_fib, QuotientGroup.eq]
    simp
  · intro a _ b _ h
    exact Subtype.ext (mul_left_cancel h)
  · intro g hg
    rw [mem_fib, QuotientGroup.eq] at hg
    exact ⟨⟨x⁻¹ * g, by simpa using inv_mem hg⟩, mem_univ _, by simp⟩

/-- The sections of `G → G ⧸ U`: one element chosen in every left coset. -/
def secs (U : Subgroup G) : Finset (G ⧸ U → G) := Fintype.piFinset fun K => fib U K

/-- The transversals of the left `⟨T⟩`-cosets. -/
def transv (T : Finset G) : Finset (Finset G) := univ.filter fun W => IsTransversal T W

omit [DecidableEq G] in
lemma sec_mk {U : Subgroup G} {σ : G ⧸ U → G} (hσ : σ ∈ secs U) (K : G ⧸ U) :
    ((σ K : G) : G ⧸ U) = K :=
  mem_fib.1 (Fintype.mem_piFinset.1 hσ K)

omit [DecidableEq G] in
lemma sec_injective {U : Subgroup G} {σ : G ⧸ U → G} (hσ : σ ∈ secs U) :
    Function.Injective σ := by
  intro K K' h
  rw [← sec_mk hσ K, ← sec_mk hσ K', h]

lemma transv_eq (T : Finset G) :
    transv T = (secs (Subgroup.closure (T : Set G))).image (fun σ => univ.image σ) := by
  set U := Subgroup.closure (T : Set G)
  ext W
  simp only [transv, mem_filter, mem_univ, true_and, mem_image]
  constructor
  · intro hW
    have hex : ∀ K : G ⧸ U, ∃ w ∈ W, (w : G ⧸ U) = K := by
      intro K
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective K
      obtain ⟨w, hw⟩ := card_pos.1 (by rw [hW x]; norm_num :
        0 < (W.filter fun w => x⁻¹ * w ∈ U).card)
      rw [mem_filter] at hw
      exact ⟨w, hw.1, (QuotientGroup.eq.2 hw.2).symm⟩
    choose σ hσW hσK using hex
    have hσ : σ ∈ secs U := Fintype.mem_piFinset.2 fun K => mem_fib.2 (hσK K)
    refine ⟨σ, hσ, ?_⟩
    ext w
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨K, rfl⟩
      exact hσW K
    · intro hw
      refine ⟨(w : G ⧸ U), ?_⟩
      have h1 := card_le_one.1 (hW w).le
      refine h1 _ (mem_filter.2 ⟨hσW _, ?_⟩) _ (mem_filter.2 ⟨hw, by simp⟩)
      exact QuotientGroup.eq.1 (hσK _).symm
  · rintro ⟨σ, hσ, rfl⟩
    intro x
    rw [card_eq_one]
    refine ⟨σ (x : G ⧸ U), ?_⟩
    ext w
    simp only [mem_filter, mem_image, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨⟨K, rfl⟩, h⟩
      have : (x : G ⧸ U) = K := by
        rw [QuotientGroup.eq.2 h, sec_mk hσ]
      rw [this]
    · rintro rfl
      exact ⟨⟨_, rfl⟩, QuotientGroup.eq.1 (sec_mk hσ _).symm⟩

lemma image_injOn (U : Subgroup G) :
    Set.InjOn (fun σ : G ⧸ U → G => univ.image σ) (secs U : Set (G ⧸ U → G)) := by
  intro σ hσ σ' hσ' h
  funext K
  have hK : σ K ∈ univ.image σ' := by
    have : σ K ∈ univ.image σ := mem_image_of_mem _ (mem_univ _)
    simpa [h] using this
  obtain ⟨K', -, hK'⟩ := mem_image.1 hK
  have : K' = K := by
    rw [← sec_mk hσ' K', hK', sec_mk hσ K]
  rw [← hK', this]

lemma card_transv (T : Finset G) :
    (transv T).card = Nat.card (Subgroup.closure (T : Set G)) ^
      Fintype.card (G ⧸ Subgroup.closure (T : Set G)) := by
  rw [transv_eq, card_image_of_injOn (image_injOn _), secs, Fintype.card_piFinset]
  simp [card_fib]

lemma transv_sum_exp (T : Finset G) (ψ : G → ℝ) :
    ∑ W ∈ transv T, Real.exp (∑ w ∈ W, ψ w) =
      ∏ K : G ⧸ Subgroup.closure (T : Set G),
        ∑ g ∈ fib (Subgroup.closure (T : Set G)) K, Real.exp (ψ g) := by
  rw [transv_eq, sum_image (image_injOn _), secs, prod_univ_sum]
  refine sum_congr rfl fun σ hσ => ?_
  rw [sum_image fun K _ K' _ h => sec_injective hσ h, Real.exp_sum]

/-- **Exponential moment over uniform transversals.** For `0 ≤ ψ ≤ 1`, the number of
transversals `W` with `∑_{w ∈ W} ψ w ≥ t` is at most `exp((e - 1) (∑ ψ) / u - t)` times the
number of all transversals. -/
lemma transv_tail (T : Finset G) (ψ : G → ℝ) (hψ : ∀ g, 0 ≤ ψ g ∧ ψ g ≤ 1) (t : ℝ) :
    (((transv T).filter fun W => t ≤ ∑ w ∈ W, ψ w).card : ℝ) ≤
      (transv T).card * Real.exp ((Real.exp 1 - 1) / Nat.card (Subgroup.closure (T : Set G)) *
        ∑ g, ψ g - t) := by
  set U := Subgroup.closure (T : Set G)
  set u : ℝ := (Nat.card U : ℝ) with hu
  have hupos : 0 < u := by rw [hu]; exact_mod_cast Nat.card_pos
  set c := (Real.exp 1 - 1) / u with hc
  have h1 : (((transv T).filter fun W => t ≤ ∑ w ∈ W, ψ w).card : ℝ) ≤
      ∑ W ∈ transv T, Real.exp (∑ w ∈ W, ψ w) * Real.exp (-t) := by
    rw [card_filter]
    push_cast
    refine sum_le_sum fun W _ => ?_
    split_ifs with h
    · rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    · positivity
  have h2 : ∀ K : G ⧸ U, ∑ g ∈ fib U K, Real.exp (ψ g) ≤
      u * Real.exp (c * ∑ g ∈ fib U K, ψ g) := by
    intro K
    calc ∑ g ∈ fib U K, Real.exp (ψ g) ≤ ∑ g ∈ fib U K, (1 + (Real.exp 1 - 1) * ψ g) := by
          refine sum_le_sum fun g _ => ?_
          have := exp_mul_le_of_mem_Icc 1 (ψ g) (hψ g).1 (hψ g).2
          simpa using this
      _ = u * (1 + c * ∑ g ∈ fib U K, ψ g) := by
          rw [sum_add_distrib, sum_const, card_fib, ← mul_sum, hc]
          field_simp
          simp [hu]
      _ ≤ u * Real.exp (c * ∑ g ∈ fib U K, ψ g) :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (c * ∑ g ∈ fib U K, ψ g)])
            hupos.le
  have h3 : ∑ W ∈ transv T, Real.exp (∑ w ∈ W, ψ w) ≤
      (transv T).card * Real.exp (c * ∑ g, ψ g) := by
    rw [transv_sum_exp]
    refine (prod_le_prod₀ (fun K _ => sum_nonneg fun g _ => (Real.exp_pos _).le)
      fun K _ => h2 K).trans (le_of_eq ?_)
    rw [prod_mul_distrib, prod_const, ← Real.exp_sum, ← mul_sum, card_transv, card_univ]
    simp only [fib]
    rw [sum_fiberwise]
    push_cast
    rfl
  calc _ ≤ _ := h1
    _ = (∑ W ∈ transv T, Real.exp (∑ w ∈ W, ψ w)) * Real.exp (-t) := by rw [sum_mul]
    _ ≤ (transv T).card * Real.exp (c * ∑ g, ψ g) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add, ← sub_eq_add_neg]

end Transversal

/-! ### Cuts of `X₀` and the coset quotient multigraph -/

section Cuts

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
lemma cay_adj_iff {S₀ : Finset G} (hS : IsConnectionSet S₀) (x y : G) :
    (cayleyGraph S₀).Adj x y ↔ x⁻¹ * y ∈ S₀ := by
  rw [cayleyGraph, SimpleGraph.mulCayley_adj]
  simp only [Finset.mem_coe]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · simpa using hS.1 _ h
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    exact hS.2 (by simpa using h)

lemma card_adj_le {S₀ : Finset G} (hS : IsConnectionSet S₀) (x : G) :
    (univ.filter fun y => (cayleyGraph S₀).Adj x y).card ≤ S₀.card := by
  calc _ ≤ (S₀.image (x * ·)).card := card_le_card fun y hy => by
          rw [mem_filter, cay_adj_iff hS] at hy
          exact mem_image.2 ⟨x⁻¹ * y, hy.2, by simp⟩
    _ ≤ S₀.card := card_image_le

/-- The ordered cut edges `(x, y)`, `x ∈ Z`, `y ∉ Z`, of `X₀ = Cay(G, S₀)`. -/
def cutE (S₀ Z : Finset G) : Finset (G × G) :=
  (Z ×ˢ (univ \ Z)).filter fun p => (cayleyGraph S₀).Adj p.1 p.2

/-- The number of cut edges at `w`, counted from both ends. -/
def phi (S₀ Z : Finset G) (w : G) : ℕ :=
  ((cutE S₀ Z).filter fun p => p.1 = w).card + ((cutE S₀ Z).filter fun p => p.2 = w).card

lemma phi_le {S₀ : Finset G} (hS : IsConnectionSet S₀) (Z : Finset G) (w : G) :
    phi S₀ Z w ≤ 2 * S₀.card := by
  have h1 : ((cutE S₀ Z).filter fun p => p.1 = w).card ≤ S₀.card := by
    refine le_trans ?_ (card_adj_le hS w)
    refine card_le_card_of_injOn (fun p => p.2) ?_ ?_
    · intro p hp
      simp only [coe_filter, cutE, mem_filter, Set.mem_ofPred_eq] at hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      rw [← hp.2]
      exact hp.1.2
    · intro p hp q hq h
      simp only [coe_filter, Set.mem_ofPred_eq] at hp hq
      exact Prod.ext (hp.2.trans hq.2.symm) h
  have h2 : ((cutE S₀ Z).filter fun p => p.2 = w).card ≤ S₀.card := by
    refine le_trans ?_ (card_adj_le hS w)
    refine card_le_card_of_injOn (fun p => p.1) ?_ ?_
    · intro p hp
      simp only [coe_filter, cutE, mem_filter, Set.mem_ofPred_eq] at hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      rw [← hp.2]
      exact hp.1.2.symm
    · intro p hp q hq h
      simp only [coe_filter, Set.mem_ofPred_eq] at hp hq
      exact Prod.ext h (hp.2.trans hq.2.symm)
  unfold phi
  omega

lemma sum_phi (S₀ Z : Finset G) : ∑ w, phi S₀ Z w = 2 * (cutE S₀ Z).card := by
  have e1 := card_eq_sum_card_fiberwise (s := cutE S₀ Z) (f := Prod.fst) (t := univ)
    (by intro p _; simp)
  have e2 := card_eq_sum_card_fiberwise (s := cutE S₀ Z) (f := Prod.snd) (t := univ)
    (by intro p _; simp)
  unfold phi
  rw [sum_add_distrib, ← e1, ← e2]
  ring

lemma lost_le (S₀ Z W : Finset G) :
    (cutE S₀ Z).card ≤ ((Z ×ˢ (univ \ Z)).filter fun p =>
        (cayleyGraph S₀).Adj p.1 p.2 ∧ p.1 ∉ W ∧ p.2 ∉ W).card + ∑ w ∈ W, phi S₀ Z w := by
  set R := (Z ×ˢ (univ \ Z)).filter fun p =>
    (cayleyGraph S₀).Adj p.1 p.2 ∧ p.1 ∉ W ∧ p.2 ∉ W
  have hsub : cutE S₀ Z ⊆ R ∪ W.biUnion (fun w => ((cutE S₀ Z).filter fun p => p.1 = w) ∪
      ((cutE S₀ Z).filter fun p => p.2 = w)) := by
    intro p hp
    by_cases h1 : p.1 ∈ W
    · exact mem_union_right _
        (mem_biUnion.2 ⟨p.1, h1, mem_union_left _ (mem_filter.2 ⟨hp, rfl⟩)⟩)
    by_cases h2 : p.2 ∈ W
    · exact mem_union_right _
        (mem_biUnion.2 ⟨p.2, h2, mem_union_right _ (mem_filter.2 ⟨hp, rfl⟩)⟩)
    · have hp' := mem_filter.1 hp
      exact mem_union_left _ (mem_filter.2 ⟨hp'.1, hp'.2, h1, h2⟩)
  calc (cutE S₀ Z).card ≤ _ := card_le_card hsub
    _ ≤ R.card + (W.biUnion (fun w => ((cutE S₀ Z).filter fun p => p.1 = w) ∪
      ((cutE S₀ Z).filter fun p => p.2 = w))).card := card_union_le _ _
    _ ≤ R.card + ∑ w ∈ W, phi S₀ Z w := by
        refine Nat.add_le_add_left ?_ _
        exact card_biUnion_le.trans (sum_le_sum fun w _ => card_union_le _ _)

/-- The union of the left cosets in `I`. -/
def zset (U : Subgroup G) (I : Finset (G ⧸ U)) : Finset G :=
  univ.filter fun x => (x : G ⧸ U) ∈ I

omit [DecidableEq G] in
lemma zset_closed (U : Subgroup G) (I : Finset (G ⧸ U)) :
    ∀ x ∈ zset U I, ∀ y ∈ U, x * y ∈ zset U I := by
  intro x hx y hy
  simp only [zset, mem_filter, mem_univ, true_and] at hx ⊢
  rwa [QuotientGroup.mk_mul_of_mem x hy]

omit [DecidableEq G] in
lemma zset_nonempty {U : Subgroup G} {I : Finset (G ⧸ U)} (h : I.Nonempty) :
    (zset U I).Nonempty := by
  obtain ⟨K, hK⟩ := h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective K
  exact ⟨x, by simpa [zset] using hK⟩

omit [DecidableEq G] in
lemma zset_ne_univ {U : Subgroup G} {I : Finset (G ⧸ U)} (h : I ≠ univ) : zset U I ≠ univ := by
  obtain ⟨K, hK⟩ : ∃ K, K ∉ I := by
    by_contra hc
    push Not at hc
    exact h (eq_univ_iff_forall.2 hc)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective K
  intro hZ
  have : x ∈ zset U I := hZ ▸ mem_univ x
  exact hK (by simpa [zset] using this)

omit [DecidableEq G] in
lemma zset_image {U : Subgroup G} {Z : Finset G} (hZ : ∀ x ∈ Z, ∀ y ∈ U, x * y ∈ Z) :
    zset U (Z.image (QuotientGroup.mk : G → G ⧸ U)) = Z := by
  ext x
  simp only [zset, mem_filter, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have := hZ y hy _ (QuotientGroup.eq.1 hyx)
    simpa using this
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The edges of the coset quotient multigraph: the ordered adjacent pairs of `X₀`. -/
abbrev QE (S₀ : Finset G) := {p : G × G // (cayleyGraph S₀).Adj p.1 p.2}

/-- The ends of an edge of the coset quotient multigraph. -/
def qends (S₀ : Finset G) (U : Subgroup G) (e : QE S₀) : (G ⧸ U) × (G ⧸ U) :=
  ((e.1.1 : G ⧸ U), (e.1.2 : G ⧸ U))

lemma qcut_eq (S₀ : Finset G) (U : Subgroup G) (I : Finset (G ⧸ U)) :
    (univ.filter fun e : QE S₀ => ((qends S₀ U e).1 ∈ I) ≠ ((qends S₀ U e).2 ∈ I)).card =
      2 * (cutE S₀ (zset U I)).card := by
  have h1 : (univ.filter fun e : QE S₀ => ((qends S₀ U e).1 ∈ I) ≠ ((qends S₀ U e).2 ∈ I)).card =
      ((univ : Finset (G × G)).filter fun p => (cayleyGraph S₀).Adj p.1 p.2 ∧
        ((p.1 : G ⧸ U) ∈ I) ≠ ((p.2 : G ⧸ U) ∈ I)).card := by
    refine card_bij (fun e _ => e.1) ?_ ?_ ?_
    · intro e he
      rw [mem_filter] at he ⊢
      exact ⟨mem_univ _, e.2, by simpa [qends] using he.2⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      exact ⟨⟨p, hp.1⟩, by simpa [qends] using hp.2, rfl⟩
  have hA : cutE S₀ (zset U I) = (univ : Finset (G × G)).filter fun p =>
      (cayleyGraph S₀).Adj p.1 p.2 ∧ ((p.1 : G ⧸ U) ∈ I) ∧ ((p.2 : G ⧸ U) ∉ I) := by
    ext p
    simp only [cutE, zset, mem_filter, mem_product, mem_sdiff, mem_univ, true_and]
    tauto
  have hB : ((univ : Finset (G × G)).filter fun p => (cayleyGraph S₀).Adj p.1 p.2 ∧
      ((p.1 : G ⧸ U) ∉ I) ∧ ((p.2 : G ⧸ U) ∈ I)).card = (cutE S₀ (zset U I)).card := by
    rw [hA]
    refine card_bij (fun p _ => p.swap) ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨hp.1.symm, hp.2.2, hp.2.1⟩
    · intro a _ b _ h
      simpa using congrArg Prod.swap h
    · intro p hp
      refine ⟨p.swap, ?_, Prod.swap_swap p⟩
      simp only [mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨hp.1.symm, hp.2.2, hp.2.1⟩
  have hsplit : ((univ : Finset (G × G)).filter fun p => (cayleyGraph S₀).Adj p.1 p.2 ∧
      ((p.1 : G ⧸ U) ∈ I) ≠ ((p.2 : G ⧸ U) ∈ I)) =
      ((univ : Finset (G × G)).filter fun p =>
        (cayleyGraph S₀).Adj p.1 p.2 ∧ ((p.1 : G ⧸ U) ∈ I) ∧ ((p.2 : G ⧸ U) ∉ I)) ∪
      ((univ : Finset (G × G)).filter fun p =>
        (cayleyGraph S₀).Adj p.1 p.2 ∧ ((p.1 : G ⧸ U) ∉ I) ∧ ((p.2 : G ⧸ U) ∈ I)) := by
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_union, ne_eq, eq_iff_iff]
    tauto
  rw [h1, hsplit, card_union_of_disjoint, hB, ← hA]
  · ring
  · rw [disjoint_filter]
    intro p _ ha hb
    exact hb.2.1 ha.2.1

lemma qcut_ge {S₀ : Finset G} (hS : IsConnectionSet S₀) (hconn : (cayleyGraph S₀).Connected)
    (U : Subgroup G) (I : Finset (G ⧸ U)) (hne : I.Nonempty) (hne' : I ≠ univ) :
    Nat.card U ≤
      (univ.filter fun e : QE S₀ => ((qends S₀ U e).1 ∈ I) ≠ ((qends S₀ U e).2 ∈ I)).card := by
  rw [qcut_eq]
  have := coset_cut S₀ hS hconn U (zset U I) (zset_closed U I) (zset_nonempty hne)
    (zset_ne_univ hne')
  have h2 : (Nat.card U : ℝ) ≤ 2 * (cutE S₀ (zset U I)).card := by
    unfold cutE
    linarith
  exact_mod_cast h2

/-- The neighbours in the coset `H` of the vertex `w`. -/
def chi (S₀ : Finset G) (U : Subgroup G) (H : G ⧸ U) (w : G) : ℕ :=
  ((fib U H).filter fun v => (cayleyGraph S₀).Adj v w).card

lemma chi_le {S₀ : Finset G} (hS : IsConnectionSet S₀) (U : Subgroup G) (H : G ⧸ U) (w : G) :
    chi S₀ U H w ≤ S₀.card := by
  refine le_trans (card_le_card fun v hv => ?_) (card_adj_le hS w)
  rw [mem_filter] at hv ⊢
  exact ⟨mem_univ _, hv.2.symm⟩

lemma sum_chi {S₀ : Finset G} (hS : IsConnectionSet S₀) (U : Subgroup G) (H : G ⧸ U) :
    ∑ w, chi S₀ U H w ≤ Nat.card U * S₀.card := by
  unfold chi
  simp only [card_filter]
  rw [sum_comm, ← card_fib U H, ← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun v _ => ?_
  rw [← card_filter]
  exact card_adj_le hS v

lemma res66_le (S₀ W : Finset G) (U : Subgroup G) (H : G ⧸ U) :
    ∑ v ∈ univ.filter (fun v => v ∉ W ∧ (v : G ⧸ U) = H),
      (W.filter fun w => (cayleyGraph S₀).Adj v w).card ≤ ∑ w ∈ W, chi S₀ U H w := by
  calc _ ≤ ∑ v ∈ fib U H, (W.filter fun w => (cayleyGraph S₀).Adj v w).card :=
        sum_le_sum_of_subset fun v hv => by
          simp only [mem_filter, mem_univ, true_and] at hv
          exact mem_fib.2 hv.2
    _ = ∑ w ∈ W, chi S₀ U H w := by
        simp only [chi, card_filter]
        exact sum_comm

end Cuts

/-! ### The tail bounds -/

section Tails

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

omit [Group G] [Fintype G] [DecidableEq G] in
/-- `Finset.mem_filter` for an arbitrary decidability instance, found by unification. -/
lemma mem_filter_any {α : Type*} {s : Finset α} {p : α → Prop} {inst : DecidablePred p}
    {a : α} : a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a :=
  Finset.mem_filter

lemma exp_one_sub_one_lt_two : Real.exp 1 - 1 < 2 := by
  have := Real.exp_one_lt_d9
  linarith

/-- The tail bound behind (6.5) for a fixed cut. -/
lemma tail65 {S₀ T : Finset G} (hS : IsConnectionSet S₀) (k : ℕ) (hk : S₀.card ≤ k)
    (hk0 : 0 < k) (hu : 16 ≤ Nat.card (Subgroup.closure (T : Set G))) (Z : Finset G) :
    (((transv T).filter fun W => ((cutE S₀ Z).card : ℝ) / (4 * k) ≤
        ∑ w ∈ W, (phi S₀ Z w : ℝ) / (2 * k)).card : ℝ) ≤
      (transv T).card * Real.exp (-((cutE S₀ Z).card : ℝ) / (8 * k)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hψ : ∀ g, 0 ≤ (phi S₀ Z g : ℝ) / (2 * k) ∧ (phi S₀ Z g : ℝ) / (2 * k) ≤ 1 := by
    intro g
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    have := phi_le hS Z g
    have : (phi S₀ Z g : ℝ) ≤ 2 * S₀.card := by exact_mod_cast this
    have : (S₀.card : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine (transv_tail T _ hψ _).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Nat.cast_nonneg _)
  have hsum : ∑ g, (phi S₀ Z g : ℝ) / (2 * k) = (cutE S₀ Z).card / k := by
    rw [← sum_div]
    have := sum_phi S₀ Z
    have : ∑ g, (phi S₀ Z g : ℝ) = 2 * (cutE S₀ Z).card := by exact_mod_cast this
    rw [this]
    field_simp
  rw [hsum]
  set z : ℝ := ((cutE S₀ Z).card : ℝ)
  have hz : 0 ≤ z / k := by positivity
  have huR : (16 : ℝ) ≤ Nat.card (Subgroup.closure (T : Set G)) := by exact_mod_cast hu
  have hc : (Real.exp 1 - 1) / Nat.card (Subgroup.closure (T : Set G)) ≤ 1 / 8 := by
    rw [div_le_iff₀ (by linarith)]
    linarith [exp_one_sub_one_lt_two]
  have h1 := mul_le_mul_of_nonneg_right hc hz
  have e1 : z / (4 * k) = 2 * (z / k) / 8 := by field_simp; ring
  have e2 : -z / (8 * k) = -(z / k) / 8 := by field_simp
  rw [e1, e2]
  linarith

/-- The tail bound behind (6.6) for a fixed coset. -/
lemma tail66 {S₀ T : Finset G} (hS : IsConnectionSet S₀) (k : ℕ) (hk : S₀.card ≤ k)
    (hk0 : 0 < k) (H : G ⧸ Subgroup.closure (T : Set G)) (t : ℝ) :
    (((transv T).filter fun W => t ≤
        ∑ w ∈ W, (chi S₀ (Subgroup.closure (T : Set G)) H w : ℝ) / k).card : ℝ) ≤
      (transv T).card * Real.exp (2 - t) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hSk : (S₀.card : ℝ) ≤ k := by exact_mod_cast hk
  have hψ : ∀ g, 0 ≤ (chi S₀ (Subgroup.closure (T : Set G)) H g : ℝ) / k ∧
      (chi S₀ (Subgroup.closure (T : Set G)) H g : ℝ) / k ≤ 1 := by
    intro g
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hkR]
    have := chi_le hS (Subgroup.closure (T : Set G)) H g
    have : (chi S₀ (Subgroup.closure (T : Set G)) H g : ℝ) ≤ S₀.card := by exact_mod_cast this
    linarith
  refine (transv_tail T _ hψ _).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Nat.cast_nonneg _)
  have huR : (0 : ℝ) < Nat.card (Subgroup.closure (T : Set G)) := by exact_mod_cast Nat.card_pos
  have hsum : ∑ g, (chi S₀ (Subgroup.closure (T : Set G)) H g : ℝ) / k ≤
      Nat.card (Subgroup.closure (T : Set G)) := by
    rw [← sum_div, div_le_iff₀ hkR]
    have := sum_chi hS (Subgroup.closure (T : Set G)) H
    have : ∑ g, (chi S₀ (Subgroup.closure (T : Set G)) H g : ℝ) ≤
        Nat.card (Subgroup.closure (T : Set G)) * S₀.card := by exact_mod_cast this
    exact this.trans (mul_le_mul_of_nonneg_left hSk (Nat.cast_nonneg _))
  have h0 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp 1]
  have h1 : (Real.exp 1 - 1) / Nat.card (Subgroup.closure (T : Set G)) *
      ∑ g, (chi S₀ (Subgroup.closure (T : Set G)) H g : ℝ) / k ≤ Real.exp 1 - 1 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ huR]
    exact mul_le_mul_of_nonneg_left hsum h0
  have h2 := exp_one_sub_one_lt_two
  linarith

omit [Group G] [DecidableEq G] in
lemma one_le_log_card (hn : 3 ≤ Fintype.card G) : 1 ≤ Real.log (Fintype.card G) := by
  have hnR : (3 : ℝ) ≤ Fintype.card G := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- One term of the union bound over cut sizes in (6.5). -/
lemma cut_term_le (n j k : ℕ) (u : ℝ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hk0 : 0 < k)
    (hu : 448 * k * Real.log n ≤ u) :
    ((n : ℝ) ^ 3) ^ (4 * (j + 1)) * Real.exp (-(j * u) / (16 * k)) ≤ ((n : ℝ) ^ 4)⁻¹ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hjR : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have h1 : Real.exp (-(j * u) / (16 * k)) ≤ Real.exp (-(((28 * j : ℕ) : ℝ) * Real.log n)) := by
    apply Real.exp_le_exp.2
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    push_cast
    have := mul_le_mul_of_nonneg_left hu hjR
    linarith
  have h2 : Real.exp (-(((28 * j : ℕ) : ℝ) * Real.log n)) = ((n : ℝ) ^ (28 * j))⁻¹ := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hnpos]
  have h3 : ((n : ℝ) ^ 3) ^ (4 * (j + 1)) * (n : ℝ) ^ 4 ≤ (n : ℝ) ^ (28 * j) := by
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ (by exact_mod_cast hn) (by omega)
  calc ((n : ℝ) ^ 3) ^ (4 * (j + 1)) * Real.exp (-(j * u) / (16 * k))
      ≤ ((n : ℝ) ^ 3) ^ (4 * (j + 1)) * ((n : ℝ) ^ (28 * j))⁻¹ :=
        mul_le_mul_of_nonneg_left (h1.trans h2.le) (by positivity)
    _ ≤ ((n : ℝ) ^ 4)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity), inv_mul_eq_div,
          le_div_iff₀ (by positivity)]
        exact h3

/-- **The union bound over coset-union cuts behind (6.5).** Cut counting (6.4) on the coset
quotient multigraph (vertices the left cosets, edges the ordered adjacent pairs of `X₀`), whose
minimum cut is at least `u` by Lemma 6.2, against the tail bound `exp(-z / (8k))`. -/
lemma sum65_le {S₀ : Finset G} (hS : IsConnectionSet S₀) (hconn : (cayleyGraph S₀).Connected)
    (U : Subgroup G) (k : ℕ) (hk0 : 0 < k) (hn : 3 ≤ Fintype.card G)
    (hu : 448 * k * Real.log (Fintype.card G) ≤ Nat.card U) :
    ∑ I ∈ (univ : Finset (Finset (G ⧸ U))).filter (fun I => I.Nonempty ∧ I ≠ univ),
      Real.exp (-((cutE S₀ (zset U I)).card : ℝ) / (8 * k)) ≤ 1 / 8 := by
  have hL1 := one_le_log_card hn
  obtain ⟨n, hn_def⟩ : ∃ n, Fintype.card G = n := ⟨_, rfl⟩
  rw [hn_def] at hn hu hL1
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hu16 : 16 ≤ Nat.card U := by
    have : (448 : ℝ) ≤ Nat.card U := by nlinarith
    exact_mod_cast (by linarith : (16 : ℝ) ≤ Nat.card U)
  have hupos : 0 < Nat.card U := by omega
  have hc2 : ∀ I : Finset (G ⧸ U), (univ.filter fun e : QE S₀ =>
      ((qends S₀ U e).1 ∈ I) ≠ ((qends S₀ U e).2 ∈ I)).card =
      2 * (cutE S₀ (zset U I)).card := fun I => qcut_eq S₀ U I
  have hcge : ∀ I : Finset (G ⧸ U), I.Nonempty → I ≠ univ → Nat.card U ≤ (univ.filter
      fun e : QE S₀ => ((qends S₀ U e).1 ∈ I) ≠ ((qends S₀ U e).2 ∈ I)).card :=
    fun I h1 h2 => qcut_ge hS hconn U I h1 h2
  have hE : Fintype.card (QE S₀) ≤ n ^ 2 := by
    refine (Fintype.card_subtype_le _).trans ?_
    rw [Fintype.card_prod, hn_def]
    ring_nf
    exact le_rfl
  have hcle : ∀ I : Finset (G ⧸ U), (univ.filter fun e : QE S₀ =>
      ((qends S₀ U e).1 ∈ I) ≠ ((qends S₀ U e).2 ∈ I)).card ≤ n ^ 2 :=
    fun I => (card_filter_le _ _).trans hE
  have hq : Fintype.card (G ⧸ U) ≤ n :=
    hn_def ▸ Fintype.card_le_of_surjective _ QuotientGroup.mk_surjective
  have hcount : ∀ j : ℕ, ((univ : Finset (Finset (G ⧸ U))).filter fun I =>
      (univ.filter fun e : QE S₀ => ((qends S₀ U e).1 ∈ I) ≠ ((qends S₀ U e).2 ∈ I)).card <
        (j + 1) * Nat.card U).card ≤ (n ^ 3) ^ (4 * (j + 1)) := by
    intro j
    refine (cut_count (qends S₀ U) (Nat.card U) (by omega)
      (fun I h1 h2 => hcge I h1 h2) j).trans ?_
    apply Nat.pow_le_pow_left
    have h1 : 2 * (Fintype.card (G ⧸ U) + Fintype.card (QE S₀)) ≤ 2 * (n + n ^ 2) := by omega
    refine h1.trans ?_
    have h2 : 3 * n ≤ n * n := Nat.mul_le_mul_right n hn
    have h3 : 3 * (n * n) ≤ n * (n * n) := Nat.mul_le_mul_right (n * n) hn
    have e1 : n ^ 2 = n * n := by ring
    have e2 : n ^ 3 = n * (n * n) := by ring
    rw [e1, e2]
    omega
  -- each nontrivial cut is dominated by the terms of the cut-size classes containing it
  have step1 : ∀ I ∈ (univ : Finset (Finset (G ⧸ U))).filter (fun I => I.Nonempty ∧ I ≠ univ),
      Real.exp (-((cutE S₀ (zset U I)).card : ℝ) / (8 * k)) ≤
        ∑ j ∈ Icc 1 (n ^ 2), if (univ.filter fun e : QE S₀ =>
          ((qends S₀ U e).1 ∈ I) ≠ ((qends S₀ U e).2 ∈ I)).card < (j + 1) * Nat.card U
        then Real.exp (-(j * (Nat.card U : ℝ)) / (16 * k)) else 0 := by
    intro I hI
    rw [mem_filter] at hI
    have hge := hcge I hI.2.1 hI.2.2
    obtain ⟨c, hc⟩ : ∃ c, (univ.filter fun e : QE S₀ =>
        ((qends S₀ U e).1 ∈ I) ≠ ((qends S₀ U e).2 ∈ I)).card = c := ⟨_, rfl⟩
    have hcz := hc2 I
    rw [hc] at hge hcz ⊢
    have hj1 : 1 ≤ c / Nat.card U := (Nat.le_div_iff_mul_le hupos).2 (by simpa using hge)
    have hjN : c / Nat.card U ≤ n ^ 2 := (Nat.div_le_self _ _).trans (hc ▸ hcle I)
    have hlt : c < (c / Nat.card U + 1) * Nat.card U := by
      have := Nat.lt_div_mul_add (a := c) hupos
      rw [add_mul, one_mul]
      exact this
    have hle : c / Nat.card U * Nat.card U ≤ c := Nat.div_mul_le_self _ _
    have hterm : Real.exp (-((cutE S₀ (zset U I)).card : ℝ) / (8 * k)) ≤
        Real.exp (-(((c / Nat.card U : ℕ) : ℝ) * (Nat.card U : ℝ)) / (16 * k)) := by
      apply Real.exp_le_exp.2
      have h1 : (((c / Nat.card U) * Nat.card U : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast hle
      have h1' : (c : ℝ) = 2 * ((cutE S₀ (zset U I)).card : ℝ) := by exact_mod_cast hcz
      push_cast at h1
      have e : -((cutE S₀ (zset U I)).card : ℝ) / (8 * k) =
          -(2 * ((cutE S₀ (zset U I)).card : ℝ)) / (16 * k) := by
        field_simp
        ring
      rw [e]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    refine hterm.trans ?_
    have hmem : c / Nat.card U ∈ Icc 1 (n ^ 2) := mem_Icc.2 ⟨hj1, hjN⟩
    refine le_trans (le_of_eq ?_) (single_le_sum (f := fun j => if c < (j + 1) * Nat.card U
      then Real.exp (-(j * (Nat.card U : ℝ)) / (16 * k)) else 0)
      (fun j _ => by split_ifs <;> positivity) hmem)
    simp only [hlt, ite_true]
  calc ∑ I ∈ (univ : Finset (Finset (G ⧸ U))).filter (fun I => I.Nonempty ∧ I ≠ univ),
        Real.exp (-((cutE S₀ (zset U I)).card : ℝ) / (8 * k))
      ≤ ∑ I ∈ (univ : Finset (Finset (G ⧸ U))).filter (fun I => I.Nonempty ∧ I ≠ univ),
        ∑ j ∈ Icc 1 (n ^ 2), if (univ.filter fun e : QE S₀ =>
          ((qends S₀ U e).1 ∈ I) ≠ ((qends S₀ U e).2 ∈ I)).card < (j + 1) * Nat.card U
        then Real.exp (-(j * (Nat.card U : ℝ)) / (16 * k)) else 0 := sum_le_sum step1
    _ = ∑ j ∈ Icc 1 (n ^ 2),
        ∑ I ∈ (univ : Finset (Finset (G ⧸ U))).filter (fun I => I.Nonempty ∧ I ≠ univ),
        if (univ.filter fun e : QE S₀ =>
          ((qends S₀ U e).1 ∈ I) ≠ ((qends S₀ U e).2 ∈ I)).card < (j + 1) * Nat.card U
        then Real.exp (-(j * (Nat.card U : ℝ)) / (16 * k)) else 0 := sum_comm
    _ ≤ ∑ j ∈ Icc 1 (n ^ 2), ((n : ℝ) ^ 3) ^ (4 * (j + 1)) *
        Real.exp (-(j * (Nat.card U : ℝ)) / (16 * k)) := by
        refine sum_le_sum fun j _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        refine le_trans (Nat.cast_le.2 (card_le_card (filter_subset_filter _ (filter_subset _ _))))
          ?_
        exact_mod_cast hcount j
    _ ≤ ∑ j ∈ Icc 1 (n ^ 2), ((n : ℝ) ^ 4)⁻¹ := by
        refine sum_le_sum fun j hj => ?_
        exact cut_term_le n j k _ (by omega) (mem_Icc.1 hj).1 hk0 hu
    _ = (n : ℝ) ^ 2 * ((n : ℝ) ^ 4)⁻¹ := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast
        simp
    _ ≤ 1 / 8 := by
        have e : (n : ℝ) ^ 2 * ((n : ℝ) ^ 4)⁻¹ = 1 / (n : ℝ) ^ 2 := by
          field_simp
        rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith

/-- A failure of (6.5) is witnessed by a nontrivial set of cosets `I` for which the cut edges at
the reserved vertices are at least half of the cut. -/
lemma bad65_of_not {S₀ T W : Finset G} (k : ℕ) (hk0 : 0 < k) (h : ¬ Res65 T S₀ W) :
    ∃ I ∈ (univ : Finset (Finset (G ⧸ Subgroup.closure (T : Set G)))).filter
        (fun I => I.Nonempty ∧ I ≠ univ),
      ((cutE S₀ (zset _ I)).card : ℝ) / (4 * k) ≤
        ∑ w ∈ W, (phi S₀ (zset _ I) w : ℝ) / (2 * k) := by
  unfold Res65 at h
  push Not at h
  obtain ⟨Z, hZc, hZne, hZu, hlt⟩ := h
  refine ⟨Z.image QuotientGroup.mk, mem_filter.2 ⟨mem_univ _, hZne.image _, ?_⟩, ?_⟩
  · intro hI
    obtain ⟨x, hx⟩ : ∃ x, x ∉ Z := by
      by_contra hc
      push Not at hc
      exact hZu (eq_univ_iff_forall.2 hc)
    have : x ∈ zset _ (Z.image (QuotientGroup.mk : G → G ⧸ Subgroup.closure (T : Set G))) := by
      rw [hI]
      simp [zset]
    rw [zset_image hZc] at this
    exact hx this
  · rw [zset_image hZc]
    have hl := lost_le S₀ Z W
    have h2 : (cutE S₀ Z).card ≤ 2 * ∑ w ∈ W, phi S₀ Z w := by
      unfold cutE at hl ⊢
      omega
    have h2R : ((cutE S₀ Z).card : ℝ) ≤ 2 * ∑ w ∈ W, (phi S₀ Z w : ℝ) := by exact_mod_cast h2
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    rw [← sum_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right h2R (by positivity : (0 : ℝ) ≤ 2 * k)
    linarith

/-- A failure of (6.6) at the bound `4 k L` is witnessed by a coset `H` for which the neighbours
in `H` of the reserved vertices number at least `4 k L`. -/
lemma bad66_of_not {S₀ T W : Finset G} (k : ℕ) (hk0 : 0 < k) (L : ℝ)
    (h : ¬ Res66 T S₀ W (4 * k * L)) :
    ∃ H : G ⧸ Subgroup.closure (T : Set G),
      4 * L ≤ ∑ w ∈ W, (chi S₀ (Subgroup.closure (T : Set G)) H w : ℝ) / k := by
  unfold Res66 at h
  push Not at h
  obtain ⟨H, hH⟩ := h
  refine ⟨H, ?_⟩
  have hle := res66_le S₀ W (Subgroup.closure (T : Set G)) H
  have hleR : ((∑ v ∈ univ.filter (fun v => v ∉ W ∧
      (v : G ⧸ Subgroup.closure (T : Set G)) = H),
      (W.filter fun w => (cayleyGraph S₀).Adj v w).card : ℕ) : ℝ) ≤
      ∑ w ∈ W, (chi S₀ (Subgroup.closure (T : Set G)) H w : ℝ) := by exact_mod_cast hle
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  rw [← sum_div, le_div_iff₀ hkR]
  linarith

end Tails

/-- **Reservation estimates (6.5)–(6.6).** Let `X₀ = Cay(G, S₀)` be connected of degree at most
`k`, and let `u = |⟨T⟩|` be odd with `u ≥ C k L`. If the reserved set is a uniformly random
transversal of the left `⟨T⟩`-cosets (5.7), then with probability at least `3/4` every coset-union
cut retains half its edges in `X₀ - W` (6.5), and `e_{X₀}(H \ W, W) ≤ B_* = C k L` for every
coset `H` (6.6). The proof uses Lemma 6.2 and cut counting (6.4) on the coset quotient, and
exponential moments of independent variables in `[0, k]`. -/
theorem reservation_estimates :
    ∃ Cres CB : ℝ, 0 < Cres ∧ 0 < CB ∧ ∃ n₀ : ℕ,
      ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (T S₀ : Finset G)
        (μ : FinDist (Allocation G)) (k : ℕ),
        n₀ ≤ Fintype.card G → IsConnectionSet S₀ → (cayleyGraph S₀).Connected → S₀.card ≤ k →
        Cres * k * Real.log (Fintype.card G) ≤ Nat.card (Subgroup.closure (T : Set G)) →
        ReservationLaw μ T → Odd (Nat.card (Subgroup.closure (T : Set G))) →
        μ.P (fun 𝒜 => ¬ (Res65 T S₀ 𝒜.W ∧
          Res66 T S₀ 𝒜.W (CB * k * Real.log (Fintype.card G)))) ≤ 1 / 4 := by
  refine ⟨448, 4, by norm_num, by norm_num, 5, ?_⟩
  intro G _ _ _ T S₀ μ k hn hS hconn hk hu hlaw hodd
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      have hS0 : S₀ = ∅ := card_eq_zero.1 (by omega)
      have htop := closure_eq_top_of_connected S₀ hconn
      rw [hS0, coe_empty, Subgroup.closure_empty] at htop
      have : Fintype.card G ≤ 1 := Fintype.card_le_one_iff.2 fun a b => by
        have ha : a ∈ (⊥ : Subgroup G) := htop ▸ Subgroup.mem_top a
        have hb : b ∈ (⊥ : Subgroup G) := htop ▸ Subgroup.mem_top b
        rw [Subgroup.mem_bot] at ha hb
        rw [ha, hb]
      omega
    · exact h0
  have hnR : (5 : ℝ) ≤ Fintype.card G := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < Fintype.card G := by linarith
  have hL1 := one_le_log_card (G := G) (by omega)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hu16 : 16 ≤ Nat.card (Subgroup.closure (T : Set G)) := by
    have : (448 : ℝ) ≤ Nat.card (Subgroup.closure (T : Set G)) := by nlinarith
    exact_mod_cast (by linarith : (16 : ℝ) ≤ Nat.card (Subgroup.closure (T : Set G)))
  have h := hlaw hodd (fun W => ¬ (Res65 T S₀ W ∧
    Res66 T S₀ W (4 * k * Real.log (Fintype.card G))))
  refine h.le.trans ?_
  apply div_le_of_le_mul₀ (Nat.cast_nonneg _) (by norm_num)
  rw [show ((univ : Finset (Finset G)).filter fun W => IsTransversal T W) = transv T from rfl]
  -- the bad transversals are covered by the failures of the individual events
  refine le_trans (Nat.cast_le.2 (card_le_card (t :=
    (((univ : Finset (Finset (G ⧸ Subgroup.closure (T : Set G)))).filter
        (fun I => I.Nonempty ∧ I ≠ univ)).biUnion fun I => (transv T).filter fun W =>
          ((cutE S₀ (zset _ I)).card : ℝ) / (4 * k) ≤
            ∑ w ∈ W, (phi S₀ (zset _ I) w : ℝ) / (2 * k)) ∪
    ((univ : Finset (G ⧸ Subgroup.closure (T : Set G))).biUnion fun H =>
      (transv T).filter fun W => 4 * Real.log (Fintype.card G) ≤
        ∑ w ∈ W, (chi S₀ (Subgroup.closure (T : Set G)) H w : ℝ) / k)) ?_)) ?_
  · intro W hW
    rw [mem_filter_any] at hW
    obtain ⟨-, hWt, hbad⟩ := hW
    have hWt' : W ∈ transv T := mem_filter.2 ⟨mem_univ _, hWt⟩
    rcases not_and_or.1 hbad with h65 | h66
    · obtain ⟨I, hI, hIW⟩ := bad65_of_not k hk0 h65
      exact mem_union_left _ (mem_biUnion.2 ⟨I, hI, mem_filter.2 ⟨hWt', hIW⟩⟩)
    · obtain ⟨H, hHW⟩ := bad66_of_not k hk0 _ h66
      exact mem_union_right _ (mem_biUnion.2 ⟨H, mem_univ _, mem_filter.2 ⟨hWt', hHW⟩⟩)
  refine le_trans (Nat.cast_le.2 ((card_union_le _ _).trans
    (Nat.add_le_add card_biUnion_le card_biUnion_le))) ?_
  push_cast
  have hA : ∑ I ∈ (univ : Finset (Finset (G ⧸ Subgroup.closure (T : Set G)))).filter
        (fun I => I.Nonempty ∧ I ≠ univ), (((transv T).filter fun W =>
          ((cutE S₀ (zset _ I)).card : ℝ) / (4 * k) ≤
            ∑ w ∈ W, (phi S₀ (zset _ I) w : ℝ) / (2 * k)).card : ℝ) ≤
      (transv T).card * (1 / 8) := by
    refine (sum_le_sum fun I _ => tail65 hS k hk hk0 hu16 (zset _ I)).trans ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact sum65_le hS hconn _ k hk0 (by omega) hu
  have hB : ∑ H : G ⧸ Subgroup.closure (T : Set G), (((transv T).filter fun W =>
        4 * Real.log (Fintype.card G) ≤
          ∑ w ∈ W, (chi S₀ (Subgroup.closure (T : Set G)) H w : ℝ) / k).card : ℝ) ≤
      (transv T).card * (1 / 8) := by
    refine (sum_le_sum fun H _ => tail66 hS k hk hk0 H _).trans ?_
    rw [sum_const, card_univ, nsmul_eq_mul, mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hq : (Fintype.card (G ⧸ Subgroup.closure (T : Set G)) : ℝ) ≤ Fintype.card G := by
      exact_mod_cast Fintype.card_le_of_surjective _ QuotientGroup.mk_surjective
    have he4 : Real.exp (4 * Real.log (Fintype.card G)) = (Fintype.card G : ℝ) ^ 4 := by
      rw [show (4 : ℝ) * Real.log (Fintype.card G) = ((4 : ℕ) : ℝ) * Real.log (Fintype.card G)
        by norm_num, Real.exp_nat_mul, Real.exp_log hnpos]
    have he2 : Real.exp 2 ≤ 9 := by
      have h1 := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [h2]
      nlinarith [Real.exp_pos 1]
    rw [Real.exp_sub, he4, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    have hn3 : (125 : ℝ) ≤ (Fintype.card G : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hnR 3
      norm_num at this
      exact this
    calc (Fintype.card (G ⧸ Subgroup.closure (T : Set G)) : ℝ) * Real.exp 2
        ≤ Fintype.card G * 9 := mul_le_mul hq he2 (Real.exp_pos _).le (by positivity)
      _ ≤ 1 / 8 * (Fintype.card G : ℝ) ^ 4 := by
          have : (Fintype.card G : ℝ) ^ 4 = Fintype.card G * (Fintype.card G : ℝ) ^ 3 := by ring
          rw [this]
          nlinarith
  linarith

end Connector

end Lovasz
