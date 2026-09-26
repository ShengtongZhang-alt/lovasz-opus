/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.Connecting.Basic

/-!
# Lemma 6.3: allocation cuts

DAG node `L6.3` of `docs/BLUEPRINT.md` (Section 6.2 of the paper).
-/

universe u

noncomputable section

namespace Lovasz

open Finset Classical

namespace Connector

/-! ### Ordered-pair forms of the cut counts -/

section Pairs

variable {G : Type u} [Fintype G] [DecidableEq G]

/-- A sum over ordered pairs spanning an edge of a loopless edge set is a sum over its edges of
the two orientations. -/
lemma sum_ordered_pairs (F : Finset (Sym2 G)) (hF : ∀ e ∈ F, ¬ e.IsDiag) (f : G × G → ℕ) :
    ∑ p : G × G, (if s(p.1, p.2) ∈ F then f p else 0) =
      ∑ e ∈ F, (f (e.out.1, e.out.2) + f (e.out.2, e.out.1)) := by
  rw [← sum_filter]
  rw [← sum_fiberwise_of_maps_to (s := univ.filter fun p : G × G => s(p.1, p.2) ∈ F) (t := F)
    (g := fun p => s(p.1, p.2)) (fun p hp => (mem_filter.1 hp).2)]
  refine sum_congr rfl fun e he => ?_
  have hne : e.out.1 ≠ e.out.2 := by
    intro h
    apply hF e he
    rw [← mk_out e, Sym2.mk_isDiag_iff]
    exact h
  have : (univ.filter fun p : G × G => s(p.1, p.2) ∈ F).filter (fun p => s(p.1, p.2) = e) =
      {(e.out.1, e.out.2), (e.out.2, e.out.1)} := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨-, h⟩
      rw [← mk_out e, Sym2.eq_iff] at h
      exact h
    · intro h
      have h' : s(a, b) = e := by
        rw [← mk_out e, Sym2.eq_iff]
        exact h
      exact ⟨h' ▸ he, h'⟩
  rw [this, sum_pair]
  intro h
  simp only [Prod.mk.injEq] at h
  exact hne h.1

omit [Fintype G] [DecidableEq G] in
lemma card_bool_filter (P : Bool → Prop) [DecidablePred P] :
    (univ.filter P).card = (if P false then 1 else 0) + (if P true then 1 else 0) := by
  rw [card_filter, Fintype.sum_bool]
  ring

/-- `|δ_{D(F)}(J)|` counts the ordered lifted pairs `((x, β), (y, ¬β))` spanning an edge of `F`
with the state of `(x, β)` in `J` and that of `(y, ¬β)` outside `J`; the state of `(v, β)` is
`(π v, sg v ⊕ β)`. -/
lemma cutCnt_eq_card {t : ℕ} (π : G → Fin t) (sg : G → Bool) (J : Finset (Fin t × Bool))
    (F : Finset (Sym2 G)) (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    cutCnt π sg J F = (univ.filter fun x : (G × G) × Bool => s(x.1.1, x.1.2) ∈ F ∧
      (π x.1.1, xor (sg x.1.1) x.2) ∈ J ∧ (π x.1.2, xor (sg x.1.2) (!x.2)) ∉ J).card := by
  rw [card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  have h1 : ∀ p : G × G, (∑ b : Bool, if s(p.1, p.2) ∈ F ∧
      (π p.1, xor (sg p.1) b) ∈ J ∧ (π p.2, xor (sg p.2) (!b)) ∉ J then 1 else 0) =
      if s(p.1, p.2) ∈ F then (univ.filter fun b : Bool =>
        (π p.1, xor (sg p.1) b) ∈ J ∧ (π p.2, xor (sg p.2) (!b)) ∉ J).card else 0 := by
    intro p
    by_cases h : s(p.1, p.2) ∈ F
    · simp only [h, true_and, ite_true, card_eq_sum_ones, sum_filter]
    · simp [h]
  rw [sum_congr rfl fun p _ => h1 p, sum_ordered_pairs F hF]
  unfold cutCnt outCnt inCnt outArcs inArcs
  rw [← sum_add_distrib]
  refine sum_congr rfl fun e _ => ?_
  rw [card_bool_filter, card_bool_filter, card_bool_filter, card_bool_filter]
  simp only [arcTail, arcHead, Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.not_false]
  by_cases h1 : (π e.out.1, sg e.out.1) ∈ J <;> by_cases h2 : (π e.out.2, sg e.out.2) ∈ J <;>
    by_cases h3 : (π e.out.1, !sg e.out.1) ∈ J <;> by_cases h4 : (π e.out.2, !sg e.out.2) ∈ J <;>
    simp [h1, h2, h3, h4]

/-- The ordinary cut count as a count of ordered pairs. -/
lemma partCross_eq_card {t : ℕ} (π : G → Fin t) (I : Finset (Fin t)) (F : Finset (Sym2 G))
    (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    (F.filter (PartCross π I)).card = (univ.filter fun x : G × G => s(x.1, x.2) ∈ F ∧
      π x.1 ∈ I ∧ π x.2 ∉ I).card := by
  rw [card_eq_sum_ones, sum_filter, card_eq_sum_ones, sum_filter]
  have h1 : ∀ p : G × G, (if s(p.1, p.2) ∈ F ∧ π p.1 ∈ I ∧ π p.2 ∉ I then 1 else 0) =
      if s(p.1, p.2) ∈ F then (if π p.1 ∈ I ∧ π p.2 ∉ I then 1 else 0) else 0 := by
    intro p
    by_cases h : s(p.1, p.2) ∈ F <;> simp [h]
  rw [sum_congr rfl fun p _ => h1 p, sum_ordered_pairs F hF]
  refine sum_congr rfl fun e _ => ?_
  unfold PartCross
  split_ifs <;> simp_all

end Pairs

/-! ### Three generic steps -/

section Generic

/-- **The large-bad-set bound.** If every bad vertex has at least `c` neighbours across the
shore `Z`, then the number of ordered crossing pairs is at least `c |B| / 2`. -/
lemma large_bad_count {V : Type*} [Fintype V] [DecidableEq V] (Adj : V → V → Prop)
    [DecidableRel Adj] (hsymm : ∀ p q, Adj p q → Adj q p) (Z : V → Prop) [DecidablePred Z]
    (Bad : Finset V) (N : V → Finset V) (c : ℝ)
    (hN : ∀ b ∈ Bad, c ≤ (N b).card) (hNadj : ∀ b ∈ Bad, ∀ q ∈ N b, Adj b q ∧ (Z b ↔ ¬ Z q)) :
    c * Bad.card ≤ 2 * (univ.filter fun pq : V × V => Adj pq.1 pq.2 ∧ Z pq.1 ∧ ¬ Z pq.2).card := by
  set P := univ.filter fun pq : V × V => Adj pq.1 pq.2 ∧ Z pq.1 ∧ ¬ Z pq.2 with hP
  have h1 : c * Bad.card ≤ ∑ b ∈ Bad, ((N b).card : ℝ) := by
    calc c * Bad.card = ∑ _b ∈ Bad, c := by rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ _ := sum_le_sum hN
  have h2 : ∑ b ∈ Bad, (N b).card ≤ (P ∪ P.image Prod.swap).card := by
    rw [← card_sigma]
    refine card_le_card_of_injOn (fun x => (x.1, x.2)) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, mem_sigma] at hx
      obtain ⟨hadj, hZ⟩ := hNadj x.1 hx.1 x.2 hx.2
      rw [Finset.mem_coe, mem_union]
      by_cases hb : Z x.1
      · exact Or.inl (mem_filter.2 ⟨mem_univ _, hadj, hb, hZ.1 hb⟩)
      · refine Or.inr (mem_image.2 ⟨(x.2, x.1), mem_filter.2 ⟨mem_univ _, hsymm _ _ hadj, ?_, hb⟩,
          rfl⟩)
        by_contra h
        exact hb (hZ.2 h)
    · intro x _ y _ h
      simp only [Prod.mk.injEq] at h
      exact Sigma.ext h.1 (heq_of_eq h.2)
  have h3 : (P ∪ P.image Prod.swap).card ≤ 2 * P.card := by
    have := card_union_le P (P.image Prod.swap)
    have := card_image_le (s := P) (f := Prod.swap)
    omega
  have h4 : (∑ b ∈ Bad, (N b).card : ℝ) ≤ 2 * P.card := by
    have := h2.trans h3
    exact_mod_cast this
  linarith

variable {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]

omit [Fintype Γ] [DecidableEq Γ] in
lemma cay_label {S₀ : Finset Γ} (hsymm : ∀ s ∈ S₀, s⁻¹ ∈ S₀) {x y : Γ}
    (h : (cayleyGraph S₀).Adj x y) : x⁻¹ * y ∈ S₀ := by
  rw [SimpleGraph.mulCayley_adj] at h
  rcases h.2 with h' | h'
  · exact h'
  · simpa using hsymm _ h'

/-- **Watkins inside one coset.** If the shore `Z` is preserved by every `T̃`-edge avoiding the
removed vertices `Rm` and the bad set, and one coset of `⟨T̃⟩` contains fewer than `|T̃|/2` removed
or bad vertices, then `Z` is constant on the rest of that coset. -/
lemma coset_agree (T' : Finset Γ) (hT : IsConnectionSet T') (Rm : Γ → Prop) [DecidablePred Rm]
    (Bad : Finset Γ)
    (r : ℕ) (x₀ : Γ)
    (hR : (univ.filter fun p => Rm p ∧ x₀⁻¹ * p ∈ Subgroup.closure (T' : Set Γ)).card ≤ r)
    (hB : 2 * ((Bad.filter fun p => x₀⁻¹ * p ∈ Subgroup.closure (T' : Set Γ)).card + r) <
      T'.card)
    (Z : Γ → Prop)
    (hZ : ∀ p, ∀ s ∈ T', ¬ Rm p → p ∉ Bad → ¬ Rm (p * s) → p * s ∉ Bad → (Z p ↔ Z (p * s)))
    {p q : Γ} (hp : ¬ Rm p) (hpB : p ∉ Bad) (hp0 : x₀⁻¹ * p ∈ Subgroup.closure (T' : Set Γ))
    (hq : ¬ Rm q) (hqB : q ∉ Bad) (hq0 : x₀⁻¹ * q ∈ Subgroup.closure (T' : Set Γ)) :
    (Z p ↔ Z q) := by
  set U' := Subgroup.closure (T' : Set Γ) with hU'
  set D := univ.filter fun v => (Rm v ∨ v ∈ Bad) ∧ x₀⁻¹ * v ∈ U' with hDdef
  have hD : D ⊆ (univ.filter fun p => Rm p ∧ x₀⁻¹ * p ∈ U') ∪
      (Bad.filter fun p => x₀⁻¹ * p ∈ U') := by
    intro v hv
    simp only [D, mem_filter, mem_univ, true_and] at hv
    rcases hv with ⟨h | h, h'⟩
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, h, h'⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨h, h'⟩)
  have hDc : 2 * D.card < T'.card := by
    have := (card_le_card hD).trans (card_union_le _ _)
    omega
  have hmemD : ∀ v, v ∈ D ↔ (Rm v ∨ v ∈ Bad) ∧ x₀⁻¹ * v ∈ U' := fun v => by
    simp [D]
  have hpD : p ∉ D := by
    rw [hmemD]
    tauto
  have hqD : q ∉ D := by
    rw [hmemD]
    tauto
  have hpq : p⁻¹ * q ∈ U' := by
    have := mul_mem (inv_mem hp0) hq0
    simpa [mul_assoc] using this
  have hreach := watkins_cayley T' hT D hDc p q hpD hqD hpq
  have key : ∀ w : ↥((D : Set Γ)ᶜ),
      ((cayleyGraph T').induce ((D : Set Γ)ᶜ)).Reachable ⟨p, hpD⟩ w →
        x₀⁻¹ * w.1 ∈ U' ∧ (Z p ↔ Z w.1) := by
    intro w hw
    rw [SimpleGraph.reachable_iff_reflTransGen] at hw
    induction hw with
    | refl => exact ⟨hp0, Iff.rfl⟩
    | tail _ hadj ih =>
      rename_i c d _
      obtain ⟨ih1, ih2⟩ := ih
      have hadj' : (cayleyGraph T').Adj c.1 d.1 := hadj
      have hs : c.1⁻¹ * d.1 ∈ T' := cay_label hT.1 hadj'
      have hd : c.1 * (c.1⁻¹ * d.1) = d.1 := by group
      have hd0 : x₀⁻¹ * d.1 ∈ U' := by
        rw [← hd, ← mul_assoc]
        exact mul_mem ih1 (Subgroup.subset_closure hs)
      have hcD : c.1 ∉ D := c.2
      have hdD : d.1 ∉ D := d.2
      rw [hmemD] at hcD hdD
      have hc1 : ¬ Rm c.1 := fun h => hcD ⟨Or.inl h, ih1⟩
      have hc2 : c.1 ∉ Bad := fun h => hcD ⟨Or.inr h, ih1⟩
      have hd1 : ¬ Rm d.1 := fun h => hdD ⟨Or.inl h, hd0⟩
      have hd2 : d.1 ∉ Bad := fun h => hdD ⟨Or.inr h, hd0⟩
      refine ⟨hd0, ih2.trans ?_⟩
      have := hZ c.1 _ hs hc1 hc2 (by rw [hd]; exact hd1) (by rw [hd]; exact hd2)
      rw [hd] at this
      exact this
  exact (key ⟨q, hqD⟩ hreach).2

/-- The coset shore: if `Z` is constant off `Rm ∪ Bad` on every coset of `⟨T̃⟩`, it agrees off
`Rm ∪ Bad` with a union of such cosets. -/
lemma exists_coset_shore (U' : Subgroup Γ) (Rm : Γ → Prop) (Bad : Finset Γ) (Z : Γ → Prop)
    (hZ : ∀ p q, ¬ Rm p → p ∉ Bad → ¬ Rm q → q ∉ Bad → p⁻¹ * q ∈ U' → (Z p ↔ Z q)) :
    ∃ Zs : Finset Γ, (∀ x ∈ Zs, ∀ g ∈ U', x * g ∈ Zs) ∧
      (∀ x, ¬ Rm x → x ∉ Bad → (x ∈ Zs ↔ Z x)) := by
  refine ⟨univ.filter fun x => ∃ y, x⁻¹ * y ∈ U' ∧ ¬ Rm y ∧ y ∉ Bad ∧ Z y, ?_, ?_⟩
  · intro x hx g hg
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    obtain ⟨y, hy, h1, h2, h3⟩ := hx
    refine ⟨y, ?_, h1, h2, h3⟩
    have := mul_mem (inv_mem hg) hy
    simpa [mul_assoc] using this
  · intro x hx hxB
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, h1, h2, h3⟩
      exact (hZ x y hx hxB h1 h2 hy).2 h3
    · intro h
      exact ⟨x, by simp, hx, hxB, h⟩

/-- **Returning from the coset cut.** Off the bad set the shore `Z` agrees with a union `Zs` of
cosets of `U'`; only labels leaving `U'` cross `Zs`, so at most `2 |B| |S₁|` crossing pairs of
`Zs` are lost. -/
lemma cut_transfer (S₀' S₁' : Finset Γ) (hsymm : ∀ s ∈ S₀', s⁻¹ ∈ S₀') (U' : Subgroup Γ)
    (hlab : ∀ s ∈ S₀', s ∉ U' → s ∈ S₁') (Zs : Finset Γ) (hZs : ∀ x ∈ Zs, ∀ g ∈ U', x * g ∈ Zs)
    (Rm : Γ → Prop) [DecidablePred Rm] (Bad : Finset Γ) (Z : Γ → Prop) [DecidablePred Z]
    (hagree : ∀ x, ¬ Rm x → x ∉ Bad → (x ∈ Zs ↔ Z x)) :
    ((Zs ×ˢ (univ \ Zs)).filter fun pq =>
        (cayleyGraph S₀').Adj pq.1 pq.2 ∧ ¬ Rm pq.1 ∧ ¬ Rm pq.2).card ≤
      (univ.filter fun pq : Γ × Γ => (cayleyGraph S₀').Adj pq.1 pq.2 ∧ ¬ Rm pq.1 ∧ ¬ Rm pq.2 ∧
        Z pq.1 ∧ ¬ Z pq.2).card + 2 * (Bad.card * S₁'.card) := by
  set A := (Zs ×ˢ (univ \ Zs)).filter fun pq =>
    (cayleyGraph S₀').Adj pq.1 pq.2 ∧ ¬ Rm pq.1 ∧ ¬ Rm pq.2 with hA
  set P := univ.filter fun pq : Γ × Γ => (cayleyGraph S₀').Adj pq.1 pq.2 ∧ ¬ Rm pq.1 ∧
    ¬ Rm pq.2 ∧ Z pq.1 ∧ ¬ Z pq.2 with hP
  have hmemA : ∀ pq, pq ∈ A ↔ (pq.1 ∈ Zs ∧ pq.2 ∉ Zs) ∧
      (cayleyGraph S₀').Adj pq.1 pq.2 ∧ ¬ Rm pq.1 ∧ ¬ Rm pq.2 := fun pq => by
    simp [A]
  -- the label of a crossing pair leaves `U'`
  have hlabA : ∀ pq ∈ A, pq.1⁻¹ * pq.2 ∈ S₁' ∧ pq.2⁻¹ * pq.1 ∈ S₁' := by
    intro pq hpq
    rw [hmemA] at hpq
    have hl := cay_label hsymm hpq.2.1
    have hnot : pq.1⁻¹ * pq.2 ∉ U' := by
      intro h
      have := hZs _ hpq.1.1 _ h
      rw [show pq.1 * (pq.1⁻¹ * pq.2) = pq.2 by group] at this
      exact hpq.1.2 this
    refine ⟨hlab _ hl hnot, hlab _ (by simpa using hsymm _ hl) fun h => hnot ?_⟩
    simpa using inv_mem h
  have hsub : A ⊆ P ∪ A.filter (fun pq => pq.1 ∈ Bad) ∪ A.filter (fun pq => pq.2 ∈ Bad) := by
    intro pq hpq
    by_cases h1 : pq.1 ∈ Bad
    · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hpq, h1⟩))
    by_cases h2 : pq.2 ∈ Bad
    · exact mem_union_right _ (mem_filter.2 ⟨hpq, h2⟩)
    refine mem_union_left _ (mem_union_left _ ?_)
    rw [hmemA] at hpq
    refine mem_filter.2 ⟨mem_univ _, hpq.2.1, hpq.2.2.1, hpq.2.2.2, ?_, ?_⟩
    · exact (hagree _ hpq.2.2.1 h1).1 hpq.1.1
    · exact fun h => hpq.1.2 ((hagree _ hpq.2.2.2 h2).2 h)
  have hA1 : (A.filter (fun pq => pq.1 ∈ Bad)).card ≤ Bad.card * S₁'.card := by
    rw [← card_product]
    refine card_le_card_of_injOn (fun pq => (pq.1, pq.1⁻¹ * pq.2)) ?_ ?_
    · intro pq hpq
      rw [Finset.mem_coe, mem_filter] at hpq
      exact mem_product.2 ⟨hpq.2, (hlabA _ hpq.1).1⟩
    · intro x _ y _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1] at h2
      exact Prod.ext h1 (mul_left_cancel h2)
  have hA2 : (A.filter (fun pq => pq.2 ∈ Bad)).card ≤ Bad.card * S₁'.card := by
    rw [← card_product]
    refine card_le_card_of_injOn (fun pq => (pq.2, pq.2⁻¹ * pq.1)) ?_ ?_
    · intro pq hpq
      rw [Finset.mem_coe, mem_filter] at hpq
      exact mem_product.2 ⟨hpq.2, (hlabA _ hpq.1).2⟩
    · intro x _ y _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1] at h2
      exact Prod.ext (mul_left_cancel h2) h1
  have := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  omega

end Generic

/-! ### The bad set of a signed contraction

The ordinary and the lifted arguments are run together on a group `Γ` with a projection
`ρ : Γ →* G` and a lift `lf` of the labels: `Γ = G` (ordinary) or `Γ = G × C₂` (lifted). The
shore is `Z p ⇔ (π (ρ p), κ p) ∈ J`, where `κ p` is the local state of `p` and `κc i p` the state
of the full copy `i` through `p`. -/

section BadSet

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]

omit [Fintype G] [DecidableEq G] in
lemma copyGraph_mono {Ss T Ap Am : Finset G} (h : Ss ⊆ T) {g x y : G}
    (hxy : (copyGraph Ss Ap Am g).Adj x y) : (copyGraph T Ap Am g).Adj x y :=
  ⟨hxy.1, hxy.2.1, hxy.2.2.imp (fun h' => h h') (fun h' => h h')⟩

/-- The bad set: remaining vertices of a full copy whose allocated state lies across the cut. -/
def badSet (𝒜 : Allocation G) (Ap Am : Finset G) (π : G → Fin 𝒜.t) (ρ : Γ →* G) (κ : Γ → Bool)
    (κc : Fin 𝒜.t → Γ → Bool) (J : Finset (Fin 𝒜.t × Bool)) : Finset Γ :=
  univ.filter fun p => ρ p ∉ 𝒜.W ∧
    ∃ i, ρ p ∈ copyVerts Ap Am (𝒜.g i) ∧ ((π (ρ p), κ p) ∈ J ↔ (i, κc i p) ∉ J)

variable {S T Ap Am : Finset G} {𝒜 : Allocation G} {lam D σ η ω cN CN : ℝ}
  {π : G → Fin 𝒜.t}

omit [Fintype G] [DecidableEq G] [Fintype Γ] [DecidableEq Γ] in
lemma lf_injective (ρ : Γ →* G) (lf : G → Γ) (hρlf : ∀ s, ρ (lf s) = s) :
    Function.Injective lf := fun s s' h => by
  have := congrArg ρ h
  rwa [hρlf, hρlf] at this

/-- Every bad vertex sends at least `β` edges of `Y` across the cut, into the allocated part of its
witnessing copy (6.2). -/
lemma bad_nbrs (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN)
    (hπ : ∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v)) {S₀ Ss : Finset G} (hS₀ : IsConnectionSet S₀)
    (hSs : Ss ⊆ S₀) (hSsT : Ss ⊆ T) (ρ : Γ →* G) (lf : G → Γ) (hρlf : ∀ s, ρ (lf s) = s)
    (κ : Γ → Bool) (κc : Fin 𝒜.t → Γ → Bool)
    (hP1 : ∀ p i, ρ p ∈ 𝒜.part i → κ p = κc i p)
    (hP2 : ∀ p i s, (copyGraph T Ap Am (𝒜.g i)).Adj (ρ p) (ρ p * s) → κc i (p * lf s) = κc i p)
    (β : ℝ) (h62 : ∀ i, ∀ v ∈ copyVerts Ap Am (𝒜.g i),
      β ≤ ((𝒜.part i).filter fun y => (copyGraph Ss Ap Am (𝒜.g i)).Adj v y).card)
    (J : Finset (Fin 𝒜.t × Bool)) {b : Γ} (hb : b ∈ badSet 𝒜 Ap Am π ρ κ κc J) :
    ∃ N : Finset Γ, β ≤ N.card ∧ ∀ q ∈ N, (cayleyGraph (S₀.image lf)).Adj b q ∧ ρ q ∉ 𝒜.W ∧
      (ρ b)⁻¹ * ρ q ∈ Subgroup.closure (T : Set G) ∧
      ((π (ρ b), κ b) ∈ J ↔ ¬ (π (ρ q), κ q) ∈ J) := by
  simp only [badSet, mem_filter, mem_univ, true_and] at hb
  obtain ⟨-, i, hbi, hbst⟩ := hb
  set Nb := (𝒜.part i).filter fun y => (copyGraph Ss Ap Am (𝒜.g i)).Adj (ρ b) y with hNb
  have hinj : Function.Injective fun y => b * lf ((ρ b)⁻¹ * y) := by
    intro y y' h
    have := congrArg ρ h
    simp only [map_mul, hρlf] at this
    simpa using this
  refine ⟨Nb.image fun y => b * lf ((ρ b)⁻¹ * y), ?_, ?_⟩
  · rw [card_image_of_injective _ hinj]
    exact h62 i _ hbi
  · intro q hq
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hq
    rw [hNb, mem_filter] at hy
    have hρq : ρ (b * lf ((ρ b)⁻¹ * y)) = y := by
      rw [map_mul, hρlf]
      group
    rw [hρq]
    have hyW : y ∉ 𝒜.W := fun h => disjoint_left.1 (hgood.part_disjoint i) hy.1 h
    have hlab := copyGraph_adj_label hy.2
    have hs0 : (ρ b)⁻¹ * y ∈ S₀ := by
      rcases hlab with h | h
      · exact hSs h
      · simpa using hS₀.1 _ (hSs h)
    have hsU : (ρ b)⁻¹ * y ∈ Subgroup.closure (T : Set G) := by
      rcases hlab with h | h
      · exact Subgroup.subset_closure (hSsT h)
      · simpa using inv_mem (Subgroup.subset_closure (hSsT h) :
          y⁻¹ * ρ b ∈ Subgroup.closure (T : Set G))
    refine ⟨?_, hyW, hsU, ?_⟩
    · rw [SimpleGraph.mulCayley_adj]
      refine ⟨fun h => ?_, Or.inl ?_⟩
      · have h1 : lf ((ρ b)⁻¹ * y) = 1 :=
          (mul_left_cancel (h.symm.trans (mul_one b).symm) :)
        have h2 := congrArg ρ h1
        rw [hρlf, map_one] at h2
        exact hS₀.2 (h2 ▸ hs0)
      · rw [inv_mul_cancel_left]
        exact Finset.mem_coe.2 (mem_image_of_mem lf hs0)
    · have hπy : π y = i := pi_eq_of_mem hgood hπ hy.1
      have hκ : κ (b * lf ((ρ b)⁻¹ * y)) = κc i b := by
        rw [hP1 _ i (by rw [hρq]; exact hy.1)]
        apply hP2 b i
        rw [show ρ b * ((ρ b)⁻¹ * y) = y by group]
        exact copyGraph_mono hSsT hy.2
      rw [hπy, hκ]
      exact hbst

omit [DecidableEq Γ] in
/-- A `T`-edge avoiding the reserved and the bad vertices does not cross the cut: it is covered by
a full copy, whose allocated state both ends agree with. -/
lemma bad_closed (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN) (ρ : Γ →* G) (lf : G → Γ)
    (hρlf : ∀ s, ρ (lf s) = s) (κ : Γ → Bool) (κc : Fin 𝒜.t → Γ → Bool)
    (hP2 : ∀ p i s, (copyGraph T Ap Am (𝒜.g i)).Adj (ρ p) (ρ p * s) → κc i (p * lf s) = κc i p)
    (J : Finset (Fin 𝒜.t × Bool)) (p : Γ) {s : G} (hs : s ∈ T) (hp : ρ p ∉ 𝒜.W)
    (hpB : p ∉ badSet 𝒜 Ap Am π ρ κ κc J) (hq : ρ (p * lf s) ∉ 𝒜.W)
    (hqB : p * lf s ∉ badSet 𝒜 Ap Am π ρ κ κc J) :
    ((π (ρ p), κ p) ∈ J ↔ (π (ρ (p * lf s)), κ (p * lf s)) ∈ J) := by
  obtain ⟨i, hi⟩ := hgood.cover_edges (ρ p) s hs
  have hmem := copyGraph_adj_mem hi
  have hρq : ρ (p * lf s) = ρ p * s := by rw [map_mul, hρlf]
  simp only [badSet, mem_filter, mem_univ, true_and, not_and, not_exists] at hpB hqB
  have h1 := hpB hp i hmem.1
  have h2 := hqB hq i (by rw [hρq]; exact hmem.2)
  rw [hP2 p i s hi] at h2
  tauto

omit [Fintype G] [DecidableEq G] in
lemma exists_good_lift (ρ : Γ →* G) (κ : Γ → Bool) (Bad : Finset Γ) (V : Finset G) (β' : Bool)
    (hlift : ∀ y ∈ V, ∃ p, ρ p = y ∧ κ p = β') (hcard : (Bad.card : ℝ) < V.card) :
    ∃ p, p ∉ Bad ∧ ρ p ∈ V ∧ κ p = β' := by
  choose! f hf using hlift
  by_contra hcon
  push Not at hcon
  have hmaps : ∀ y ∈ V, f y ∈ Bad := fun y hy => by
    by_contra h
    exact (hcon (f y) h (by rw [(hf y hy).1]; exact hy)) (hf y hy).2
  have h1 : V.card ≤ Bad.card :=
    card_le_card_of_injOn f (fun y hy => hmaps y hy) (fun y hy y' hy' h => by
      rw [← (hf y hy).1, ← (hf y' hy').1, h])
  have : (V.card : ℝ) ≤ Bad.card := by exact_mod_cast h1
  linarith

omit [Fintype G] [DecidableEq G] [Fintype Γ] in
lemma rho_closure (ρ : Γ →* G) (lf : G → Γ) (hρlf : ∀ s, ρ (lf s) = s) (T : Finset G) {g : Γ}
    (hg : g ∈ Subgroup.closure ((T.image lf : Finset Γ) : Set Γ)) :
    ρ g ∈ Subgroup.closure (T : Set G) := by
  have : Subgroup.closure ((T.image lf : Finset Γ) : Set Γ) ≤
      (Subgroup.closure (T : Set G)).comap ρ := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [Finset.coe_image] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    show ρ (lf s) ∈ Subgroup.closure (T : Set G)
    rw [hρlf]
    exact Subgroup.subset_closure hs
  exact this hg

omit [Fintype G] [DecidableEq G] [Fintype Γ] in
lemma isConnectionSet_image (ρ : Γ →* G) (lf : G → Γ) (hρlf : ∀ s, ρ (lf s) = s)
    (hlfinv : ∀ s, lf s⁻¹ = (lf s)⁻¹) {T : Finset G} (hT : IsConnectionSet T) :
    IsConnectionSet (T.image lf) := by
  refine ⟨fun s' hs' => ?_, fun h => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := mem_image.1 hs'
    rw [← hlfinv]
    exact mem_image_of_mem lf (hT.1 s hs)
  · obtain ⟨s, hs, h1⟩ := mem_image.1 h
    have := congrArg ρ h1
    rw [hρlf, map_one] at this
    exact hT.2 (this ▸ hs)

/-- Each coset of `⟨lf T⟩` contains at most `r` removed vertices, when the fibres of `ρ` have at
most `r` elements. -/
lemma fib_reserved (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN) (ρ : Γ →* G) (lf : G → Γ)
    (hρlf : ∀ s, ρ (lf s) = s) (r : ℕ)
    (hfib : ∀ y : G, (univ.filter fun p : Γ => ρ p = y).card ≤ r) (x : Γ) :
    (univ.filter fun p => ρ p ∈ 𝒜.W ∧
      x⁻¹ * p ∈ Subgroup.closure ((T.image lf : Finset Γ) : Set Γ)).card ≤ r := by
  by_cases hne : (univ.filter fun p => ρ p ∈ 𝒜.W ∧
      x⁻¹ * p ∈ Subgroup.closure ((T.image lf : Finset Γ) : Set Γ)).Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    refine le_trans (card_le_card fun p hp => ?_) (hfib (ρ p₀))
    rw [mem_filter] at hp hp₀
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have h1 := rho_closure ρ lf hρlf T hp.2.2
    have h2 := rho_closure ρ lf hρlf T hp₀.2.2
    rw [map_mul, map_inv] at h1 h2
    exact reserved_unique hgood (ρ x) _ _ hp.2.1 hp₀.2.1 h1 h2
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty]
    exact Nat.zero_le _

lemma card_filter_mono' {α : Type*} (s : Finset α) {p q : α → Prop} [DecidablePred p]
    [DecidablePred q] (h : ∀ x ∈ s, p x → q x) : (s.filter p).card ≤ (s.filter q).card :=
  card_le_card fun x hx => by
    rw [mem_filter] at hx ⊢
    exact ⟨hx.1, h x hx.1 hx.2⟩

/-- **The global signed-contraction bound.** Either the bad set is large and (6.2) gives
`β b₀ / 2` crossing pairs, or it is small, and the cut agrees off the bad set with a nontrivial
union of `⟨lf T⟩`-cosets, whose `M` crossing pairs lose at most `2 b₀ |S₁|`. -/
theorem generic_global (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN)
    (hπ : ∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v)) (hT : IsConnectionSet T) {S₀ S₁ Ss : Finset G}
    (hS₀ : IsConnectionSet S₀) (hS₀eq : S₀ = S₁ ∪ Ss) (hSsT : Ss ⊆ T)
    (ρ : Γ →* G) (lf : G → Γ) (hρlf : ∀ s, ρ (lf s) = s) (hlfinv : ∀ s, lf s⁻¹ = (lf s)⁻¹)
    (κ : Γ → Bool) (κc : Fin 𝒜.t → Γ → Bool)
    (hP1 : ∀ p i, ρ p ∈ 𝒜.part i → κ p = κc i p)
    (hP2 : ∀ p i s, (copyGraph T Ap Am (𝒜.g i)).Adj (ρ p) (ρ p * s) → κc i (p * lf s) = κc i p)
    (β : ℝ) (hβ : 0 ≤ β) (h62 : ∀ i, ∀ v ∈ copyVerts Ap Am (𝒜.g i),
      β ≤ ((𝒜.part i).filter fun y => (copyGraph Ss Ap Am (𝒜.g i)).Adj v y).card)
    (J : Finset (Fin 𝒜.t × Bool)) (r : ℕ)
    (hfib : ∀ y : G, (univ.filter fun p : Γ => ρ p = y).card ≤ r)
    (b₀ : ℝ) (hb₀V : ∀ i, b₀ ≤ (𝒜.part i).card) (hb₀T : 2 * (b₀ + r) ≤ T.card) (M : ℝ)
    (hcoset : ∀ Zs : Finset Γ,
      (∀ x ∈ Zs, ∀ g ∈ Subgroup.closure ((T.image lf : Finset Γ) : Set Γ), x * g ∈ Zs) →
      Zs.Nonempty → Zs ≠ univ →
      M ≤ ((Zs ×ˢ (univ \ Zs)).filter fun pq =>
        (cayleyGraph (S₀.image lf)).Adj pq.1 pq.2 ∧ ρ pq.1 ∉ 𝒜.W ∧ ρ pq.2 ∉ 𝒜.W).card)
    (hin : ∃ i β', (i, β') ∈ J ∧ ∀ y ∈ 𝒜.part i, ∃ p, ρ p = y ∧ κ p = β')
    (hout : ∃ i β', (i, β') ∉ J ∧ ∀ y ∈ 𝒜.part i, ∃ p, ρ p = y ∧ κ p = β') :
    β * b₀ ≤ 2 * ((univ.filter fun pq : Γ × Γ => (cayleyGraph (S₀.image lf)).Adj pq.1 pq.2 ∧
        ρ pq.1 ∉ 𝒜.W ∧ ρ pq.2 ∉ 𝒜.W ∧ (π (ρ pq.1), κ pq.1) ∈ J ∧
        (π (ρ pq.2), κ pq.2) ∉ J).card : ℝ) ∨
      M ≤ ((univ.filter fun pq : Γ × Γ => (cayleyGraph (S₀.image lf)).Adj pq.1 pq.2 ∧
        ρ pq.1 ∉ 𝒜.W ∧ ρ pq.2 ∉ 𝒜.W ∧ (π (ρ pq.1), κ pq.1) ∈ J ∧
        (π (ρ pq.2), κ pq.2) ∉ J).card : ℝ) + 2 * b₀ * S₁.card := by
  set Bad := badSet 𝒜 Ap Am π ρ κ κc J with hBad
  set P := univ.filter fun pq : Γ × Γ => (cayleyGraph (S₀.image lf)).Adj pq.1 pq.2 ∧
    ρ pq.1 ∉ 𝒜.W ∧ ρ pq.2 ∉ 𝒜.W ∧ (π (ρ pq.1), κ pq.1) ∈ J ∧ (π (ρ pq.2), κ pq.2) ∉ J with hP
  have hSs0 : Ss ⊆ S₀ := hS₀eq ▸ subset_union_right
  by_cases hlarge : b₀ ≤ Bad.card
  · left
    have hN := fun b (hb : b ∈ Bad) =>
      bad_nbrs hgood hπ hS₀ hSs0 hSsT ρ lf hρlf κ κc hP1 hP2 β h62 J hb
    choose! N hN1 hN2 using hN
    have hcount := large_bad_count
      (fun p q => (cayleyGraph (S₀.image lf)).Adj p q ∧ ρ p ∉ 𝒜.W ∧ ρ q ∉ 𝒜.W)
      (fun p q h => ⟨h.1.symm, h.2.2, h.2.1⟩) (fun p => (π (ρ p), κ p) ∈ J) Bad N β hN1
      (fun b hb q hq => by
        obtain ⟨h1, h2, -, h4⟩ := hN2 b hb q hq
        have hbW : ρ b ∉ 𝒜.W := by
          have := hb
          simp only [hBad, badSet, mem_filter] at this
          exact this.2.1
        exact ⟨⟨h1, hbW, h2⟩, h4⟩)
    have hsub := card_filter_mono' (univ : Finset (Γ × Γ))
      (p := fun pq : Γ × Γ => ((cayleyGraph (S₀.image lf)).Adj pq.1 pq.2 ∧ ρ pq.1 ∉ 𝒜.W ∧
        ρ pq.2 ∉ 𝒜.W) ∧ (π (ρ pq.1), κ pq.1) ∈ J ∧ ¬ (π (ρ pq.2), κ pq.2) ∈ J)
      (q := fun pq : Γ × Γ => (cayleyGraph (S₀.image lf)).Adj pq.1 pq.2 ∧
        ρ pq.1 ∉ 𝒜.W ∧ ρ pq.2 ∉ 𝒜.W ∧ (π (ρ pq.1), κ pq.1) ∈ J ∧ (π (ρ pq.2), κ pq.2) ∉ J)
      (fun x _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩)
    have hsub' : (((univ : Finset (Γ × Γ)).filter fun pq : Γ × Γ =>
        ((cayleyGraph (S₀.image lf)).Adj pq.1 pq.2 ∧ ρ pq.1 ∉ 𝒜.W ∧ ρ pq.2 ∉ 𝒜.W) ∧
          (π (ρ pq.1), κ pq.1) ∈ J ∧ ¬ (π (ρ pq.2), κ pq.2) ∈ J).card : ℝ) ≤ P.card := by
      exact_mod_cast hsub
    have hc' : β * b₀ ≤ β * Bad.card := mul_le_mul_of_nonneg_left hlarge hβ
    have hcount' : β * Bad.card ≤ 2 * (((univ : Finset (Γ × Γ)).filter fun pq : Γ × Γ =>
        ((cayleyGraph (S₀.image lf)).Adj pq.1 pq.2 ∧ ρ pq.1 ∉ 𝒜.W ∧ ρ pq.2 ∉ 𝒜.W) ∧
          (π (ρ pq.1), κ pq.1) ∈ J ∧ ¬ (π (ρ pq.2), κ pq.2) ∈ J).card : ℝ) := by
      convert hcount using 3
    linarith
  · right
    push Not at hlarge
    have hb₀pos : 0 < b₀ := lt_of_le_of_lt (Nat.cast_nonneg _) hlarge
    set T' := T.image lf with hT'def
    have hT' : IsConnectionSet T' := isConnectionSet_image ρ lf hρlf hlfinv hT
    have hT'c : T'.card = T.card := card_image_of_injective _ (lf_injective ρ lf hρlf)
    set U' := Subgroup.closure (T' : Set Γ) with hU'
    have hZcos : ∀ p q, ρ p ∉ 𝒜.W → p ∉ Bad → ρ q ∉ 𝒜.W → q ∉ Bad → p⁻¹ * q ∈ U' →
        ((π (ρ p), κ p) ∈ J ↔ (π (ρ q), κ q) ∈ J) := by
      intro p q hp hpB hq hqB hpq
      refine coset_agree T' hT' (fun v => ρ v ∈ 𝒜.W) Bad r p
        (fib_reserved hgood ρ lf hρlf r hfib p) ?_ (fun v => (π (ρ v), κ v) ∈ J) ?_ hp hpB
        (by simp) hq hqB hpq
      · have h1 : ((Bad.filter fun v => p⁻¹ * v ∈ U').card : ℝ) ≤ Bad.card := by
          exact_mod_cast card_filter_le _ _
        have : (2 * ((Bad.filter fun v => p⁻¹ * v ∈ U').card + r) : ℝ) < T'.card := by
          rw [hT'c]
          linarith
        exact_mod_cast this
      · intro v s' hs' hv hvB hvs hvsB
        obtain ⟨s, hs, rfl⟩ := mem_image.1 hs'
        exact bad_closed hgood ρ lf hρlf κ κc hP2 J v hs hv hvB hvs hvsB
    obtain ⟨Zs, hZs1, hZs2⟩ := exists_coset_shore U' (fun v => ρ v ∈ 𝒜.W) Bad
      (fun v => (π (ρ v), κ v) ∈ J) hZcos
    obtain ⟨i, β', hiJ, hlift⟩ := hin
    obtain ⟨p, hpB, hpV, hpκ⟩ :=
      exists_good_lift ρ κ Bad (𝒜.part i) β' hlift (by linarith [hb₀V i])
    obtain ⟨j, β'', hjJ, hlift'⟩ := hout
    obtain ⟨q, hqB, hqV, hqκ⟩ :=
      exists_good_lift ρ κ Bad (𝒜.part j) β'' hlift' (by linarith [hb₀V j])
    have hpW : ρ p ∉ 𝒜.W := fun h => disjoint_left.1 (hgood.part_disjoint i) hpV h
    have hqW : ρ q ∉ 𝒜.W := fun h => disjoint_left.1 (hgood.part_disjoint j) hqV h
    have hpZ : p ∈ Zs := by
      refine (hZs2 p hpW hpB).2 ?_
      show (π (ρ p), κ p) ∈ J
      rw [pi_eq_of_mem hgood hπ hpV, hpκ]
      exact hiJ
    have hqZ : q ∉ Zs := by
      intro h
      have : (π (ρ q), κ q) ∈ J := (hZs2 q hqW hqB).1 h
      rw [pi_eq_of_mem hgood hπ hqV, hqκ] at this
      exact hjJ this
    have hM := hcoset Zs hZs1 ⟨p, hpZ⟩ (fun h => hqZ (h ▸ mem_univ q))
    have hsymm' : ∀ s ∈ S₀.image lf, s⁻¹ ∈ S₀.image lf := by
      intro s' hs'
      obtain ⟨s, hs, rfl⟩ := mem_image.1 hs'
      rw [← hlfinv]
      exact mem_image_of_mem lf (hS₀.1 s hs)
    have hlab : ∀ s ∈ S₀.image lf, s ∉ U' → s ∈ S₁.image lf := by
      intro s' hs' hnot
      obtain ⟨s, hs, rfl⟩ := mem_image.1 hs'
      rw [hS₀eq, mem_union] at hs
      rcases hs with hs | hs
      · exact mem_image_of_mem lf hs
      · exact absurd (Subgroup.subset_closure (Finset.mem_coe.2 (mem_image_of_mem lf (hSsT hs))))
          hnot
    have htr := cut_transfer (S₀.image lf) (S₁.image lf) hsymm' U' hlab Zs hZs1
      (fun v => ρ v ∈ 𝒜.W) Bad (fun v => (π (ρ v), κ v) ∈ J) hZs2
    have hA : ((Zs ×ˢ (univ \ Zs)).filter fun pq =>
        (cayleyGraph (S₀.image lf)).Adj pq.1 pq.2 ∧ ρ pq.1 ∉ 𝒜.W ∧ ρ pq.2 ∉ 𝒜.W).card ≤
        P.card + 2 * (Bad.card * (S₁.image lf).card) := by
      convert htr using 3
    have hA' : (((Zs ×ˢ (univ \ Zs)).filter fun pq =>
        (cayleyGraph (S₀.image lf)).Adj pq.1 pq.2 ∧ ρ pq.1 ∉ 𝒜.W ∧ ρ pq.2 ∉ 𝒜.W).card : ℝ) ≤
        P.card + 2 * ((Bad.card : ℝ) * (S₁.image lf).card) := by
      exact_mod_cast hA
    have hS1c : ((S₁.image lf).card : ℝ) ≤ S₁.card := by exact_mod_cast card_image_le
    have hprod : (Bad.card : ℝ) * (S₁.image lf).card ≤ b₀ * S₁.card :=
      mul_le_mul hlarge.le hS1c (Nat.cast_nonneg _) hb₀pos.le
    linarith

/-- **The local signed-contraction bound** (one coset `H`, when `⟨lf T⟩` is the full preimage of
`⟨T⟩`): a small bad set is impossible, since the single component of the coset minus the reserved
and the bad vertices would meet both shores. -/
theorem generic_local (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN)
    (hπ : ∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v)) (hT : IsConnectionSet T) {S₀ Ss : Finset G}
    (hS₀ : IsConnectionSet S₀) (hSs0 : Ss ⊆ S₀) (hSsT : Ss ⊆ T)
    (ρ : Γ →* G) (lf : G → Γ) (hρlf : ∀ s, ρ (lf s) = s) (hlfinv : ∀ s, lf s⁻¹ = (lf s)⁻¹)
    (κ : Γ → Bool) (κc : Fin 𝒜.t → Γ → Bool)
    (hP1 : ∀ p i, ρ p ∈ 𝒜.part i → κ p = κc i p)
    (hP2 : ∀ p i s, (copyGraph T Ap Am (𝒜.g i)).Adj (ρ p) (ρ p * s) → κc i (p * lf s) = κc i p)
    (β : ℝ) (hβ : 0 ≤ β) (h62 : ∀ i, ∀ v ∈ copyVerts Ap Am (𝒜.g i),
      β ≤ ((𝒜.part i).filter fun y => (copyGraph Ss Ap Am (𝒜.g i)).Adj v y).card)
    (J : Finset (Fin 𝒜.t × Bool)) (r : ℕ)
    (hfib : ∀ y : G, (univ.filter fun p : Γ => ρ p = y).card ≤ r)
    (H : G ⧸ Subgroup.closure (T : Set G))
    (hUfull : ∀ p q : Γ, (ρ p)⁻¹ * ρ q ∈ Subgroup.closure (T : Set G) →
      p⁻¹ * q ∈ Subgroup.closure ((T.image lf : Finset Γ) : Set Γ))
    (b₀ : ℝ) (hb₀V : ∀ i, b₀ ≤ (𝒜.part i).card) (hb₀T : 2 * (b₀ + r) ≤ T.card)
    (hin : ∃ i β', (i, β') ∈ J ∧ (∀ y ∈ 𝒜.part i, (y : G ⧸ Subgroup.closure (T : Set G)) = H) ∧
      ∀ y ∈ 𝒜.part i, ∃ p, ρ p = y ∧ κ p = β')
    (hout : ∃ i β', (i, β') ∉ J ∧ (∀ y ∈ 𝒜.part i, (y : G ⧸ Subgroup.closure (T : Set G)) = H) ∧
      ∀ y ∈ 𝒜.part i, ∃ p, ρ p = y ∧ κ p = β') :
    β * b₀ ≤ 2 * ((univ.filter fun pq : Γ × Γ => (cayleyGraph (S₀.image lf)).Adj pq.1 pq.2 ∧
        ρ pq.1 ∉ 𝒜.W ∧ ρ pq.2 ∉ 𝒜.W ∧ (ρ pq.1 : G ⧸ Subgroup.closure (T : Set G)) = H ∧
        (ρ pq.2 : G ⧸ Subgroup.closure (T : Set G)) = H ∧ (π (ρ pq.1), κ pq.1) ∈ J ∧
        (π (ρ pq.2), κ pq.2) ∉ J).card : ℝ) := by
  set Bad := badSet 𝒜 Ap Am π ρ κ κc J with hBad
  set BadH := Bad.filter fun p => (ρ p : G ⧸ Subgroup.closure (T : Set G)) = H with hBadH
  by_cases hlarge : b₀ ≤ BadH.card
  · have hN := fun b (hb : b ∈ BadH) =>
      bad_nbrs hgood hπ hS₀ hSs0 hSsT ρ lf hρlf κ κc hP1 hP2 β h62 J (mem_filter.1 hb).1
    choose! N hN1 hN2 using hN
    have hcount := large_bad_count
      (fun p q => (cayleyGraph (S₀.image lf)).Adj p q ∧ ρ p ∉ 𝒜.W ∧ ρ q ∉ 𝒜.W ∧
        (ρ p : G ⧸ Subgroup.closure (T : Set G)) = H ∧
        (ρ q : G ⧸ Subgroup.closure (T : Set G)) = H)
      (fun p q h => ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩)
      (fun p => (π (ρ p), κ p) ∈ J) BadH N β hN1
      (fun b hb q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := hN2 b hb q hq
        have hb' := mem_filter.1 hb
        have hbW : ρ b ∉ 𝒜.W := by
          have := hb'.1
          simp only [hBad, badSet, mem_filter] at this
          exact this.2.1
        have hqH : (ρ q : G ⧸ Subgroup.closure (T : Set G)) = H := by
          rw [← hb'.2]
          exact (QuotientGroup.eq.2 h3).symm
        exact ⟨⟨h1, hbW, h2, hb'.2, hqH⟩, h4⟩)
    have hsub := card_filter_mono' (univ : Finset (Γ × Γ))
      (p := fun pq : Γ × Γ => ((cayleyGraph (S₀.image lf)).Adj pq.1 pq.2 ∧ ρ pq.1 ∉ 𝒜.W ∧
        ρ pq.2 ∉ 𝒜.W ∧ (ρ pq.1 : G ⧸ Subgroup.closure (T : Set G)) = H ∧
        (ρ pq.2 : G ⧸ Subgroup.closure (T : Set G)) = H) ∧ (π (ρ pq.1), κ pq.1) ∈ J ∧
          ¬ (π (ρ pq.2), κ pq.2) ∈ J)
      (q := fun pq : Γ × Γ => (cayleyGraph (S₀.image lf)).Adj pq.1 pq.2 ∧
        ρ pq.1 ∉ 𝒜.W ∧ ρ pq.2 ∉ 𝒜.W ∧ (ρ pq.1 : G ⧸ Subgroup.closure (T : Set G)) = H ∧
        (ρ pq.2 : G ⧸ Subgroup.closure (T : Set G)) = H ∧ (π (ρ pq.1), κ pq.1) ∈ J ∧
        (π (ρ pq.2), κ pq.2) ∉ J)
      (fun x _ h => ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2, h.2.1, h.2.2⟩)
    have hcount' : β * BadH.card ≤ 2 * (((univ : Finset (Γ × Γ)).filter fun pq : Γ × Γ =>
        ((cayleyGraph (S₀.image lf)).Adj pq.1 pq.2 ∧ ρ pq.1 ∉ 𝒜.W ∧
        ρ pq.2 ∉ 𝒜.W ∧ (ρ pq.1 : G ⧸ Subgroup.closure (T : Set G)) = H ∧
        (ρ pq.2 : G ⧸ Subgroup.closure (T : Set G)) = H) ∧ (π (ρ pq.1), κ pq.1) ∈ J ∧
          ¬ (π (ρ pq.2), κ pq.2) ∈ J).card : ℝ) := by
      convert hcount using 3
    have hsub' := (Nat.cast_le (α := ℝ)).2 hsub
    have hc' : β * b₀ ≤ β * BadH.card := mul_le_mul_of_nonneg_left hlarge hβ
    linarith
  · exfalso
    push Not at hlarge
    set T' := T.image lf with hT'def
    have hT' : IsConnectionSet T' := isConnectionSet_image ρ lf hρlf hlfinv hT
    have hT'c : T'.card = T.card := card_image_of_injective _ (lf_injective ρ lf hρlf)
    set U' := Subgroup.closure (T' : Set Γ) with hU'
    obtain ⟨i, β', hiJ, hiH, hlift⟩ := hin
    obtain ⟨p, hpB, hpV, hpκ⟩ :=
      exists_good_lift ρ κ BadH (𝒜.part i) β' hlift (by linarith [hb₀V i])
    obtain ⟨j, β'', hjJ, hjH, hlift'⟩ := hout
    obtain ⟨q, hqB, hqV, hqκ⟩ :=
      exists_good_lift ρ κ BadH (𝒜.part j) β'' hlift' (by linarith [hb₀V j])
    have hpH := hiH _ hpV
    have hqH := hjH _ hqV
    have hpB' : p ∉ Bad := fun h => hpB (mem_filter.2 ⟨h, hpH⟩)
    have hqB' : q ∉ Bad := fun h => hqB (mem_filter.2 ⟨h, hqH⟩)
    have hpW : ρ p ∉ 𝒜.W := fun h => disjoint_left.1 (hgood.part_disjoint i) hpV h
    have hqW : ρ q ∉ 𝒜.W := fun h => disjoint_left.1 (hgood.part_disjoint j) hqV h
    have hpq : p⁻¹ * q ∈ U' := hUfull p q (QuotientGroup.eq.1 (hpH.trans hqH.symm))
    have hagree := coset_agree T' hT' (fun v => ρ v ∈ 𝒜.W) Bad r p
      (fib_reserved hgood ρ lf hρlf r hfib p) ?_ (fun v => (π (ρ v), κ v) ∈ J) ?_ hpW hpB'
        (by simp) hqW hqB' hpq
    · have h1 : (π (ρ p), κ p) ∈ J := by
        rw [pi_eq_of_mem hgood hπ hpV, hpκ]
        exact hiJ
      have h2 : (π (ρ q), κ q) ∈ J := hagree.1 h1
      rw [pi_eq_of_mem hgood hπ hqV, hqκ] at h2
      exact hjJ h2
    · have hsub : (Bad.filter fun v => p⁻¹ * v ∈ U') ⊆ BadH := by
        intro v hv
        rw [mem_filter] at hv
        refine mem_filter.2 ⟨hv.1, ?_⟩
        have := rho_closure ρ lf hρlf T hv.2
        rw [map_mul, map_inv] at this
        rw [← hpH]
        exact (QuotientGroup.eq.2 this).symm
      have h1 : ((Bad.filter fun v => p⁻¹ * v ∈ U').card : ℝ) ≤ BadH.card := by
        exact_mod_cast card_le_card hsub
      have : (2 * ((Bad.filter fun v => p⁻¹ * v ∈ U').card + r) : ℝ) < T'.card := by
        rw [hT'c]
        linarith
      exact_mod_cast this
    · intro v s' hs' hv hvB hvs hvsB
      obtain ⟨s, hs, rfl⟩ := mem_image.1 hs'
      exact bad_closed hgood ρ lf hρlf κ κc hP2 J v hs hv hvB hvs hvsB

end BadSet

/-! ### The double cover `G × C₂` -/

section Lift

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

/-- The element of `C₂` as a Boolean. -/
def ofC (η : Multiplicative (ZMod 2)) : Bool := decide (η = Multiplicative.ofAdd 1)

/-- A Boolean as an element of `C₂`. -/
def toC (b : Bool) : Multiplicative (ZMod 2) := if b then Multiplicative.ofAdd 1 else 1

lemma ofC_mul (η : Multiplicative (ZMod 2)) : ofC (η * Multiplicative.ofAdd 1) = !ofC η := by
  revert η
  decide

lemma toC_ofC (η : Multiplicative (ZMod 2)) : toC (ofC η) = η := by
  revert η
  decide

lemma ofC_toC (b : Bool) : ofC (toC b) = b := by
  revert b
  decide

lemma toC_not (b : Bool) : toC (!b) = toC b * Multiplicative.ofAdd 1 := by
  revert b
  decide

lemma c2_eq (η η' : Multiplicative (ZMod 2)) :
    η⁻¹ * η' = Multiplicative.ofAdd 1 ↔ η' = η * Multiplicative.ofAdd 1 := by
  revert η η'
  decide

lemma c2_cases (η : Multiplicative (ZMod 2)) : η = 1 ∨ η = Multiplicative.ofAdd 1 := by
  revert η
  decide

omit [Fintype G] [DecidableEq G] in
lemma xor_xor_self (a b : Bool) : xor a (xor a b) = b := by
  cases a <;> cases b <;> rfl

/-- The lift `s ↦ (s, 1)` of a label to the double cover. -/
def lft (s : G) : G × Multiplicative (ZMod 2) := (s, Multiplicative.ofAdd 1)

omit [Fintype G] [DecidableEq G] in
lemma lft_inv (s : G) : lft s⁻¹ = (lft s)⁻¹ := by
  refine Prod.ext rfl ?_
  show Multiplicative.ofAdd (1 : ZMod 2) = (Multiplicative.ofAdd 1)⁻¹
  decide

omit [Group G] [Fintype G] in
lemma mem_image_lft {S₀ : Finset G} (a : G) (b : Multiplicative (ZMod 2)) :
    (a, b) ∈ S₀.image lft ↔ a ∈ S₀ ∧ b = Multiplicative.ofAdd 1 := by
  rw [mem_image]
  constructor
  · rintro ⟨s, hs, h⟩
    simp only [lft, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hs, rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨a, ha, rfl⟩

omit [Group G] [Fintype G] in
lemma mem_coe_image_lft {S₀ : Finset G} (a : G) (b : Multiplicative (ZMod 2)) :
    (a, b) ∈ ((S₀.image lft : Finset _) : Set (G × Multiplicative (ZMod 2))) ↔
      a ∈ S₀ ∧ b = Multiplicative.ofAdd 1 := by
  rw [Finset.mem_coe]
  exact mem_image_lft a b

omit [Fintype G] in
/-- Adjacency in the bipartite double cover `Cay(G × C₂, S₀ × {1})`. -/
lemma liftAdj {S₀ : Finset G} (hS₀ : IsConnectionSet S₀) (x y : G)
    (η η' : Multiplicative (ZMod 2)) :
    (cayleyGraph (S₀.image lft)).Adj (x, η) (y, η') ↔
      (cayleyGraph S₀).Adj x y ∧ η' = η * Multiplicative.ofAdd 1 := by
  rw [SimpleGraph.mulCayley_adj, SimpleGraph.mulCayley_adj]
  simp only [Prod.inv_mk, Prod.mk_mul_mk, Finset.mem_coe, mem_image_lft]
  have hsw : η = η' * Multiplicative.ofAdd 1 ↔ η' = η * Multiplicative.ofAdd 1 := by
    revert η η'
    decide
  constructor
  · rintro ⟨-, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · refine ⟨⟨?_, Or.inl h1⟩, (c2_eq η η').1 h2⟩
      rintro rfl
      exact hS₀.2 (by simpa using h1)
    · refine ⟨⟨?_, Or.inr h1⟩, hsw.1 ((c2_eq η' η).1 h2)⟩
      rintro rfl
      exact hS₀.2 (by simpa using h1)
  · rintro ⟨⟨hne, h⟩, h2⟩
    refine ⟨fun h' => hne (congrArg Prod.fst h'), ?_⟩
    rcases h with h | h
    · exact Or.inl ⟨h, (c2_eq η η').2 h2⟩
    · exact Or.inr ⟨h, (c2_eq η' η).2 (hsw.2 h2)⟩

/-- The lifted cut count as a count of ordered pairs in `G × C₂`, for an edge set `F` of `Y`
restricted by a vertex predicate `P`. -/
lemma cutCnt_lift {S₀ W : Finset G} (hS₀ : IsConnectionSet S₀) (P : G → Prop) [DecidablePred P]
    {t : ℕ}
    (π : G → Fin t) (sg : G → Bool) (J : Finset (Fin t × Bool)) (F : Finset (Sym2 G))
    (hF : ∀ x y, s(x, y) ∈ F ↔ (cayleyGraph S₀).Adj x y ∧ x ∉ W ∧ y ∉ W ∧ P x ∧ P y) :
    cutCnt π sg J F = (univ.filter fun pq : (G × Multiplicative (ZMod 2)) ×
        (G × Multiplicative (ZMod 2)) => (cayleyGraph (S₀.image lft)).Adj pq.1 pq.2 ∧
      pq.1.1 ∉ W ∧ pq.2.1 ∉ W ∧ P pq.1.1 ∧ P pq.2.1 ∧
      (π pq.1.1, xor (sg pq.1.1) (ofC pq.1.2)) ∈ J ∧
      (π pq.2.1, xor (sg pq.2.1) (ofC pq.2.2)) ∉ J).card := by
  have hloop : ∀ e ∈ F, ¬ e.IsDiag := by
    intro e he
    rw [← mk_out e] at he ⊢
    rw [Sym2.mk_isDiag_iff]
    exact ((hF _ _).1 he).1.ne
  rw [cutCnt_eq_card π sg J F hloop]
  refine card_nbij' (fun x => ((x.1.1, toC x.2), (x.1.2, toC (!x.2))))
    (fun pq => ((pq.1.1, pq.2.1), ofC pq.1.2)) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, mem_filter] at hx
    obtain ⟨-, hF1, hJ1, hJ2⟩ := hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := (hF _ _).1 hF1
    rw [Finset.mem_coe, mem_filter]
    refine ⟨mem_univ _, (liftAdj hS₀ _ _ _ _).2 ⟨h1, toC_not _⟩, h2, h3, h4, h5, ?_, ?_⟩
    · simpa [ofC_toC] using hJ1
    · simpa [ofC_toC] using hJ2
  · intro pq hpq
    rw [Finset.mem_coe, mem_filter] at hpq
    obtain ⟨-, hadj, h2, h3, h4, h5, hJ1, hJ2⟩ := hpq
    obtain ⟨h1, hη⟩ := (liftAdj hS₀ _ _ _ _).1 hadj
    rw [Finset.mem_coe, mem_filter]
    refine ⟨mem_univ _, (hF _ _).2 ⟨h1, h2, h3, h4, h5⟩, hJ1, ?_⟩
    rw [hη, ofC_mul] at hJ2
    exact hJ2
  · intro x _
    simp [ofC_toC]
  · intro pq hpq
    rw [Finset.mem_coe, mem_filter] at hpq
    obtain ⟨h1, hη⟩ := (liftAdj hS₀ _ _ _ _).1 hpq.2.1
    obtain ⟨⟨a, η⟩, ⟨b, η'⟩⟩ := pq
    simp only at hη ⊢
    rw [toC_not, toC_ofC, hη]

omit [Fintype G] in
/-- When `u = |⟨T⟩|` is odd, `⟨(s, 1) : s ∈ T⟩ = ⟨T⟩ × C₂`: `(s, 1)^u = (1, 1)`. -/
lemma lift_closure_full {T : Finset G} (hTne : T.Nonempty)
    (hodd : Odd (Nat.card (Subgroup.closure (T : Set G)))) {y : G}
    (hy : y ∈ Subgroup.closure (T : Set G)) (η : Multiplicative (ZMod 2)) :
    (y, η) ∈ Subgroup.closure ((T.image lft : Finset _) : Set (G × Multiplicative (ZMod 2))) := by
  set U' := Subgroup.closure ((T.image lft : Finset _) : Set (G × Multiplicative (ZMod 2)))
  have hgen : ∀ s ∈ T, (s, Multiplicative.ofAdd (1 : ZMod 2)) ∈ U' := fun s hs =>
    Subgroup.subset_closure ((mem_coe_image_lft s _).2 ⟨hs, rfl⟩)
  have h1 : ∀ y ∈ Subgroup.closure (T : Set G), ∃ η, (y, η) ∈ U' := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem s hs => exact ⟨_, hgen s hs⟩
    | one => exact ⟨1, one_mem _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a * b, mul_mem ha hb⟩
    | inv x _ hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨a⁻¹, inv_mem ha⟩
  have h2 : ((1 : G), Multiplicative.ofAdd (1 : ZMod 2)) ∈ U' := by
    obtain ⟨s, hs⟩ := hTne
    have hsU : s ∈ Subgroup.closure (T : Set G) := Subgroup.subset_closure hs
    have hpow : s ^ Nat.card (Subgroup.closure (T : Set G)) = 1 := by
      have := pow_card_eq_one' (G := Subgroup.closure (T : Set G)) (x := ⟨s, hsU⟩)
      exact congrArg Subtype.val this
    obtain ⟨k, hk⟩ := hodd
    have hmem := pow_mem (hgen s hs) (Nat.card (Subgroup.closure (T : Set G)))
    have : (s, Multiplicative.ofAdd (1 : ZMod 2)) ^ Nat.card (Subgroup.closure (T : Set G)) =
        ((1 : G), Multiplicative.ofAdd (1 : ZMod 2)) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.pow_fst]
        exact hpow
      · rw [Prod.pow_snd, hk, pow_succ, pow_mul]
        have : (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 := by decide
        rw [this, one_pow, one_mul]
    rwa [this] at hmem
  have h3 : ∀ θ : Multiplicative (ZMod 2), ((1 : G), θ) ∈ U' := by
    intro θ
    rcases c2_cases θ with rfl | rfl
    · exact one_mem _
    · exact h2
  obtain ⟨η₀, hη₀⟩ := h1 y hy
  have := mul_mem hη₀ (h3 (η₀⁻¹ * η))
  have e : (y, η₀) * ((1 : G), η₀⁻¹ * η) = (y, η) := by
    refine Prod.ext ?_ ?_
    · show y * 1 = y
      exact mul_one y
    · show η₀ * (η₀⁻¹ * η) = η
      exact mul_inv_cancel_left η₀ η
  rwa [e] at this

omit [Fintype G] in
lemma closure_lft_top {S₀ S₁ : Finset G} (h1 : S₁ ⊆ S₀) (hnb : IsNonbip S₁) :
    Subgroup.closure ((S₀.image lft : Finset _) : Set (G × Multiplicative (ZMod 2))) = ⊤ := by
  rw [eq_top_iff, ← hnb]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨s, hs, rfl⟩
  exact (mem_coe_image_lft s _).2 ⟨h1 hs, rfl⟩

omit [Group G] [Fintype G] in
lemma card_image_lft (T : Finset G) : (T.image lft).card = T.card :=
  card_image_of_injective _ fun _ _ h => congrArg Prod.fst h

end Lift

section SgnAt

variable {G : Type u} [Group G]

/-- The local sign of `v` in the copy `i`: `true` iff `g_i⁻¹ v ∈ A⁺`. -/
def sgnAt (𝒜 : Allocation G) (Ap : Finset G) (i : Fin 𝒜.t) (v : G) : Bool :=
  decide ((𝒜.g i)⁻¹ * v ∈ Ap)

lemma sgnOf_eq (𝒜 : Allocation G) (Ap : Finset G) (π : G → Fin 𝒜.t) (v : G) :
    sgnOf 𝒜 Ap π v = sgnAt 𝒜 Ap (π v) v := rfl

/-- The two ends of an edge of a copy have opposite local signs in that copy. -/
lemma sgnAt_flip {𝒜 : Allocation G} {T Ap Am : Finset G} (hdisj : Disjoint Ap Am) {i : Fin 𝒜.t}
    {x y : G} (h : (copyGraph T Ap Am (𝒜.g i)).Adj x y) : sgnAt 𝒜 Ap i y = !sgnAt 𝒜 Ap i x := by
  unfold sgnAt
  rcases h.2.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : (𝒜.g i)⁻¹ * y ∉ Ap := fun h' => disjoint_left.1 hdisj h' h2
    simp [h1, this]
  · have : (𝒜.g i)⁻¹ * x ∉ Ap := fun h' => disjoint_left.1 hdisj h' h1
    simp [h2, this]

end SgnAt

/-! ### The coset cuts of the two instances -/

section Instances

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable {S T Ap Am : Finset G} {𝒜 : Allocation G} {lam D σ η ω cN CN : ℝ}

omit [Fintype G] [DecidableEq G] in
lemma conY_adj (S₀ W : Finset G) (x y : G) :
    (conY S₀ W).Adj x y ↔ (cayleyGraph S₀).Adj x y ∧ x ∉ W ∧ y ∉ W := Iff.rfl

lemma cayley_connected_of_sub {S₀ S₁ : Finset G} (hS₀ : IsConnectionSet S₀) (h1 : S₁ ⊆ S₀)
    (hS₁ : Subgroup.closure (S₁ : Set G) = ⊤) : (cayleyGraph S₀).Connected :=
  cayley_connected S₀ hS₀.1 (by
    rw [eq_top_iff, ← hS₁]
    exact Subgroup.closure_mono (by exact_mod_cast h1))

/-- The coset cuts in the double cover: `≥ |T|/2` lifted pairs of `Y`, by Lemma 6.2 in the
connected double cover (`u` even, `W = ∅`) or by Lemma 6.2 in `X₀` and (6.5) (`u` odd, when the
cosets of `⟨(s, 1)⟩` are the sets `H × C₂`). -/
lemma lift_coset_bound (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN) (hTne : T.Nonempty)
    {S₀ S₁ : Finset G} (hS₀ : IsConnectionSet S₀) (h1 : S₁ ⊆ S₀)
    (hS₁ : Subgroup.closure (S₁ : Set G) = ⊤) (hnb : IsNonbip S₁)
    (hres : Odd (Nat.card (Subgroup.closure (T : Set G))) → Res65 T S₀ 𝒜.W)
    (Zs : Finset (G × Multiplicative (ZMod 2)))
    (hZs : ∀ x ∈ Zs, ∀ g ∈ Subgroup.closure ((T.image lft : Finset _) :
      Set (G × Multiplicative (ZMod 2))), x * g ∈ Zs)
    (hne : Zs.Nonempty) (hne' : Zs ≠ univ) :
    (T.card : ℝ) / 2 ≤ ((Zs ×ˢ (univ \ Zs)).filter fun pq =>
      (cayleyGraph (S₀.image lft)).Adj pq.1 pq.2 ∧
        (MonoidHom.fst G (Multiplicative (ZMod 2))) pq.1 ∉ 𝒜.W ∧
        (MonoidHom.fst G (Multiplicative (ZMod 2))) pq.2 ∉ 𝒜.W).card := by
  have hTu : (T.card : ℝ) ≤ Nat.card (Subgroup.closure (T : Set G)) := by
    exact_mod_cast card_le_closure T
  have hconn0 := cayley_connected_of_sub hS₀ h1 hS₁
  rcases Nat.even_or_odd (Nat.card (Subgroup.closure (T : Set G))) with hev | hodd
  · have hW := hgood.reserved.2 hev
    have hTU : (T.card : ℝ) ≤ Nat.card (Subgroup.closure ((T.image lft : Finset _) :
        Set (G × Multiplicative (ZMod 2)))) := by
      have := card_le_closure (T.image lft)
      rw [card_image_lft] at this
      exact_mod_cast this
    have hS₀' : IsConnectionSet (S₀.image lft) :=
      isConnectionSet_image (MonoidHom.fst G _) lft (fun _ => rfl) lft_inv hS₀
    have hconn : (cayleyGraph (S₀.image lft)).Connected :=
      cayley_connected _ hS₀'.1 (closure_lft_top h1 hnb)
    have hcc := coset_cut (S₀.image lft) hS₀' hconn _ Zs hZs hne hne'
    have heq : ((Zs ×ˢ (univ \ Zs)).filter fun pq =>
        (cayleyGraph (S₀.image lft)).Adj pq.1 pq.2 ∧
          (MonoidHom.fst G (Multiplicative (ZMod 2))) pq.1 ∉ 𝒜.W ∧
          (MonoidHom.fst G (Multiplicative (ZMod 2))) pq.2 ∉ 𝒜.W) =
        ((Zs ×ˢ (univ \ Zs)).filter fun pq => (cayleyGraph (S₀.image lft)).Adj pq.1 pq.2) :=
      filter_congr fun pq _ => by simp [hW]
    rw [heq]
    linarith
  · have hres' := hres hodd
    have hfull := fun y (hy : y ∈ Subgroup.closure (T : Set G)) η =>
      lift_closure_full hTne hodd hy η
    have hZη : ∀ x η, (x, η) ∈ Zs ↔ (x, (1 : Multiplicative (ZMod 2))) ∈ Zs := by
      intro x η
      constructor
      · intro h
        have := hZs _ h _ (hfull 1 (one_mem _) η⁻¹)
        rwa [show (x, η) * ((1 : G), η⁻¹) = (x, 1) from
          Prod.ext (mul_one x) (mul_inv_cancel η)] at this
      · intro h
        have := hZs _ h _ (hfull 1 (one_mem _) η)
        rwa [show (x, (1 : Multiplicative (ZMod 2))) * ((1 : G), η) = (x, η) from
          Prod.ext (mul_one x) (one_mul η)] at this
    set Zg := univ.filter fun x : G => (x, (1 : Multiplicative (ZMod 2))) ∈ Zs with hZgdef
    have hmemZg : ∀ x, x ∈ Zg ↔ (x, (1 : Multiplicative (ZMod 2))) ∈ Zs := fun x => by
      simp [Zg]
    have hZg : ∀ x ∈ Zg, ∀ y ∈ Subgroup.closure (T : Set G), x * y ∈ Zg := by
      intro x hx y hy
      rw [hmemZg] at hx ⊢
      have := hZs _ hx _ (hfull y hy 1)
      rwa [show (x, (1 : Multiplicative (ZMod 2))) * (y, 1) = (x * y, 1) from
        Prod.ext rfl (one_mul _)] at this
    have hZgne : Zg.Nonempty := by
      obtain ⟨⟨x, η⟩, h⟩ := hne
      exact ⟨x, (hmemZg x).2 ((hZη x η).1 h)⟩
    have hZgne' : Zg ≠ univ := by
      intro h
      apply hne'
      ext ⟨x, η⟩
      simp only [mem_univ, iff_true]
      rw [hZη, ← hmemZg, h]
      exact mem_univ x
    have hcc := coset_cut S₀ hS₀ hconn0 _ Zg hZg hZgne hZgne'
    have hr := hres' Zg hZg hZgne hZgne'
    have hlift : 2 * ((Zg ×ˢ (univ \ Zg)).filter fun p =>
        (cayleyGraph S₀).Adj p.1 p.2 ∧ p.1 ∉ 𝒜.W ∧ p.2 ∉ 𝒜.W).card ≤
        ((Zs ×ˢ (univ \ Zs)).filter fun pq => (cayleyGraph (S₀.image lft)).Adj pq.1 pq.2 ∧
          (MonoidHom.fst G (Multiplicative (ZMod 2))) pq.1 ∉ 𝒜.W ∧
          (MonoidHom.fst G (Multiplicative (ZMod 2))) pq.2 ∉ 𝒜.W).card := by
      have hc2 : (univ : Finset (Multiplicative (ZMod 2))).card = 2 := by decide
      have hcp : (((Zg ×ˢ (univ \ Zg)).filter fun p =>
          (cayleyGraph S₀).Adj p.1 p.2 ∧ p.1 ∉ 𝒜.W ∧ p.2 ∉ 𝒜.W) ×ˢ
          (univ : Finset (Multiplicative (ZMod 2)))).card = 2 * ((Zg ×ˢ (univ \ Zg)).filter
            fun p => (cayleyGraph S₀).Adj p.1 p.2 ∧ p.1 ∉ 𝒜.W ∧ p.2 ∉ 𝒜.W).card := by
        rw [card_product, hc2, mul_comm]
      rw [← hcp]
      refine card_le_card_of_injOn
        (fun x => ((x.1.1, x.2), (x.1.2, x.2 * Multiplicative.ofAdd 1))) ?_ ?_
      · intro x hx
        rw [Finset.mem_coe, mem_product, mem_filter, mem_product] at hx
        obtain ⟨⟨⟨h1, h2⟩, hadj, hw1, hw2⟩, -⟩ := hx
        rw [mem_sdiff] at h2
        rw [Finset.mem_coe, mem_filter, mem_product, mem_sdiff]
        refine ⟨⟨(hZη _ _).2 ((hmemZg _).1 h1),
          ⟨mem_univ _, fun h => h2.2 ((hmemZg _).2 ((hZη _ _).1 h))⟩⟩,
          (liftAdj hS₀ _ _ _ _).2 ⟨hadj, rfl⟩, hw1, hw2⟩
      · intro x _ y _ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1 h.2.1) h.1.2
    have hr' : (((Zg ×ˢ (univ \ Zg)).filter fun p => (cayleyGraph S₀).Adj p.1 p.2).card : ℝ) ≤
        2 * ((Zg ×ˢ (univ \ Zg)).filter fun p =>
          (cayleyGraph S₀).Adj p.1 p.2 ∧ p.1 ∉ 𝒜.W ∧ p.2 ∉ 𝒜.W).card := by
      exact_mod_cast hr
    have hlift' : (2 * ((Zg ×ˢ (univ \ Zg)).filter fun p =>
        (cayleyGraph S₀).Adj p.1 p.2 ∧ p.1 ∉ 𝒜.W ∧ p.2 ∉ 𝒜.W).card : ℝ) ≤
        ((Zs ×ˢ (univ \ Zs)).filter fun pq => (cayleyGraph (S₀.image lft)).Adj pq.1 pq.2 ∧
          (MonoidHom.fst G (Multiplicative (ZMod 2))) pq.1 ∉ 𝒜.W ∧
          (MonoidHom.fst G (Multiplicative (ZMod 2))) pq.2 ∉ 𝒜.W).card := by
      exact_mod_cast hlift
    linarith

/-- The ordinary coset cuts: `≥ |T|/4` pairs of `Y`, by Lemma 6.2 in `X₀` and (6.5). -/
lemma ord_coset_bound (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN) {S₀ S₁ : Finset G}
    (hS₀ : IsConnectionSet S₀) (h1 : S₁ ⊆ S₀) (hS₁ : Subgroup.closure (S₁ : Set G) = ⊤)
    (hres : Odd (Nat.card (Subgroup.closure (T : Set G))) → Res65 T S₀ 𝒜.W) (Zs : Finset G)
    (hZs : ∀ x ∈ Zs, ∀ g ∈ Subgroup.closure ((T.image id : Finset G) : Set G), x * g ∈ Zs)
    (hne : Zs.Nonempty) (hne' : Zs ≠ univ) :
    (T.card : ℝ) / 4 ≤ ((Zs ×ˢ (univ \ Zs)).filter fun pq =>
      (cayleyGraph (S₀.image id)).Adj pq.1 pq.2 ∧ (MonoidHom.id G) pq.1 ∉ 𝒜.W ∧
        (MonoidHom.id G) pq.2 ∉ 𝒜.W).card := by
  rw [image_id] at hZs
  simp only [image_id, MonoidHom.id_apply]
  have hTu : (T.card : ℝ) ≤ Nat.card (Subgroup.closure (T : Set G)) := by
    exact_mod_cast card_le_closure T
  have hcc := coset_cut S₀ hS₀ (cayley_connected_of_sub hS₀ h1 hS₁) _ Zs hZs hne hne'
  rcases Nat.even_or_odd (Nat.card (Subgroup.closure (T : Set G))) with hev | hodd
  · have hW := hgood.reserved.2 hev
    have heq : ((Zs ×ˢ (univ \ Zs)).filter fun pq =>
        (cayleyGraph S₀).Adj pq.1 pq.2 ∧ pq.1 ∉ 𝒜.W ∧ pq.2 ∉ 𝒜.W) =
        ((Zs ×ˢ (univ \ Zs)).filter fun pq => (cayleyGraph S₀).Adj pq.1 pq.2) :=
      filter_congr fun pq _ => by simp [hW]
    rw [heq]
    have h0 : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
    linarith
  · have hr := hres hodd Zs hZs hne hne'
    have hr' : (((Zs ×ˢ (univ \ Zs)).filter fun p => (cayleyGraph S₀).Adj p.1 p.2).card : ℝ) ≤
        2 * ((Zs ×ˢ (univ \ Zs)).filter fun p =>
          (cayleyGraph S₀).Adj p.1 p.2 ∧ p.1 ∉ 𝒜.W ∧ p.2 ∉ 𝒜.W).card := by
      exact_mod_cast hr
    linarith

end Instances

/-- **Lemma 6.3 (Allocation cuts).** Let `X₀ = Cay(G, S₁ ∪ S_s)` with `S_s ⊆ T` the retained
labels satisfying (6.2) and `S₁` the added labels, and let `Y = X₀ - W` with (6.5) when `u` is
odd. Put `µ = c₃ d / L`.
* In the nonbipartite case, the contracted double cover (the two-state graph) has minimum cut at
  least `µ`.
* If `u` is odd, the same holds within any single `⟨T⟩`-coset `H`, using only edges with both
  endpoints in `H`, for state sets that are nontrivial on the states of the parts in `H`.
* In the bipartite case, the ordinary contraction of `Y` on the parts has minimum cut at
  least `µ`.

Proof sketch (paper, §6.2): for a nontrivial union `Z` of states let `B` be the remaining lifted
vertices lying in a full lifted copy whose allocated state is across the cut. By (6.2) and
`cover_mult`, `e(Z, Zᶜ) ≥ c₂ L |B| / (4λ)`, which is `Ω(d/L)` when `|B| ≥ c₀ d/λ`. Otherwise every
lifted `T`-edge avoiding `B` stays on one side (it is covered by a full lifted copy), and by
Watkins (applied inside each `⟨(s,1) : s ∈ T⟩`-coset, deleting `B` and the at most two reserved
lifts) the cut agrees off `B` with a nontrivial union of such cosets; Lemma 6.2 in the connected
double cover of `X₀` and (6.5) give `≥ u/4 ≥ c_T d/4` edges there, of which at most `|S₁| |B|`
(the added labels) are lost. In an odd coset only the first case can occur. -/
theorem allocation_cuts (cT A₀ cN c₂ Cg : ℝ) (hcT : 0 < cT) (hA₀ : 0 < A₀) (hcN : 0 < cN)
    (hc₂ : 0 < c₂) (hCg : 0 < Cg) :
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∃ n₀ : ℕ,
      ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S T Ap Am S₁ Ss : Finset G)
        (𝒜 : Allocation G) (D σ η ω CN : ℝ) (π : G → Fin 𝒜.t),
        n₀ ≤ Fintype.card G → IsConnectionSet S → (cayleyGraph S).Connected →
        Real.log (Fintype.card G) ^ 12 ≤ S.card → IsTemplate S T Ap Am cT →
        𝒜.Good S T Ap Am (A₀ * Real.log (Fintype.card G)) D σ η ω cN CN →
        (∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v)) →
        IsConnectionSet (S₁ ∪ Ss) → S₁ ∪ Ss ⊆ S → Ss ⊆ T →
        Subgroup.closure (S₁ : Set G) = ⊤ → (IsNonbip S → IsNonbip S₁) →
        (S₁.card : ℝ) ≤ Cg * Real.log (Fintype.card G) →
        (∀ i, ∀ v ∈ copyVerts Ap Am (𝒜.g i), c₂ * Real.log (Fintype.card G) ≤
          ((𝒜.part i).filter fun y => (copyGraph Ss Ap Am (𝒜.g i)).Adj v y).card) →
        (Odd (Nat.card (Subgroup.closure (T : Set G))) → Res65 T (S₁ ∪ Ss) 𝒜.W) →
        (IsNonbip S → ∀ J : Finset (Fin 𝒜.t × Bool), J.Nonempty → J ≠ univ →
          c₃ * S.card / Real.log (Fintype.card G) ≤
            cutCnt π (sgnOf 𝒜 Ap π) J (conY (S₁ ∪ Ss) 𝒜.W).edgeFinset) ∧
        (Odd (Nat.card (Subgroup.closure (T : Set G))) →
          ∀ (H : G ⧸ Subgroup.closure (T : Set G)) (J : Finset (Fin 𝒜.t × Bool)),
            (∃ v, v ∉ 𝒜.W ∧ (v : G ⧸ Subgroup.closure (T : Set G)) = H ∧ ∃ β, (π v, β) ∈ J) →
            (∃ v, v ∉ 𝒜.W ∧ (v : G ⧸ Subgroup.closure (T : Set G)) = H ∧ ∃ β, (π v, β) ∉ J) →
            c₃ * S.card / Real.log (Fintype.card G) ≤
              cutCnt π (sgnOf 𝒜 Ap π) J ((conY (S₁ ∪ Ss) 𝒜.W).edgeFinset.filter fun e =>
                ∀ v ∈ e, (v : G ⧸ Subgroup.closure (T : Set G)) = H)) ∧
        (¬ IsNonbip S → ∀ I : Finset (Fin 𝒜.t), I.Nonempty → I ≠ univ →
          c₃ * S.card / Real.log (Fintype.card G) ≤
            ((conY (S₁ ∪ Ss) 𝒜.W).edgeFinset.filter (PartCross π I)).card) := by
  obtain ⟨κ₀, hκ₀, hκ₁, hκ₂, hκ₃⟩ : ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ ≤ cN / A₀ ∧ κ₀ ≤ cT / 4 ∧
      κ₀ ≤ cT / (16 * Cg) :=
    ⟨min (cN / A₀) (min (cT / 4) (cT / (16 * Cg))),
      lt_min (div_pos hcN hA₀) (lt_min (by positivity) (by positivity)), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  refine ⟨min (cT / 8) (c₂ * κ₀ / 2), lt_min (by positivity) (by positivity),
    ⌈Real.exp (max 1 (16 / cT))⌉₊, ?_⟩
  intro G _ _ _ S T Ap Am S₁ Ss 𝒜 D σ η ω CN π hn hS hconn hd12 hT hgood hπ hS₀ hS₀S hSsT
    hS₁top hnb hS₁c h62 hres
  have hc₃1 : min (cT / 8) (c₂ * κ₀ / 2) ≤ cT / 8 := min_le_left _ _
  have hc₃2 : min (cT / 8) (c₂ * κ₀ / 2) ≤ c₂ * κ₀ / 2 := min_le_right _ _
  have hc₃0 : 0 < min (cT / 8) (c₂ * κ₀ / 2) := lt_min (by positivity) (by positivity)
  set c₃ := min (cT / 8) (c₂ * κ₀ / 2) with hc₃
  set L := Real.log (Fintype.card G) with hLdef
  set d : ℝ := (S.card : ℝ) with hddef
  have hnpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hLge : max 1 (16 / cT) ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hnpos]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hLge
  have hL16 : 16 / cT ≤ L := (le_max_right _ _).trans hLge
  have hL0 : 0 < L := by linarith
  have hLd : L ≤ d := (le_self_pow₀ hL1 (by norm_num : (12 : ℕ) ≠ 0)).trans hd12
  have hd0 : 0 < d := by linarith
  have hcTd : 16 ≤ cT * d := by
    have := (div_le_iff₀ hcT).1 (hL16.trans hLd)
    linarith
  have hTc : cT * d ≤ T.card := hT.card_T
  have hTS : IsConnectionSet T := ⟨hT.symm, fun h => hS.2 (hT.sub h)⟩
  have hTne : T.Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < T.card := by linarith
    exact_mod_cast this
  have hSs0 : Ss ⊆ S₁ ∪ Ss := subset_union_right
  have hS₁0 : S₁ ⊆ S₁ ∪ Ss := subset_union_left
  set b₀ := κ₀ * d / L with hb₀
  have hb₀V : ∀ i, b₀ ≤ (𝒜.part i).card := by
    intro i
    refine le_trans ?_ (hgood.size_lower i)
    rw [hb₀, show cN * (S.card : ℝ) / (A₀ * L) = cN / A₀ * d / L by rw [hddef]; field_simp]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hκ₁ hd0.le) hL0.le
  have hb₀le : b₀ ≤ cT / 4 * d := by
    rw [hb₀, div_le_iff₀ hL0]
    calc κ₀ * d ≤ cT / 4 * d := mul_le_mul_of_nonneg_right hκ₂ hd0.le
      _ ≤ cT / 4 * d * L := le_mul_of_one_le_right (by positivity) hL1
  have hb₀T : ∀ r : ℕ, r ≤ 2 → 2 * (b₀ + r) ≤ T.card := by
    intro r hr
    have : (r : ℝ) ≤ 2 := by exact_mod_cast hr
    linarith
  have hloss : 2 * b₀ * S₁.card ≤ cT * d / 8 := by
    have h1 : 2 * b₀ * S₁.card ≤ 2 * b₀ * (Cg * L) :=
      mul_le_mul_of_nonneg_left hS₁c (by positivity)
    have h2 : 2 * b₀ * (Cg * L) = 2 * Cg * d * κ₀ := by
      rw [hb₀]
      field_simp
    have h3 : 2 * Cg * d * κ₀ ≤ 2 * Cg * d * (cT / (16 * Cg)) :=
      mul_le_mul_of_nonneg_left hκ₃ (by positivity)
    have h4 : 2 * Cg * d * (cT / (16 * Cg)) = cT * d / 8 := by
      field_simp
      ring
    linarith
  have hβ : 0 ≤ c₂ * L := by positivity
  have hfinal : ∀ M X : ℝ, cT * d / 4 ≤ M →
      (c₂ * L * b₀ ≤ 2 * X ∨ M ≤ X + 2 * b₀ * S₁.card) → c₃ * d / L ≤ X := by
    intro M X hM hX
    have hc3d : c₃ * d / L ≤ c₃ * d := by
      rw [div_le_iff₀ hL0]
      exact le_mul_of_one_le_right (by positivity) hL1
    rcases hX with hX | hX
    · have e : c₂ * L * b₀ = c₂ * κ₀ * d := by
        rw [hb₀]
        field_simp
      have : c₃ * d ≤ c₂ * κ₀ / 2 * d := mul_le_mul_of_nonneg_right hc₃2 hd0.le
      linarith
    · have : c₃ * d ≤ cT / 8 * d := mul_le_mul_of_nonneg_right hc₃1 hd0.le
      linarith
  -- the double cover
  have hfib2 : ∀ y : G, (univ.filter fun p : G × Multiplicative (ZMod 2) =>
      (MonoidHom.fst G (Multiplicative (ZMod 2))) p = y).card ≤ 2 := by
    intro y
    calc _ ≤ (({y} : Finset G) ×ˢ (univ : Finset (Multiplicative (ZMod 2)))).card :=
          card_le_card fun p hp => by
            rw [mem_filter] at hp
            rw [mem_product, mem_singleton]
            exact ⟨hp.2, mem_univ _⟩
      _ = 2 := by
        rw [card_product, card_singleton, one_mul]
        decide
  have hP1L : ∀ (p : G × Multiplicative (ZMod 2)) (i : Fin 𝒜.t),
      (MonoidHom.fst G (Multiplicative (ZMod 2))) p ∈ 𝒜.part i →
      (fun p : G × Multiplicative (ZMod 2) => xor (sgnOf 𝒜 Ap π p.1) (ofC p.2)) p =
        (fun (i : Fin 𝒜.t) (p : G × Multiplicative (ZMod 2)) =>
          xor (sgnAt 𝒜 Ap i p.1) (ofC p.2)) i p := by
    intro p i hp
    have hpi : π p.1 = i := pi_eq_of_mem hgood hπ hp
    show xor (sgnOf 𝒜 Ap π p.1) (ofC p.2) = xor (sgnAt 𝒜 Ap i p.1) (ofC p.2)
    rw [sgnOf_eq, hpi]
  have hP2L : ∀ (p : G × Multiplicative (ZMod 2)) (i : Fin 𝒜.t) (s : G),
      (copyGraph T Ap Am (𝒜.g i)).Adj ((MonoidHom.fst G (Multiplicative (ZMod 2))) p)
        ((MonoidHom.fst G (Multiplicative (ZMod 2))) p * s) →
      (fun (i : Fin 𝒜.t) (p : G × Multiplicative (ZMod 2)) =>
          xor (sgnAt 𝒜 Ap i p.1) (ofC p.2)) i (p * lft s) =
        (fun (i : Fin 𝒜.t) (p : G × Multiplicative (ZMod 2)) =>
          xor (sgnAt 𝒜 Ap i p.1) (ofC p.2)) i p := by
    intro p i s hadj
    have hadj' : (copyGraph T Ap Am (𝒜.g i)).Adj p.1 (p.1 * s) := hadj
    show xor (sgnAt 𝒜 Ap i (p.1 * s)) (ofC (p.2 * Multiplicative.ofAdd 1)) =
      xor (sgnAt 𝒜 Ap i p.1) (ofC p.2)
    rw [sgnAt_flip hT.disjoint hadj', ofC_mul]
    cases sgnAt 𝒜 Ap i p.1 <;> cases ofC p.2 <;> rfl
  have hliftL : ∀ (β' : Bool) (y : G), ∃ p : G × Multiplicative (ZMod 2),
      (MonoidHom.fst G (Multiplicative (ZMod 2))) p = y ∧
      (fun p : G × Multiplicative (ZMod 2) => xor (sgnOf 𝒜 Ap π p.1) (ofC p.2)) p = β' := by
    intro β' y
    refine ⟨(y, toC (xor (sgnOf 𝒜 Ap π y) β')), rfl, ?_⟩
    show xor (sgnOf 𝒜 Ap π y) (ofC (toC (xor (sgnOf 𝒜 Ap π y) β'))) = β'
    rw [ofC_toC, xor_xor_self]
  have hloop : ∀ e ∈ (conY (S₁ ∪ Ss) 𝒜.W).edgeFinset, ¬ e.IsDiag := fun e he =>
    SimpleGraph.not_isDiag_of_mem_edgeSet _ (SimpleGraph.mem_edgeFinset.1 he)
  refine ⟨?_, ?_, ?_⟩
  · -- the contracted double cover
    intro hnbS J hJne hJuniv
    obtain ⟨⟨i, β'⟩, hiJ⟩ := hJne
    obtain ⟨⟨j, β''⟩, hjJ⟩ : ∃ x, x ∉ J := by
      by_contra h
      push Not at h
      exact hJuniv (eq_univ_iff_forall.2 h)
    have key := generic_global (Γ := G × Multiplicative (ZMod 2)) hgood hπ hTS hS₀ rfl hSsT
      (MonoidHom.fst G (Multiplicative (ZMod 2))) lft (fun _ => rfl) lft_inv
      (fun p => xor (sgnOf 𝒜 Ap π p.1) (ofC p.2))
      (fun i p => xor (sgnAt 𝒜 Ap i p.1) (ofC p.2)) hP1L hP2L (c₂ * L) hβ h62 J 2
      hfib2 b₀ hb₀V (hb₀T 2 le_rfl) (T.card / 2)
      (fun Zs hZs hne hne' => lift_coset_bound hgood hTne hS₀ hS₁0 hS₁top (hnb hnbS) hres Zs
        hZs hne hne')
      ⟨i, β', hiJ, fun y _ => hliftL β' y⟩ ⟨j, β'', hjJ, fun y _ => hliftL β'' y⟩
    refine le_of_le_of_eq (hfinal _ _ (by linarith) key) ?_
    rw [cutCnt_lift (W := 𝒜.W) hS₀ (fun _ => True) π (sgnOf 𝒜 Ap π) J (conY (S₁ ∪ Ss) 𝒜.W).edgeFinset
      (fun x y => by
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, and_true]
        exact Iff.rfl)]
    exact congrArg (fun n : ℕ => (n : ℝ)) (congrArg Finset.card (filter_congr fun pq _ => by
      simp only [MonoidHom.coe_fst, true_and]))
  · -- within one odd coset
    intro hodd H J hin hout
    have hUfull : ∀ p q : G × Multiplicative (ZMod 2),
        ((MonoidHom.fst G (Multiplicative (ZMod 2))) p)⁻¹ *
          (MonoidHom.fst G (Multiplicative (ZMod 2))) q ∈ Subgroup.closure (T : Set G) →
        p⁻¹ * q ∈ Subgroup.closure ((T.image lft : Finset _) :
          Set (G × Multiplicative (ZMod 2))) := by
      intro p q h
      have e : p⁻¹ * q = (p.1⁻¹ * q.1, p.2⁻¹ * q.2) := rfl
      rw [e]
      exact lift_closure_full hTne hodd h _
    have hcosH : ∀ w, w ∉ 𝒜.W → (w : G ⧸ Subgroup.closure (T : Set G)) = H →
        ∀ y ∈ 𝒜.part (π w), (y : G ⧸ Subgroup.closure (T : Set G)) = H := by
      intro w hw hwH y hy
      rw [← hwH]
      exact (QuotientGroup.eq.2 (copy_coset hT _ (hgood.part_sub _ (hπ w hw))
        (hgood.part_sub _ hy))).symm
    obtain ⟨v, hvW, hvH, β', hβ'⟩ := hin
    obtain ⟨v', hvW', hvH', β'', hβ''⟩ := hout
    have key := generic_local (Γ := G × Multiplicative (ZMod 2)) hgood hπ hTS hS₀ hSs0 hSsT
      (MonoidHom.fst G (Multiplicative (ZMod 2))) lft (fun _ => rfl) lft_inv
      (fun p => xor (sgnOf 𝒜 Ap π p.1) (ofC p.2))
      (fun i p => xor (sgnAt 𝒜 Ap i p.1) (ofC p.2)) hP1L hP2L (c₂ * L) hβ h62 J 2
      hfib2 H hUfull b₀ hb₀V (hb₀T 2 le_rfl)
      ⟨π v, β', hβ', hcosH v hvW hvH, fun y _ => hliftL β' y⟩
      ⟨π v', β'', hβ'', hcosH v' hvW' hvH', fun y _ => hliftL β'' y⟩
    refine le_of_le_of_eq (hfinal (cT * d / 4) _ le_rfl (Or.inl key)) ?_
    rw [cutCnt_lift (W := 𝒜.W) hS₀ (fun v => (v : G ⧸ Subgroup.closure (T : Set G)) = H) π (sgnOf 𝒜 Ap π) J
      ((conY (S₁ ∪ Ss) 𝒜.W).edgeFinset.filter fun e =>
        ∀ v ∈ e, (v : G ⧸ Subgroup.closure (T : Set G)) = H)
      (fun x y => by
        rw [mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, conY_adj]
        simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq, and_assoc])]
    exact congrArg (fun n : ℕ => (n : ℝ)) (congrArg Finset.card (filter_congr fun pq _ => by
      simp only [MonoidHom.coe_fst]))
  · -- the ordinary contraction
    intro _ I hIne hIuniv
    obtain ⟨i, hi⟩ := hIne
    obtain ⟨j, hj⟩ : ∃ j, j ∉ I := by
      by_contra h
      push Not at h
      exact hIuniv (eq_univ_iff_forall.2 h)
    have hfib1 : ∀ y : G, (univ.filter fun p : G => (MonoidHom.id G) p = y).card ≤ 1 := by
      intro y
      refine card_le_one.2 fun a ha b hb => ?_
      rw [mem_filter] at ha hb
      exact ha.2.trans hb.2.symm
    have key := generic_global (Γ := G) hgood hπ hTS hS₀ rfl hSsT (MonoidHom.id G) id
      (fun _ => rfl) (fun _ => rfl) (fun _ => false) (fun _ _ => false) (fun _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (c₂ * L) hβ h62 (I ×ˢ univ) 1 hfib1 b₀ hb₀V (hb₀T 1 (by norm_num))
      (T.card / 4)
      (fun Zs hZs hne hne' => ord_coset_bound hgood hS₀ hS₁0 hS₁top hres Zs hZs hne hne')
      ⟨i, false, mem_product.2 ⟨hi, mem_univ _⟩, fun y _ => ⟨y, rfl, rfl⟩⟩
      ⟨j, false, fun h => hj (mem_product.1 h).1, fun y _ => ⟨y, rfl, rfl⟩⟩
    refine le_of_le_of_eq (hfinal _ _ (by linarith) key) ?_
    rw [partCross_eq_card π I _ hloop]
    exact congrArg (fun n : ℕ => (n : ℝ)) (congrArg Finset.card (filter_congr fun pq _ => by
      simp only [image_id, MonoidHom.id_apply, mem_product, mem_univ, and_true,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, conY_adj, and_assoc]))

end Connector

end Lovasz
