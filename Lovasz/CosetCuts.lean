/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 6.2: coset cuts

DAG node `L6.2` of `docs/BLUEPRINT.md`.
-/

universe u

namespace Lovasz

open Finset

/-- **Lemma 6.2 (Coset cuts).** In a connected Cayley graph on `G`, every nontrivial cut whose
shore `Z` is a union of left `U`-cosets has at least `|U|/2` physical edges. (Physical edges
across the cut are counted as ordered pairs `(x, y)` with `x ∈ Z`, `y ∉ Z`.) -/
theorem coset_cut {G : Type u} [Group G] [Fintype G] [DecidableEq G] (S : Finset G)
    (hS : IsConnectionSet S) (hconn : (cayleyGraph S).Connected) (U : Subgroup G)
    (Z : Finset G) (hZ : ∀ x ∈ Z, ∀ y ∈ U, x * y ∈ Z) (hne : Z.Nonempty) (hne' : Z ≠ univ) :
    (Nat.card U : ℝ) / 2 ≤
      ((Z ×ˢ (univ \ Z)).filter fun p => (cayleyGraph S).Adj p.1 p.2).card := by
  set X := cayleyGraph S with hX
  set C := ((Z ×ˢ (univ \ Z)).filter fun p => X.Adj p.1 p.2) with hC
  suffices h : Nat.card U ≤ 2 * C.card by
    have : (Nat.card U : ℝ) ≤ 2 * C.card := by exact_mod_cast h
    linarith
  classical
  -- the quotient graph on left cosets
  let Q : SimpleGraph (G ⧸ U) := SimpleGraph.fromRel
    (fun p q => ∃ a b : G, X.Adj a b ∧ (a : G ⧸ U) = p ∧ (b : G ⧸ U) = q)
  have hQconn : Q.Connected := by
    have key : ∀ a b : G, X.Reachable a b → Q.Reachable (a : G ⧸ U) b := by
      intro a b ⟨w⟩
      induction w with
      | nil => rfl
      | @cons u v w' h w ih =>
        refine SimpleGraph.Reachable.trans ?_ ih
        by_cases heq : (u : G ⧸ U) = v
        · rw [heq]
        · exact SimpleGraph.Adj.reachable
            (by rw [SimpleGraph.fromRel_adj]; exact ⟨heq, Or.inl ⟨u, v, h, rfl, rfl⟩⟩)
    have : Nonempty (G ⧸ U) := ⟨((1 : G) : G ⧸ U)⟩
    refine SimpleGraph.Connected.mk (fun p q => ?_)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    exact key a b (hconn.preconnected a b)
  obtain ⟨T, hTQ, hT⟩ := hQconn.exists_isTree_le
  -- physical representatives of the tree edges
  have hrep : ∀ e : Sym2 (G ⧸ U), ∃ ab : G × G, e ∈ T.edgeSet →
      X.Adj ab.1 ab.2 ∧ s((ab.1 : G ⧸ U), (ab.2 : G ⧸ U)) = e := by
    intro e
    by_cases he : e ∈ T.edgeSet
    · induction e using Sym2.ind with
      | h p q =>
        have hpq : Q.Adj p q := hTQ (by simpa using he)
        rw [SimpleGraph.fromRel_adj] at hpq
        obtain ⟨_, ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩⟩ := hpq
        · exact ⟨(a, b), fun _ => ⟨hab, rfl⟩⟩
        · exact ⟨(a, b), fun _ => ⟨hab, Sym2.eq_swap⟩⟩
    · exact ⟨(1, 1), fun h => absurd h he⟩
  choose rep hrep using hrep
  set F := T.edgeFinset with hF
  have hFcard : F.card + 1 = Fintype.card (G ⧸ U) := hT.card_edgeFinset
  let cross : Sym2 (G ⧸ U) → G → Prop := fun e h =>
    (h * (rep e).1 ∈ Z ∧ h * (rep e).2 ∉ Z) ∨ (h * (rep e).2 ∈ Z ∧ h * (rep e).1 ∉ Z)
  -- every translate of the representative tree crosses the cut
  have hcover : ∀ h : G, ∃ e ∈ F, cross e h := by
    intro h
    let A : Set (G ⧸ U) := {p | ∃ g : G, (g : G ⧸ U) = p ∧ h * g ∈ Z}
    have hA : ∀ g : G, (g : G ⧸ U) ∈ A ↔ h * g ∈ Z := by
      intro g
      constructor
      · rintro ⟨g', hg', hZg'⟩
        rw [QuotientGroup.eq] at hg'
        have := hZ _ hZg' _ hg'
        simpa [mul_assoc] using this
      · intro hg; exact ⟨g, rfl, hg⟩
    obtain ⟨z, hz⟩ := hne
    obtain ⟨w, hw⟩ : ∃ w, w ∉ Z := by
      by_contra hcon
      exact hne' (Finset.eq_univ_iff_forall.mpr fun x => not_not.1 fun hx => hcon ⟨x, hx⟩)
    obtain ⟨p⟩ := hT.connected.preconnected ((h⁻¹ * z : G) : G ⧸ U) ((h⁻¹ * w : G) : G ⧸ U)
    obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart A ((hA _).2 (by simpa using hz))
      (fun hc => hw (by simpa using (hA _).1 hc))
    have hdT : d.edge ∈ T.edgeSet := d.edge_mem
    obtain ⟨-, heq⟩ := hrep d.edge hdT
    refine ⟨d.edge, by simp [hF], ?_⟩
    rw [SimpleGraph.Dart.edge, Sym2.eq_iff] at heq
    rcases heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · left
      exact ⟨(hA _).1 (e1 ▸ hd1), fun hc => hd2 (e2 ▸ (hA _).2 hc)⟩
    · right
      exact ⟨(hA _).1 (e2 ▸ hd1), fun hc => hd2 (e1 ▸ (hA _).2 hc)⟩
  -- each representative edge crosses the cut in at most `2 |C|` translates
  have hle1 : ∀ e ∈ F, ((univ : Finset G).filter (cross e)).card ≤ 2 * C.card := by
    intro e he
    obtain ⟨hadj, -⟩ := hrep e (by simpa [hF] using he)
    have h1 : ((univ : Finset G).filter
        (fun h => h * (rep e).1 ∈ Z ∧ h * (rep e).2 ∉ Z)).card ≤ C.card := by
      apply Finset.card_le_card_of_injOn (fun h => (h * (rep e).1, h * (rep e).2))
      · intro h hh
        have hh' := (Finset.mem_filter.1 (Finset.mem_coe.1 hh)).2
        exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_product.2
          ⟨hh'.1, Finset.mem_sdiff.2 ⟨mem_univ _, hh'.2⟩⟩,
          SimpleGraph.mulCayley_adj_mul_iff_right.2 hadj⟩)
      · intro h _ h' _ hhh
        simpa using congrArg Prod.fst hhh
    have h2 : ((univ : Finset G).filter
        (fun h => h * (rep e).2 ∈ Z ∧ h * (rep e).1 ∉ Z)).card ≤ C.card := by
      apply Finset.card_le_card_of_injOn (fun h => (h * (rep e).2, h * (rep e).1))
      · intro h hh
        have hh' := (Finset.mem_filter.1 (Finset.mem_coe.1 hh)).2
        exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_product.2
          ⟨hh'.1, Finset.mem_sdiff.2 ⟨mem_univ _, hh'.2⟩⟩,
          SimpleGraph.mulCayley_adj_mul_iff_right.2 hadj.symm⟩)
      · intro h _ h' _ hhh
        simpa using congrArg Prod.fst hhh
    calc ((univ : Finset G).filter (cross e)).card
        ≤ (((univ : Finset G).filter
            (fun h => h * (rep e).1 ∈ Z ∧ h * (rep e).2 ∉ Z)) ∪
          ((univ : Finset G).filter
            (fun h => h * (rep e).2 ∈ Z ∧ h * (rep e).1 ∉ Z))).card := by
          rw [← Finset.filter_or]
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ 2 * C.card := by omega
  have hmain : Fintype.card G ≤ F.card * (2 * C.card) := by
    calc Fintype.card G = (univ : Finset G).card := rfl
      _ ≤ (F.biUnion fun e => (univ : Finset G).filter (cross e)).card := by
          apply Finset.card_le_card
          intro h _
          obtain ⟨e, he, hc⟩ := hcover h
          exact Finset.mem_biUnion.2 ⟨e, he, by simp [hc]⟩
      _ ≤ ∑ e ∈ F, ((univ : Finset G).filter (cross e)).card := Finset.card_biUnion_le
      _ ≤ ∑ e ∈ F, 2 * C.card := Finset.sum_le_sum hle1
      _ = F.card * (2 * C.card) := by rw [Finset.sum_const, smul_eq_mul]
  have hidx : Nat.card U * U.index = Fintype.card G := by
    rw [Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  have hidx2 : U.index = Fintype.card (G ⧸ U) := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  rw [hidx2, ← hFcard] at hidx
  refine Nat.le_of_not_lt fun hcon => ?_
  nlinarith

end Lovasz
