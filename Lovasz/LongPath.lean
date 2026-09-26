/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent)
-/
import Lovasz.GapCut

/-!
# Long paths from the spectral gap (Section 3.2, before Section 3.3)

DAG node `L3.dfs` of `docs/BLUEPRINT.md`.

We model depth-first search by its invariant: a completed set `S`, an unexplored set `T` with
no edges between `S` and `T`, and the stack (all remaining vertices) forming a path. Each DFS
step either pushes an unexplored vertex or completes the top of the stack, so `|T| - |S|`
drops by one; hence some state has `|S| = |T|`.
-/

universe u

namespace Lovasz

open Finset

section DFS

variable {V : Type*} (G : SimpleGraph V)

/-- A depth-first-search state: the completed set `S` and the unexplored set `T` are disjoint
with no edges between them, and the remaining vertices (the stack) are empty or form a path. -/
def DFSState (S T : Finset V) : Prop :=
  Disjoint S T ∧ (∀ x ∈ S, ∀ y ∈ T, ¬ G.Adj x y) ∧
    ((∀ v, v ∈ S ∨ v ∈ T) ∨
      ∃ x y, ∃ p : G.Walk x y, p.IsPath ∧ ∀ v, v ∈ p.support ↔ v ∉ S ∧ v ∉ T)

lemma dfsState_init [Fintype V] : DFSState G ∅ univ :=
  ⟨disjoint_empty_left _, by simp, Or.inl fun v => Or.inr (mem_univ v)⟩

/-- One DFS step: from a state with unexplored vertices, either push an unexplored vertex or
complete the top of the stack. -/
lemma dfsState_step [DecidableEq V] (S T : Finset V) (h : DFSState G S T) (hT : T.Nonempty) :
    ∃ S' T', DFSState G S' T' ∧ S.card + T'.card + 1 = S'.card + T.card := by
  obtain ⟨hdisj, hnoadj, hstack⟩ := h
  rcases hstack with hcov | ⟨x, y, p, hp, hsupp⟩
  · obtain ⟨u, hu⟩ := hT
    have huS : u ∉ S := fun hS => disjoint_left.mp hdisj hS hu
    refine ⟨S, T.erase u, ⟨disjoint_of_subset_right (erase_subset u T) hdisj,
      fun x hx y hy => hnoadj x hx y (mem_of_mem_erase hy),
      Or.inr ⟨u, u, SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, ?_⟩⟩, ?_⟩
    · intro v
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton, mem_erase]
      constructor
      · rintro rfl
        exact ⟨huS, fun h => h.1 rfl⟩
      · rintro ⟨hS, hT'⟩
        by_contra hne
        rcases hcov v with h | h
        · exact hS h
        · exact hT' ⟨hne, h⟩
    · rw [card_erase_of_mem hu]
      have := card_pos.mpr ⟨u, hu⟩
      omega
  · by_cases hext : ∃ u ∈ T, G.Adj x u
    · obtain ⟨u, hu, hxu⟩ := hext
      have huS : u ∉ S := fun hS => disjoint_left.mp hdisj hS hu
      have hup : u ∉ p.support := fun hm => ((hsupp u).mp hm).2 hu
      refine ⟨S, T.erase u, ⟨disjoint_of_subset_right (erase_subset u T) hdisj,
        fun x hx y hy => hnoadj x hx y (mem_of_mem_erase hy),
        Or.inr ⟨u, y, SimpleGraph.Walk.cons hxu.symm p, hp.cons hup, ?_⟩⟩, ?_⟩
      · intro v
        rw [SimpleGraph.Walk.support_cons, List.mem_cons, hsupp v, mem_erase]
        constructor
        · rintro (rfl | ⟨hS, hT'⟩)
          · exact ⟨huS, fun h => h.1 rfl⟩
          · exact ⟨hS, fun h => hT' h.2⟩
        · rintro ⟨hS, hT'⟩
          by_cases hvu : v = u
          · exact Or.inl hvu
          · exact Or.inr ⟨hS, fun h => hT' ⟨hvu, h⟩⟩
      · rw [card_erase_of_mem hu]
        have := card_pos.mpr ⟨u, hu⟩
        omega
    · push Not at hext
      have hxS : x ∉ S := ((hsupp x).mp p.start_mem_support).1
      have hxT : x ∉ T := ((hsupp x).mp p.start_mem_support).2
      refine ⟨insert x S, T, ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [disjoint_insert_left]
        exact ⟨hxT, hdisj⟩
      · intro v hv w hw
        rcases mem_insert.mp hv with rfl | hv
        · exact hext w hw
        · exact hnoadj v hv w hw
      · cases p with
        | nil =>
          left
          intro v
          by_cases hvx : v = x
          · exact Or.inl (mem_insert.mpr (Or.inl hvx))
          · by_contra hcon
            push Not at hcon
            have := (hsupp v).mpr ⟨fun h => hcon.1 (mem_insert_of_mem h), hcon.2⟩
            simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at this
            exact hvx this
        | cons hxy q =>
          right
          rw [SimpleGraph.Walk.cons_isPath_iff] at hp
          refine ⟨_, _, q, hp.1, ?_⟩
          intro v
          have hv := hsupp v
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
          rw [mem_insert, not_or]
          constructor
          · intro hvq
            have hvx : v ≠ x := fun h => hp.2 (h ▸ hvq)
            exact ⟨⟨hvx, (hv.mp (Or.inr hvq)).1⟩, (hv.mp (Or.inr hvq)).2⟩
          · rintro ⟨⟨hvx, hS⟩, hT'⟩
            rcases hv.mpr ⟨hS, hT'⟩ with h | h
            · exact absurd h hvx
            · exact h
      · rw [card_insert_of_notMem hxS]
        omega

/-- DFS reaches a balanced state `|S| = |T|`. -/
lemma dfsState_balanced [DecidableEq V] : ∀ (k : ℕ) (S T : Finset V), T.card = S.card + k → DFSState G S T →
    ∃ S' T', DFSState G S' T' ∧ S'.card = T'.card := by
  intro k
  induction k with
  | zero => exact fun S T hk h => ⟨S, T, h, by omega⟩
  | succ k ih =>
    intro S T hk h
    have hT : T.Nonempty := by
      rw [← card_pos]
      omega
    obtain ⟨S', T', h', hc⟩ := dfsState_step G S T h hT
    exact ih S' T' (by omega) h'

end DFS

/-- **Depth-first-search path.** A weighted graph on `M` vertices with degrees in `[aD, bD]`
and normalized gap `σ ∈ (0, 1]` has a path with at least `c σ M` vertices. -/
theorem exists_long_path (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V] (H : WGraph V) (D σ : ℝ),
        0 < D → H.DegBetween (a * D) (b * D) → H.HasGap σ → 0 < σ → σ ≤ 1 →
        ∃ x y, ∃ p : H.supp.Walk x y, p.IsPath ∧ c * σ * Fintype.card V ≤ p.support.length := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < a ^ 2 / (6 * b ^ 2) := div_pos (pow_pos ha 2) (by positivity)
  refine ⟨a ^ 2 / (6 * b ^ 2), hc, ?_⟩
  intro V _ _ _ H D σ hD hdeg hσ hσ0 hσ1
  obtain ⟨S, T, ⟨hdisj, hnoadj, hstack⟩, hST⟩ :=
    dfsState_balanced H.supp (Fintype.card V) ∅ univ (by simp) (dfsState_init H.supp)
  set P : Finset V := univ \ (S ∪ T) with hP
  have hPcard : P.card + 2 * S.card = Fintype.card V := by
    have h1 : P.card + (S ∪ T).card = Fintype.card V := by
      rw [hP, card_sdiff_add_card_eq_card (subset_univ _), card_univ]
    rw [card_union_of_disjoint hdisj] at h1
    omega
  have hScompl : (univ \ S).card + S.card = Fintype.card V := by
    rw [card_sdiff_add_card_eq_card (subset_univ _), card_univ]
  have hw0 : ∀ x ∈ S, ∀ y ∈ T, H.w x y = 0 := fun x hx y hy =>
    le_antisymm (not_lt.mp (hnoadj x hx y hy)) (H.nonneg x y)
  have hup : H.edgeWeight S (univ \ S) ≤ b * D * P.card := by
    unfold WGraph.edgeWeight
    calc ∑ x ∈ S, ∑ y ∈ univ \ S, H.w x y = ∑ x ∈ S, ∑ y ∈ P, H.w x y := by
          refine sum_congr rfl fun x hx => (sum_subset ?_ ?_).symm
          · intro y hy
            simp only [hP, mem_sdiff, mem_univ, mem_union, true_and, not_or] at hy ⊢
            exact hy.1
          · intro y hy hyP
            have hyT : y ∈ T := by
              simp only [hP, mem_sdiff, mem_univ, mem_union, true_and, not_or] at hy hyP
              tauto
            exact hw0 x hx y hyT
      _ = ∑ y ∈ P, ∑ x ∈ S, H.w y x := by
          rw [sum_comm]
          exact sum_congr rfl fun y _ => sum_congr rfl fun x _ => H.symm x y
      _ ≤ ∑ y ∈ P, H.deg y := sum_le_sum fun y _ =>
          sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun x _ _ => H.nonneg y x)
      _ ≤ ∑ y ∈ P, b * D := sum_le_sum fun y _ => (hdeg y).2
      _ = b * D * P.card := by rw [sum_const, nsmul_eq_mul, mul_comm]
  have hcut := WGraph.isCutDense_of_hasGap H hσ hσ0.le ha hD hdeg S
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hmain : a ^ 2 / (6 * b ^ 2) * σ * Fintype.card V ≤ P.card := by
    have hq : (P.card : ℝ) + 2 * S.card = Fintype.card V := by exact_mod_cast hPcard
    have hsc : ((univ \ S).card : ℝ) = Fintype.card V - S.card := by
      rw [← hScompl]; push_cast; ring
    rw [hsc] at hcut
    set n : ℝ := ((Fintype.card V : ℕ) : ℝ)
    set s : ℝ := ((S.card : ℕ) : ℝ)
    set q : ℝ := ((P.card : ℕ) : ℝ)
    have hs0 : 0 ≤ s := Nat.cast_nonneg _
    have hq0 : 0 ≤ q := Nat.cast_nonneg _
    have h2 : σ * a ^ 2 * s * (n - s) ≤ b ^ 2 * n * q := by
      have h3 : σ * a ^ 2 * s * (n - s) * D / (b * n) ≤ b * D * q := by
        calc σ * a ^ 2 * s * (n - s) * D / (b * n) = σ * a ^ 2 * D / (b * n) * s * (n - s) := by
              ring
          _ ≤ _ := hcut
          _ ≤ _ := hup
      rw [div_le_iff₀ (by positivity)] at h3
      have h4 : σ * a ^ 2 * s * (n - s) * D ≤ b ^ 2 * n * q * D :=
        calc _ ≤ b * D * q * (b * n) := h3
          _ = _ := by ring
      exact le_of_mul_le_mul_right h4 hD
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have ha2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
    rcases le_or_gt n (3 * q) with h | h
    · calc a ^ 2 * σ * n ≤ b ^ 2 * 1 * n := by
            apply mul_le_mul_of_nonneg_right _ hn.le
            exact mul_le_mul ha2 hσ1 hσ0.le (sq_nonneg b)
        _ ≤ q * (6 * b ^ 2) := by nlinarith [sq_nonneg b]
    · have h5 : n / 3 ≤ s := by linarith
      have h6 : n / 2 ≤ n - s := by linarith
      have h7 : σ * a ^ 2 * (n / 3) * (n / 2) ≤ σ * a ^ 2 * s * (n - s) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h5 (by positivity)) h6 (by positivity)
          (by positivity)
      have h8 : n * (a ^ 2 * σ * n) ≤ n * (q * (6 * b ^ 2)) := by linarith
      exact le_of_mul_le_mul_left h8 hn
  rcases hstack with hcov | ⟨x, y, p, hp, hsupp⟩
  · exfalso
    have hP0 : P = ∅ := by
      ext v
      simp only [hP, mem_sdiff, mem_univ, mem_union, true_and, not_or, notMem_empty,
        iff_false, not_and, not_not]
      intro hvS
      exact (hcov v).resolve_left hvS
    rw [hP0, card_empty, Nat.cast_zero] at hmain
    have : 0 < a ^ 2 / (6 * b ^ 2) * σ * Fintype.card V := mul_pos (mul_pos hc hσ0) hn
    linarith
  · refine ⟨x, y, p, hp, ?_⟩
    have hlen : p.support.length = P.card := by
      rw [← List.toFinset_card_of_nodup hp.support_nodup]
      congr 1
      ext v
      simp only [List.mem_toFinset, hsupp v, hP, mem_sdiff, mem_univ, mem_union, true_and,
        not_or]
    rw [hlen]
    exact hmain

end Lovasz
