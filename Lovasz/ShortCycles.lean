/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 3.7: many disjoint short cycles

DAG node `L3.7` of `docs/BLUEPRINT.md`.

The proof follows the paper: a packing of vertex-disjoint short cycles of maximum size covers
a constant fraction of the vertices, since otherwise the uncovered part contains a dense core
of large minimum degree, which contains a short cycle by the Moore bound.

* `ShortCycles.exists_cycle_of_two_paths`: two distinct paths with the same ends span a cycle
  of length at most their total length.
* `ShortCycles.exists_short_cycle`: the Moore bound (a graph of minimum degree `k + 1` on fewer
  than `k ^ r` vertices has a cycle of length at most `2r`), via counting paths.
* `ShortCycles.exists_dense_core`: a set of large average degree contains a nonempty subset of
  large minimum degree.
-/

universe u

namespace Lovasz

open Finset SimpleGraph

namespace ShortCycles

variable {V : Type*}

/-- Two distinct paths with the same ends span a cycle of at most their total length. -/
theorem exists_cycle_of_two_paths [DecidableEq V] {G : SimpleGraph V} {x y : V}
    (p q : G.Walk x y) (hp : p.IsPath) (hq : q.IsPath) (hpq : p ≠ q) :
    ∃ z, ∃ c : G.Walk z z, c.IsCycle ∧ c.length ≤ p.length + q.length := by
  let K : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ (s(a, b) ∈ p.edges ∨ s(a, b) ∈ q.edges)
      symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
      loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩ }
  have hKG : K ≤ G := fun a b h => h.1
  have hpK : ∀ e ∈ p.edges, e ∈ K.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h a b => exact ⟨p.edges_subset_edgeSet he, Or.inl he⟩
  have hqK : ∀ e ∈ q.edges, e ∈ K.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h a b => exact ⟨q.edges_subset_edgeSet he, Or.inr he⟩
  have hK : ¬ K.IsAcyclic := by
    intro hac
    have h1 := (isAcyclic_iff_subsingleton_path.mp hac x y).elim
      ⟨p.transfer K hpK, hp.transfer hpK⟩ ⟨q.transfer K hqK, hq.transfer hqK⟩
    apply hpq
    apply Walk.ext_support
    have h2 := congrArg (fun r : K.Path x y => (r : K.Walk x y).support) h1
    simpa using h2
  simp only [IsAcyclic, not_forall, not_not] at hK
  obtain ⟨z, c, hc⟩ := hK
  refine ⟨z, c.mapLe hKG, hc.mapLe hKG, ?_⟩
  rw [Walk.length_mapLe]
  have h1 : c.edges.toFinset.card = c.length := by
    rw [List.toFinset_card_of_nodup hc.edges_nodup, Walk.length_edges]
  have h2 : c.edges.toFinset ⊆ (p.edges ++ q.edges).toFinset := by
    intro e he
    rw [List.mem_toFinset] at he ⊢
    have h3 := c.edges_subset_edgeSet he
    induction e using Sym2.ind with
    | h a b => exact List.mem_append.mpr ((SimpleGraph.mem_edgeSet K).mp h3).2
  calc c.length = c.edges.toFinset.card := h1.symm
    _ ≤ (p.edges ++ q.edges).toFinset.card := card_le_card h2
    _ ≤ (p.edges ++ q.edges).length := List.toFinset_card_le _
    _ = p.length + q.length := by simp

/-- The start of a path does not lie on the part of the path after another vertex. -/
theorem start_notMem_dropUntil [DecidableEq V] {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (hp : p.IsPath) (hw : w ∈ p.support) (hwu : w ≠ u) :
    u ∉ (p.dropUntil w hw).support := by
  intro hu
  have hnd := hp.support_nodup
  rw [← p.take_spec hw, Walk.support_append] at hnd
  have hu' : u ∈ (p.dropUntil w hw).support.tail := by
    rw [← Walk.cons_tail_support] at hu
    rcases List.mem_cons.mp hu with h | h
    · exact absurd h.symm hwu
    · exact h
  exact List.disjoint_of_nodup_append hnd (p.takeUntil w hw).start_mem_support hu'

/-- **Moore bound.** If every vertex that can reach `v` has degree at least `k + 1` and there
are fewer than `k ^ r` vertices, then there is a cycle of length at most `2r`. -/
theorem exists_short_cycle [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (k r : ℕ)
    (hdeg : ∀ u, G.Reachable u v → k + 1 ≤ (univ.filter (G.Adj u)).card)
    (hcard : Fintype.card V < k ^ r) :
    ∃ z, ∃ c : G.Walk z z, c.IsCycle ∧ c.length ≤ 2 * r := by
  by_contra hno
  push Not at hno
  let P : ℕ → Finset (Σ u, G.Walk u v) := fun n =>
    (univ : Finset V).sigma fun u => (G.finsetWalkLength n u v).filter fun p => p.IsPath
  have memP : ∀ n (a : Σ u, G.Walk u v), a ∈ P n ↔ a.2.length = n ∧ a.2.IsPath := by
    intro n a
    simp [P, SimpleGraph.mem_finsetWalkLength_iff]
  -- at most one neighbour of the start of a short path lies on the path
  have key : ∀ n, n < r → ∀ u (p : G.Walk u v), p.IsPath → p.length = n →
      ((univ.filter (G.Adj u)) ∩ p.support.toFinset).card ≤ 1 := by
    intro n hn u p hp hlen
    by_contra hlt
    push Not at hlt
    obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := Finset.one_lt_card.mp hlt
    simp only [Finset.mem_inter, mem_filter, mem_univ, true_and, List.mem_toFinset] at hw₁ hw₂
    let q₁ : G.Walk u v := Walk.cons hw₁.1 (p.dropUntil w₁ hw₁.2)
    let q₂ : G.Walk u v := Walk.cons hw₂.1 (p.dropUntil w₂ hw₂.2)
    have hq₁ : q₁.IsPath := by
      rw [Walk.cons_isPath_iff]
      exact ⟨hp.dropUntil _, start_notMem_dropUntil p hp _ (G.ne_of_adj hw₁.1).symm⟩
    have hq₂ : q₂.IsPath := by
      rw [Walk.cons_isPath_iff]
      exact ⟨hp.dropUntil _, start_notMem_dropUntil p hp _ (G.ne_of_adj hw₂.1).symm⟩
    have hne' : q₁ ≠ q₂ := by
      intro h
      simp only [q₁, q₂, Walk.cons.injEq] at h
      exact hne h.1
    obtain ⟨z, c, hc, hlc⟩ := exists_cycle_of_two_paths q₁ q₂ hq₁ hq₂ hne'
    have l₁ : q₁.length ≤ n + 1 := by
      simp only [q₁, Walk.length_cons]
      have := p.length_dropUntil_le_length hw₁.2
      omega
    have l₂ : q₂.length ≤ n + 1 := by
      simp only [q₂, Walk.length_cons]
      have := p.length_dropUntil_le_length hw₂.2
      omega
    have := hno z c hc
    omega
  have step : ∀ n, n < r → k * (P n).card ≤ (P (n + 1)).card := by
    intro n hn
    let T := (P n).sigma fun a => (univ.filter (G.Adj a.1)) \ a.2.support.toFinset
    have hT : k * (P n).card ≤ T.card := by
      calc k * (P n).card = ∑ _a ∈ P n, k := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ a ∈ P n, ((univ.filter (G.Adj a.1)) \ a.2.support.toFinset).card := by
          apply Finset.sum_le_sum
          intro a ha
          obtain ⟨hlen, hpath⟩ := (memP n a).mp ha
          have h1 := key n hn a.1 a.2 hpath hlen
          have h2 := hdeg a.1 a.2.reachable
          have h3 := Finset.card_sdiff_add_card_inter (univ.filter (G.Adj a.1))
            a.2.support.toFinset
          omega
        _ = T.card := (Finset.card_sigma _ _).symm
    let f : (Σ _ : (Σ u, G.Walk u v), V) → (Σ u, G.Walk u v) := fun b =>
      if h : G.Adj b.2 b.1.1 then ⟨b.2, Walk.cons h b.1.2⟩ else b.1
    have hmaps : Set.MapsTo f T (P (n + 1)) := by
      rintro ⟨⟨u, p⟩, w⟩ hb
      simp only [T, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_sdiff,
        mem_filter, mem_univ, true_and, List.mem_toFinset] at hb
      obtain ⟨ha, hadj, hw⟩ := hb
      obtain ⟨hlen, hpath⟩ := (memP n _).mp ha
      have hadj' : G.Adj w u := hadj.symm
      simp only [f, hadj', ↓reduceDIte, Finset.mem_coe]
      rw [memP]
      exact ⟨by simp [hlen], by rw [Walk.cons_isPath_iff]; exact ⟨hpath, hw⟩⟩
    have hinj : Set.InjOn f T := by
      rintro ⟨⟨u, p⟩, w⟩ hb ⟨⟨u', p'⟩, w'⟩ hb' heq
      simp only [T, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_sdiff,
        mem_filter, mem_univ, true_and, List.mem_toFinset] at hb hb'
      have h1 : G.Adj w u := hb.2.1.symm
      have h2 : G.Adj w' u' := hb'.2.1.symm
      simp only [f, h1, h2, ↓reduceDIte] at heq
      obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp heq
      have h' := eq_of_heq h
      simp only [Walk.cons.injEq] at h'
      obtain ⟨rfl, h''⟩ := h'
      cases h''
      rfl
    exact hT.trans (Finset.card_le_card_of_injOn f hmaps hinj)
  have lower : ∀ n, n ≤ r → k ^ n ≤ (P n).card := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [pow_zero, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
      exact ⟨⟨v, Walk.nil⟩, (memP 0 _).mpr ⟨rfl, Walk.IsPath.nil⟩⟩
    | succ n ih =>
      intro hn
      calc k ^ (n + 1) = k * k ^ n := by ring
        _ ≤ k * (P n).card := Nat.mul_le_mul_left _ (ih (by omega))
        _ ≤ (P (n + 1)).card := step n (by omega)
  have upper : (P r).card ≤ Fintype.card V := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn Sigma.fst (fun _ _ => Finset.mem_coe.mpr (mem_univ _)) ?_
    rintro ⟨u, p⟩ ha ⟨u', p'⟩ hb (hfst : u = u')
    subst hfst
    obtain ⟨hl, hp⟩ := (memP r _).mp ha
    obtain ⟨hl', hp'⟩ := (memP r _).mp hb
    by_contra hne
    have hne' : p ≠ p' := fun h => hne (by rw [h])
    obtain ⟨z, c, hc, hlc⟩ := exists_cycle_of_two_paths p p' hp hp' hne'
    have := hno z c hc
    simp only at hl hl'
    omega
  have := lower r le_rfl
  omega

/-- A set `S` of large average degree (with respect to the symmetric weights `A`) contains a
nonempty subset of large minimum degree. -/
theorem exists_dense_core [DecidableEq V] (A : V → V → ℝ) (hsymm : ∀ x y, A x y = A y x)
    (hdiag : ∀ x, A x x = 0) (S : Finset V) (t : ℝ)
    (h : 2 * t * S.card < ∑ x ∈ S, ∑ y ∈ S, A x y) :
    ∃ T ⊆ S, T.Nonempty ∧ ∀ x ∈ T, t ≤ ∑ y ∈ T, A x y := by
  let Ψ : Finset V → ℝ := fun T => ∑ x ∈ T, ∑ y ∈ T, A x y - 2 * t * T.card
  obtain ⟨T, hT, hmax⟩ := S.powerset.exists_max_image Ψ ⟨S, mem_powerset_self S⟩
  rw [mem_powerset] at hT
  have hpos : 0 < Ψ T :=
    lt_of_lt_of_le (by simp only [Ψ]; linarith) (hmax S (mem_powerset_self S))
  refine ⟨T, hT, ?_, ?_⟩
  · rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp [Ψ] at hpos
  · intro x hx
    have hle := hmax (T.erase x) (mem_powerset.mpr ((erase_subset x T).trans hT))
    have e1 : ∑ u ∈ T, ∑ y ∈ T, A u y =
        ∑ y ∈ T, A x y + ∑ u ∈ T.erase x, ∑ y ∈ T, A u y := (add_sum_erase T _ hx).symm
    have e2 : ∀ u, ∑ y ∈ T, A u y = A u x + ∑ y ∈ T.erase x, A u y :=
      fun u => (add_sum_erase T _ hx).symm
    have e3 : ∑ u ∈ T.erase x, A u x = ∑ y ∈ T, A x y := by
      have := sum_erase_add T (fun u => A u x) hx
      rw [hdiag x, add_zero] at this
      rw [this]
      exact sum_congr rfl fun u _ => hsymm u x
    have e4 : ∑ u ∈ T.erase x, ∑ y ∈ T, A u y =
        ∑ u ∈ T.erase x, A u x + ∑ u ∈ T.erase x, ∑ y ∈ T.erase x, A u y := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun u _ => e2 u
    have e5 : ((T.erase x).card : ℝ) + 1 = T.card := by
      exact_mod_cast card_erase_add_one hx
    have e6 : t * T.card = t * (T.erase x).card + t := by rw [← e5]; ring
    simp only [Ψ] at hle
    linarith

/-- A closed walk of positive length has at most as many distinct vertices as its length. -/
theorem card_support_toFinset_le [DecidableEq V] {G : SimpleGraph V} {x : V} (p : G.Walk x x)
    (hp : ¬ p.Nil) : p.support.toFinset.card ≤ p.length := by
  have hx := p.end_mem_tail_support hp
  rw [← p.cons_tail_support, List.toFinset_cons,
    Finset.insert_eq_of_mem (List.mem_toFinset.mpr hx)]
  calc p.support.tail.toFinset.card ≤ p.support.tail.length := List.toFinset_card_le _
    _ = p.length := by simp [List.length_tail, Walk.length_support]

/-- If every edge of `G` lies inside `T`, every vertex of a walk of positive length lies in `T`. -/
theorem mem_of_mem_support {G : SimpleGraph V} {T : Set V}
    (hT : ∀ x y, G.Adj x y → x ∈ T ∧ y ∈ T) :
    ∀ {x y : V} (p : G.Walk x y), 0 < p.length → ∀ z ∈ p.support, z ∈ T
  | _, _, .nil, h, _, _ => by simp at h
  | _, _, .cons h q, _, z, hz => by
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact (hT _ _ h).1
    · cases q with
      | nil =>
        simp only [Walk.support_nil, List.mem_singleton] at hz
        subst hz
        exact (hT _ _ h).2
      | cons h' q' => exact mem_of_mem_support hT (.cons h' q') (by simp) z hz

end ShortCycles

/-- **Lemma 3.7.** A bipartite weighted graph on `M` vertices with weights in `[ω, 1]` and
degrees comparable to `D_C ≥ C` (in `[a D_C, b D_C]`) contains at least `cM/g` vertex-disjoint
cycles of length at most `g`, provided `g ≥ C log (2M) / log (2 + D_C)`. -/
theorem many_short_cycles (ω a b : ℝ) (hω : 0 < ω) (ha : 0 < a) (hab : a ≤ b) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (col : V → Bool) (DC g : ℝ),
        H.IsBipartiteWith col → H.WeightsIn ω → H.DegBetween (a * DC) (b * DC) → C ≤ DC →
        C * Real.log (2 * Fintype.card V) / Real.log (2 + DC) ≤ g →
        ∃ Z : Finset (Finset V), c * Fintype.card V / g ≤ Z.card ∧
          (Z : Set (Finset V)).PairwiseDisjoint id ∧
          ∀ z ∈ Z, ∃ x, ∃ p : H.supp.Walk x x, p.IsCycle ∧ (p.length : ℝ) ≤ g ∧
            p.support.toFinset = z := by
  refine ⟨a * ω / (4 * b), 20 + 40 / a + 600 / a ^ 2,
    div_pos (mul_pos ha hω) (by linarith), by positivity, ?_⟩
  intro V _ _ H col DC g _hbip hW hdeg hC hg
  classical
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have ha' : a ≠ 0 := ha.ne'
  set C : ℝ := 20 + 40 / a + 600 / a ^ 2 with hCdef
  set M : ℕ := Fintype.card V with hM
  -- a packing of disjoint short cycles of maximum size
  let good : Finset (Finset V) → Prop := fun Z => (Z : Set (Finset V)).PairwiseDisjoint id ∧
    ∀ z ∈ Z, ∃ x, ∃ p : H.supp.Walk x x, p.IsCycle ∧ (p.length : ℝ) ≤ g ∧
      p.support.toFinset = z
  obtain ⟨Z, hZ, hmax⟩ := (univ.filter good).exists_max_image Finset.card
    ⟨∅, by simp [good]⟩
  rw [mem_filter] at hZ
  obtain ⟨-, hZdisj, hZcyc⟩ := hZ
  refine ⟨Z, ?_, hZdisj, hZcyc⟩
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · rw [hM0]; simp
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hMr1 : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
  -- the support indicator and support degrees
  let A : V → V → ℝ := fun x y => if 0 < H.w x y then 1 else 0
  have hAw : ∀ x y, ω * A x y ≤ H.w x y ∧ H.w x y ≤ A x y := by
    intro x y
    by_cases h : 0 < H.w x y
    · simp only [A, h, ↓reduceIte, mul_one]; exact hW x y h
    · simp only [A, h, ↓reduceIte, mul_zero]
      have := H.nonneg x y
      constructor <;> linarith [not_lt.mp h]
  have hAnn : ∀ x y, 0 ≤ A x y := fun x y => by simp only [A]; split_ifs <;> norm_num
  have hA1 : ∀ x y, A x y ≤ 1 := fun x y => by simp only [A]; split_ifs <;> norm_num
  have hAsymm : ∀ x y, A x y = A y x := fun x y => by simp only [A, H.symm x y]
  have hAdiag : ∀ x, A x x = 0 := fun x => by simp [A, H.loopless x]
  let d : V → ℝ := fun x => ∑ y, A x y
  have hdeg_eq : ∀ x, H.deg x = ∑ y, H.w x y := fun x => rfl
  have hd_lo : ∀ x, a * DC ≤ d x := fun x =>
    (hdeg x).1.trans ((hdeg_eq x).le.trans (sum_le_sum fun y _ => (hAw x y).2))
  have hd_hi : ∀ x, ω * d x ≤ b * DC := by
    intro x
    have : ω * d x ≤ H.deg x := by
      rw [hdeg_eq]
      simp only [d, Finset.mul_sum]
      exact sum_le_sum fun y _ => (hAw x y).1
    linarith [(hdeg x).2]
  have hd_M : ∀ x, d x ≤ M := by
    intro x
    calc d x ≤ ∑ _y : V, (1 : ℝ) := sum_le_sum fun y _ => hA1 x y
      _ = M := by simp [hM]
  -- constants
  have hCpos : 0 < C := by positivity
  have hDC : 0 < DC := lt_of_lt_of_le hCpos hC
  have haC : a * C = 20 * a + 40 + 600 / a := by rw [hCdef]; field_simp
  have haDC : 40 ≤ a * DC := by
    have : a * C ≤ a * DC := mul_le_mul_of_nonneg_left hC ha.le
    have : 0 ≤ 20 * a + 600 / a := by positivity
    linarith
  have ha2C : a ^ 2 * C = 20 * a ^ 2 + 40 * a + 600 := by rw [hCdef]; field_simp
  have ha2DC : 600 ≤ a ^ 2 * DC := by
    have : a ^ 2 * C ≤ a ^ 2 * DC := mul_le_mul_of_nonneg_left hC (by positivity)
    have : 0 ≤ 20 * a ^ 2 + 40 * a := by positivity
    linarith
  have hDC20 : 20 ≤ DC := by
    have : 20 ≤ C := by
      rw [hCdef]
      have : 0 ≤ 40 / a + 600 / a ^ 2 := by positivity
      linarith
    linarith
  obtain ⟨x₀⟩ : Nonempty V := Fintype.card_pos_iff.mp hMpos
  have haDCM : a * DC ≤ M := (hd_lo x₀).trans (hd_M x₀)
  set lam := Real.log (2 + DC) with hlam
  have hlam_pos : 0 < lam := Real.log_pos (by linarith)
  have hL2pos : 0 < Real.log (2 * M) := Real.log_pos (by linarith)
  have hgpos : 0 < g := lt_of_lt_of_le (by positivity) hg
  -- the vertices covered by the packing
  set U := Z.biUnion id with hU
  have hzcard : ∀ z ∈ Z, (z.card : ℝ) ≤ g := by
    intro z hz
    obtain ⟨x, p, hp, hpl, rfl⟩ := hZcyc z hz
    exact le_trans (by exact_mod_cast ShortCycles.card_support_toFinset_le p hp.not_nil) hpl
  have hUZ : (U.card : ℝ) ≤ Z.card * g := by
    calc (U.card : ℝ) ≤ ∑ z ∈ Z, (z.card : ℝ) := by
          have := Finset.card_biUnion_le (s := Z) (t := id)
          exact_mod_cast this
      _ ≤ ∑ _z ∈ Z, g := sum_le_sum hzcard
      _ = Z.card * g := by rw [sum_const, nsmul_eq_mul]
  have hcover : a * ω / (4 * b) * M ≤ U.card := by
    by_contra hlt
    push Not at hlt
    set S₀ := univ \ U with hS₀
    have hsplit : ∀ x, d x = ∑ y ∈ S₀, A x y + ∑ y ∈ U, A x y := fun x =>
      (sum_sdiff (subset_univ U)).symm
    have hcross : ∑ x ∈ S₀, ∑ y ∈ U, A x y ≤ ∑ y ∈ U, d y := by
      rw [sum_comm]
      refine sum_le_sum fun y _ => ?_
      calc ∑ x ∈ S₀, A x y = ∑ x ∈ S₀, A y x := sum_congr rfl fun x _ => hAsymm x y
        _ ≤ ∑ x, A y x :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => hAnn y x
    have hin : ∑ x ∈ S₀, ∑ y ∈ S₀, A x y =
        ∑ x, d x - ∑ x ∈ U, d x - ∑ x ∈ S₀, ∑ y ∈ U, A x y := by
      have e1 : ∀ x, ∑ y ∈ S₀, A x y = d x - ∑ y ∈ U, A x y := fun x => by
        rw [hsplit x]; ring
      rw [sum_congr rfl fun x _ => e1 x, sum_sub_distrib]
      have e2 := sum_sdiff (subset_univ U) (f := d)
      linarith
    have htot : M * (a * DC) ≤ ∑ x, d x := by
      calc (M : ℝ) * (a * DC) = ∑ _x : V, a * DC := by simp [hM]
        _ ≤ ∑ x, d x := sum_le_sum fun x _ => hd_lo x
    have hUd : ∑ x ∈ U, d x ≤ U.card * (b * DC / ω) := by
      calc ∑ x ∈ U, d x ≤ ∑ _x ∈ U, b * DC / ω := sum_le_sum fun x _ => by
            rw [le_div_iff₀ hω]; linarith [hd_hi x]
        _ = U.card * (b * DC / ω) := by rw [sum_const, nsmul_eq_mul]
    have hUb : (U.card : ℝ) * (b * DC / ω) < a * DC * M / 4 := by
      calc (U.card : ℝ) * (b * DC / ω) < a * ω / (4 * b) * M * (b * DC / ω) :=
            mul_lt_mul_of_pos_right hlt (by positivity)
        _ = a * DC * M / 4 := by field_simp
    have hdense : 2 * (a * DC / 8) * S₀.card < ∑ x ∈ S₀, ∑ y ∈ S₀, A x y := by
      have hS₀M : (S₀.card : ℝ) ≤ M := by exact_mod_cast card_le_univ S₀
      have : 2 * (a * DC / 8) * S₀.card ≤ 2 * (a * DC / 8) * M := by
        apply mul_le_mul_of_nonneg_left hS₀M; positivity
      have : 0 < a * DC * M := by positivity
      linarith
    obtain ⟨T, hTS, hTne, hTdeg⟩ :=
      ShortCycles.exists_dense_core A hAsymm hAdiag S₀ (a * DC / 8) hdense
    obtain ⟨v, hvT⟩ := hTne
    let GT : SimpleGraph V :=
      { Adj := fun x y => 0 < H.w x y ∧ x ∈ T ∧ y ∈ T
        symm := ⟨fun x y h => ⟨by rw [H.symm]; exact h.1, h.2.2, h.2.1⟩⟩
        loopless := ⟨fun x h => by simp [H.loopless] at h⟩ }
    have hGT : GT ≤ H.supp := fun x y h => h.1
    set t := a * DC / 8 with ht
    set k := ⌊t⌋₊ - 1 with hk
    set r := ⌊g / 2⌋₊ with hr
    have ht5 : (5 : ℝ) ≤ t := by rw [ht]; linarith
    have hfl5 : 5 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht5)
    have hk1 : k + 1 = ⌊t⌋₊ := by omega
    have hkt : t - 2 ≤ (k : ℝ) := by
      have h1 := Nat.lt_floor_add_one t
      have h2 : ((k + 1 : ℕ) : ℝ) = ⌊t⌋₊ := by rw [hk1]
      push_cast at h2
      linarith
    -- the minimum degree condition in the core
    have hdegT : ∀ u, GT.Reachable u v → k + 1 ≤ (univ.filter (GT.Adj u)).card := by
      intro u hu
      have huT : u ∈ T := by
        obtain ⟨p⟩ := hu
        cases p with
        | nil => exact hvT
        | cons h _ => exact h.2.1
      have hfil : univ.filter (GT.Adj u) = T.filter (fun y => 0 < H.w u y) := by
        ext y; simp [GT, huT]; tauto
      have hsum : ∑ y ∈ T, A u y = ((T.filter (fun y => 0 < H.w u y)).card : ℝ) := by
        simp only [A]; rw [Finset.sum_boole]
      rw [hk1, hfil]
      apply Nat.floor_le_of_le
      rw [← hsum]; exact hTdeg u huT
    -- the Moore bound applies
    have hcardk : Fintype.card V < k ^ r := by
      have hk_lo : a * DC / 16 ≤ (k : ℝ) := by rw [ht] at hkt; linarith
      have hkpos : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk_lo
      have hk2 : 2 + DC ≤ (k : ℝ) ^ 2 := by
        have h1 : (a * DC / 16) ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hk_lo 2
        have h2 : (a * DC / 16) ^ 2 = DC * (a ^ 2 * DC) / 256 := by ring
        have h3 : DC * 600 ≤ DC * (a ^ 2 * DC) := mul_le_mul_of_nonneg_left ha2DC hDC.le
        nlinarith
      have hlogk : lam ≤ 2 * Real.log k := by
        calc lam ≤ Real.log ((k : ℝ) ^ 2) := Real.log_le_log (by linarith) hk2
          _ = 2 * Real.log k := by rw [Real.log_pow]; norm_num
      have hr1 : g / 2 < r + 1 := Nat.lt_floor_add_one _
      have hgl : C * Real.log (2 * M) ≤ g * lam := by
        rwa [div_le_iff₀ hlam_pos] at hg
      have hlamM : lam ≤ Real.log M + Real.log (2 + 1 / a) := by
        rw [← Real.log_mul hMr.ne' (by positivity)]
        apply Real.log_le_log (by linarith)
        have : DC ≤ M / a := by rw [le_div_iff₀ ha]; linarith
        have : (M : ℝ) * (2 + 1 / a) = 2 * M + M / a := by ring
        linarith
      have hβ : Real.log (2 + 1 / a) < 2 + 1 / a := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 + 1 / a by positivity)
        linarith
      have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      have hlogM : 0 ≤ Real.log M := Real.log_nonneg hMr1
      have hL2 : Real.log (2 * M) = Real.log 2 + Real.log M :=
        Real.log_mul (by norm_num) hMr.ne'
      have hmain : Real.log M < r * Real.log k := by
        have h1 : C * Real.log (2 * M) / 2 - lam < r * lam := by
          have := mul_lt_mul_of_pos_right hr1 hlam_pos
          linarith
        have h2 : r * lam ≤ r * (2 * Real.log k) :=
          mul_le_mul_of_nonneg_left hlogk (Nat.cast_nonneg r)
        have h3 : Real.log M + lam / 2 ≤ C * Real.log (2 * M) / 4 := by
          have i0 : 0 < 1 / a := by positivity
          have i1 : 0 ≤ 40 / a * Real.log M := by positivity
          have i2 : 0 ≤ 600 / a ^ 2 * Real.log 2 := by positivity
          have i3 : 0 ≤ 600 / a ^ 2 * Real.log M := by positivity
          have i4 : 40 / a * (1 / 2) ≤ 40 / a * Real.log 2 :=
            mul_le_mul_of_nonneg_left hlog2.le (by positivity)
          rw [hL2, hCdef]
          have : 40 / a * (1 / 2) = 20 * (1 / a) := by ring
          linarith
        linarith
      have hpow : (M : ℝ) < (k : ℝ) ^ r := by
        rw [← Real.log_lt_log_iff hMr (by positivity), Real.log_pow]
        exact hmain
      exact_mod_cast hpow
    obtain ⟨x, c, hc, hcl⟩ := ShortCycles.exists_short_cycle GT v k r hdegT hcardk
    have hsuppT : ∀ y ∈ c.support, y ∈ T :=
      ShortCycles.mem_of_mem_support (G := GT) (T := (T : Set V)) (fun a b h => ⟨h.2.1, h.2.2⟩) c
        (by have := hc.three_le_length; omega)
    let c' : H.supp.Walk x x := c.mapLe hGT
    have hr2 : (2 * r : ℝ) ≤ g := by
      have := Nat.floor_le (show 0 ≤ g / 2 by positivity)
      linarith
    let z := c'.support.toFinset
    have hzT : ∀ y ∈ z, y ∈ T := by
      intro y hy
      simp only [z, c', Walk.support_mapLe_eq_support, List.mem_toFinset] at hy
      exact hsuppT y hy
    have hzU : ∀ y ∈ z, y ∉ U := by
      intro y hy
      have := hTS (hzT y hy)
      simp only [S₀, mem_sdiff] at this
      exact this.2
    have hxz : x ∈ z := by simp [z, c']
    have hznot : z ∉ Z := fun hz => hzU x hxz (mem_biUnion.mpr ⟨z, hz, hxz⟩)
    have hgood : good (insert z Z) := by
      refine ⟨?_, ?_⟩
      · rw [coe_insert]
        refine hZdisj.insert fun z' hz' _ => ?_
        rw [id, id, Finset.disjoint_left]
        intro y hy hy'
        exact hzU y hy (mem_biUnion.mpr ⟨z', hz', hy'⟩)
      · intro z' hz'
        rcases mem_insert.mp hz' with rfl | hz'
        · refine ⟨x, c', hc.mapLe hGT, ?_, rfl⟩
          rw [Walk.length_mapLe]
          have : (c.length : ℝ) ≤ 2 * r := by exact_mod_cast hcl
          linarith
        · exact hZcyc z' hz'
    have := hmax (insert z Z) (mem_filter.mpr ⟨mem_univ _, hgood⟩)
    rw [card_insert_of_notMem hznot] at this
    omega
  rw [div_le_iff₀ hgpos]
  exact hcover.trans hUZ

end Lovasz
