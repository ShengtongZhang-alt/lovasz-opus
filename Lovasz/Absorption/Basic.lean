/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.GapCut
import Lovasz.LongPath
import Lovasz.Perturbation
import Lovasz.RobustHall
import Lovasz.SpectralConnection
import Lovasz.Comparator
import Lovasz.Router
import Lovasz.ShortCycles
import Lovasz.BipartiteSampling
import Lovasz.ColumnSampling
import Lovasz.Chernoff

/-!
# Theorem 3.2: local absorption — shared definitions and proved steps

DAG node `T3.2` of `docs/BLUEPRINT.md`. Its proof is Section 3.3 of the paper, from the nodes
of Sections 2 and 3. The proof is decomposed into the following steps (sub-nodes `T3.2a`–`g`).

* `T3.2a` `LocalAbsorption.deletion_step` (proved): `H₀ = H - E` keeps degrees `(1 ± 2cσ) D`
  and gap `σ / 2` (Lemma 2.1).
* `T3.2b` `LocalAbsorption.initial_partition` (probabilistic; `Absorption/InitialPartition.lean`): the initial random
  partition of §3.3 (the sets `R₁, Q, C, Z, I, O, U, V`, the ports and dummies, the filler
  matching of the special transition) satisfies all the events used later, recorded in the
  structure `InitPartition`.
* `T3.2c` `LocalAbsorption.router_step` (deterministic from Lemmas 3.4–3.7; `Absorption/RouterStep.lean`): a Hamilton
  router on a vertex set inside `C ∪ Q ∪ I ∪ O` with terminals `I, O`.
* `T3.2d` attachments: Lemma 3.4 in `R₁` (`spectral_connection`, applied directly).
* `T3.2e` `LocalAbsorption.divisibility_step` (proved): a path of prescribed odd length in `Z`
  (the depth-first-search lemma).
* `T3.2f` `LocalAbsorption.fresh_layers` (probabilistic; `Absorption/FreshLayers.lean`): the fresh equipartition of
  the pool into layers with perfect matchings between consecutive layers (Lemmas 2.3, 2.4
  (`LocalAbsorption.fixed_boundary_fresh_layer`, `Absorption/FixedBoundary.lean`), 2.5); its output is recorded as a
  grid of `w` vertex-disjoint `O`–`I` paths.
* `T3.2g` (proved) `LocalAbsorption.expansion`, `LocalAbsorption.uv_bijection`,
  `LocalAbsorption.assembly_core`, and the bookkeeping `LocalAbsorption.absorb_of_partition`:
  router + outside paths + expansion of the formal edges ⇒ the path system required by
  `IsMatchingAbsorbing`.

Modification of the paper (harmless): the divisibility residue is taken in `[1, m]` instead
of `[0, m)`, so that the divisibility path is always used (when the paper's residue is `0` we
remove `m` vertices of each colour, i.e. one layer fewer). This avoids a case split.
-/

universe u

namespace Lovasz

open Finset

namespace LocalAbsorption

/-! ### General combinatorial lemmas -/

section General

variable {V : Type*}

/-- Transfer reachability when every edge of `G` is realized by reachability in `G'`. -/
lemma reach_of_forall_adj {G G' : SimpleGraph V} (h : ∀ a b, G.Adj a b → G'.Reachable a b)
    {a b : V} (hab : G.Reachable a b) : G'.Reachable a b := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

lemma isHamRouter_mono {K K' : SimpleGraph V} (hK : K ≤ K') {A I O : Set V}
    (h : IsHamRouter K A I O) : IsHamRouter K' A I O := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun β => ?_⟩
  obtain ⟨P, hP, h1, h2, h3⟩ := h.2.2.2 β
  exact ⟨P, hP.trans hK, h1, h2, h3⟩

/-- **Union of vertex-disjoint paths.** A family of paths with distinct endpoints and pairwise
disjoint vertex sets forms a path system on the union of their vertex sets, with the set of
their endpoints as endpoint set. -/
theorem pathSystem_of_paths {G : SimpleGraph V} {κ : Type*} (a b : κ → V)
    (p : ∀ j, G.Walk (a j) (b j)) (hp : ∀ j, (p j).IsPath) (hab : ∀ j, a j ≠ b j)
    (hdisj : ∀ j k, j ≠ k → ∀ v ∈ (p j).support, v ∉ (p k).support) :
    SimpleGraph.fromEdgeSet {e | ∃ j, e ∈ (p j).edges} ≤ G ∧
      IsPathSystem (SimpleGraph.fromEdgeSet {e | ∃ j, e ∈ (p j).edges})
        {v | ∃ j, v ∈ (p j).support} {v | ∃ j, v = a j ∨ v = b j} ∧
      (∀ j, ∀ v ∈ (p j).support,
        (SimpleGraph.fromEdgeSet {e | ∃ j, e ∈ (p j).edges}).Reachable v (a j)) := by
  classical
  set X := SimpleGraph.fromEdgeSet {e | ∃ j, e ∈ (p j).edges} with hX
  have hadj : ∀ u v, X.Adj u v ↔ ∃ j, (p j).toSubgraph.Adj u v := by
    intro u v
    rw [hX, SimpleGraph.fromEdgeSet_adj]
    simp only [Set.mem_ofPred_eq, SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    constructor
    · rintro ⟨⟨j, hj⟩, -⟩; exact ⟨j, hj⟩
    · rintro ⟨j, hj⟩; exact ⟨⟨j, hj⟩, G.ne_of_adj (SimpleGraph.Walk.adj_of_mem_edges _ hj)⟩
  have hnbr : ∀ j, ∀ v ∈ (p j).support, X.neighborSet v = (p j).toSubgraph.neighborSet v := by
    intro j v hv
    ext u
    simp only [SimpleGraph.mem_neighborSet, SimpleGraph.Subgraph.mem_neighborSet, hadj]
    constructor
    · rintro ⟨k, hk⟩
      by_cases hjk : j = k
      · subst hjk; exact hk
      · exact absurd (SimpleGraph.Walk.mem_support_of_adj_toSubgraph hk) (hdisj j k hjk v hv)
    · exact fun h => ⟨j, h⟩
  have hT : ∀ j, ∀ v ∈ (p j).support, (∃ k, v = a k ∨ v = b k) ↔ (v = a j ∨ v = b j) := by
    intro j v hv
    constructor
    · rintro ⟨k, hk⟩
      by_cases hjk : j = k
      · subst hjk; exact hk
      · exfalso
        refine hdisj j k hjk v hv ?_
        rcases hk with rfl | rfl
        · exact (p k).start_mem_support
        · exact (p k).end_mem_support
    · exact fun h => ⟨j, h⟩
  have hreach : ∀ j, ∀ v ∈ (p j).support, X.Reachable v (a j) := by
    intro j v hv
    have hq : ∀ e ∈ ((p j).takeUntil v hv).edges, e ∈ X.edgeSet := by
      intro e he
      have he' := (p j).edges_takeUntil_subset_edges hv he
      revert he'
      refine Sym2.ind (fun x y => ?_) e
      intro he'
      rw [SimpleGraph.mem_edgeSet, hadj]
      exact ⟨j, SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.2 he'⟩
    exact SimpleGraph.Reachable.symm ⟨((p j).takeUntil v hv).transfer X hq⟩
  refine ⟨fun u v h => ?_, ⟨fun x y h => ?_, ?_, ?_, ?_, ?_⟩, hreach⟩
  · obtain ⟨j, hj⟩ := (hadj u v).1 h
    exact SimpleGraph.Walk.adj_of_mem_edges _
      (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.1 hj)
  · obtain ⟨j, hj⟩ := (hadj x y).1 h
    exact ⟨⟨j, SimpleGraph.Walk.mem_support_of_adj_toSubgraph hj⟩,
      ⟨j, SimpleGraph.Walk.mem_support_of_adj_toSubgraph hj.symm⟩⟩
  · rintro v ⟨j, rfl | rfl⟩
    · exact ⟨j, (p j).start_mem_support⟩
    · exact ⟨j, (p j).end_mem_support⟩
  · rintro v ⟨j, hv⟩
    have hnil : ¬ (p j).Nil := SimpleGraph.Walk.not_nil_of_ne (hab j)
    rcases hv with rfl | rfl
    · rw [hnbr j _ (p j).start_mem_support, (hp j).neighborSet_toSubgraph_startpoint hnil]
      simp
    · rw [hnbr j _ (p j).end_mem_support, (hp j).neighborSet_toSubgraph_endpoint hnil]
      simp
  · rintro v ⟨j, hv⟩ hvT
    have hvT' : ¬ (v = a j ∨ v = b j) := fun h => hvT ((hT j v hv).2 h)
    rw [not_or] at hvT'
    obtain ⟨i, rfl, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hv
    have hi0 : i ≠ 0 := fun h => hvT'.1 (by rw [h, SimpleGraph.Walk.getVert_zero])
    have hil : i < (p j).length := by
      rcases Nat.lt_or_ge i (p j).length with h | h
      · exact h
      · exact absurd (by rw [show i = (p j).length by omega, SimpleGraph.Walk.getVert_length])
          hvT'.2
    rw [hnbr j _ hv]
    exact (hp j).ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil
  · rintro v ⟨j, hv⟩
    exact ⟨a j, ⟨j, Or.inl rfl⟩, hreach j v hv⟩


/-- **Colour balance of a path system** (handshake in each colour class): if a path system of
a bipartite graph has vertex set `A` and endpoint set `T`, then
`2 |A ∩ col⁻¹ true| - |T ∩ col⁻¹ true| = 2 |A ∩ col⁻¹ false| - |T ∩ col⁻¹ false|`. -/
theorem card_balance_of_pathSystem [Fintype V] [DecidableEq V] {P : SimpleGraph V}
    {A T : Finset V} (col : V → Bool) (hbip : ∀ x y, P.Adj x y → col x ≠ col y)
    (hP : IsPathSystem P (A : Set V) (T : Set V)) :
    2 * (A.filter fun x => col x = true).card + (T.filter fun x => col x = false).card =
      2 * (A.filter fun x => col x = false).card + (T.filter fun x => col x = true).card := by
  classical
  have hnb : ∀ v ∈ A, ∀ u, P.Adj v u → u ∈ A ∧ col u ≠ col v := fun v _ u h =>
    ⟨(hP.adj_mem v u h).2, (hbip v u h).symm⟩
  have hdeg : ∀ v ∈ A, ∀ b, col v = b →
      ((A.filter fun x => col x = !b).filter (P.Adj v)).card + (if v ∈ T then 1 else 0) = 2 := by
    intro v hv b hb
    have : ((A.filter fun x => col x = !b).filter (P.Adj v)).card = (P.neighborSet v).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext u
      simp only [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_neighborSet]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨⟨(hnb v hv u h).1, ?_⟩, h⟩
        have := (hnb v hv u h).2
        rw [hb] at this
        cases b <;> simpa using this
    rw [this]
    split_ifs with hvT
    · rw [hP.deg_end v hvT]
    · rw [hP.deg_inner v hv hvT]
  have hT : ∀ b, (T.filter fun x => col x = b).card =
      ((A.filter fun x => col x = b).filter (· ∈ T)).card := by
    intro b
    congr 1
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨hP.subset h1, h2⟩, h1⟩
    · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
  have hsum : ∀ b, ∑ v ∈ A.filter (fun x => col x = b),
      (((A.filter fun x => col x = !b).filter (P.Adj v)).card + (if v ∈ T then 1 else 0)) =
      2 * (A.filter fun x => col x = b).card := by
    intro b
    rw [Finset.sum_congr rfl (fun v hv => hdeg v (Finset.mem_filter.1 hv).1 b
      (Finset.mem_filter.1 hv).2)]
    simp [mul_comm]
  have hsum' : ∀ b, ∑ v ∈ A.filter (fun x => col x = b), (if v ∈ T then 1 else 0) =
      (T.filter fun x => col x = b).card := by
    intro b; rw [hT b, Finset.card_filter]
  have hcomm : ∑ v ∈ A.filter (fun x => col x = true),
      ((A.filter fun x => col x = false).filter (P.Adj v)).card =
      ∑ u ∈ A.filter (fun x => col x = false),
        ((A.filter fun x => col x = true).filter (P.Adj u)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    simp only [P.adj_comm]
  have h1 := hsum true
  have h2 := hsum false
  rw [Finset.sum_add_distrib, hsum'] at h1 h2
  simp only [Bool.not_true, Bool.not_false] at h1 h2
  omega


/-- **The special transition** `U–V`: the formal edges `F` form a perfect matching between
`FU ⊆ U'` and `FW ⊆ W'`, and `μ` is a perfect matching (by edges of `G`) between the fillers
`U' \ FU` and `W' \ FW`. Together they give a bijection `τ : U' → W'` along edges of `G` or `F`,
through which every formal edge passes. -/
theorem uv_bijection [DecidableEq V] (G F : SimpleGraph V) (U' W' FU FW : Finset V) (μ : V → V)
    (hFU : FU ⊆ U') (hFW : FW ⊆ W') (hUW : Disjoint U' W')
    (hF : ∀ u v, F.Adj u v → (u ∈ FU ∧ v ∈ FW) ∨ (u ∈ FW ∧ v ∈ FU))
    (hFm : ∀ u v v', F.Adj u v → F.Adj u v' → v = v')
    (hFex : ∀ u ∈ FU, ∃ v, F.Adj u v) (hFex' : ∀ v ∈ FW, ∃ u, F.Adj u v)
    (hμ : Set.BijOn μ (↑(U' \ FU)) (↑(W' \ FW))) (hμG : ∀ u ∈ U' \ FU, G.Adj u (μ u)) :
    ∃ τ : V → V, Set.BijOn τ ↑U' ↑W' ∧ (∀ u ∈ U', G.Adj u (τ u) ∨ F.Adj u (τ u)) ∧
      ∀ u v, F.Adj u v → (u ∈ U' ∧ τ u = v) ∨ (v ∈ U' ∧ τ v = u) := by
  classical
  let τ : V → V := fun u => if h : u ∈ FU then (hFex u h).choose else μ u
  have hτFU : ∀ u (hu : u ∈ FU), F.Adj u (τ u) := fun u hu => by
    simp only [τ, hu, ↓reduceDIte]; exact (hFex u hu).choose_spec
  have hτnot : ∀ u, u ∉ FU → τ u = μ u := fun u hu => by simp only [τ, hu, ↓reduceDIte]
  have hFUW : ∀ u ∈ FU, ∀ v, F.Adj u v → v ∈ FW := by
    intro u hu v huv
    rcases hF u v huv with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact absurd (hFW h) (Finset.disjoint_left.1 hUW (hFU hu))
  have hμmaps : ∀ u ∈ U', u ∉ FU → μ u ∈ W' ∧ μ u ∉ FW := fun u hu hu' =>
    Finset.mem_sdiff.1 (Finset.mem_coe.1 (hμ.mapsTo (Finset.mem_coe.2
      (Finset.mem_sdiff.2 ⟨hu, hu'⟩))))
  refine ⟨τ, ⟨fun u hu => ?_, fun u₁ hu₁ u₂ hu₂ h => ?_, fun w hw => ?_⟩, fun u hu => ?_,
    fun u v huv => ?_⟩
  · rw [Finset.mem_coe] at hu ⊢
    by_cases h : u ∈ FU
    · exact hFW (hFUW u h _ (hτFU u h))
    · rw [hτnot u h]; exact (hμmaps u hu h).1
  · rw [Finset.mem_coe] at hu₁ hu₂
    by_cases h₁ : u₁ ∈ FU <;> by_cases h₂ : u₂ ∈ FU
    · have a₁ := hτFU u₁ h₁
      have a₂ := hτFU u₂ h₂
      rw [← h] at a₂
      exact hFm _ _ _ a₁.symm a₂.symm
    · exact absurd (h ▸ hFUW u₁ h₁ _ (hτFU u₁ h₁)) (by rw [hτnot u₂ h₂]; exact (hμmaps u₂ hu₂ h₂).2)
    · exact absurd (h.symm ▸ hFUW u₂ h₂ _ (hτFU u₂ h₂))
        (by rw [hτnot u₁ h₁]; exact (hμmaps u₁ hu₁ h₁).2)
    · rw [hτnot u₁ h₁, hτnot u₂ h₂] at h
      exact hμ.injOn (Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨hu₁, h₁⟩))
        (Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨hu₂, h₂⟩)) h
  · rw [Finset.mem_coe] at hw
    by_cases h : w ∈ FW
    · obtain ⟨u, hu⟩ := hFex' w h
      have huFU : u ∈ FU := by
        rcases hF u w hu with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact h1
        · exact absurd (hFU h2) (Finset.disjoint_right.1 hUW hw)
      exact ⟨u, Finset.mem_coe.2 (hFU huFU), hFm _ _ _ (hτFU u huFU) hu⟩
    · obtain ⟨u, hu, rfl⟩ := hμ.surjOn (Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨hw, h⟩))
      have hu' := Finset.mem_sdiff.1 (Finset.mem_coe.1 hu)
      exact ⟨u, Finset.mem_coe.2 hu'.1, hτnot u hu'.2⟩
  · by_cases h : u ∈ FU
    · exact Or.inr (hτFU u h)
    · rw [hτnot u h]; exact Or.inl (hμG u (Finset.mem_sdiff.2 ⟨hu, h⟩))
  · rcases hF u v huv with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact Or.inl ⟨hFU h1, hFm _ _ _ (hτFU u h1) huv⟩
    · exact Or.inr ⟨hFU h2, hFm _ _ _ (hτFU v h2) huv.symm⟩


/-- **Assembly (`T3.2g`).** Let `A` carry an `I, O`-Hamilton router of `G`. Let `φ` be a grid
of `w` vertex-disjoint rows `φ i 0, …, φ i k` from `O` to `I` (the union of the transition
matchings), with interior outside `A`, whose steps are edges of `G` or formal edges `F`; the
formal edges form a matching of interior grid vertices. Let `X ≤ G` be a path system on
`Rem ∪ ends(F)` with endpoints `E ∪ ends(F)` (the expansions: attachments and divisibility
path), such that each formal edge is realized in `X ⊔ J`. If `A`, `Rem` and the grid interior
cover all vertices, then `G` has a spanning subgraph `P` with degree one on `E`, two elsewhere,
and `P ⊔ J` connected. -/
theorem assembly_core [Fintype V] [DecidableEq V] (G J F X : SimpleGraph V)
    (E Rem A I O : Set V) (w k : ℕ) (φ : Fin w → ℕ → V) (hw : 0 < w) (hk : 2 ≤ k)
    (hR : IsHamRouter G A I O)
    (hinj : ∀ i j i' j', j ≤ k → j' ≤ k → φ i j = φ i' j' → i = i' ∧ j = j')
    (hO : ∀ v, v ∈ O ↔ ∃ i, φ i 0 = v) (hI : ∀ v, v ∈ I ↔ ∃ i, φ i k = v)
    (hmid : ∀ i j, 0 < j → j < k → φ i j ∉ A)
    (hstep : ∀ i j, j < k → ¬ F.Adj (φ i j) (φ i (j + 1)) → G.Adj (φ i j) (φ i (j + 1)))
    (hF : ∀ u v, F.Adj u v → ∃ i j, 0 < j ∧ j + 1 < k ∧ s(u, v) = s(φ i j, φ i (j + 1)))
    (hFm : ∀ u v v', F.Adj u v → F.Adj u v' → v = v')
    (hX : IsPathSystem X (Rem ∪ {v | ∃ u, F.Adj v u}) (E ∪ {v | ∃ u, F.Adj v u}))
    (hXG : X ≤ G) (hXrem : ∀ u v, X.Adj u v → u ∈ Rem ∨ v ∈ Rem) (hE : E ⊆ Rem)
    (hFreach : ∀ u v, F.Adj u v → (X ⊔ J).Reachable u v)
    (hRemreach : ∀ v ∈ Rem, ∃ u, (∃ u', F.Adj u u') ∧ (X ⊔ J).Reachable v u)
    (hcover : ∀ v, v ∈ A ∨ v ∈ Rem ∨ ∃ i j, 0 < j ∧ j < k ∧ φ i j = v)
    (hRemA : ∀ v ∈ Rem, v ∉ A) (hRemφ : ∀ i j, j ≤ k → φ i j ∉ Rem) :
    ∃ P : SimpleGraph V, P ≤ G ∧ (∀ x ∈ E, (P.neighborSet x).ncard = 1) ∧
      (∀ x ∉ E, (P.neighborSet x).ncard = 2) ∧ (P ⊔ J).Connected := by
  classical
  -- grid facts
  have hne : ∀ i j j', j ≤ k → j' ≤ k → j ≠ j' → φ i j ≠ φ i j' :=
    fun i j j' hj hj' hjj' h => hjj' (hinj i j i j' hj hj' h).2
  have hO' : ∀ i, φ i 0 ∈ O := fun i => (hO _).2 ⟨i, rfl⟩
  have hI' : ∀ i, φ i k ∈ I := fun i => (hI _).2 ⟨i, rfl⟩
  have hIOA : I ∪ O ⊆ A := hR.2.2.1
  have hOA : ∀ i, φ i 0 ∈ A := fun i => hIOA (Or.inr (hO' i))
  have hIA : ∀ i, φ i k ∈ A := fun i => hIOA (Or.inl (hI' i))
  have hFg : ∀ v u, F.Adj v u → ∃ i j, 0 < j ∧ j < k ∧ v = φ i j ∧
      ((j + 1 < k ∧ u = φ i (j + 1)) ∨ (1 < j ∧ u = φ i (j - 1))) := by
    intro v u h
    obtain ⟨i, j, hj0, hjk, he⟩ := hF v u h
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨i, j, hj0, by omega, rfl, Or.inl ⟨hjk, rfl⟩⟩
    · exact ⟨i, j + 1, by omega, hjk, rfl, Or.inr ⟨by omega, by simp⟩⟩
  have hFendgrid : ∀ v, (∃ u, F.Adj v u) → ∃ i j, 0 < j ∧ j < k ∧ v = φ i j := by
    rintro v ⟨u, hu⟩
    obtain ⟨i, j, hj0, hjk, rfl, -⟩ := hFg v u hu
    exact ⟨i, j, hj0, hjk, rfl⟩
  have hFendRem : ∀ v, (∃ u, F.Adj v u) → v ∉ Rem := by
    intro v hv
    obtain ⟨i, j, -, hjk, rfl⟩ := hFendgrid v hv
    exact hRemφ i j hjk.le
  -- the bijection `β : O → I` given by the rows
  have hbO : Function.Bijective (fun i : Fin w => (⟨φ i 0, hO' i⟩ : O)) :=
    ⟨fun i i' h => (hinj i 0 i' 0 (by omega) (by omega) (congrArg Subtype.val h)).1,
      fun ⟨v, hv⟩ => by obtain ⟨i, rfl⟩ := (hO v).1 hv; exact ⟨i, rfl⟩⟩
  have hbI : Function.Bijective (fun i : Fin w => (⟨φ i k, hI' i⟩ : I)) :=
    ⟨fun i i' h => (hinj i k i' k le_rfl le_rfl (congrArg Subtype.val h)).1,
      fun ⟨v, hv⟩ => by obtain ⟨i, rfl⟩ := (hI v).1 hv; exact ⟨i, rfl⟩⟩
  set eO := Equiv.ofBijective _ hbO with heO
  set eI := Equiv.ofBijective _ hbI with heI
  set β : O ≃ I := eO.symm.trans eI with hβdef
  have hβ : ∀ i, (β ⟨φ i 0, hO' i⟩ : V) = φ i k := by
    intro i
    show (eI (eO.symm (eO i)) : V) = φ i k
    rw [Equiv.symm_apply_apply]
    rfl
  obtain ⟨PS, hPSG, hPS, -, hconn⟩ := hR.2.2.2 β
  -- the outside matching edges
  set M : SimpleGraph V := SimpleGraph.fromEdgeSet {e | ∃ i j, j < k ∧
    ¬ F.Adj (φ i j) (φ i (j + 1)) ∧ e = s(φ i j, φ i (j + 1))} with hMdef
  have hMadj : ∀ u v, M.Adj u v ↔ ∃ i j, j < k ∧ ¬ F.Adj (φ i j) (φ i (j + 1)) ∧
      ((u = φ i j ∧ v = φ i (j + 1)) ∨ (u = φ i (j + 1) ∧ v = φ i j)) := by
    intro u v
    rw [hMdef, SimpleGraph.fromEdgeSet_adj]
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨i, j, hjk, hF', he⟩, -⟩
      exact ⟨i, j, hjk, hF', Sym2.eq_iff.1 he⟩
    · rintro ⟨i, j, hjk, hF', h⟩
      refine ⟨⟨i, j, hjk, hF', Sym2.eq_iff.2 h⟩, ?_⟩
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne i j (j + 1) (by omega) (by omega) (by omega)
      · exact hne i (j + 1) j (by omega) (by omega) (by omega)
  have hMgrid : ∀ i j, j ≤ k → ∀ u, M.Adj (φ i j) u ↔
      ((j < k ∧ ¬ F.Adj (φ i j) (φ i (j + 1)) ∧ u = φ i (j + 1)) ∨
        (0 < j ∧ ¬ F.Adj (φ i (j - 1)) (φ i j) ∧ u = φ i (j - 1))) := by
    intro i j hj u
    rw [hMadj]
    constructor
    · rintro ⟨i', j', hj', hF', (⟨h1, rfl⟩ | ⟨h1, rfl⟩)⟩
      · obtain ⟨rfl, rfl⟩ := hinj i j i' j' hj (by omega) h1
        exact Or.inl ⟨hj', hF', rfl⟩
      · obtain ⟨rfl, rfl⟩ := hinj i j i' (j' + 1) hj (by omega) h1
        refine Or.inr ⟨by omega, ?_, by simp⟩
        simpa using hF'
    · rintro (⟨hjk, hF', rfl⟩ | ⟨hj0, hF', rfl⟩)
      · exact ⟨i, j, hjk, hF', Or.inl ⟨rfl, rfl⟩⟩
      · refine ⟨i, j - 1, by omega, ?_, Or.inr ⟨?_, rfl⟩⟩
        · rwa [Nat.sub_add_cancel hj0]
        · rw [Nat.sub_add_cancel hj0]
  have hMnot : ∀ v, (∀ i j, j ≤ k → φ i j ≠ v) → ∀ u, ¬ M.Adj v u := by
    intro v hv u h
    obtain ⟨i, j, hjk, -, (⟨rfl, -⟩ | ⟨rfl, -⟩)⟩ := (hMadj v u).1 h
    · exact hv i j (by omega) rfl
    · exact hv i (j + 1) (by omega) rfl
  have hXnb : ∀ v, v ∉ Rem → (¬ ∃ u, F.Adj v u) → X.neighborSet v = ∅ := by
    intro v h1 h2
    refine Set.eq_empty_iff_forall_notMem.2 fun u h => ?_
    rcases (hX.adj_mem v u h).1 with h' | h'
    · exact h1 h'
    · exact h2 h'
  have hPSnb : ∀ v, v ∉ A → PS.neighborSet v = ∅ := fun v hv =>
    Set.eq_empty_iff_forall_notMem.2 fun u h => hv (hPS.adj_mem v u h).1
  have hMnb : ∀ v, (∀ i j, j ≤ k → φ i j ≠ v) → M.neighborSet v = ∅ := fun v hv =>
    Set.eq_empty_iff_forall_notMem.2 fun u h => hMnot v hv u h
  -- the path system
  set P := PS ⊔ M ⊔ X with hPdef
  have hPnbr : ∀ v, P.neighborSet v = PS.neighborSet v ∪ M.neighborSet v ∪ X.neighborSet v := by
    intro v
    rw [hPdef, SimpleGraph.neighborSet_sup, SimpleGraph.neighborSet_sup]
  have hdegRem : ∀ v ∈ Rem, P.neighborSet v = X.neighborSet v := by
    intro v hv
    rw [hPnbr, hPSnb v (hRemA v hv),
      hMnb v (fun i j hj h => hRemφ i j hj (h ▸ hv)), Set.empty_union, Set.empty_union]
  have hdegA : ∀ v ∈ A, v ∉ I → v ∉ O → (P.neighborSet v).ncard = 2 := by
    intro v hvA hvI hvO
    have hng : ∀ i j, j ≤ k → φ i j ≠ v := by
      intro i j hj h
      subst h
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact hvO (hO' i)
      · rcases eq_or_lt_of_le hj with hjk | hjk
        · exact hvI (by rw [hjk]; exact hI' i)
        · exact hmid i j hj0 hjk hvA
    have hvF : ¬ ∃ u, F.Adj v u := fun h => by
      obtain ⟨i, j, -, hjk, rfl⟩ := hFendgrid v h
      exact hng i j hjk.le rfl
    have hvR : v ∉ Rem := fun h => hRemA v h hvA
    rw [hPnbr, hMnb v hng, hXnb v hvR hvF, Set.union_empty, Set.union_empty]
    exact hPS.deg_inner v hvA (by rintro (h | h); exact hvI h; exact hvO h)
  have hdegO : ∀ i, (P.neighborSet (φ i 0)).ncard = 2 := by
    intro i
    have hvF : ¬ ∃ u, F.Adj (φ i 0) u := fun h => by
      obtain ⟨i', j', hj0', hjk', he⟩ := hFendgrid _ h
      have := (hinj i 0 i' j' (by omega) hjk'.le he).2
      omega
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 (hPS.deg_end (φ i 0) (Or.inr (hO' i)))
    have haA : a ∈ A := (hPS.adj_mem _ a (by
      rw [← SimpleGraph.mem_neighborSet, ha]; exact Set.mem_singleton a)).2
    have hM0 : M.neighborSet (φ i 0) = {φ i 1} := by
      ext u
      rw [SimpleGraph.mem_neighborSet, hMgrid i 0 (by omega), Set.mem_singleton_iff]
      constructor
      · rintro (⟨-, -, rfl⟩ | ⟨h, -⟩)
        · rfl
        · omega
      · rintro rfl
        exact Or.inl ⟨by omega, fun h => hvF ⟨_, h⟩, rfl⟩
    rw [hPnbr, ha, hM0, hXnb _ (hRemφ i 0 (by omega)) hvF, Set.union_empty, Set.singleton_union]
    exact Set.ncard_pair (fun h => hmid i 1 (by omega) (by omega) (h ▸ haA))
  have hdegI : ∀ i, (P.neighborSet (φ i k)).ncard = 2 := by
    intro i
    have hvF : ¬ ∃ u, F.Adj (φ i k) u := fun h => by
      obtain ⟨i', j', -, hjk', he⟩ := hFendgrid _ h
      have := (hinj i k i' j' le_rfl hjk'.le he).2
      omega
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 (hPS.deg_end (φ i k) (Or.inl (hI' i)))
    have haA : a ∈ A := (hPS.adj_mem _ a (by
      rw [← SimpleGraph.mem_neighborSet, ha]; exact Set.mem_singleton a)).2
    have hM0 : M.neighborSet (φ i k) = {φ i (k - 1)} := by
      ext u
      rw [SimpleGraph.mem_neighborSet, hMgrid i k le_rfl, Set.mem_singleton_iff]
      constructor
      · rintro (⟨h, -⟩ | ⟨-, -, rfl⟩)
        · omega
        · rfl
      · rintro rfl
        exact Or.inr ⟨by omega, fun h => hvF ⟨_, h.symm⟩, rfl⟩
    rw [hPnbr, ha, hM0, hXnb _ (hRemφ i k le_rfl) hvF, Set.union_empty, Set.singleton_union]
    exact Set.ncard_pair (fun h => hmid i (k - 1) (by omega) (by omega) (h ▸ haA))
  have hdegmid : ∀ i j, 0 < j → j < k → (P.neighborSet (φ i j)).ncard = 2 := by
    intro i j hj0 hjk
    have hj : j ≤ k := hjk.le
    have hvRem : φ i j ∉ Rem := hRemφ i j hj
    have hPS0 : PS.neighborSet (φ i j) = ∅ := hPSnb _ (hmid i j hj0 hjk)
    by_cases hvF : ∃ u, F.Adj (φ i j) u
    · obtain ⟨x, hx⟩ := Set.ncard_eq_one.1 (hX.deg_end (φ i j) (Or.inr hvF))
      have hxRem : x ∈ Rem := by
        have hadj : X.Adj (φ i j) x := by
          rw [← SimpleGraph.mem_neighborSet, hx]; exact Set.mem_singleton x
        rcases hXrem _ _ hadj with h | h
        · exact absurd h hvRem
        · exact h
      obtain ⟨u, hu⟩ := hvF
      obtain ⟨i', j', hj0', hjk', he, hu'⟩ := hFg _ _ hu
      obtain ⟨rfl, rfl⟩ := hinj i j i' j' hj hjk'.le he
      rcases hu' with ⟨hjk1, rfl⟩ | ⟨hj1, rfl⟩
      · have hnb : ¬ F.Adj (φ i (j - 1)) (φ i j) := fun h =>
          hne i (j + 1) (j - 1) (by omega) (by omega) (by omega) (hFm _ _ _ hu h.symm)
        have hM : M.neighborSet (φ i j) = {φ i (j - 1)} := by
          ext u
          rw [SimpleGraph.mem_neighborSet, hMgrid i j hj, Set.mem_singleton_iff]
          constructor
          · rintro (⟨-, h, -⟩ | ⟨-, -, rfl⟩)
            · exact absurd hu h
            · rfl
          · rintro rfl
            exact Or.inr ⟨hj0, hnb, rfl⟩
        rw [hPnbr, hPS0, hM, hx, Set.empty_union, Set.singleton_union]
        exact Set.ncard_pair (fun h => hRemφ i (j - 1) (by omega) (h ▸ hxRem))
      · have hnf : ¬ F.Adj (φ i j) (φ i (j + 1)) := fun h =>
          hne i (j - 1) (j + 1) (by omega) (by omega) (by omega) (hFm _ _ _ hu h)
        have hM : M.neighborSet (φ i j) = {φ i (j + 1)} := by
          ext u'
          rw [SimpleGraph.mem_neighborSet, hMgrid i j hj, Set.mem_singleton_iff]
          constructor
          · rintro (⟨-, -, rfl⟩ | ⟨-, h, -⟩)
            · rfl
            · exact absurd hu.symm h
          · rintro rfl
            exact Or.inl ⟨hjk, hnf, rfl⟩
        rw [hPnbr, hPS0, hM, hx, Set.empty_union, Set.singleton_union]
        exact Set.ncard_pair (fun h => hRemφ i (j + 1) (by omega) (h ▸ hxRem))
    · have hM : M.neighborSet (φ i j) = {φ i (j + 1), φ i (j - 1)} := by
        ext u
        rw [SimpleGraph.mem_neighborSet, hMgrid i j hj, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        constructor
        · rintro (⟨-, -, rfl⟩ | ⟨-, -, rfl⟩)
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact Or.inl ⟨hjk, fun h => hvF ⟨_, h⟩, rfl⟩
          · exact Or.inr ⟨hj0, fun h => hvF ⟨_, h.symm⟩, rfl⟩
      rw [hPnbr, hPS0, hM, hXnb _ hvRem hvF, Set.empty_union, Set.union_empty]
      exact Set.ncard_pair (hne i (j + 1) (j - 1) (by omega) (by omega) (by omega))
  -- connectivity
  have hXP : X ⊔ J ≤ P ⊔ J := sup_le_sup_right le_sup_right J
  have hrow : ∀ i j, j ≤ k → (P ⊔ J).Reachable (φ i 0) (φ i j) := by
    intro i j hj
    induction j with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ j ih =>
      refine (ih (by omega)).trans ?_
      by_cases hFs : F.Adj (φ i j) (φ i (j + 1))
      · exact (hFreach _ _ hFs).mono hXP
      · have hM : M.Adj (φ i j) (φ i (j + 1)) :=
          (hMadj _ _).2 ⟨i, j, by omega, hFs, Or.inl ⟨rfl, rfl⟩⟩
        exact SimpleGraph.Adj.reachable (Or.inl (Or.inl (Or.inr hM)))
  have hbij : ∀ u v, (PS ⊔ bijMatching β).Adj u v → (P ⊔ J).Reachable u v := by
    intro u v h
    rcases h with h | h
    · exact SimpleGraph.Adj.reachable (Or.inl (Or.inl (Or.inl h)))
    · rw [bijMatching, SimpleGraph.fromEdgeSet_adj] at h
      obtain ⟨⟨o, he⟩, -⟩ := h
      obtain ⟨i, hi⟩ := (hO o).1 o.2
      have ho : o = ⟨φ i 0, hO' i⟩ := Subtype.ext hi.symm
      subst ho
      rw [hβ i] at he
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hrow i k le_rfl
      · exact (hrow i k le_rfl).symm
  have hAreach : ∀ v ∈ A, (P ⊔ J).Reachable (φ ⟨0, hw⟩ 0) v := by
    intro v hv
    have h1 := hconn.preconnected ⟨φ ⟨0, hw⟩ 0, hOA _⟩ ⟨v, hv⟩
    exact reach_of_forall_adj hbij (h1.map (SimpleGraph.Embedding.induce A).toHom)
  have hall : ∀ v, (P ⊔ J).Reachable (φ ⟨0, hw⟩ 0) v := by
    intro v
    rcases hcover v with hv | hv | ⟨i, j, hj0, hjk, rfl⟩
    · exact hAreach v hv
    · obtain ⟨u, ⟨u', hu'⟩, hr⟩ := hRemreach v hv
      obtain ⟨i, j, -, hjk, rfl⟩ := hFendgrid u ⟨u', hu'⟩
      exact ((hAreach _ (hOA i)).trans (hrow i j hjk.le)).trans (hr.mono hXP).symm
    · exact (hAreach _ (hOA i)).trans (hrow i j hjk.le)
  have : Nonempty V := ⟨φ ⟨0, hw⟩ 0⟩
  refine ⟨P, ?_, fun x hx => ?_, fun x hx => ?_, ⟨fun u v => (hall u).symm.trans (hall v)⟩⟩
  · intro u v h
    rcases h with (h | h) | h
    · exact hPSG h
    · obtain ⟨i, j, hjk, hF', (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := (hMadj u v).1 h
      · exact hstep i j hjk hF'
      · exact (hstep i j hjk hF').symm
    · exact hXG h
  · rw [hdegRem x (hE hx)]
    exact hX.deg_end x (Or.inl hx)
  · rcases hcover x with hxA | hxR | ⟨i, j, hj0, hjk, rfl⟩
    · by_cases hxI : x ∈ I
      · obtain ⟨i, rfl⟩ := (hI x).1 hxI
        exact hdegI i
      by_cases hxO : x ∈ O
      · obtain ⟨i, rfl⟩ := (hO x).1 hxO
        exact hdegO i
      exact hdegA x hxA hxI hxO
    · rw [hdegRem x hxR]
      refine hX.deg_inner x (Or.inl hxR) ?_
      rintro (h | h)
      · exact hx h
      · exact hFendRem x h hxR
    · exact hdegmid i j hj0 hjk


/-- First endpoints of the expansion paths: `zA` for the divisibility path, `x` for the
attachment of `x ∈ E`. -/
def expA (zA : V) (E : Finset V) : Option E → V := fun j => j.elim zA fun x => (x : V)

/-- Second endpoints of the expansion paths. -/
def expB (port : V → V) (zB : V) (E : Finset V) : Option E → V :=
  fun j => j.elim zB fun x => port x

/-- The expansion paths: the divisibility path and the attachments. -/
def expP {G : SimpleGraph V} (E : Finset V) (port : V → V) (zA zB : V)
    (patt : ∀ x : E, G.Walk x (port x)) (pd : G.Walk zA zB) :
    ∀ j, G.Walk (expA zA E j) (expB port zB E j)
  | none => pd
  | some x => patt x

/-- **Expansion of the formal edges.** The attachment paths `patt x` (from `x ∈ E` to its
port) and the divisibility path `pd` (from `zA` to `zB`) are vertex-disjoint paths. Their
union `X` is a path system on `Rem ∪ Fend` with endpoints `E ∪ Fend`, where `Fend` is the set of
ends of the formal edges `F` (`port x port y` for `xy ∈ J`, and `zA zB`) and `Rem` is the set of
the other path vertices; every formal edge is realized in `X ⊔ J`. -/
theorem expansion [Fintype V] [DecidableEq V] {G J : SimpleGraph V} (E : Finset V)
    (port : V → V) (zA zB : V) (patt : ∀ x : E, G.Walk x (port x)) (pd : G.Walk zA zB)
    (F X : SimpleGraph V) (Fend Rem : Finset V)
    (hFdef : F = SimpleGraph.fromEdgeSet
      ({e | ∃ x y, J.Adj x y ∧ e = s(port x, port y)} ∪ {s(zA, zB)}))
    (hXdef : X = SimpleGraph.fromEdgeSet ({e | ∃ x : E, e ∈ (patt x).edges} ∪ {e | e ∈ pd.edges}))
    (hFend : Fend = E.image port ∪ {zA, zB})
    (hRem : ∀ v, v ∈ Rem ↔ ((∃ x : E, v ∈ (patt x).support) ∨ v ∈ pd.support) ∧ v ∉ Fend)
    (hJ : IsPerfectMatchingOn J ↑E)
    (hpatt : ∀ x, (patt x).IsPath) (hpd : pd.IsPath) (hpdlen : 2 ≤ pd.length)
    (hne : ∀ x : E, (x : V) ≠ port x)
    (hdisj : ∀ x y : E, x ≠ y → ∀ v ∈ (patt x).support, v ∉ (patt y).support)
    (hdisj' : ∀ x : E, ∀ v ∈ (patt x).support, v ∉ pd.support)
    (hportE : ∀ x ∈ E, port x ∉ E) (hzA : zA ∉ E) (hzB : zB ∉ E) :
    (∀ v, (∃ u, F.Adj v u) ↔ v ∈ Fend) ∧ (∀ u v v', F.Adj u v → F.Adj u v' → v = v') ∧
      X ≤ G ∧ IsPathSystem X (↑Rem ∪ ↑Fend) (↑E ∪ ↑Fend) ∧
      (∀ u v, X.Adj u v → u ∈ Rem ∨ v ∈ Rem) ∧ E ⊆ Rem ∧
      (∀ u v, F.Adj u v → (X ⊔ J).Reachable u v) ∧
      (∀ v ∈ Rem, ∃ u ∈ Fend, (X ⊔ J).Reachable v u) := by
  classical
  set a := expA zA E
  set b := expB port zB E
  set p := expP E port zA zB patt pd
  have hzAB : zA ≠ zB := by
    intro h
    subst h
    have := SimpleGraph.Walk.length_eq_zero_iff.2 (SimpleGraph.Walk.isPath_iff_nil.1 hpd)
    omega
  have hab : ∀ j, a j ≠ b j := by
    rintro (_ | x)
    · exact hzAB
    · exact hne x
  have hpp : ∀ j, (p j).IsPath := by
    rintro (_ | x)
    · exact hpd
    · exact hpatt x
  have hdj : ∀ j k, j ≠ k → ∀ v ∈ (p j).support, v ∉ (p k).support := by
    rintro (_ | x) (_ | y) hjk v hv hv'
    · exact hjk rfl
    · exact hdisj' y v hv' hv
    · exact hdisj' x v hv hv'
    · exact hdisj x y (fun h => hjk (by rw [h])) v hv hv'
  obtain ⟨hle, hsys, hreach⟩ := pathSystem_of_paths a b p hpp hab hdj
  have hXX : X = SimpleGraph.fromEdgeSet {e | ∃ j, e ∈ (p j).edges} := by
    rw [hXdef]
    congr 1
    ext e
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨x, hx⟩ | h)
      · exact ⟨some x, hx⟩
      · exact ⟨none, h⟩
    · rintro ⟨_ | x, h⟩
      · exact Or.inr h
      · exact Or.inl ⟨x, h⟩
  -- ports are injective on `E` and avoid `zA, zB`
  have hpinj : ∀ x y : E, port x = port y → x = y := by
    intro x y h
    by_contra hxy
    exact hdisj x y hxy _ (patt x).end_mem_support (by rw [h]; exact (patt y).end_mem_support)
  have hpz : ∀ x : E, port x ≠ zA ∧ port x ≠ zB := fun x =>
    ⟨fun h => hdisj' x _ (patt x).end_mem_support (h ▸ pd.start_mem_support),
      fun h => hdisj' x _ (patt x).end_mem_support (h ▸ pd.end_mem_support)⟩
  have hFendmem : ∀ v, v ∈ Fend ↔ (∃ x : E, v = port x) ∨ v = zA ∨ v = zB := by
    intro v
    rw [hFend, Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨x, hx, rfl⟩ | h)
      · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
      · exact Or.inr h
    · rintro (⟨x, rfl⟩ | h)
      · exact Or.inl ⟨x, x.2, rfl⟩
      · exact Or.inr h
  have hnotF_att : ∀ x : E, ∀ v ∈ (patt x).support, v ≠ port x → v ∉ Fend := by
    intro x v hv hvx hF
    rcases (hFendmem v).1 hF with ⟨y, rfl⟩ | rfl | rfl
    · by_cases hxy : x = y
      · exact hvx (by rw [hxy])
      · exact hdisj x y hxy _ hv (patt y).end_mem_support
    · exact hdisj' x _ hv pd.start_mem_support
    · exact hdisj' x _ hv pd.end_mem_support
  have hnotF_pd : ∀ v ∈ pd.support, v ≠ zA → v ≠ zB → v ∉ Fend := by
    intro v hv h1 h2 hF
    rcases (hFendmem v).1 hF with ⟨y, rfl⟩ | h | h
    · exact hdisj' y _ (patt y).end_mem_support hv
    · exact h1 h
    · exact h2 h
  -- the formal edges
  have hFadj : ∀ u v, F.Adj u v ↔ ((∃ x y, J.Adj x y ∧ u = port x ∧ v = port y) ∨
      (u = zA ∧ v = zB) ∨ (u = zB ∧ v = zA)) := by
    intro u v
    rw [hFdef, SimpleGraph.fromEdgeSet_adj]
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨x, y, hxy, he⟩ | he, -⟩
      · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨x, y, hxy, rfl, rfl⟩
        · exact Or.inl ⟨y, x, hxy.symm, rfl, rfl⟩
      · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · rintro (⟨x, y, hxy, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · refine ⟨Or.inl ⟨x, y, hxy, rfl⟩, fun h => ?_⟩
        have hx := (hJ.1 x y hxy).1
        have hy := (hJ.1 x y hxy).2
        exact J.ne_of_adj hxy (congrArg Subtype.val (hpinj ⟨x, hx⟩ ⟨y, hy⟩ h))
      · exact ⟨Or.inr rfl, hzAB⟩
      · exact ⟨Or.inr (Sym2.eq_swap), hzAB.symm⟩
  have hFend' : ∀ v, (∃ u, F.Adj v u) ↔ v ∈ Fend := by
    intro v
    rw [hFendmem]
    constructor
    · rintro ⟨u, hu⟩
      rcases (hFadj v u).1 hu with ⟨x, y, hxy, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨⟨x, (hJ.1 x y hxy).1⟩, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (⟨x, rfl⟩ | rfl | rfl)
      · obtain ⟨y, hy⟩ := (hJ.2 x x.2).exists
        exact ⟨port y, (hFadj _ _).2 (Or.inl ⟨x, y, hy, rfl, rfl⟩)⟩
      · exact ⟨zB, (hFadj _ _).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · exact ⟨zA, (hFadj _ _).2 (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  have hFm : ∀ u v v', F.Adj u v → F.Adj u v' → v = v' := by
    intro u v v' h1 h2
    rcases (hFadj u v).1 h1 with ⟨x, y, hxy, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases (hFadj _ v').1 h2 with ⟨x', y', hxy', he, rfl⟩ | ⟨he, rfl⟩ | ⟨he, rfl⟩
    · have hx := (hJ.1 x y hxy).1
      have hx' := (hJ.1 x' y' hxy').1
      have := congrArg Subtype.val (hpinj ⟨x, hx⟩ ⟨x', hx'⟩ he)
      simp only at this
      subst this
      rw [(hJ.2 x hx).unique hxy hxy']
    · exact absurd he (hpz ⟨x, (hJ.1 x y hxy).1⟩).1
    · exact absurd he (hpz ⟨x, (hJ.1 x y hxy).1⟩).2
    · exact absurd he.symm (hpz ⟨x', (hJ.1 x' y' hxy').1⟩).1
    · rfl
    · exact absurd he hzAB
    · exact absurd he.symm (hpz ⟨x', (hJ.1 x' y' hxy').1⟩).2
    · exact absurd he hzAB.symm
    · rfl
  -- the path system
  have hA : {v | ∃ j, v ∈ (p j).support} = (↑Rem ∪ ↑Fend : Set V) := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_union, Finset.mem_coe]
    constructor
    · rintro ⟨j, hj⟩
      by_cases hF : v ∈ Fend
      · exact Or.inr hF
      · refine Or.inl ((hRem v).2 ⟨?_, hF⟩)
        rcases j with _ | x
        · exact Or.inr hj
        · exact Or.inl ⟨x, hj⟩
    · rintro (h | h)
      · rcases ((hRem v).1 h).1 with ⟨x, hx⟩ | hx
        · exact ⟨some x, hx⟩
        · exact ⟨none, hx⟩
      · rcases (hFendmem v).1 h with ⟨x, rfl⟩ | rfl | rfl
        · exact ⟨some x, (patt x).end_mem_support⟩
        · exact ⟨none, pd.start_mem_support⟩
        · exact ⟨none, pd.end_mem_support⟩
  have hT : {v | ∃ j, v = a j ∨ v = b j} = (↑E ∪ ↑Fend : Set V) := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_union, Finset.mem_coe]
    constructor
    · rintro ⟨_ | x, rfl | rfl⟩
      · exact Or.inr ((hFendmem _).2 (Or.inr (Or.inl rfl)))
      · exact Or.inr ((hFendmem _).2 (Or.inr (Or.inr rfl)))
      · exact Or.inl x.2
      · exact Or.inr ((hFendmem _).2 (Or.inl ⟨x, rfl⟩))
    · rintro (h | h)
      · exact ⟨some ⟨v, h⟩, Or.inl rfl⟩
      · rcases (hFendmem v).1 h with ⟨x, rfl⟩ | rfl | rfl
        · exact ⟨some x, Or.inr rfl⟩
        · exact ⟨none, Or.inl rfl⟩
        · exact ⟨none, Or.inr rfl⟩
  rw [hA, hT] at hsys
  rw [← hXX] at hle hsys hreach
  have hERem : E ⊆ Rem := by
    intro x hx
    refine (hRem x).2 ⟨Or.inl ⟨⟨x, hx⟩, (patt ⟨x, hx⟩).start_mem_support⟩, fun hF => ?_⟩
    rcases (hFendmem x).1 hF with ⟨y, rfl⟩ | rfl | rfl
    · exact hportE y y.2 hx
    · exact hzA hx
    · exact hzB hx
  refine ⟨hFend', hFm, hle, hsys, ?_, hERem, ?_, ?_⟩
  · -- every expansion edge has an end in `Rem`
    intro u v huv
    rw [hXX, SimpleGraph.fromEdgeSet_adj] at huv
    obtain ⟨⟨j, hj⟩, -⟩ := huv
    rw [← SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges, SimpleGraph.Walk.toSubgraph_adj_iff]
      at hj
    obtain ⟨i, he, hi⟩ := hj
    have key : (p j).getVert i ∈ Rem ∨ (p j).getVert (i + 1) ∈ Rem := by
      rcases j with _ | x
      · have hsupp : ∀ n, pd.getVert n ∈ pd.support := fun n => pd.getVert_mem_support n
        by_cases hi0 : i = 0
        · right
          subst hi0
          refine (hRem _).2 ⟨Or.inr (hsupp 1), hnotF_pd _ (hsupp 1) ?_ ?_⟩
          · intro h
            have := (hpd.getVert_eq_start_iff (by omega)).1 h
            omega
          · intro h
            have := (hpd.getVert_eq_end_iff (by omega)).1 h
            omega
        · left
          refine (hRem _).2 ⟨Or.inr (hsupp i), hnotF_pd _ (hsupp i) ?_ ?_⟩
          · intro h
            exact hi0 ((hpd.getVert_eq_start_iff (by exact hi.le)).1 h)
          · intro h
            have := (hpd.getVert_eq_end_iff (by exact hi.le)).1 h
            change i < pd.length at hi
            omega
      · left
        have hsupp := (patt x).getVert_mem_support i
        refine (hRem _).2 ⟨Or.inl ⟨x, hsupp⟩, hnotF_att x _ hsupp ?_⟩
        intro h
        have := ((hpatt x).getVert_eq_end_iff (by exact hi.le)).1 h
        change i < (patt x).length at hi
        omega
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact key
    · rw [← h1, ← h2]; exact key.symm
  · -- formal edges are realized in `X ⊔ J`
    intro u v huv
    rcases (hFadj u v).1 huv with ⟨x, y, hxy, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hx := (hJ.1 x y hxy).1
      have hy := (hJ.1 x y hxy).2
      have r1 : X.Reachable (port x) x := hreach (some ⟨x, hx⟩) _ (patt ⟨x, hx⟩).end_mem_support
      have r2 : X.Reachable (port y) y := hreach (some ⟨y, hy⟩) _ (patt ⟨y, hy⟩).end_mem_support
      exact ((r1.mono le_sup_left).trans (SimpleGraph.Adj.reachable
        (show (X ⊔ J).Adj x y from Or.inr hxy))).trans (r2.mono le_sup_left).symm
    · exact ((hreach none _ pd.end_mem_support).mono le_sup_left).symm
    · exact (hreach none _ pd.end_mem_support).mono le_sup_left
  · -- every removed vertex reaches a formal end
    intro v hv
    rcases ((hRem v).1 hv).1 with ⟨x, hx⟩ | hx
    · have r1 : X.Reachable v x := hreach (some x) v hx
      have r2 : X.Reachable (port x) x := hreach (some x) _ (patt x).end_mem_support
      exact ⟨port x, (hFendmem _).2 (Or.inl ⟨x, rfl⟩), (r1.trans r2.symm).mono le_sup_left⟩
    · exact ⟨zA, (hFendmem _).2 (Or.inr (Or.inl rfl)), (hreach none v hx).mono le_sup_left⟩


/-- Monotonicity of `d(v, ·)`. -/
lemma degOn_mono [Fintype V] (H : WGraph V) (v : V) {S T : Finset V} (h : S ⊆ T) :
    H.degOn v S ≤ H.degOn v T :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun y _ _ => H.nonneg v y

/-- Number of vertices of colour `b` in `X`. -/
def ccount (col : V → Bool) (X : Finset V) (b : Bool) : ℕ := (X.filter fun x => col x = b).card

lemma ccount_union [DecidableEq V] (col : V → Bool) {X Y : Finset V} (h : Disjoint X Y) (b : Bool) :
    ccount col (X ∪ Y) b = ccount col X b + ccount col Y b := by
  unfold ccount
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

lemma ccount_sdiff [DecidableEq V] (col : V → Bool) {X Y : Finset V} (h : Y ⊆ X) (b : Bool) :
    ccount col (X \ Y) b + ccount col Y b = ccount col X b := by
  rw [← ccount_union col Finset.sdiff_disjoint, Finset.sdiff_union_of_subset h]

lemma card_eq_ccount (col : V → Bool) (X : Finset V) :
    X.card = ccount col X true + ccount col X false := by
  unfold ccount
  rw [← Finset.card_filter_add_card_filter_not (s := X) (fun x => col x = true)]
  congr 2

lemma ccount_swap [DecidableEq V] (col : V → Bool) {X : Finset V} {d z : V} (hd : d ∈ X)
    (hz : z ∉ X) (hc : col d = col z) (b : Bool) :
    ccount col (insert z (X.erase d)) b = ccount col X b := by
  unfold ccount
  rw [Finset.filter_insert, Finset.filter_erase]
  by_cases h : col z = b
  · rw [ite_eq_left h, Finset.card_insert_of_notMem (by simp [hz]),
      Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨hd, hc.trans h⟩)]
    have : 0 < (X.filter fun x => col x = b).card :=
      Finset.card_pos.2 ⟨d, Finset.mem_filter.2 ⟨hd, hc.trans h⟩⟩
    omega
  · rw [ite_eq_right h, Finset.erase_eq_of_notMem (by simp [hc, h])]

end General

/-! ### Data of the initial partition -/

/-- The cells of the initial partition of §3.3: the endpoint set `E`, the reservoirs `R₁`
(`att`, attachments), `Q` (`rtr`, router connections), `C` (`cyc`, short cycles), `Z` (`div`,
divisibility), the layers `I` (`inp`), `O` (`out`), `U` (`lu`), `V` (`lv`), and the pool. -/
inductive Cell
  | ends | att | rtr | cyc | div | inp | out | lu | lv | pool
  deriving DecidableEq

variable {V : Type*}

/-- The vertices with a given label. -/
def cellSet [Fintype V] (lab : V → Cell) (c : Cell) : Finset V :=
  univ.filter fun x => lab x = c

@[simp] lemma mem_cellSet [Fintype V] {lab : V → Cell} {c : Cell} {x : V} :
    x ∈ cellSet lab c ↔ lab x = c := by
  simp [cellSet]

lemma cellSet_disjoint [Fintype V] (lab : V → Cell) {c c' : Cell} (h : c ≠ c') :
    Disjoint (cellSet lab c) (cellSet lab c') :=
  Finset.disjoint_left.2 fun _ h1 h2 => h ((mem_cellSet.1 h1).symm.trans (mem_cellSet.1 h2))

/-- The colour class `b` of the graph `H₀ = H - E`. -/
def classOf [Fintype V] [DecidableEq V] (E : Finset V) (col : V → Bool) (b : Bool) : Finset V :=
  (univ \ E).filter fun x => col x = b

/-- Centred biadjacency entry of `H₀ = H[A₀ ∪ B₀]` (Lemma 2.3):
`F_{xy} = a_{xy} - d₀(x) d₀(y) / e(H₀)` for `x ∈ A₀`, `y ∈ B₀`. -/
noncomputable def centred [Fintype V] (H : WGraph V) (A₀ B₀ : Finset V) (x y : V) : ℝ :=
  H.w x y - H.degOn x B₀ * H.degOn y A₀ / H.edgeWeight A₀ B₀

/-- **The one-sided events (2.9)** for a fixed block `U ⊆ A₀` of `pN₀` rows of the bipartite
host `H₀ = H[A₀ ∪ B₀]` (degrees `(1 ± η₀) D`, gap `σ₀`): `‖F[U, B₀]‖ ≤ √p ‖F‖ + K √(DL)`,
column norms `‖F[U, {y}]‖² ≤ K p D`, and `d(y, U) = (1 ± δσ₀) p D` for every `y ∈ B₀`. The
operator norm is written with the quadratic form, and `‖F‖` is replaced by its bound
`(1 + η₀)(1 - σ₀) D ≤ (1 - σ₀/2) D` (valid for `η₀ ≤ σ₀/2`), which is the only way it is used. -/
structure OneSided [Fintype V] (H : WGraph V) (A₀ B₀ U : Finset V) (p D σ₀ L K δ : ℝ) :
    Prop where
  norm_le : ∀ v : V → ℝ, ∑ x ∈ U, (∑ y ∈ B₀, centred H A₀ B₀ x y * v y) ^ 2 ≤
    (Real.sqrt p * (1 - σ₀ / 2) * D + K * Real.sqrt (D * L)) ^ 2 * ∑ y ∈ B₀, v y ^ 2
  col_le : ∀ y ∈ B₀, ∑ x ∈ U, centred H A₀ B₀ x y ^ 2 ≤ K * p * D
  deg_near : ∀ y ∈ B₀, |H.degOn y U - p * D| ≤ δ * σ₀ * p * D

/-- The filler of a special layer: the layer minus its dummy and the new ports. -/
def filler [Fintype V] [DecidableEq V] (lab : V → Cell) (c : Cell) (d : V) (E : Finset V)
    (port : V → V) : Finset V :=
  ((cellSet lab c).erase d) \ E.image port

/-- The envelope `B` of (3.10), without `E`: all reserved vertices outside the pool. -/
def envelope [Fintype V] (lab : V → Cell) : Finset V :=
  univ.filter fun x => lab x ≠ Cell.pool ∧ lab x ≠ Cell.ends

/-- **The initial partition of §3.3** and all the events imposed on it (before any path is
chosen), in the deterministic form in which the later steps use them. The constants are those
of the later steps: `εR` (Lemma 3.4 in `Q`), `c₇, C₇` (Lemma 3.7 in `C`), `εA` (Lemma 3.4 in
`R₁`), `cdfs` (depth-first search in `Z`), `δ, κ, K, CF` (fresh layers). `N₀ = N - ℓ`. The
colour `true` is the paper's positive class `A`. -/
structure InitPartition [Fintype V] [DecidableEq V] (εR c₇ C₇ εA cdfs δ κ K CF : ℝ)
    (H : WGraph V) (col : V → Bool) (E : Finset V) (J : SimpleGraph V) (N₀ : ℕ)
    (D σ L g : ℝ) where
  /-- The cell of each vertex. -/
  lab : V → Cell
  /-- Half the layer width `w = 2m`. -/
  m : ℕ
  /-- The orientation of `J`. -/
  tail : V → Bool
  /-- The new port of each original endpoint. -/
  port : V → V
  /-- The dummy of `U ∩ A`. -/
  dA : V
  /-- The dummy of `V ∩ B`. -/
  dB : V
  /-- The perfect matching of the fillers of the special transition. -/
  μ : V → V
  /-- Degree scale in `C`. -/
  DC : ℝ
  /-- Maximum degree in `Q`. -/
  ΔQ : ℝ
  /-- Gap in `Q`. -/
  σQ : ℝ
  /-- Maximum degree in `R₁`. -/
  Δ₁ : ℝ
  /-- Gap in `R₁`. -/
  σ₁ : ℝ
  /-- Degree scale in `Z`. -/
  DZ : ℝ
  /-- Gap in `Z`. -/
  σZ : ℝ
  lab_ends : ∀ x, lab x = Cell.ends ↔ x ∈ E
  one_le_m : 1 ≤ m
  block_card : ∀ c b, (c = Cell.inp ∨ c = Cell.out ∨ c = Cell.lu ∨ c = Cell.lv) →
    ((cellSet lab c).filter fun x => col x = b).card = m
  -- short cycles in `C` (Lemma 3.7, (3.7))
  cyc_deg : (H.induce (cellSet lab Cell.cyc)).DegBetween (1 / 2 * DC) (2 * DC)
  cyc_DC : C₇ ≤ DC
  cyc_girth : C₇ * Real.log (2 * (cellSet lab Cell.cyc).card) / Real.log (2 + DC) ≤ g
  cyc_many : (2 * m : ℝ) ≤ c₇ * (cellSet lab Cell.cyc).card / g
  -- the router reservoir `Q` (Lemma 3.4)
  rtr_pos : 0 < ΔQ
  rtr_deg : (H.induce (cellSet lab Cell.rtr)).DegBetween (1 / 2 * ΔQ) ΔQ
  rtr_gap : (H.induce (cellSet lab Cell.rtr)).HasGap σQ
  rtr_σ : 0 < σQ ∧ σQ ≤ 1
  rtr_log : Real.log (2 * (cellSet lab Cell.rtr).card) ≤ L
  rtr_ends : ∀ x, (lab x = Cell.cyc ∨ lab x = Cell.inp ∨ lab x = Cell.out) →
    1 / 4 * ΔQ ≤ H.degOn x (cellSet lab Cell.rtr)
  rtr_sparse : ∀ v ∈ cellSet lab Cell.rtr,
    H.degOn v (cellSet lab Cell.cyc ∪ cellSet lab Cell.inp ∪ cellSet lab Cell.out) ≤
      εR * σQ ^ (3 / 2 : ℝ) * ΔQ / L
  -- the attachment reservoir `R₁` (Lemma 3.4, (3.9))
  att_pos : 0 < Δ₁
  att_deg : (H.induce (cellSet lab Cell.att)).DegBetween (1 / 2 * Δ₁) Δ₁
  att_gap : (H.induce (cellSet lab Cell.att)).HasGap σ₁
  att_σ : 0 < σ₁ ∧ σ₁ ≤ 1
  att_log : Real.log (2 * (cellSet lab Cell.att).card) ≤ L
  att_ends : ∀ x ∈ E ∪ E.image port, 1 / 4 * Δ₁ ≤ H.degOn x (cellSet lab Cell.att)
  att_sparse : ∀ v ∈ cellSet lab Cell.att,
    H.degOn v (E ∪ E.image port) ≤ εA * σ₁ ^ (3 / 2 : ℝ) * Δ₁ / L
  -- orientation of `J` and the new ports
  tail_adj : ∀ x y, J.Adj x y → tail x ≠ tail y
  port_col : ∀ x ∈ E, col (port x) = col x
  port_inj : Set.InjOn port ↑E
  port_tail : ∀ x ∈ E, tail x = true → lab (port x) = Cell.lu ∧ port x ≠ dA
  port_head : ∀ x ∈ E, tail x = false → lab (port x) = Cell.lv ∧ port x ≠ dB
  -- the dummies
  dA_lab : lab dA = Cell.lu
  dA_col : col dA = true
  dB_lab : lab dB = Cell.lv
  dB_col : col dB = false
  -- perfect matching of the filler blocks of the special transition (without dummies)
  μ_bij : Set.BijOn μ ↑(filler lab Cell.lu dA E port) ↑(filler lab Cell.lv dB E port)
  μ_adj : ∀ u ∈ filler lab Cell.lu dA E port, H.supp.Adj u (μ u)
  -- the divisibility reservoir `Z`
  div_pos : 0 < DZ
  div_deg : (H.induce (cellSet lab Cell.div)).DegBetween (1 / 2 * DZ) (2 * DZ)
  div_gap : (H.induce (cellSet lab Cell.div)).HasGap σZ
  div_σ : 0 < σZ ∧ σZ ≤ 1
  div_long : (2 * m + 2 : ℝ) ≤ cdfs * σZ * (cellSet lab Cell.div).card
  -- the one-sided events (2.9) for every colour block of `I, O, U, V`
  one_sided : ∀ c b, (c = Cell.inp ∨ c = Cell.out ∨ c = Cell.lu ∨ c = Cell.lv) →
    OneSided H (classOf E col b) (classOf E col (!b)) ((cellSet lab c).filter fun x => col x = b)
      ((m : ℝ) / N₀) D (σ / 2) L K δ
  -- (3.8)
  layer_large : CF * (σ / 2) ^ (-(2 : ℝ)) * L ≤ (m : ℝ) / N₀ * D
  -- the envelope (3.10)
  env_deg : ∀ v, H.degOn v (envelope lab) ≤ κ * (σ / 2) * D
  env_card : ∀ b, (((envelope lab).filter fun x => col x = b).card : ℝ) ≤ κ * (σ / 2) * N₀
  pool_large : ∀ b, 5 * m ≤ ((cellSet lab Cell.pool).filter fun x => col x = b).card

/-! ### The steps of §3.3 -/

lemma hasGap_mono {W : Type*} [Fintype W] (H : WGraph W) {s s' : ℝ} (h : H.HasGap s)
    (hs : s' ≤ s) : H.HasGap s' := by
  intro f
  obtain ⟨z, hz⟩ := h f
  refine ⟨z, le_trans ?_ hz⟩
  have : 0 ≤ ∑ x, H.deg x * (f x - z) ^ 2 := Finset.sum_nonneg fun x _ =>
    mul_nonneg (Finset.sum_nonneg fun y _ => H.nonneg x y) (sq_nonneg _)
  nlinarith

lemma induce_deg [Fintype V] [DecidableEq V] (H : WGraph V) (E : Finset V) (x : ↥(univ \ E)) :
    (H.induce (univ \ E)).deg x = H.deg x - H.degOn x E := by
  unfold WGraph.deg WGraph.degOn WGraph.induce
  simp only
  rw [Finset.sum_coe_sort (univ \ E) (fun y => H.w x y),
    Finset.sum_sdiff_eq_sub (Finset.subset_univ E)]

lemma col_walk {W : Type*} (H : WGraph W) (col : W → Bool) (hbip : H.IsBipartiteWith col)
    {a b : W} (w : H.supp.Walk a b) :
    col b = (if Even w.length then col a else !col a) := by
  induction w with
  | nil => simp
  | @cons x y z h w ih =>
    have hxy : col y = !col x := by
      have := hbip x y h
      cases hx : col x <;> cases hy : col y <;> simp_all
    rw [ih, hxy, SimpleGraph.Walk.length_cons]
    by_cases he : Even w.length
    · have : ¬ Even (w.length + 1) := by rw [Nat.even_add_one]; exact not_not.2 he
      simp [he, this]
    · have : Even (w.length + 1) := by rw [Nat.even_add_one]; exact he
      simp [he, this]

/-- **`T3.2a` (deletion of `E`).** By Lemma 2.1, `H₀ = H - E` keeps degrees `(1 ± 2cσ) D` and
gap `σ / 2`, when `η ≤ cσ` and `max_v d(v, E) ≤ c σ^{5/2} D / L` with `c` small. -/
theorem deletion_step :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (E : Finset V)
      (c η D σ L : ℝ), 0 < c → c ≤ c₀ → 0 < D → H.DegNear D η → η ≤ c * σ → H.HasGap σ →
      0 < σ → σ ≤ 1 → 10 ≤ L → (∀ x, H.degOn x E ≤ c * σ ^ (5 / 2 : ℝ) * D / L) →
      (H.induce (univ \ E)).DegNear D (2 * c * σ) ∧ (H.induce (univ \ E)).HasGap (σ / 2) := by
  obtain ⟨c', C', hc', hC', hdel⟩ := hasGap_of_deletion.{u} (1 / 2) 2 (by norm_num) (by norm_num)
  refine ⟨min (1 / 2) (min c' (5 / C')), lt_min (by norm_num) (lt_min hc' (by positivity)), ?_⟩
  intro V _ _ H E c η D σ L hc hcc hD hdeg hη hgap hσ hσ1 hL hEdeg
  have hc1 : c ≤ 1 / 2 := hcc.trans (min_le_left _ _)
  have hc2 : c ≤ c' := hcc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc3 : c ≤ 5 / C' := hcc.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hs : σ ^ (5 / 2 : ℝ) ≤ σ := by
    calc σ ^ (5 / 2 : ℝ) ≤ σ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hσ hσ1 (by norm_num)
      _ = σ := Real.rpow_one σ
  have hs0 : 0 ≤ σ ^ (5 / 2 : ℝ) := Real.rpow_nonneg hσ.le _
  have hL0 : 0 < L := by linarith
  have hβ0 : 0 ≤ c * σ ^ (5 / 2 : ℝ) * D / L := by positivity
  have hβσ : c * σ ^ (5 / 2 : ℝ) * D / L ≤ c * σ * D / 10 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    have h1 : c * σ ^ (5 / 2 : ℝ) * D ≤ c * σ * D := by gcongr
    have h2 : 0 ≤ c * σ * D := by positivity
    nlinarith
  have hEnn : ∀ x, 0 ≤ H.degOn x E := fun x => Finset.sum_nonneg fun y _ => H.nonneg x y
  have hcσ : c * σ ≤ 1 / 2 := by nlinarith
  refine ⟨fun x => ?_, ?_⟩
  · rw [induce_deg]
    have h1 := abs_le.1 (hdeg x)
    have h2 := hEdeg x
    have h3 := hEnn x
    have h4 : η * D ≤ c * σ * D := by nlinarith
    rw [abs_le]
    constructor <;> nlinarith
  · have hDB : H.DegBetween (1 / 2 * D) (2 * D) := by
      intro x
      have h1 := abs_le.1 (hdeg x)
      have h4 : η * D ≤ 1 / 2 * D := by nlinarith
      constructor <;> linarith
    have hg := hdel H (univ \ E) (H.induce (univ \ E)) D σ (c * σ ^ (5 / 2 : ℝ) * D / L) hD hDB
      hgap (fun x y => le_rfl) (fun x => by rw [induce_deg]; linarith [hEdeg x]) hβ0
      (by have h5 : c * σ ≤ c' := by nlinarith
          have h6 : c * σ * D ≤ c' * D := mul_le_mul_of_nonneg_right h5 hD.le
          have h7 : 0 ≤ c * σ * D := by positivity
          linarith)
    refine hasGap_mono _ hg ?_
    have h1 : C' * (c * σ ^ (5 / 2 : ℝ) * D / L) / D ≤ C' * (c * σ * D / 10) / D := by gcongr
    have h2 : C' * (c * σ * D / 10) / D = C' * c * σ / 10 := by field_simp
    have h3 : C' * c ≤ 5 := by rw [le_div_iff₀ hC'] at hc3; linarith
    have h4 : C' * c * σ / 10 ≤ σ / 2 := by nlinarith
    linarith


/-- The statement of `T3.2c` for fixed constants `ε` (Lemma 3.4) and `c₇, C₇` (Lemma 3.7). -/
def RouterSpec (ω ε c₇ C₇ : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (col : V → Bool)
    (C Q I O : Finset V) (w : ℕ) (DC Δ σQ L g : ℝ),
    H.IsBipartiteWith col → H.WeightsIn ω →
    Disjoint C Q → Disjoint C I → Disjoint C O → Disjoint Q I → Disjoint Q O →
    Disjoint I O → I.card = w → O.card = w → 2 ≤ w →
    (H.induce C).DegBetween (1 / 2 * DC) (2 * DC) → C₇ ≤ DC →
    C₇ * Real.log (2 * C.card) / Real.log (2 + DC) ≤ g → (w : ℝ) ≤ c₇ * C.card / g →
    0 < Δ → (H.induce Q).DegBetween (1 / 2 * Δ) Δ → (H.induce Q).HasGap σQ → 0 < σQ →
    σQ ≤ 1 → Real.log (2 * Q.card) ≤ L →
    (∀ x ∈ C ∪ I ∪ O, 1 / 4 * Δ ≤ H.degOn x Q) →
    (∀ v ∈ Q, H.degOn v (C ∪ I ∪ O) ≤ ε * σQ ^ (3 / 2 : ℝ) * Δ / L) →
    ∃ A : Finset V, I ∪ O ⊆ A ∧ A ⊆ C ∪ Q ∪ I ∪ O ∧ IsHamRouter H.supp ↑A ↑I ↑O

/-- The statement of `T3.2e` for a fixed constant `c`. -/
def DivSpec (c : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (col : V → Bool)
    (Z : Finset V) (DZ σZ : ℝ) (r : ℕ),
    H.IsBipartiteWith col → 0 < DZ → (H.induce Z).DegBetween (1 / 2 * DZ) (2 * DZ) →
    (H.induce Z).HasGap σZ → 0 < σZ → σZ ≤ 1 → (2 * r + 2 : ℝ) ≤ c * σZ * Z.card →
    ∃ x y, ∃ p : H.supp.Walk x y, p.IsPath ∧ p.length = 2 * r + 1 ∧ col x = true ∧
      col y = false ∧ ∀ v ∈ p.support, v ∈ Z

/-- **`T3.2e` (divisibility).** If `H[Z]` has comparable degrees and gap `σZ`, and
`2r + 2 ≤ c σZ |Z|`, then `Z` contains a path of length `2r + 1`, from a vertex of colour `true`
to a vertex of colour `false` (the depth-first-search observation of §3.2). -/
theorem divisibility_step : ∃ c : ℝ, 0 < c ∧ DivSpec.{u} c := by
  obtain ⟨c, hc, hlong⟩ := exists_long_path.{u} (1 / 2) 2 (by norm_num) (by norm_num)
  refine ⟨c, hc, ?_⟩
  intro V _ _ H col Z DZ σZ r hbip hDZ hdeg hgap hσ hσ1 hlen
  have hZ : 0 < Z.card := by
    rcases Nat.eq_zero_or_pos Z.card with h | h
    · rw [h] at hlen; simp at hlen; linarith
    · exact h
  obtain ⟨z0, hz0⟩ := Finset.card_pos.1 hZ
  have : Nonempty ↥Z := ⟨⟨z0, hz0⟩⟩
  obtain ⟨x, y, p, hp, hplen⟩ := hlong (H.induce Z) DZ σZ hDZ hdeg hgap hσ hσ1
  let f : (H.induce Z).supp →g H.supp := ⟨Subtype.val, fun {a b} h => h⟩
  have hq : (p.map f).IsPath := SimpleGraph.Walk.IsPath.map Subtype.val_injective hp
  have hqlen : 2 * r + 1 ≤ (p.map f).length := by
    rw [Fintype.card_coe] at hplen
    have h2 : (2 * r + 2 : ℝ) ≤ p.support.length := hlen.trans hplen
    rw [SimpleGraph.Walk.length_support] at h2
    rw [SimpleGraph.Walk.length_map]
    have : 2 * r + 2 ≤ p.length + 1 := by exact_mod_cast h2
    omega
  set q := (p.map f).take (2 * r + 1) with hqdef
  have hq' : q.IsPath := hq.take _
  have hq'len : q.length = 2 * r + 1 := by
    rw [hqdef, SimpleGraph.Walk.take_length]; omega
  have hq'Z : ∀ v ∈ q.support, v ∈ Z := by
    intro v hv
    rw [hqdef, SimpleGraph.Walk.support_take] at hv
    have hv' := List.mem_of_mem_take hv
    rw [SimpleGraph.Walk.support_map] at hv'
    obtain ⟨w, _, rfl⟩ := List.mem_map.1 hv'
    exact w.2
  have hodd : ¬ Even q.length := by rw [hq'len]; exact Nat.not_even_two_mul_add_one r
  have hc := col_walk H col hbip q
  rw [ite_eq_right hodd] at hc
  cases hs : col (f x)
  · refine ⟨_, _, q.reverse, hq'.reverse, by rw [SimpleGraph.Walk.length_reverse, hq'len], ?_,
      hs, fun v hv => hq'Z v (by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv)⟩
    rw [hc, hs]; rfl
  · refine ⟨_, _, q, hq', hq'len, hs, ?_, hq'Z⟩
    rw [hc, hs]; rfl


/-- The statement of `T3.2f` for fixed constants. -/
def FreshSpec (ω cF δ κ K CF : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (col : V → Bool) (E : Finset V)
    (O I U W U' W' P S : Finset V) (N₀ m : ℕ) (η₀ D σ₀ L : ℝ) (dA dB zA zB : V)
    (τ : V → V),
    H.IsBipartiteWith col → H.WeightsIn ω →
    (classOf E col true).card = N₀ → (classOf E col false).card = N₀ →
    (H.induce (univ \ E)).DegNear D η₀ → (H.induce (univ \ E)).HasGap σ₀ →
    0 < σ₀ → σ₀ ≤ 1 → 0 ≤ η₀ → η₀ ≤ cF * σ₀ → 0 < D → Real.log (2 * N₀) ≤ L → 10 ≤ L →
    1 ≤ m →
    (∀ X : Finset V, (X = O ∨ X = I ∨ X = U ∨ X = W) → Disjoint X E ∧
      ∀ b, (X.filter fun x => col x = b).card = m ∧
        OneSided H (classOf E col b) (classOf E col (!b)) (X.filter fun x => col x = b)
          ((m : ℝ) / N₀) D σ₀ L K δ) →
    Disjoint O I → Disjoint O U → Disjoint O W → Disjoint I U → Disjoint I W →
    Disjoint U W →
    CF * σ₀ ^ (-(2 : ℝ)) * L ≤ (m : ℝ) / N₀ * D →
    dA ∈ U → col dA = true → dB ∈ W → col dB = false →
    zA ∉ E → col zA = true → zB ∉ E → col zB = false →
    zA ∉ O ∪ I ∪ U ∪ W → zB ∉ O ∪ I ∪ U ∪ W →
    U' = insert zA (U.erase dA) → W' = insert zB (W.erase dB) →
    Disjoint P E → Disjoint P (O ∪ I ∪ U' ∪ W') →
    (P.filter fun x => col x = true).card = (P.filter fun x => col x = false).card →
    m ∣ (P.filter fun x => col x = true).card →
    2 * m ≤ (P.filter fun x => col x = true).card →
    (univ \ E) \ P ⊆ S → (∀ v, H.degOn v S ≤ κ * σ₀ * D) →
    (∀ b, ((S.filter fun x => col x = b).card : ℝ) ≤ κ * σ₀ * N₀) →
    Set.BijOn τ ↑U' ↑W' →
    ∃ k : ℕ, 4 ≤ k ∧ ∃ φ : Fin (2 * m) → ℕ → V,
      (∀ i j i' j', j ≤ k → j' ≤ k → φ i j = φ i' j' → i = i' ∧ j = j') ∧
      (∀ v, v ∈ O ↔ ∃ i, φ i 0 = v) ∧ (∀ v, v ∈ I ↔ ∃ i, φ i k = v) ∧
      (∀ v, v ∈ U' ↔ ∃ i, φ i 2 = v) ∧ (∀ v, v ∈ W' ↔ ∃ i, φ i 3 = v) ∧
      (∀ v, v ∈ P ↔ ∃ i j, (j = 1 ∨ (4 ≤ j ∧ j < k)) ∧ φ i j = v) ∧
      (∀ i, φ i 3 = τ (φ i 2)) ∧
      (∀ i j, j < k → j ≠ 2 → H.supp.Adj (φ i j) (φ i (j + 1)))

/-- The conclusion of Lemma 3.4 (`spectral_connection`) for fixed constants, with the index
type in the same universe. -/
def ConnSpec (a c C : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : WGraph V) (R : Finset V) (Δ σ L β : ℝ)
    {κ : Type u} [Fintype κ] [DecidableEq κ] (pa pb : κ → V),
    0 < Δ → (H.induce R).DegBetween (a * Δ) Δ → (H.induce R).HasGap σ → 0 < σ → σ ≤ 1 →
    Real.log (2 * R.card) ≤ L → 0 < β → β < 1 →
    (∀ j, pa j ∉ R ∧ pb j ∉ R ∧ pa j ≠ pb j) →
    (∀ x, (univ.filter fun j => pa j = x ∨ pb j = x).card ≤ 10) →
    (∀ j, β * Δ ≤ H.degOn (pa j) R ∧ β * Δ ≤ H.degOn (pb j) R) →
    (∀ v ∈ R, H.degOn v (univ.image pa ∪ univ.image pb) ≤ c * β * σ ^ (3 / 2 : ℝ) * Δ / L) →
    ∃ p : ∀ j, H.supp.Walk (pa j) (pb j),
      (∀ j, (p j).IsPath) ∧ (∀ j, ((p j).length : ℝ) ≤ C * L / Real.sqrt σ) ∧
      (∀ j, ∀ z ∈ (p j).support, z ≠ pa j → z ≠ pb j → z ∈ R) ∧
      (∀ j k, j ≠ k → ∀ z ∈ R, z ∈ (p j).support → z ∉ (p k).support)

lemma hyp_mono {V : Type*} [Fintype V] {ω c c' C C' : ℝ} {H : WGraph V} {col : V → Bool}
    {N ℓ : ℕ} {η D σ L g : ℝ} {E : Finset V}
    (h : LocalAbsorptionHyp ω c' C' H col N ℓ η D σ L g E) (hc : c' ≤ c) (hC : C ≤ C')
    (hC0 : 0 < C) : LocalAbsorptionHyp ω c C H col N ℓ η D σ L g E := by
  have hσ := h.sigma_pos
  have hL : 0 < L := by linarith [h.ten_le]
  have hg : 0 < g := by linarith [h.four_le]
  have hs9 : 0 < σ ^ (-(9 / 2 : ℝ)) := Real.rpow_pos_of_pos hσ _
  have hs5 : 0 < σ ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hσ _
  have hD : 0 ≤ D := by
    have := h.deg_large
    have : 0 ≤ C' * σ ^ (-(9 / 2 : ℝ)) * L ^ 2 * g := by
      have : 0 < C' := hC0.trans_le hC
      positivity
    linarith
  refine { h with
    eta_le := ?_
    deg_large := ?_
    girth_param := ?_
    ends_few := ?_
    ends_sparse := ?_ }
  · exact h.eta_le.trans (by nlinarith)
  · refine le_trans ?_ h.deg_large
    have : 0 ≤ σ ^ (-(9 / 2 : ℝ)) * L ^ 2 * g := by positivity
    nlinarith
  · refine le_trans ?_ h.girth_param
    have h0 : 0 ≤ σ ^ (5 / 2 : ℝ) * D / L := by positivity
    have hlog : 0 < Real.log (2 + σ ^ (5 / 2 : ℝ) * D / L) := Real.log_pos (by linarith)
    gcongr
  · refine h.ends_few.trans ?_
    have : 0 ≤ σ ^ (5 / 2 : ℝ) * N / (L * g) := by positivity
    calc c' * σ ^ (5 / 2 : ℝ) * N / (L * g) = c' * (σ ^ (5 / 2 : ℝ) * N / (L * g)) := by ring
      _ ≤ c * (σ ^ (5 / 2 : ℝ) * N / (L * g)) := by gcongr
      _ = c * σ ^ (5 / 2 : ℝ) * N / (L * g) := by ring
  · intro x
    refine (h.ends_sparse x).trans ?_
    have : 0 ≤ σ ^ (5 / 2 : ℝ) * D / L := by positivity
    calc c' * σ ^ (5 / 2 : ℝ) * D / L = c' * (σ ^ (5 / 2 : ℝ) * D / L) := by ring
      _ ≤ c * (σ ^ (5 / 2 : ℝ) * D / L) := by gcongr
      _ = c * σ ^ (5 / 2 : ℝ) * D / L := by ring

end LocalAbsorption

end Lovasz
