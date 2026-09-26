/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent)
-/
import Lovasz.Allocation
import Lovasz.CosetCuts
import Lovasz.TreePacking
import Lovasz.Watkins
import Lovasz.MutualNominations
import Lovasz.SignedCirculation
import Lovasz.Circulation
import Lovasz.SignedIntegrality
import Lovasz.Chernoff

/-!
# Proposition 6.1 — shared definitions and proved steps: the sparse connecting system

DAG node `P6.1` of `docs/BLUEPRINT.md` (Section 6 of the paper). Its proof uses label sampling,
the reservation estimates (6.5)–(6.6), Lemmas 6.2–6.4, cut counting (6.4), directional balance
(6.9), Lemma 4.4, the circulation criterion (4.6) and Lemma 4.1.

The proof is decomposed into the following steps (namespace `Lovasz.Connector`).

* `added_labels` (§6.1): `O(L)` labels generating `G`, whose lifts generate `G × C₂` when
  `X` is nonbipartite (doubling argument). Proved.
* `label_sampling` (§6.1, (6.2)): the sampled label classes. Stated (Chernoff).
* `reservation_estimates` (§6.1, (6.5)–(6.6)). Stated (Lemma 6.2, (6.4), exponential moments).
* `joint_union_bound` (§6.1): the union bound in the joint allocation/label experiment. Proved.
* `allocation_cuts` (Lemma 6.3). Stated.
* `directional_balance` ((6.9)–(6.11), (6.18)). Proved.
* `state_cut_count` (cut counting (6.4) for the state cuts, nonbipartite case). Proved.
* `bip_state_cuts` (state cuts in the bipartite case). Stated.
* `exists_matching` (§6.4, (6.13)–(6.17): Lemma 6.4 and the union bound). Stated.
* `connector_of_matching` (§6.5: the paths `P_H`, the circulation, Lemma 4.4, Lemma 4.1 and
  the final checks). Proved.
* `regime` (the parameter checks of §7 used here), `connector_of_outcome` and the final
  assembly `connecting_system`. Proved.

The contracted two-state digraph (4.5) of a set of physical edges is encoded edge by edge: a
physical edge `e` (oriented by `Quot.out`) with endpoints `x, y` in parts `π x, π y` and local
signs `sg x, sg y` gives the twin arcs `(π x, sg x) → (π y, ¬ sg y)` and
`(π y, sg y) → (π x, ¬ sg x)`. These are exactly the two lifts of `e` in the contracted
bipartite double cover of §6.2.
-/

universe u

noncomputable section

namespace Lovasz

open Finset Classical

namespace Connector

/-! ### The contracted two-state digraph -/

section Arcs

variable {G : Type u} {t : ℕ}

/-- Tail of the twin arc `b` of the physical edge `e` in the two-state digraph (4.5). -/
def arcTail (π : G → Fin t) (sg : G → Bool) (e : Sym2 G) : Bool → Fin t × Bool
  | false => (π e.out.1, sg e.out.1)
  | true => (π e.out.2, sg e.out.2)

/-- Head of the twin arc `b` of the physical edge `e` in the two-state digraph (4.5). -/
def arcHead (π : G → Fin t) (sg : G → Bool) (e : Sym2 G) : Bool → Fin t × Bool
  | false => (π e.out.2, !sg e.out.2)
  | true => (π e.out.1, !sg e.out.1)

/-- The number of twin arcs of the physical edge `e` leaving the state set `J`. -/
def outArcs (π : G → Fin t) (sg : G → Bool) (J : Finset (Fin t × Bool)) (e : Sym2 G) : ℕ :=
  (univ.filter fun b : Bool => arcTail π sg e b ∈ J ∧ arcHead π sg e b ∉ J).card

/-- The number of twin arcs of the physical edge `e` entering the state set `J`. -/
def inArcs (π : G → Fin t) (sg : G → Bool) (J : Finset (Fin t × Bool)) (e : Sym2 G) : ℕ :=
  (univ.filter fun b : Bool => arcHead π sg e b ∈ J ∧ arcTail π sg e b ∉ J).card

/-- `|δ⁺_{D(F)}(J)|`: arcs of the edges of `F` leaving the state set `J`. -/
def outCnt (π : G → Fin t) (sg : G → Bool) (J : Finset (Fin t × Bool)) (F : Finset (Sym2 G)) :
    ℕ :=
  ∑ e ∈ F, outArcs π sg J e

/-- `|δ⁻_{D(F)}(J)|`: arcs of the edges of `F` entering the state set `J`. -/
def inCnt (π : G → Fin t) (sg : G → Bool) (J : Finset (Fin t × Bool)) (F : Finset (Sym2 G)) :
    ℕ :=
  ∑ e ∈ F, inArcs π sg J e

/-- `|δ_{D(F)}(J)|`, counting both directions (the size of the lifted cut). -/
def cutCnt (π : G → Fin t) (sg : G → Bool) (J : Finset (Fin t × Bool)) (F : Finset (Sym2 G)) :
    ℕ :=
  outCnt π sg J F + inCnt π sg J F

/-- The arcs of the formal loops `P` (6.18): the reserved vertex `w` gives a same-sign loop at the
part `ι w` with sign `ls w`, whose two twin arcs are `(ι w, ls w) → (ι w, ¬ ls w)`. -/
def loopCnt (ι : G → Fin t) (ls : G → Bool) (J : Finset (Fin t × Bool)) (W : Finset G) : ℕ :=
  ∑ w ∈ W, if ((ι w, ls w) ∈ J ∧ (ι w, !ls w) ∉ J) ∨ ((ι w, !ls w) ∈ J ∧ (ι w, ls w) ∉ J)
    then 2 else 0

/-- The physical edge `e` crosses the ordinary part cut `I`. -/
def PartCross (π : G → Fin t) (I : Finset (Fin t)) (e : Sym2 G) : Prop :=
  (π e.out.1 ∈ I ∧ π e.out.2 ∉ I) ∨ (π e.out.2 ∈ I ∧ π e.out.1 ∉ I)

/-- The vertex set `V(R)` of a set of edges. -/
def vtx [Fintype G] (R : Finset (Sym2 G)) : Finset G := univ.filter fun v => ∃ e ∈ R, v ∈ e

lemma mem_vtx [Fintype G] {R : Finset (Sym2 G)} {v : G} : v ∈ vtx R ↔ ∃ e ∈ R, v ∈ e := by
  unfold vtx
  simp

lemma mk_out (e : Sym2 G) : s(e.out.1, e.out.2) = e := by
  rw [Sym2.mk, e.out_eq]

end Arcs

/-! ### Local signs, the graph `Y`, and the label experiment -/

section Setup

variable {G : Type u} [Group G]

/-- The local sign of `v` in its own part `π v`: `true` iff `g_{π v}⁻¹ v ∈ A⁺`. -/
def sgnOf (𝒜 : Allocation G) (Ap : Finset G) (π : G → Fin 𝒜.t) (v : G) : Bool :=
  decide ((𝒜.g (π v))⁻¹ * v ∈ Ap)

/-- The sign of the formal loop of the reserved vertex `w` at the part `ι w`: the common local
sign of the two neighbours `a_H, b_H` of `w` in the copy `F_{ι w}`, i.e. the sign opposite to
that of `w`. -/
def loopSgn (𝒜 : Allocation G) (Am : Finset G) (ι : G → Fin 𝒜.t) (w : G) : Bool :=
  decide ((𝒜.g (ι w))⁻¹ * w ∈ Am)

variable [DecidableEq G]

/-- `Y = X₀ - W`, where `X₀ = Cay(G, S₀)`. -/
def conY (S₀ W : Finset G) : SimpleGraph G where
  Adj x y := (cayleyGraph S₀).Adj x y ∧ x ∉ W ∧ y ∉ W
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- The lifts `(s, 1)` of the labels in the double cover `G × C₂`. -/
def liftSet (S : Finset G) : Set (G × Multiplicative (ZMod 2)) :=
  (fun s => (s, Multiplicative.ofAdd (1 : ZMod 2))) '' (S : Set G)

/-- The lifts of `S` generate `G × C₂`, i.e. the bipartite double cover of `Cay(G, S)` is
connected. For connected `Cay(G, S)` this says that `Cay(G, S)` is nonbipartite (§6.1). -/
def IsNonbip (S : Finset G) : Prop := Subgroup.closure (liftSet S) = ⊤

variable [Fintype G]

/-- A canonical representative of the inverse class `{s, s⁻¹}`. -/
def classRep (s : G) : G :=
  if Fintype.equivFin G s ≤ Fintype.equivFin G s⁻¹ then s else s⁻¹

/-- The retained labels: the inverse classes of `T` whose representative's coin is `true`. -/
def sampled (T : Finset G) (ξ : G → Bool) : Finset G := T.filter fun s => ξ (classRep s) = true

/-- A coin with success probability `q` (clamped to `[0, 1]`). -/
def coinDist (q : ℝ) : FinDist Bool where
  support := univ
  prob b := if b then max 0 (min q 1) else 1 - max 0 (min q 1)
  prob_nonneg b := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, sub_nonneg]
      exact max_le zero_le_one (min_le_right _ _)
    · simp
  sum_prob := by simp [Fintype.sum_bool]

/-- The label experiment of §6.1: independent coins with probability `q` at every group element;
the inverse class `{s, s⁻¹}` of `T` is retained iff the coin of its representative succeeds, so
the classes are retained independently with probability `q`. -/
def labelLaw (G : Type u) [Fintype G] [DecidableEq G] (q : ℝ) : FinDist (G → Bool) :=
  FinDist.pi fun _ : G => coinDist q

/-- (6.2) for the retained labels: every full-copy vertex has at least `b` neighbours in the part
via retained labels. -/
def Sampled62 (𝒜 : Allocation G) (T Ap Am : Finset G) (ξ : G → Bool) (b : ℝ) : Prop :=
  ∀ i, ∀ v ∈ copyVerts Ap Am (𝒜.g i),
    b ≤ ((𝒜.part i).filter fun y => (copyGraph (sampled T ξ) Ap Am (𝒜.g i)).Adj v y).card

/-- (6.5): every nontrivial cut of `X₀ = Cay(G, S₀)` whose shore is a union of left
`⟨T⟩`-cosets retains at least half its edges in `X₀ - W`. -/
def Res65 (T S₀ W : Finset G) : Prop :=
  ∀ Z : Finset G, (∀ x ∈ Z, ∀ y ∈ Subgroup.closure (T : Set G), x * y ∈ Z) → Z.Nonempty →
    Z ≠ univ →
    ((Z ×ˢ (univ \ Z)).filter fun p => (cayleyGraph S₀).Adj p.1 p.2).card ≤
      2 * ((Z ×ˢ (univ \ Z)).filter fun p =>
        (cayleyGraph S₀).Adj p.1 p.2 ∧ p.1 ∉ W ∧ p.2 ∉ W).card

/-- (6.6): `e_{X₀}(H \ W, W) ≤ B` for every left `⟨T⟩`-coset `H`. -/
def Res66 (T S₀ W : Finset G) (B : ℝ) : Prop :=
  ∀ H : G ⧸ Subgroup.closure (T : Set G),
    ((∑ v ∈ univ.filter fun v => v ∉ W ∧ (v : G ⧸ Subgroup.closure (T : Set G)) = H,
      (W.filter fun w => (cayleyGraph S₀).Adj v w).card : ℕ) : ℝ) ≤ B

end Setup

/-! ### Auxiliary facts used in the assembly -/

section Aux

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

lemma P_congr {α : Type*} (μ : FinDist α) {E E' : α → Prop} (h : ∀ a, E a ↔ E' a) :
    μ.P E = μ.P E' := by
  have : E = E' := funext fun a => propext (h a)
  subst this
  rfl

lemma P_false {α : Type*} (μ : FinDist α) : μ.P (fun _ => False) = 0 := by
  simp [FinDist.P]

lemma mem_copyVerts {Ap Am : Finset G} {g v : G} :
    v ∈ copyVerts Ap Am g ↔ g⁻¹ * v ∈ Ap ∪ Am := by
  unfold copyVerts
  constructor
  · intro hv
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hv
    simpa using ha
  · intro hv
    exact mem_image.2 ⟨_, hv, by simp⟩

lemma copyGraph_adj_mem {T Ap Am : Finset G} {g x y : G} (h : (copyGraph T Ap Am g).Adj x y) :
    x ∈ copyVerts Ap Am g ∧ y ∈ copyVerts Ap Am g := by
  have h2 := h.2.1
  rw [mem_copyVerts, mem_copyVerts]
  rcases h2 with h2 | h2
  · exact ⟨mem_union_left _ h2.1, mem_union_right _ h2.2⟩
  · exact ⟨mem_union_right _ h2.1, mem_union_left _ h2.2⟩

lemma copyGraph_adj_label {T Ap Am : Finset G} {g x y : G} (h : (copyGraph T Ap Am g).Adj x y) :
    x⁻¹ * y ∈ T ∨ y⁻¹ * x ∈ T := by
  have h3 := h.2.2
  simpa [mul_assoc] using h3

/-- A connected template lies in a single left coset of `⟨T⟩`. -/
lemma template_coset {S T Ap Am : Finset G} {cT : ℝ} (hT : IsTemplate S T Ap Am cT) :
    ∀ a ∈ Ap ∪ Am, ∀ b ∈ Ap ∪ Am, a⁻¹ * b ∈ Subgroup.closure (T : Set G) := by
  have htemp : ∀ a b : G, (templateGraph T Ap Am).Adj a b →
      a⁻¹ * b ∈ Subgroup.closure (T : Set G) := by
    intro a b h
    rcases h.2.2 with h' | h'
    · exact Subgroup.subset_closure h'
    · have := inv_mem (Subgroup.subset_closure h' : b⁻¹ * a ∈ Subgroup.closure (T : Set G))
      simpa using this
  intro a ha
  have key : ∀ w : ↥((Ap ∪ Am : Finset G) : Set G),
      ((templateGraph T Ap Am).induce ((Ap ∪ Am : Finset G) : Set G)).Reachable ⟨a, ha⟩ w →
        a⁻¹ * w.1 ∈ Subgroup.closure (T : Set G) := by
    intro w hw
    rw [SimpleGraph.reachable_iff_reflTransGen] at hw
    induction hw with
    | refl => simp
    | tail _ hadj ih =>
      rename_i c d _
      have h2 := htemp _ _ hadj
      rw [show a⁻¹ * d.1 = (a⁻¹ * c.1) * (c.1⁻¹ * d.1) by group]
      exact mul_mem ih h2
  intro b hb
  exact key ⟨b, hb⟩ (hT.connected.preconnected _ _)

/-- Every translated copy lies in a single left coset of `⟨T⟩`. -/
lemma copy_coset {S T Ap Am : Finset G} {cT : ℝ} (hT : IsTemplate S T Ap Am cT) (g : G)
    {a b : G} (ha : a ∈ copyVerts Ap Am g) (hb : b ∈ copyVerts Ap Am g) :
    a⁻¹ * b ∈ Subgroup.closure (T : Set G) := by
  have := template_coset hT _ (mem_copyVerts.1 ha) _ (mem_copyVerts.1 hb)
  simpa [mul_assoc] using this

variable {S T Ap Am : Finset G} {cT : ℝ} {𝒜 : Allocation G} {lam D σ η ω cN CN : ℝ}

lemma pi_eq_of_mem (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN) {π : G → Fin 𝒜.t}
    (hπ : ∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v)) {v : G} {i : Fin 𝒜.t} (hv : v ∈ 𝒜.part i) :
    π v = i := by
  have hvW : v ∉ 𝒜.W := fun h => Finset.disjoint_left.1 (hgood.part_disjoint i) hv h
  obtain ⟨j, -, hj⟩ := hgood.part_unique v hvW
  exact (hj _ (hπ v hvW)).trans (hj _ hv).symm

/-- The reserved set meets every left coset of `⟨T⟩` in at most one vertex. -/
lemma reserved_unique (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN) (x w w' : G)
    (hw : w ∈ 𝒜.W) (hw' : w' ∈ 𝒜.W) (h1 : x⁻¹ * w ∈ Subgroup.closure (T : Set G))
    (h2 : x⁻¹ * w' ∈ Subgroup.closure (T : Set G)) : w = w' := by
  rcases Nat.even_or_odd (Nat.card (Subgroup.closure (T : Set G))) with he | ho
  · rw [hgood.reserved.2 he] at hw
    simp at hw
  · have := hgood.reserved.1 ho x
    exact card_le_one.1 this.le _ (mem_filter.2 ⟨hw, h1⟩) _ (mem_filter.2 ⟨hw', h2⟩)

lemma exists_copy (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN) (hTne : T.Nonempty) (w : G) :
    ∃ i, w ∈ copyVerts Ap Am (𝒜.g i) := by
  obtain ⟨s, hs⟩ := hTne
  obtain ⟨i, hi⟩ := hgood.cover_edges w s hs
  exact ⟨i, (copyGraph_adj_mem hi).1⟩

/-- A successful allocation has at least two parts, since a single part would contain almost all
`F`-neighbours of any of its vertices, contradicting (5.16). -/
lemma two_le_t (hS : IsConnectionSet S) (hT : IsTemplate S T Ap Am cT)
    (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN) (hlam : 0 < lam) (hTne : T.Nonempty)
    (hbig : CN * S.card / lam < cT * S.card - 1) : 2 ≤ 𝒜.t := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨s, hs⟩ := hTne
  have hs1 : s ≠ 1 := fun h => hS.2 (h ▸ hT.sub hs)
  have hsU : s ∈ Subgroup.closure (T : Set G) := Subgroup.subset_closure hs
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ ∉ 𝒜.W := by
    by_cases h1 : (1 : G) ∈ 𝒜.W
    · refine ⟨s, fun hsW => hs1 ?_⟩
      exact (reserved_unique hgood 1 1 s h1 hsW (by simp) (by simpa using hsU)).symm
    · exact ⟨1, h1⟩
  obtain ⟨i₀, hi₀, -⟩ := hgood.part_unique v₀ hv₀
  have hall : ∀ j : Fin 𝒜.t, j = i₀ := fun j =>
    Fin.ext (by have := j.isLt; have := i₀.isLt; omega)
  have hv₀c := hgood.part_sub i₀ hi₀
  have hsub : (univ.filter fun y => (copyGraph T Ap Am (𝒜.g i₀)).Adj v₀ y) ⊆
      ((𝒜.part i₀).filter fun y => (copyGraph T Ap Am (𝒜.g i₀)).Adj v₀ y) ∪
        (𝒜.W.filter fun y => (copyGraph T Ap Am (𝒜.g i₀)).Adj v₀ y) := by
    intro y hy
    rw [mem_filter] at hy
    by_cases hyW : y ∈ 𝒜.W
    · exact mem_union_right _ (mem_filter.2 ⟨hyW, hy.2⟩)
    · obtain ⟨j, hj, -⟩ := hgood.part_unique y hyW
      rw [hall j] at hj
      exact mem_union_left _ (mem_filter.2 ⟨hj, hy.2⟩)
  have hWle : (𝒜.W.filter fun y => (copyGraph T Ap Am (𝒜.g i₀)).Adj v₀ y).card ≤ 1 := by
    refine card_le_one.2 fun y hy y' hy' => ?_
    rw [mem_filter] at hy hy'
    have hl : ∀ z, (copyGraph T Ap Am (𝒜.g i₀)).Adj v₀ z →
        v₀⁻¹ * z ∈ Subgroup.closure (T : Set G) := by
      intro z hz
      rcases copyGraph_adj_label hz with h | h
      · exact Subgroup.subset_closure h
      · have := inv_mem (Subgroup.subset_closure h : z⁻¹ * v₀ ∈ Subgroup.closure (T : Set G))
        simpa using this
    exact reserved_unique hgood v₀ y y' hy.1 hy'.1 (hl y hy.2) (hl y' hy'.2)
  have hN : cT * S.card ≤
      ((univ.filter fun y => (copyGraph T Ap Am (𝒜.g i₀)).Adj v₀ y).card : ℝ) := by
    have h1 := hT.deg_lower ((𝒜.g i₀)⁻¹ * v₀) (mem_copyVerts.1 hv₀c)
    have h2 : (univ.filter fun y => (copyGraph T Ap Am (𝒜.g i₀)).Adj v₀ y) =
        (univ.filter fun y => (templateGraph T Ap Am).Adj ((𝒜.g i₀)⁻¹ * v₀) y).image
          ((𝒜.g i₀) * ·) := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_image]
      constructor
      · intro h
        exact ⟨(𝒜.g i₀)⁻¹ * y, h, by simp⟩
      · rintro ⟨y', h, rfl⟩
        show (templateGraph T Ap Am).Adj ((𝒜.g i₀)⁻¹ * v₀) ((𝒜.g i₀)⁻¹ * ((𝒜.g i₀) * y'))
        simpa using h
    have h3 : (templateGraph T Ap Am).neighborSet ((𝒜.g i₀)⁻¹ * v₀) =
        ↑(univ.filter fun y => (templateGraph T Ap Am).Adj ((𝒜.g i₀)⁻¹ * v₀) y) := by
      ext y
      simp
    have h5 : ((univ.filter fun y => (templateGraph T Ap Am).Adj ((𝒜.g i₀)⁻¹ * v₀) y).card : ℝ) =
        ((templateGraph T Ap Am).neighborSet ((𝒜.g i₀)⁻¹ * v₀)).ncard := by
      rw [h3, Set.ncard_coe_finset]
    rw [h2, card_image_of_injective _ (mul_right_injective _), h5]
    exact h1
  have hup := hgood.nbhd_upper i₀ v₀ hv₀c
  have h4 : ((univ.filter fun y => (copyGraph T Ap Am (𝒜.g i₀)).Adj v₀ y).card : ℝ) ≤
      ((𝒜.part i₀).filter fun y => (copyGraph T Ap Am (𝒜.g i₀)).Adj v₀ y).card + 1 := by
    have := (card_le_card hsub).trans (card_union_le _ _)
    exact_mod_cast this.trans (Nat.add_le_add_left hWle _)
  linarith

lemma t_le_card (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN) (hsize : 0 < cN * S.card / lam) :
    𝒜.t ≤ Fintype.card G := by
  have hne : ∀ i, (𝒜.part i).Nonempty := fun i => by
    rw [← card_pos]
    have := hgood.size_lower i
    have : (0 : ℝ) < (𝒜.part i).card := lt_of_lt_of_le hsize this
    exact_mod_cast this
  choose f hf using hne
  have hinj : Function.Injective f := by
    intro i j hij
    have hfW : f i ∉ 𝒜.W := fun h => disjoint_left.1 (hgood.part_disjoint i) (hf i) h
    obtain ⟨k, -, hk⟩ := hgood.part_unique (f i) hfW
    exact (hk i (hf i)).trans (hk j (by rw [hij]; exact hf j)).symm
  simpa using Fintype.card_le_of_injective f hinj

omit [Group G] [Fintype G] [DecidableEq G] in
lemma cutCnt_empty {t : ℕ} (π : G → Fin t) (sg : G → Bool) (F : Finset (Sym2 G)) :
    cutCnt π sg ∅ F = 0 := by
  simp [cutCnt, outCnt, inCnt, outArcs, inArcs]

omit [Group G] [DecidableEq G] in
lemma cutCnt_univ {t : ℕ} (π : G → Fin t) (sg : G → Bool) (F : Finset (Sym2 G)) :
    cutCnt π sg univ F = 0 := by
  simp [cutCnt, outCnt, inCnt, outArcs, inArcs]

omit [Group G] [Fintype G] [DecidableEq G] in
lemma cutCnt_prod_univ {t : ℕ} (π : G → Fin t) (sg : G → Bool) (I : Finset (Fin t))
    (F : Finset (Sym2 G)) :
    cutCnt π sg (I ×ˢ univ) F = 2 * (F.filter (PartCross π I)).card := by
  have key : ∀ e : Sym2 G,
      (univ.filter fun b : Bool => arcTail π sg e b ∈ I ×ˢ univ ∧
        arcHead π sg e b ∉ I ×ˢ univ).card +
      (univ.filter fun b : Bool => arcHead π sg e b ∈ I ×ˢ univ ∧
        arcTail π sg e b ∉ I ×ˢ univ).card = 2 * (if PartCross π I e then 1 else 0) := by
    intro e
    simp only [card_filter, Fintype.sum_bool, arcTail, arcHead, mem_product, mem_univ, and_true,
      PartCross]
    by_cases h1 : π e.out.1 ∈ I <;> by_cases h2 : π e.out.2 ∈ I <;> simp [h1, h2]
  unfold cutCnt outCnt inCnt outArcs inArcs
  rw [← sum_add_distrib, sum_congr rfl (fun e _ => key e), ← mul_sum, ← card_filter]

lemma cayley_connected (S₀ : Finset G) (hsymm : ∀ s ∈ S₀, s⁻¹ ∈ S₀)
    (h : Subgroup.closure (S₀ : Set G) = ⊤) : (cayleyGraph S₀).Connected := by
  have htrans : ∀ g a b : G, (cayleyGraph S₀).Reachable a b →
      (cayleyGraph S₀).Reachable (g * a) (g * b) := by
    intro g a b hab
    let φ : cayleyGraph S₀ →g cayleyGraph S₀ := ⟨fun x => g * x, fun {x y} hxy => by
      rw [SimpleGraph.mulCayley_adj] at hxy ⊢
      refine ⟨fun h => hxy.1 (mul_left_cancel h), ?_⟩
      simpa [mul_assoc] using hxy.2⟩
    exact hab.map φ
  have key : ∀ x ∈ Subgroup.closure (S₀ : Set G), (cayleyGraph S₀).Reachable 1 x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem s hs =>
      by_cases h1 : (1 : G) = s
      · rw [← h1]
      · exact SimpleGraph.Adj.reachable (by
          rw [SimpleGraph.mulCayley_adj]
          exact ⟨h1, Or.inl (by simpa using hs)⟩)
    | one => rfl
    | mul x y _ _ hx hy => exact hx.trans (by simpa using htrans x 1 y hy)
    | inv x _ hx => exact (by simpa using htrans x⁻¹ 1 x hx : (cayleyGraph S₀).Reachable x⁻¹ 1).symm
  haveI : Nonempty G := ⟨1⟩
  exact ⟨fun a b => (key a (h ▸ Subgroup.mem_top a)).symm.trans (key b (h ▸ Subgroup.mem_top b))⟩

lemma conY_degree_le (S₀ W : Finset G) (hsymm : ∀ s ∈ S₀, s⁻¹ ∈ S₀) (v : G) :
    (conY S₀ W).degree v ≤ S₀.card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc ((conY S₀ W).neighborFinset v).card ≤ (S₀.image (v * ·)).card := by
        apply card_le_card
        intro w hw
        rw [SimpleGraph.mem_neighborFinset] at hw
        have h := hw.1
        rw [SimpleGraph.mulCayley_adj] at h
        rw [mem_image]
        rcases h.2 with h' | h'
        · exact ⟨v⁻¹ * w, h', by simp⟩
        · exact ⟨v⁻¹ * w, by simpa using hsymm _ h', by simp⟩
    _ ≤ S₀.card := card_image_le

lemma card_le_closure (T : Finset G) : T.card ≤ Nat.card (Subgroup.closure (T : Set G)) := by
  rw [← Set.ncard_coe_finset]
  have : ((Subgroup.closure (T : Set G) : Set G)).ncard =
      Nat.card (Subgroup.closure (T : Set G)) := (Nat.card_coe_set_eq _).symm
  rw [← this]
  exact Set.ncard_le_ncard Subgroup.subset_closure

lemma classRep_inv (s : G) : classRep s⁻¹ = classRep s := by
  unfold classRep
  simp only [inv_inv]
  by_cases h1 : Fintype.equivFin G s ≤ Fintype.equivFin G s⁻¹ <;>
    by_cases h2 : Fintype.equivFin G s⁻¹ ≤ Fintype.equivFin G s <;>
    simp only [h1, h2, if_true, if_false]
  · exact ((Fintype.equivFin G).injective (le_antisymm h1 h2)).symm
  · exact absurd (le_of_lt (not_le.1 h1)) h2

lemma sampled_symm (T : Finset G) (hT : ∀ s ∈ T, s⁻¹ ∈ T) (ξ : G → Bool) :
    ∀ s ∈ sampled T ξ, s⁻¹ ∈ sampled T ξ := by
  intro s hs
  simp only [sampled, mem_filter] at hs ⊢
  exact ⟨hT s hs.1, by rw [classRep_inv]; exact hs.2⟩

/-- The parameter regime of Sections 6–7: with `d ≥ L¹³ / log L` and `L` large, all the
quantitative conditions used in the assembly hold. -/
lemma regime (cT A₀ cN CN cD CD a c₃ Cres CB K P₀ : ℝ) (hcT : 0 < cT) (hA₀ : 0 < A₀)
    (hcN : 0 < cN) (hCN : 0 < CN) (hcD : 0 < cD) (hCD : 0 < CD) (ha : 0 < a) (hc₃ : 0 < c₃)
    (hCres : 0 < Cres) (hCB : 0 < CB) (hK : 0 < K) (hP₀ : 2 ^ 19 ≤ P₀) :
    ∃ L₀ : ℝ, 3 ≤ L₀ ∧ ∀ L d : ℝ, L₀ ≤ L → L ^ 13 ≤ Real.log L * d →
      L ^ 12 ≤ d ∧
      CN * d / (A₀ * L) < cT * d - 1 ∧
      2 * ((Real.log 2 + L) / Real.log 2 + 1) ≤ 8 * L ∧
      Cres * (K * L ^ 2) * L ≤ cT * d ∧
      3 * (CB * (K * L ^ 2) * L) ≤ c₃ * d / L ∧
      6 ≤ c₃ * d / L ∧
      P₀ * L / (c₃ * d / L) * (K * L ^ 2) ^ 2 ≤ 1 ∧
      1100 ≤ P₀ * L ∧
      32 * (3 + 2 * L) + 4 ≤ P₀ * L / 2048 ∧
      4 * (P₀ * L / (c₃ * d / L) * (K * L ^ 2)) ≤ a * Real.log L / L ^ 7 ∧
      4 ≤ a * Real.log L / L ^ 7 * (cN * d / (A₀ * L)) ∧
      3 + 2 * L ≤ 3 / 40 * (a * Real.log L / L ^ 7 * (cN * d / (A₀ * L)) - 2) ∧
      2 * (P₀ * L / (c₃ * d / L) * (K * L ^ 2)) * (CN * d / (A₀ * L)) + 2 ≤
        a * (cD * d / L) / L ^ 6 ∧
      3 + 2 * L ≤ 3 / 40 * (a * (cD * d / L) / L ^ 6 - 2) ∧
      a * (CD * d / L) / L ^ 6 ≤ cN * d / (A₀ * L) := by
  refine ⟨max 3 (max (2 * CN / (A₀ * cT)) (max (3 / cT) (max (Cres * K / cT)
    (max (3 * CB * K / c₃) (max (6 / c₃) (max (P₀ * K ^ 2 / c₃) (max (4 * P₀ * K / (a * c₃))
    (max (70 * A₀ / (a * cN)) (max (4 * P₀ * K * CN / (c₃ * A₀ * (a * cD)))
    (max (70 / (a * cD)) (a * CD * A₀ / cN))))))))))), le_max_left _ _, fun L d hL hLd => ?_⟩
  simp only [max_le_iff] at hL
  obtain ⟨h3, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11⟩ := hL
  have hP₀pos : (0 : ℝ) < P₀ := lt_of_lt_of_le (by norm_num) hP₀
  have hLpos : 0 < L := by linarith only [h3]
  have hΛpos : 0 < Real.log L := Real.log_pos (by linarith only [h3])
  have hΛle : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos hLpos).trans (by linarith only [h3])
  have hdpos : 0 < d := by
    have h13 := pow_pos hLpos 13
    by_contra h
    push_neg at h
    linarith only [mul_nonneg hΛpos.le (neg_nonneg.2 h), hLd, h13]
  have hd12 : L ^ 12 ≤ d := by
    have h1 : L * L ^ 12 ≤ L * d := by
      rw [← pow_succ']
      exact hLd.trans (mul_le_mul_of_nonneg_right hΛle hdpos.le)
    exact le_of_mul_le_mul_left h1 hLpos
  have hL1 : 1 ≤ L := by linarith only [h3]
  have hpow : ∀ m n : ℕ, m ≤ n → L ^ m ≤ L ^ n := fun m n h => pow_le_pow_right₀ hL1 h
  -- the thresholds in multiplicative form
  have u1 : 2 * CN ≤ A₀ * cT * L := by
    rw [div_le_iff₀ (mul_pos hA₀ hcT)] at t1; linarith only [t1]
  have u2 : 3 ≤ cT * L := by rw [div_le_iff₀ hcT] at t2; linarith only [t2]
  have u3 : Cres * K ≤ cT * L := by rw [div_le_iff₀ hcT] at t3; linarith only [t3]
  have u4 : 3 * CB * K ≤ c₃ * L := by rw [div_le_iff₀ hc₃] at t4; linarith only [t4]
  have u5 : 6 ≤ c₃ * L := by rw [div_le_iff₀ hc₃] at t5; linarith only [t5]
  have u6 : P₀ * K ^ 2 ≤ c₃ * L := by rw [div_le_iff₀ hc₃] at t6; linarith only [t6]
  have u7 : 4 * P₀ * K ≤ a * c₃ * L := by
    rw [div_le_iff₀ (mul_pos ha hc₃)] at t7; linarith only [t7]
  have u8 : 70 * A₀ ≤ a * cN * L := by
    rw [div_le_iff₀ (mul_pos ha hcN)] at t8; linarith only [t8]
  have u9 : 4 * P₀ * K * CN ≤ c₃ * A₀ * (a * cD) * L := by
    rw [div_le_iff₀ (mul_pos (mul_pos hc₃ hA₀) (mul_pos ha hcD))] at t9; linarith only [t9]
  have u10 : 70 ≤ a * cD * L := by
    rw [div_le_iff₀ (mul_pos ha hcD)] at t10; linarith only [t10]
  have u11 : a * CD * A₀ ≤ cN * L := by rw [div_le_iff₀ hcN] at t11; linarith only [t11]
  clear t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11
  have hL6 : L ≤ L ^ 6 := by simpa using hpow 1 6 (by norm_num)
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith only [this]
  have hp : P₀ * L / (c₃ * d / L) = P₀ * L ^ 2 / (c₃ * d) := by
    field_simp
  refine ⟨hd12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (2)
    have h1 : CN * d / (A₀ * L) ≤ cT * d / 2 := by
      rw [div_le_div_iff₀ (mul_pos hA₀ hLpos) (by norm_num)]
      have := mul_le_mul_of_nonneg_right u1 hdpos.le
      linarith only [this]
    have h2 : 3 ≤ cT * d := by
      have : cT * L ≤ cT * d := mul_le_mul_of_nonneg_left
        ((by simpa using hpow 1 12 (by norm_num) : L ≤ L ^ 12).trans hd12) hcT.le
      linarith only [this, u2]
    linarith only [h1, h2]
  · -- (3)
    have h1 : (Real.log 2 + L) / Real.log 2 = 1 + L / Real.log 2 := by
      field_simp
    have h2 : L / Real.log 2 ≤ L / 0.69 :=
      div_le_div_of_nonneg_left hLpos.le (by norm_num) hlog2.le
    rw [h1]
    have h3' : L / 0.69 ≤ 1.45 * L := by
      rw [div_le_iff₀ (by norm_num)]
      linarith only [hLpos]
    linarith only [h2, h3', h3]
  · -- (4)
    have h1 : Cres * (K * L ^ 2) * L ≤ cT * L ^ 4 := by
      have : Cres * (K * L ^ 2) * L = (Cres * K) * L ^ 3 := by ring
      rw [this, show cT * L ^ 4 = (cT * L) * L ^ 3 by ring]
      exact mul_le_mul_of_nonneg_right u3 (by positivity)
    have h2 : cT * L ^ 4 ≤ cT * d :=
      mul_le_mul_of_nonneg_left ((hpow 4 12 (by norm_num)).trans hd12) hcT.le
    linarith only [h1, h2]
  · -- (5)
    rw [le_div_iff₀ hLpos]
    have h1 : 3 * (CB * (K * L ^ 2) * L) * L ≤ c₃ * L ^ 5 := by
      have : 3 * (CB * (K * L ^ 2) * L) * L = (3 * CB * K) * L ^ 4 := by ring
      rw [this, show c₃ * L ^ 5 = (c₃ * L) * L ^ 4 by ring]
      exact mul_le_mul_of_nonneg_right u4 (by positivity)
    have h2 : c₃ * L ^ 5 ≤ c₃ * d :=
      mul_le_mul_of_nonneg_left ((hpow 5 12 (by norm_num)).trans hd12) hc₃.le
    linarith only [h1, h2]
  · -- (6)
    rw [le_div_iff₀ hLpos]
    have h2 : c₃ * L ^ 2 ≤ c₃ * d :=
      mul_le_mul_of_nonneg_left ((hpow 2 12 (by norm_num)).trans hd12) hc₃.le
    have h3'' := mul_le_mul_of_nonneg_right u5 hLpos.le
    linarith only [h3'', h2]
  · -- (7)
    rw [hp, div_mul_eq_mul_div, div_le_one (mul_pos hc₃ hdpos)]
    have h1 : P₀ * L ^ 2 * (K * L ^ 2) ^ 2 = (P₀ * K ^ 2) * L ^ 6 := by ring
    rw [h1]
    have h2 : (P₀ * K ^ 2) * L ^ 6 ≤ (c₃ * L) * L ^ 6 :=
      mul_le_mul_of_nonneg_right u6 (by positivity)
    have h3' : c₃ * L ^ 7 ≤ c₃ * d :=
      mul_le_mul_of_nonneg_left ((hpow 7 12 (by norm_num)).trans hd12) hc₃.le
    linarith only [h2, h3']
  · -- (8)
    have := mul_le_mul hP₀ h3 (by norm_num) hP₀pos.le
    linarith only [this]
  · -- (9)
    have h1 := mul_le_mul_of_nonneg_right hP₀ hLpos.le
    have : 256 * L ≤ P₀ * L / 2048 := by
      rw [le_div_iff₀ (by norm_num)]
      linarith only [h1]
    linarith only [this, h3]
  · -- (10)
    rw [hp]
    have h1 : 4 * (P₀ * L ^ 2 / (c₃ * d) * (K * L ^ 2)) = 4 * P₀ * K * L ^ 4 / (c₃ * d) := by
      field_simp
    rw [h1, div_le_div_iff₀ (mul_pos hc₃ hdpos) (by positivity)]
    have h2 : 4 * P₀ * K * L ^ 4 * L ^ 7 ≤ (a * c₃ * L) * L ^ 11 := by
      have : 4 * P₀ * K * L ^ 4 * L ^ 7 = (4 * P₀ * K) * L ^ 11 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right u7 (by positivity)
    have h3' : (a * c₃ * L) * L ^ 11 ≤ a * c₃ * L ^ 13 := by
      have : (a * c₃ * L) * L ^ 11 = a * c₃ * L ^ 12 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (hpow 12 13 (by norm_num)) (by positivity)
    have h4 : a * c₃ * L ^ 13 ≤ a * c₃ * (Real.log L * d) :=
      mul_le_mul_of_nonneg_left hLd (by positivity)
    linarith only [h2, h3', h4]
  · -- (11)
    have h1 : a * Real.log L / L ^ 7 * (cN * d / (A₀ * L)) =
        a * cN * (Real.log L * d) / (A₀ * L ^ 8) := by
      field_simp
    rw [h1, le_div_iff₀ (by positivity)]
    have h5 : 4 * A₀ ≤ a * cN * L := by linarith only [u8, hA₀]
    have h2 : 4 * (A₀ * L ^ 8) ≤ a * cN * L ^ 13 := by
      have e1 : a * cN * L ^ 13 = (a * cN * L) * L ^ 12 := by ring
      have e2 : 4 * (A₀ * L ^ 8) = (4 * A₀) * L ^ 8 := by ring
      rw [e1, e2]
      exact mul_le_mul h5 (hpow 8 12 (by norm_num)) (by positivity) (by positivity)
    have h3' : a * cN * L ^ 13 ≤ a * cN * (Real.log L * d) :=
      mul_le_mul_of_nonneg_left hLd (by positivity)
    linarith only [h2, h3']
  · -- (12)
    have h1 : a * Real.log L / L ^ 7 * (cN * d / (A₀ * L)) =
        a * cN * (Real.log L * d) / (A₀ * L ^ 8) := by
      field_simp
    rw [h1]
    have h2 : 70 * L ≤ a * cN * (Real.log L * d) / (A₀ * L ^ 8) := by
      rw [le_div_iff₀ (by positivity)]
      have h3' : a * cN * L ^ 13 ≤ a * cN * (Real.log L * d) :=
        mul_le_mul_of_nonneg_left hLd (by positivity)
      have h4 : 70 * L * (A₀ * L ^ 8) ≤ a * cN * L ^ 13 := by
        have e1 : 70 * L * (A₀ * L ^ 8) = (70 * A₀) * L ^ 9 := by ring
        rw [e1, show a * cN * L ^ 13 = (a * cN * L) * L ^ 12 by ring]
        exact mul_le_mul u8 (hpow 9 12 (by norm_num)) (by positivity) (by positivity)
      linarith only [h3', h4]
    linarith only [h2, h3]
  · -- (13)
    rw [hp]
    have h1 : 2 * (P₀ * L ^ 2 / (c₃ * d) * (K * L ^ 2)) * (CN * d / (A₀ * L)) =
        2 * P₀ * K * CN * L ^ 3 / (c₃ * A₀) := by
      field_simp
    have h2 : a * (cD * d / L) / L ^ 6 = a * cD * d / L ^ 7 := by
      field_simp
    rw [h1, h2]
    have h3' : a * cD * L ^ 5 ≤ a * cD * d / L ^ 7 := by
      rw [le_div_iff₀ (by positivity)]
      have : a * cD * L ^ 5 * L ^ 7 = a * cD * L ^ 12 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hd12 (by positivity)
    have h4 : 2 * P₀ * K * CN * L ^ 3 / (c₃ * A₀) ≤ a * cD * L ^ 5 / 2 := by
      rw [div_le_div_iff₀ (mul_pos hc₃ hA₀) (by norm_num)]
      have e1 : 2 * P₀ * K * CN * L ^ 3 * 2 = (4 * P₀ * K * CN) * L ^ 3 := by ring
      rw [e1, show a * cD * L ^ 5 * (c₃ * A₀) = (c₃ * A₀ * (a * cD) * L) * L ^ 4 by ring]
      calc (4 * P₀ * K * CN) * L ^ 3 ≤ (c₃ * A₀ * (a * cD) * L) * L ^ 3 :=
            mul_le_mul_of_nonneg_right u9 (by positivity)
        _ ≤ (c₃ * A₀ * (a * cD) * L) * L ^ 4 :=
            mul_le_mul_of_nonneg_left (hpow 3 4 (by norm_num)) (by positivity)
    have h5 : 2 ≤ a * cD * L ^ 5 / 2 := by
      rw [le_div_iff₀ (by norm_num)]
      have : a * cD * L ≤ a * cD * L ^ 5 :=
        mul_le_mul_of_nonneg_left (by simpa using hpow 1 5 (by norm_num)) (by positivity)
      linarith only [this, u10]
    linarith only [h3', h4, h5]
  · -- (14)
    have h2 : a * (cD * d / L) / L ^ 6 = a * cD * d / L ^ 7 := by
      field_simp
    rw [h2]
    have h3' : 70 * L ≤ a * cD * d / L ^ 7 := by
      rw [le_div_iff₀ (by positivity)]
      have e1 : 70 * L ^ 8 ≤ (a * cD * L) * L ^ 8 := mul_le_mul_of_nonneg_right u10 (by positivity)
      have e2 : (a * cD * L) * L ^ 8 ≤ a * cD * d := by
        rw [show (a * cD * L) * L ^ 8 = a * cD * L ^ 9 by ring]
        exact mul_le_mul_of_nonneg_left ((hpow 9 12 (by norm_num)).trans hd12) (by positivity)
      linarith only [e1, e2]
    linarith only [h3', h3]
  · -- (15)
    have h2 : a * (CD * d / L) / L ^ 6 = a * CD * d / L ^ 7 := by
      field_simp
    rw [h2, div_le_div_iff₀ (by positivity) (mul_pos hA₀ hLpos)]
    have e1 : a * CD * d * (A₀ * L) = (a * CD * A₀) * (d * L) := by ring
    rw [e1, show cN * d * L ^ 7 = (cN * L) * (d * L ^ 6) by ring]
    exact mul_le_mul u11 (mul_le_mul_of_nonneg_left hL6 hdpos.le) (by positivity) (by positivity)

end Aux

/-! ### Generic tools for the integral connector -/

section IntegralAux

/-- The per-edge form of (6.10): the out-arcs minus the in-arcs of a physical edge equal the sum
of the signed state indicators of its two ends. -/
lemma arc_count_identity {A B C D : Prop} {i1 : Decidable (C ∧ ¬ D)} {i2 : Decidable (A ∧ ¬ B)}
    {i3 : Decidable (D ∧ ¬ C)} {i4 : Decidable (B ∧ ¬ A)} {j1 : Decidable A} {j2 : Decidable D}
    {j3 : Decidable C} {j4 : Decidable B} :
    ((@ite ℝ (C ∧ ¬ D) i1 1 0 + @ite ℝ (A ∧ ¬ B) i2 1 0) -
      (@ite ℝ (D ∧ ¬ C) i3 1 0 + @ite ℝ (B ∧ ¬ A) i4 1 0)) =
      (@ite ℝ A j1 1 0 - @ite ℝ D j2 1 0) + (@ite ℝ C j3 1 0 - @ite ℝ B j4 1 0) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> by_cases hD : D <;>
    simp [hA, hB, hC, hD]

lemma sum_bool_ite (P : Bool → Prop) [DecidablePred P] (c : ℝ) :
    ∑ b, (if P b then c else 0) = c * (univ.filter P).card := by
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

lemma connected_of_forall_cut {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (H : SimpleGraph V) (h : ∀ I : Finset V, I.Nonempty → I ≠ univ → ∃ i ∈ I, ∃ j ∉ I, H.Adj i j) :
    H.Connected := by
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have hall : ∀ v, H.Reachable v₀ v := by
    by_contra hc
    push_neg at hc
    obtain ⟨u, hu⟩ := hc
    obtain ⟨i, hi, j, hj, hij⟩ := h (univ.filter (H.Reachable v₀)) ⟨v₀, by simp⟩
      (fun heq => hu (by
        have := mem_univ u
        rw [← heq] at this
        simpa using this))
    simp only [mem_filter, mem_univ, true_and] at hi hj
    exact hj (hi.trans hij.reachable)
  exact ⟨fun a b => (hall a).symm.trans (hall b)⟩

/-- A point of the convex hull of `s ⊆ (-∞, 1]^E` with `x_e = 1` is a convex combination of points
of `s` that all have `z_e = 1`; in particular some `z ∈ s` has `z_e = 1` wherever `x_e = 1`. -/
lemma exists_face_point {E : Type*} {s : Set (E → ℝ)} {x : E → ℝ} (hx : x ∈ convexHull ℝ s)
    (hs : ∀ z ∈ s, ∀ e, z e ≤ 1) : ∃ z ∈ s, ∀ e, x e = 1 → z e = 1 := by
  rw [_root_.convexHull_eq] at hx
  obtain ⟨ι, t, w, z, hw0, hw1, hz, hcm⟩ := hx
  have hcm' : ∀ e, ∑ i ∈ t, w i * z i e = x e := by
    intro e
    have := congrFun hcm e
    simpa [Finset.centerMass, hw1, Finset.sum_apply, smul_eq_mul] using this
  obtain ⟨i₀, hi₀, hwpos⟩ : ∃ i ∈ t, 0 < w i := by
    by_contra h
    push_neg at h
    have : ∑ i ∈ t, w i ≤ 0 := sum_nonpos h
    linarith
  refine ⟨z i₀, hz i₀ hi₀, fun e he => ?_⟩
  have hsum : ∑ i ∈ t, w i * (1 - z i e) = 0 := by
    have : ∑ i ∈ t, w i * (1 - z i e) = ∑ i ∈ t, w i - ∑ i ∈ t, w i * z i e := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [this, hw1, hcm' e, he]
    ring
  have hnn : ∀ i ∈ t, 0 ≤ w i * (1 - z i e) := fun i hi =>
    mul_nonneg (hw0 i hi) (by linarith [hs _ (hz i hi) e])
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i₀ hi₀
  rcases mul_eq_zero.1 h0 with h | h
  · linarith
  · linarith

lemma ncard_eq_one_iff_nonempty {V : Type*} [Finite V] (s : Set V)
    (h : ∀ x ∈ s, ∀ y ∈ s, x = y) : s.ncard = 1 ↔ s.Nonempty := by
  constructor
  · intro h1
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  · rintro ⟨x, hx⟩
    rw [Set.ncard_eq_one]
    exact ⟨x, Set.eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => h y hy x hx⟩⟩

end IntegralAux

/-! ### Probability tools -/

section Prob

/-- **The joint union bound of §6.1.** Let `a ∼ μ` (the allocation) and `b ∼ ν` (the labels) be
independent. If the allocation fails with probability at most `1/8`, if for every successful
allocation the label estimates fail with probability at most `ε₁`, and if for every label outcome
with few labels the reservation estimates fail with probability at most `ε₂`, where
`1/8 + ε₁ + ε₂ < 1`, then some outcome satisfies everything. -/
theorem joint_union_bound {α β : Type*} (μ : FinDist α) (ν : FinDist β) (A : α → Prop)
    (B : α → β → Prop) (K : β → Prop) (C : α → β → Prop) (ε₁ ε₂ : ℝ)
    (hA : μ.P (fun a => ¬ A a) ≤ 1 / 8)
    (hB : ∀ a ∈ μ.support, A a → ν.P (fun b => ¬ (B a b ∧ K b)) ≤ ε₁)
    (hC : ∀ b ∈ ν.support, K b → μ.P (fun a => ¬ C a b) ≤ ε₂) (hε : 1 / 8 + ε₁ + ε₂ < 1)
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) :
    ∃ a ∈ μ.support, ∃ b ∈ ν.support, A a ∧ B a b ∧ K b ∧ C a b := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ a ∈ μ.support, ∀ b ∈ ν.support,
      μ.prob a * ν.prob b ≤ (if A a then 0 else μ.prob a * ν.prob b) +
        (if A a ∧ ¬ (B a b ∧ K b) then μ.prob a * ν.prob b else 0) +
        (if K b ∧ ¬ C a b then μ.prob a * ν.prob b else 0) := by
    intro a ha b hb
    have h0 : 0 ≤ μ.prob a * ν.prob b := mul_nonneg (μ.prob_nonneg a) (ν.prob_nonneg b)
    have h1 : 0 ≤ (if A a then 0 else μ.prob a * ν.prob b) := by split_ifs <;> linarith
    have h2 : 0 ≤ (if A a ∧ ¬ (B a b ∧ K b) then μ.prob a * ν.prob b else 0) := by
      split_ifs <;> linarith
    have h3 : 0 ≤ (if K b ∧ ¬ C a b then μ.prob a * ν.prob b else 0) := by
      split_ifs <;> linarith
    by_cases hA' : A a
    · by_cases hBK : B a b ∧ K b
      · have hC' : ¬ C a b := hcon a ha b hb hA' hBK.1 hBK.2
        have : (if K b ∧ ¬ C a b then μ.prob a * ν.prob b else 0) = μ.prob a * ν.prob b :=
          if_pos ⟨hBK.2, hC'⟩
        linarith
      · have : (if A a ∧ ¬ (B a b ∧ K b) then μ.prob a * ν.prob b else 0) =
            μ.prob a * ν.prob b := if_pos ⟨hA', hBK⟩
        linarith
    · have : (if A a then 0 else μ.prob a * ν.prob b) = μ.prob a * ν.prob b := if_neg hA'
      linarith
  have hsum : (1 : ℝ) = ∑ a ∈ μ.support, ∑ b ∈ ν.support, μ.prob a * ν.prob b := by
    rw [← μ.sum_prob]
    refine sum_congr rfl fun a _ => ?_
    rw [← mul_sum, ν.sum_prob, mul_one]
  have hle := sum_le_sum fun a ha => sum_le_sum fun b hb => key a ha b hb
  rw [← hsum] at hle
  simp only [sum_add_distrib] at hle
  have e1 : ∑ a ∈ μ.support, ∑ b ∈ ν.support, (if A a then 0 else μ.prob a * ν.prob b) =
      μ.P (fun a => ¬ A a) := by
    unfold FinDist.P
    refine sum_congr rfl fun a _ => ?_
    by_cases h : A a
    · simp [h]
    · simp [h, ← mul_sum, ν.sum_prob]
  have e2 : ∑ a ∈ μ.support, ∑ b ∈ ν.support,
      (if A a ∧ ¬ (B a b ∧ K b) then μ.prob a * ν.prob b else 0) ≤ ε₁ := by
    calc _ ≤ ∑ a ∈ μ.support, μ.prob a * ε₁ := by
          refine sum_le_sum fun a ha => ?_
          by_cases h : A a
          · have hb := hB a ha h
            unfold FinDist.P at hb
            refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hb (μ.prob_nonneg a))
            rw [mul_sum]
            refine sum_congr rfl fun b _ => ?_
            by_cases hb' : B a b ∧ K b <;> simp [h, hb']
          · simp only [h, false_and, if_false, sum_const_zero]
            exact mul_nonneg (μ.prob_nonneg a) hε₁
      _ = ε₁ := by rw [← sum_mul, μ.sum_prob, one_mul]
  have e3 : ∑ a ∈ μ.support, ∑ b ∈ ν.support,
      (if K b ∧ ¬ C a b then μ.prob a * ν.prob b else 0) ≤ ε₂ := by
    rw [sum_comm]
    calc _ ≤ ∑ b ∈ ν.support, ν.prob b * ε₂ := by
          refine sum_le_sum fun b hb => ?_
          by_cases h : K b
          · have hc := hC b hb h
            unfold FinDist.P at hc
            refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hc (ν.prob_nonneg b))
            rw [mul_sum]
            refine sum_congr rfl fun a _ => ?_
            by_cases hc' : C a b <;> simp [h, hc', mul_comm]
          · simp only [h, false_and, if_false, sum_const_zero]
            exact mul_nonneg (ν.prob_nonneg b) hε₂
      _ = ε₂ := by rw [← sum_mul, ν.sum_prob, one_mul]
  linarith

end Prob

/-! ### Step E6.1: the added labels -/

section AddedLabels

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

/-- The doubling argument of §6.1: adjoining an element outside the subgroup generated so far at
least doubles its order, so `r` steps either generate everything or reach order `≥ 2^r`. -/
lemma doubling {K : Type*} [Group K] [Finite K] {α : Type*} [DecidableEq α] (φ : α → K)
    (A : Finset α) (hA : Subgroup.closure (φ '' (A : Set α)) = ⊤) (r : ℕ) :
    ∃ B ⊆ A, B.card ≤ r ∧ (Subgroup.closure (φ '' (B : Set α)) = ⊤ ∨
      2 ^ r ≤ Nat.card (Subgroup.closure (φ '' (B : Set α)))) := by
  induction r with
  | zero =>
    refine ⟨∅, empty_subset _, by simp, Or.inr ?_⟩
    simpa using Nat.card_pos (α := Subgroup.closure (φ '' ((∅ : Finset α) : Set α)))
  | succ r ih =>
    obtain ⟨B, hBA, hBc, hB⟩ := ih
    by_cases htop : Subgroup.closure (φ '' (B : Set α)) = ⊤
    · exact ⟨B, hBA, by omega, Or.inl htop⟩
    · have h2 := hB.resolve_left htop
      obtain ⟨a, haA, ha⟩ : ∃ a ∈ A, φ a ∉ Subgroup.closure (φ '' (B : Set α)) := by
        by_contra h
        push_neg at h
        apply htop
        rw [eq_top_iff, ← hA]
        exact (Subgroup.closure_le _).2 (by rintro _ ⟨a, ha, rfl⟩; exact h a ha)
      refine ⟨insert a B, insert_subset haA hBA, (card_insert_le _ _).trans (by omega), Or.inr ?_⟩
      have hle : Subgroup.closure (φ '' (B : Set α)) ≤
          Subgroup.closure (φ '' ((insert a B : Finset α) : Set α)) :=
        Subgroup.closure_mono (Set.image_mono (by simp [Set.subset_insert]))
      have hne : Subgroup.closure (φ '' (B : Set α)) ≠
          Subgroup.closure (φ '' ((insert a B : Finset α) : Set α)) := fun h =>
        ha (h ▸ Subgroup.subset_closure ⟨a, by simp, rfl⟩)
      obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
      have hpos : 0 < Nat.card (Subgroup.closure (φ '' (B : Set α))) := Nat.card_pos
      have hpos' : 0 < Nat.card (Subgroup.closure (φ '' ((insert a B : Finset α) : Set α))) :=
        Nat.card_pos
      have hk2 : 2 ≤ k := by
        rcases k with _ | _ | k
        · rw [mul_zero] at hk
          omega
        · simp only [zero_add, mul_one] at hk
          exact absurd (Subgroup.eq_of_le_of_card_ge hle hk.le) hne
        · omega
      calc 2 ^ (r + 1) = 2 * 2 ^ r := by ring
        _ ≤ 2 * Nat.card (Subgroup.closure (φ '' (B : Set α))) := by omega
        _ ≤ Nat.card (Subgroup.closure (φ '' (B : Set α))) * k := by
          rw [mul_comm]
          exact Nat.mul_le_mul_left _ hk2
        _ = _ := hk.symm

lemma closure_eq_top_of_connected {G : Type u} [Group G] (S : Finset G)
    (hconn : (cayleyGraph S).Connected) : Subgroup.closure (S : Set G) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨w⟩ := hconn.preconnected 1 g
  suffices h : ∀ (a b : G) (_ : (cayleyGraph S).Walk a b), a ∈ Subgroup.closure (S : Set G) →
      b ∈ Subgroup.closure (S : Set G) from h 1 g w (one_mem _)
  intro a b w
  induction w with
  | nil => exact id
  | cons h _ ih =>
    intro ha
    apply ih
    rename_i u v _
    rw [SimpleGraph.mulCayley_adj] at h
    rcases h.2 with h' | h'
    · have := mul_mem ha (Subgroup.subset_closure h')
      simpa using this
    · have := mul_mem ha (inv_mem (Subgroup.subset_closure h'))
      simpa using this

/-- **Added labels (§6.1).** If `Cay(G, S)` is connected, there is a symmetric `S₁ ⊆ S` with
`|S₁| ≤ 2 (⌊log₂ (2n)⌋ + 1)` generating `G`, whose lifts generate `G × C₂` whenever those of `S`
do (the nonbipartite case). Obtained by repeatedly adjoining a label outside the subgroup
generated so far, which at least doubles its order. -/
theorem added_labels (S : Finset G) (hS : IsConnectionSet S) (hconn : (cayleyGraph S).Connected) :
    ∃ S₁ : Finset G, S₁ ⊆ S ∧ (∀ s ∈ S₁, s⁻¹ ∈ S₁) ∧
      S₁.card ≤ 2 * (Nat.log 2 (2 * Fintype.card G) + 1) ∧
      Subgroup.closure (S₁ : Set G) = ⊤ ∧ (IsNonbip S → IsNonbip S₁) := by
  have hgen : Subgroup.closure (S : Set G) = ⊤ := closure_eq_top_of_connected S hconn
  -- symmetrization of a subset of `S`
  have hsym : ∀ B ⊆ S, (B ∪ B.image (·⁻¹)) ⊆ S ∧
      (∀ s ∈ B ∪ B.image (·⁻¹), s⁻¹ ∈ B ∪ B.image (·⁻¹)) ∧
      (B ∪ B.image (·⁻¹)).card ≤ 2 * B.card := by
    intro B hB
    refine ⟨union_subset hB (fun s hs => ?_), fun s hs => ?_, ?_⟩
    · obtain ⟨b, hb, rfl⟩ := mem_image.1 hs
      exact hS.1 b (hB hb)
    · rcases mem_union.1 hs with h | h
      · exact mem_union_right _ (mem_image_of_mem _ h)
      · obtain ⟨b, hb, rfl⟩ := mem_image.1 h
        rw [inv_inv]
        exact mem_union_left _ hb
    · calc (B ∪ B.image (·⁻¹)).card ≤ B.card + (B.image (·⁻¹)).card := card_union_le _ _
        _ ≤ B.card + B.card := Nat.add_le_add_left card_image_le _
        _ = 2 * B.card := by ring
  have hsub : ∀ B : Finset G, (B : Set G) ⊆ ((B ∪ B.image (·⁻¹) : Finset G) : Set G) := by
    intro B
    rw [Finset.coe_union]
    exact Set.subset_union_left
  have hlog : Nat.log 2 (Fintype.card G) ≤ Nat.log 2 (2 * Fintype.card G) :=
    Nat.log_mono_right (by omega)
  by_cases hnb : IsNonbip S
  · obtain ⟨B, hBS, hBc, hB⟩ := doubling (fun s : G => (s, Multiplicative.ofAdd (1 : ZMod 2))) S
      hnb (Nat.log 2 (2 * Fintype.card G) + 1)
    have htop : Subgroup.closure
        ((fun s : G => (s, Multiplicative.ofAdd (1 : ZMod 2))) '' (B : Set G)) = ⊤ := by
      refine hB.resolve_right fun h => ?_
      have h1 := Subgroup.card_le_card_group
        (Subgroup.closure ((fun s : G => (s, Multiplicative.ofAdd (1 : ZMod 2))) '' (B : Set G)))
      have h2 : Nat.card (G × Multiplicative (ZMod 2)) = 2 * Fintype.card G := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := G)]
        have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
          rw [Nat.card_eq_fintype_card]
          rfl
        rw [this, mul_comm]
      have h3 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (2 * Fintype.card G)
      omega
    obtain ⟨h1, h2, h3⟩ := hsym B hBS
    have hS1top : Subgroup.closure ((fun s : G => (s, Multiplicative.ofAdd (1 : ZMod 2))) ''
        ((B ∪ B.image (·⁻¹) : Finset G) : Set G)) = ⊤ := by
      rw [eq_top_iff, ← htop]
      exact Subgroup.closure_mono (Set.image_mono (hsub B))
    refine ⟨B ∪ B.image (·⁻¹), h1, h2, h3.trans (by omega), ?_, fun _ => hS1top⟩
    have := congrArg (Subgroup.map (MonoidHom.fst G (Multiplicative (ZMod 2)))) hS1top
    rw [MonoidHom.map_closure, Set.image_image, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 Prod.fst_surjective] at this
    simpa using this
  · obtain ⟨B, hBS, hBc, hB⟩ := doubling (fun s : G => s) S (by simpa using hgen)
      (Nat.log 2 (Fintype.card G) + 1)
    have htop : Subgroup.closure ((fun s : G => s) '' (B : Set G)) = ⊤ := by
      refine hB.resolve_right fun h => ?_
      have h1 := Subgroup.card_le_card_group (Subgroup.closure ((fun s : G => s) '' (B : Set G)))
      rw [Nat.card_eq_fintype_card (α := G)] at h1
      have h3 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Fintype.card G)
      omega
    obtain ⟨h1, h2, h3⟩ := hsym B hBS
    refine ⟨B ∪ B.image (·⁻¹), h1, h2, h3.trans (by omega), ?_, fun h => absurd h hnb⟩
    rw [eq_top_iff, ← htop]
    exact Subgroup.closure_mono (by simpa using hsub B)

end AddedLabels

/-! ### Step E6.1: label sampling (6.2) -/

/-! ### Directional balance (6.9)–(6.11) and the loop bound (6.18) -/

section DirBal

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

/-- **Directional balance (6.9)–(6.11), (6.18).** For every state set `J`, each direction of the
cut `δ_{D(Y)}(J)` has at least a third of its arcs, and the formal loops satisfy
`µ |δ_{D(P)}(J)| ≤ 2 s(J)`. Uses the identity (6.10), `|A_i| = |B_i|`, regularity of `X₀`, the
boundary bound (6.6) with `3 B_* ≤ µ`, and the local form of Lemma 6.3 when `u` is odd. -/
theorem directional_balance (S T Ap Am S₀ : Finset G) (cT : ℝ) (𝒜 : Allocation G)
    (lam D σ η ω cN CN μ B : ℝ) (π ι : G → Fin 𝒜.t)
    (hT : IsTemplate S T Ap Am cT) (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN)
    (hsize : 0 < cN * S.card / lam)
    (hπ : ∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v))
    (hι : ∀ w ∈ 𝒜.W, w ∈ copyVerts Ap Am (𝒜.g (ι w)))
    (hS₀ : IsConnectionSet S₀) (hμB : 3 * B ≤ μ)
    (hB : Odd (Nat.card (Subgroup.closure (T : Set G))) → Res66 T S₀ 𝒜.W B)
    (hloc : Odd (Nat.card (Subgroup.closure (T : Set G))) →
      ∀ (H : G ⧸ Subgroup.closure (T : Set G)) (J : Finset (Fin 𝒜.t × Bool)),
        (∃ v, v ∉ 𝒜.W ∧ (v : G ⧸ Subgroup.closure (T : Set G)) = H ∧ ∃ β, (π v, β) ∈ J) →
        (∃ v, v ∉ 𝒜.W ∧ (v : G ⧸ Subgroup.closure (T : Set G)) = H ∧ ∃ β, (π v, β) ∉ J) →
        μ ≤ cutCnt π (sgnOf 𝒜 Ap π) J ((conY S₀ 𝒜.W).edgeFinset.filter fun e =>
          ∀ v ∈ e, (v : G ⧸ Subgroup.closure (T : Set G)) = H))
    (J : Finset (Fin 𝒜.t × Bool)) :
    (cutCnt π (sgnOf 𝒜 Ap π) J (conY S₀ 𝒜.W).edgeFinset : ℝ) ≤
        3 * outCnt π (sgnOf 𝒜 Ap π) J (conY S₀ 𝒜.W).edgeFinset ∧
      (cutCnt π (sgnOf 𝒜 Ap π) J (conY S₀ 𝒜.W).edgeFinset : ℝ) ≤
        3 * inCnt π (sgnOf 𝒜 Ap π) J (conY S₀ 𝒜.W).edgeFinset ∧
      μ * loopCnt ι (loopSgn 𝒜 Am ι) J 𝒜.W ≤
        2 * cutCnt π (sgnOf 𝒜 Ap π) J (conY S₀ 𝒜.W).edgeFinset := by
  have hpartW : ∀ i, ∀ v ∈ 𝒜.part i, v ∉ 𝒜.W := fun i v hv h =>
    disjoint_left.1 (hgood.part_disjoint i) hv h
  have hπeq : ∀ i, ∀ v ∈ 𝒜.part i, π v = i := fun i v hv => pi_eq_of_mem hgood hπ hv
  obtain ⟨E, hE⟩ : ∃ E : Finset (Sym2 G), E = (conY S₀ 𝒜.W).edgeFinset := ⟨_, rfl⟩
  rw [← hE]
  -- `σ_i` and the signed state indicator `φ`
  let σ : Fin 𝒜.t → ℝ := fun i =>
    (if (i, true) ∈ J then 1 else 0) - (if (i, false) ∈ J then 1 else 0)
  let φ : G → ℝ := fun v => (if (π v, sgnOf 𝒜 Ap π v) ∈ J then 1 else 0) -
    (if (π v, !sgnOf 𝒜 Ap π v) ∈ J then 1 else 0)
  have hφσ : ∀ v, φ v = (if sgnOf 𝒜 Ap π v then 1 else -1) * σ (π v) := by
    intro v
    rcases Bool.eq_false_or_eq_true (sgnOf 𝒜 Ap π v) with h | h <;>
      by_cases h1 : (π v, true) ∈ J <;> by_cases h2 : (π v, false) ∈ J <;> simp [φ, σ, h, h1, h2]
  -- (6.10), edge by edge
  have hedge : ∀ e : Sym2 G, (outArcs π (sgnOf 𝒜 Ap π) J e : ℝ) -
      inArcs π (sgnOf 𝒜 Ap π) J e = φ e.out.1 + φ e.out.2 := by
    intro e
    simp only [outArcs, inArcs, card_filter, Fintype.sum_bool]
    push_cast
    simp only [arcTail, arcHead, φ]
    exact arc_count_identity
  -- the handshake identity
  have hhand : ∀ f : G → ℝ, ∑ e ∈ E, (f e.out.1 + f e.out.2) =
      ∑ v, ((conY S₀ 𝒜.W).degree v : ℝ) * f v := by
    intro f
    have h1 : ∀ e ∈ E, f e.out.1 + f e.out.2 = ∑ v, if v ∈ e then f v else 0 := by
      intro e he
      rw [← sum_filter]
      have hne : e.out.1 ≠ e.out.2 := by
        rw [hE, SimpleGraph.mem_edgeFinset, ← mk_out e, SimpleGraph.mem_edgeSet] at he
        exact he.ne
      have : univ.filter (· ∈ e) = {e.out.1, e.out.2} := by
        ext v
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        constructor
        · intro hv
          rw [← mk_out e, Sym2.mem_iff] at hv
          exact hv
        · rintro (rfl | rfl)
          exacts [Sym2.out_fst_mem e, Sym2.out_snd_mem e]
      rw [this, sum_pair hne]
    rw [sum_congr rfl h1, sum_comm]
    refine sum_congr rfl fun v _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, hE, ← SimpleGraph.incidenceFinset_eq_filter,
      SimpleGraph.card_incidenceFinset_eq_degree]
  -- degrees of `Y = X₀ - W`
  have hnbrX : ∀ v, (univ.filter fun w => (cayleyGraph S₀).Adj v w) = S₀.image (v * ·) := by
    intro v
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_image, SimpleGraph.mulCayley_adj]
    constructor
    · rintro ⟨-, h | h⟩
      · exact ⟨v⁻¹ * w, h, by simp⟩
      · exact ⟨v⁻¹ * w, by simpa using hS₀.1 _ h, by simp⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨fun h => hS₀.2 ?_, Or.inl (by simpa using hs)⟩
      have : v * s = v * 1 := by rw [mul_one]; exact h.symm
      rw [mul_left_cancel this] at hs
      exact hs
  have hdegY : ∀ v, v ∉ 𝒜.W → ((conY S₀ 𝒜.W).degree v : ℝ) =
      S₀.card - (𝒜.W.filter fun w => (cayleyGraph S₀).Adj v w).card := by
    intro v hv
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have h1 : (conY S₀ 𝒜.W).neighborFinset v =
        (univ.filter fun w => (cayleyGraph S₀).Adj v w).filter (fun w => w ∉ 𝒜.W) := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, mem_filter, mem_univ, true_and]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hv, h.2⟩⟩
    have h2 := card_filter_add_card_filter_not (s := univ.filter fun w => (cayleyGraph S₀).Adj v w)
      (fun w => w ∈ 𝒜.W)
    have h3 : (univ.filter fun w => (cayleyGraph S₀).Adj v w).filter (fun w => w ∈ 𝒜.W) =
        𝒜.W.filter fun w => (cayleyGraph S₀).Adj v w := by
      ext w
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    have h4 : (univ.filter fun w => (cayleyGraph S₀).Adj v w).card = S₀.card := by
      rw [hnbrX, card_image_of_injective _ (mul_right_injective v)]
    rw [h3, h4] at h2
    rw [h1]
    have h5 : ((univ.filter fun w => (cayleyGraph S₀).Adj v w).filter (fun w => w ∉ 𝒜.W)).card +
        (𝒜.W.filter fun w => (cayleyGraph S₀).Adj v w).card = S₀.card := by omega
    have h6 : (((univ.filter fun w => (cayleyGraph S₀).Adj v w).filter
        (fun w => w ∉ 𝒜.W)).card : ℝ) + (𝒜.W.filter fun w => (cayleyGraph S₀).Adj v w).card =
        S₀.card := by exact_mod_cast h5
    linarith
  have hdegYW : ∀ v ∈ 𝒜.W, (conY S₀ 𝒜.W).degree v = 0 := by
    intro v hv
    rw [← SimpleGraph.card_neighborFinset_eq_degree, card_eq_zero, eq_empty_iff_forall_notMem]
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    exact hw.2.1 hv
  -- every part is balanced, so the state indicators cancel on `G \ W`
  have hpart0 : ∀ i, ∑ v ∈ 𝒜.part i, φ v = 0 := by
    intro i
    have h1 : ∀ v ∈ 𝒜.part i, φ v = σ i * ((if (𝒜.g i)⁻¹ * v ∈ Ap then 1 else 0) -
        (if (𝒜.g i)⁻¹ * v ∈ Am then 1 else 0)) := by
      intro v hv
      rw [hφσ v, hπeq i v hv]
      have hc : (𝒜.g i)⁻¹ * v ∈ Ap ∪ Am := mem_copyVerts.1 (hgood.part_sub i hv)
      have hsgv : sgnOf 𝒜 Ap π v = true ↔ (𝒜.g i)⁻¹ * v ∈ Ap := by
        unfold sgnOf
        rw [hπeq i v hv]
        simp only [decide_eq_true_eq]
      by_cases hA : (𝒜.g i)⁻¹ * v ∈ Ap
      · have hB : (𝒜.g i)⁻¹ * v ∉ Am := fun h => disjoint_left.1 hT.disjoint hA h
        have hs : sgnOf 𝒜 Ap π v = true := hsgv.2 hA
        simp [hs, hA, hB]
      · have hB : (𝒜.g i)⁻¹ * v ∈ Am := (mem_union.1 hc).resolve_left hA
        have hs : sgnOf 𝒜 Ap π v = false := by
          cases h : sgnOf 𝒜 Ap π v
          · rfl
          · exact absurd (hsgv.1 h) hA
        simp [hs, hA, hB]
    rw [sum_congr rfl h1, ← mul_sum, sum_sub_distrib, sum_boole, sum_boole, hgood.balanced i,
      sub_self, mul_zero]
  have hnotW0 : ∑ v ∈ univ.filter (fun v => v ∉ 𝒜.W), φ v = 0 := by
    rw [← sum_fiberwise_of_maps_to (g := π) (t := univ) (fun v _ => mem_univ (π v)) φ]
    refine sum_eq_zero fun i _ => ?_
    have : (univ.filter fun v => v ∉ 𝒜.W).filter (fun v => π v = i) = 𝒜.part i := by
      ext v
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hv, rfl⟩
        exact hπ v hv
      · intro hv
        exact ⟨hpartW i v hv, hπeq i v hv⟩
    rw [this, hpart0 i]
  -- reserved neighbours
  let ω' : G → ℝ := fun v => ((𝒜.W.filter fun w => (cayleyGraph S₀).Adj v w).card : ℝ)
  have hdiff : (outCnt π (sgnOf 𝒜 Ap π) J E : ℝ) - inCnt π (sgnOf 𝒜 Ap π) J E =
      -∑ v ∈ univ.filter (fun v => v ∉ 𝒜.W), ω' v * φ v := by
    have h1 : (outCnt π (sgnOf 𝒜 Ap π) J E : ℝ) - inCnt π (sgnOf 𝒜 Ap π) J E =
        ∑ e ∈ E, (φ e.out.1 + φ e.out.2) := by
      unfold outCnt inCnt
      push_cast
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun e _ => hedge e
    rw [h1, hhand φ, ← sum_filter_add_sum_filter_not univ (fun v => v ∈ 𝒜.W)]
    have hW0 : ∑ v ∈ univ.filter (fun v => v ∈ 𝒜.W), ((conY S₀ 𝒜.W).degree v : ℝ) * φ v = 0 :=
      sum_eq_zero fun v hv => by rw [hdegYW v (mem_filter.1 hv).2]; simp
    rw [hW0, zero_add, sum_congr rfl (fun v hv => by rw [hdegY v (mem_filter.1 hv).2])]
    simp only [sub_mul, sum_sub_distrib]
    rw [← mul_sum, hnotW0, mul_zero, zero_sub]
  have hsgn_abs : ∀ v, |(if sgnOf 𝒜 Ap π v then (1 : ℝ) else -1)| = 1 := by
    intro v
    split_ifs <;> norm_num
  have hφbd : ∀ v, |φ v| ≤ if σ (π v) ≠ 0 then 1 else 0 := by
    intro v
    rw [hφσ v, abs_mul, hsgn_abs v, one_mul]
    have hσ : |σ (π v)| ≤ 1 := by
      simp only [σ]
      split_ifs <;> norm_num
    by_cases h : σ (π v) = 0
    · rw [if_neg (not_not.2 h), h, abs_zero]
    · rw [if_pos h]
      exact hσ
  have hsumbd : |∑ v ∈ univ.filter (fun v => v ∉ 𝒜.W), ω' v * φ v| ≤
      ∑ v ∈ univ.filter (fun v => v ∉ 𝒜.W ∧ σ (π v) ≠ 0), ω' v := by
    calc _ ≤ ∑ v ∈ univ.filter (fun v => v ∉ 𝒜.W), |ω' v * φ v| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ v ∈ univ.filter (fun v => v ∉ 𝒜.W), (if σ (π v) ≠ 0 then ω' v else 0) :=
          sum_le_sum fun v _ => by
            have hω : 0 ≤ ω' v := Nat.cast_nonneg _
            rw [abs_mul, abs_of_nonneg hω]
            have := hφbd v
            split_ifs at this ⊢ with h
            · calc ω' v * |φ v| ≤ ω' v * 1 := mul_le_mul_of_nonneg_left this hω
                _ = ω' v := mul_one _
            · have : |φ v| = 0 := le_antisymm this (abs_nonneg _)
              rw [this, mul_zero]
      _ = _ := by rw [← sum_filter, filter_filter]
  -- the cosets met by a part with `σ ≠ 0`
  let Q : Finset (G ⧸ Subgroup.closure (T : Set G)) :=
    (univ.filter fun v => v ∉ 𝒜.W ∧ σ (π v) ≠ 0).image
      (fun v : G => (v : G ⧸ Subgroup.closure (T : Set G)))
  have hcut_eq : (cutCnt π (sgnOf 𝒜 Ap π) J E : ℝ) =
      outCnt π (sgnOf 𝒜 Ap π) J E + inCnt π (sgnOf 𝒜 Ap π) J E := by
    unfold cutCnt
    push_cast
    ring
  have hout0 : (0 : ℝ) ≤ outCnt π (sgnOf 𝒜 Ap π) J E := Nat.cast_nonneg _
  have hin0 : (0 : ℝ) ≤ inCnt π (sgnOf 𝒜 Ap π) J E := Nat.cast_nonneg _
  by_cases hodd : Odd (Nat.card (Subgroup.closure (T : Set G)))
  · have hRes := hB hodd
    have hcoset : ∑ v ∈ univ.filter (fun v => v ∉ 𝒜.W ∧ σ (π v) ≠ 0), ω' v ≤ Q.card * B := by
      have hmaps : ∀ v ∈ univ.filter (fun v => v ∉ 𝒜.W ∧ σ (π v) ≠ 0),
          (v : G ⧸ Subgroup.closure (T : Set G)) ∈ Q := fun v hv =>
        mem_image_of_mem (fun v : G => (v : G ⧸ Subgroup.closure (T : Set G))) hv
      rw [← Finset.sum_fiberwise_of_maps_to hmaps ω']
      calc ∑ H ∈ Q, ∑ v ∈ (univ.filter fun v => v ∉ 𝒜.W ∧ σ (π v) ≠ 0).filter
            (fun v : G => (v : G ⧸ Subgroup.closure (T : Set G)) = H), ω' v
          ≤ ∑ _H ∈ Q, B := sum_le_sum fun H _ => by
            have hH := hRes H
            push_cast at hH
            refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.cast_nonneg _)) hH
            intro v hv
            simp only [mem_filter, mem_univ, true_and] at hv ⊢
            exact ⟨hv.1.1, hv.2⟩
        _ = Q.card * B := by rw [sum_const, nsmul_eq_mul]
    have hsQ : (Q.card : ℝ) * μ ≤ cutCnt π (sgnOf 𝒜 Ap π) J E := by
      have hEH : ∀ H ∈ Q, μ ≤ cutCnt π (sgnOf 𝒜 Ap π) J (E.filter fun e =>
          ∀ v : G, v ∈ e → (v : G ⧸ Subgroup.closure (T : Set G)) = H) := by
        intro H hH
        obtain ⟨v, hv, rfl⟩ := mem_image.1 hH
        rw [mem_filter] at hv
        have hσ := hv.2.2
        rw [hE]
        apply hloc hodd _ J
        · by_cases h1 : (π v, true) ∈ J
          · exact ⟨v, hv.2.1, rfl, true, h1⟩
          · by_cases h2 : (π v, false) ∈ J
            · exact ⟨v, hv.2.1, rfl, false, h2⟩
            · exfalso
              apply hσ
              simp [σ, h1, h2]
        · by_cases h1 : (π v, true) ∈ J
          · by_cases h2 : (π v, false) ∈ J
            · exfalso
              apply hσ
              simp [σ, h1, h2]
            · exact ⟨v, hv.2.1, rfl, false, h2⟩
          · exact ⟨v, hv.2.1, rfl, true, h1⟩
      have hdisjE : (Q : Set (G ⧸ Subgroup.closure (T : Set G))).PairwiseDisjoint (fun H =>
          E.filter fun e => ∀ v : G, v ∈ e → (v : G ⧸ Subgroup.closure (T : Set G)) = H) := by
        intro H _ H' _ hne
        simp only [Function.onFun]
        rw [disjoint_left]
        intro e he he'
        rw [mem_filter] at he he'
        exact hne ((he.2 _ (Sym2.out_fst_mem e)).symm.trans (he'.2 _ (Sym2.out_fst_mem e)))
      have hsub : (Q.biUnion fun H => E.filter fun e =>
          ∀ v : G, v ∈ e → (v : G ⧸ Subgroup.closure (T : Set G)) = H) ⊆ E :=
        biUnion_subset.2 fun H _ => filter_subset _ _
      calc (Q.card : ℝ) * μ = ∑ _H ∈ Q, μ := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ H ∈ Q, (cutCnt π (sgnOf 𝒜 Ap π) J (E.filter fun e =>
            ∀ v : G, v ∈ e → (v : G ⧸ Subgroup.closure (T : Set G)) = H) : ℝ) := sum_le_sum hEH
        _ = cutCnt π (sgnOf 𝒜 Ap π) J (Q.biUnion fun H => E.filter fun e =>
            ∀ v : G, v ∈ e → (v : G ⧸ Subgroup.closure (T : Set G)) = H) := by
          unfold cutCnt outCnt inCnt
          push_cast
          rw [sum_biUnion hdisjE, sum_biUnion hdisjE, ← sum_add_distrib]
        _ ≤ cutCnt π (sgnOf 𝒜 Ap π) J E := by
          unfold cutCnt outCnt inCnt
          push_cast
          exact add_le_add (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _)
            (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _)
    have hdev : |(outCnt π (sgnOf 𝒜 Ap π) J E : ℝ) - inCnt π (sgnOf 𝒜 Ap π) J E| ≤
        Q.card * B := by
      rw [hdiff, abs_neg]
      exact hsumbd.trans hcoset
    have hB3 : (Q.card : ℝ) * B ≤ cutCnt π (sgnOf 𝒜 Ap π) J E / 3 := by
      have : (Q.card : ℝ) * (3 * B) ≤ Q.card * μ :=
        mul_le_mul_of_nonneg_left hμB (Nat.cast_nonneg _)
      linarith
    have habs := abs_le.1 hdev
    refine ⟨by linarith [habs.1, habs.2], by linarith [habs.1, habs.2], ?_⟩
    -- the formal loops (6.18)
    have hloopQ : (loopCnt ι (loopSgn 𝒜 Am ι) J 𝒜.W : ℝ) ≤ 2 * Q.card := by
      have hcond : ∀ w ∈ 𝒜.W, (((ι w, loopSgn 𝒜 Am ι w) ∈ J ∧ (ι w, !loopSgn 𝒜 Am ι w) ∉ J) ∨
          ((ι w, !loopSgn 𝒜 Am ι w) ∈ J ∧ (ι w, loopSgn 𝒜 Am ι w) ∉ J)) →
          (w : G ⧸ Subgroup.closure (T : Set G)) ∈ Q := by
        intro w hw hc
        have hσ : σ (ι w) ≠ 0 := by
          rcases Bool.eq_false_or_eq_true (loopSgn 𝒜 Am ι w) with h | h <;>
            rw [h] at hc <;> rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all [σ]
        obtain ⟨v, hv⟩ : (𝒜.part (ι w)).Nonempty := by
          rw [← card_pos]
          have := hgood.size_lower (ι w)
          have : (0 : ℝ) < (𝒜.part (ι w)).card := lt_of_lt_of_le hsize this
          exact_mod_cast this
        refine mem_image.2 ⟨v, mem_filter.2 ⟨mem_univ _, hpartW _ v hv,
          by rwa [hπeq _ v hv]⟩, ?_⟩
        rw [QuotientGroup.eq]
        exact copy_coset hT _ (hgood.part_sub _ hv) (hι w hw)
      unfold loopCnt
      push_cast
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
      have hcard : (𝒜.W.filter fun w => ((ι w, loopSgn 𝒜 Am ι w) ∈ J ∧
          (ι w, !loopSgn 𝒜 Am ι w) ∉ J) ∨ ((ι w, !loopSgn 𝒜 Am ι w) ∈ J ∧
          (ι w, loopSgn 𝒜 Am ι w) ∉ J)).card ≤ Q.card := by
        refine card_le_card_of_injOn (fun w : G => (w : G ⧸ Subgroup.closure (T : Set G))) ?_ ?_
        · intro w hw
          rw [Finset.mem_coe, mem_filter] at hw
          exact hcond w hw.1 hw.2
        · intro w hw w' hw' h
          rw [Finset.mem_coe, mem_filter] at hw hw'
          exact reserved_unique hgood w w w' hw.1 hw'.1 (by simp) (QuotientGroup.eq.1 h)
      have : ((𝒜.W.filter fun w => ((ι w, loopSgn 𝒜 Am ι w) ∈ J ∧
          (ι w, !loopSgn 𝒜 Am ι w) ∉ J) ∨ ((ι w, !loopSgn 𝒜 Am ι w) ∈ J ∧
          (ι w, loopSgn 𝒜 Am ι w) ∉ J)).card : ℝ) ≤ Q.card := by exact_mod_cast hcard
      linarith
    have hl0 : (0 : ℝ) ≤ loopCnt ι (loopSgn 𝒜 Am ι) J 𝒜.W := Nat.cast_nonneg _
    by_cases hμ0 : 0 ≤ μ
    · have := mul_le_mul_of_nonneg_left hloopQ hμ0
      nlinarith
    · push_neg at hμ0
      have : μ * loopCnt ι (loopSgn 𝒜 Am ι) J 𝒜.W ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hμ0.le hl0
      linarith
  · have hW : 𝒜.W = ∅ := hgood.reserved.2 (Nat.not_odd_iff_even.1 hodd)
    have hω0 : ∀ v, ω' v = 0 := by
      intro v
      simp [ω', hW]
    have hdev : (outCnt π (sgnOf 𝒜 Ap π) J E : ℝ) - inCnt π (sgnOf 𝒜 Ap π) J E = 0 := by
      rw [hdiff]
      simp [hω0]
    refine ⟨by linarith, by linarith, ?_⟩
    have : loopCnt ι (loopSgn 𝒜 Am ι) J 𝒜.W = 0 := by simp [loopCnt, hW]
    rw [this, Nat.cast_zero, mul_zero]
    linarith

end DirBal

/-! ### Cut counting for state cuts -/

section CutCount

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

/-- **Cut counting (6.4) for the two-state graph** (nonbipartite case): if there is at least one
part and every nontrivial state cut has at least `µ ≥ 6` arcs, then fewer than `(j+1)µ` arcs cross
at most `(4 (t + |F|))^{16(j+1)}` state sets. (For `t = 0` and `F = ∅` the bound would fail.) -/
theorem state_cut_count {t : ℕ} (ht : 0 < t) (π : G → Fin t) (sg : G → Bool) (F : Finset (Sym2 G)) (μ : ℝ)
    (hμ : 6 ≤ μ)
    (hcut : ∀ J : Finset (Fin t × Bool), J.Nonempty → J ≠ univ → μ ≤ cutCnt π sg J F) (j : ℕ) :
    (((univ : Finset (Finset (Fin t × Bool))).filter fun J =>
      (cutCnt π sg J F : ℝ) < (j + 1) * μ).card : ℝ) ≤ (4 * (t + F.card)) ^ (16 * (j + 1)) := by
  haveI : Nonempty (Fin t × Bool) := ⟨(⟨0, ht⟩, true)⟩
  -- the two-state multigraph: arcs are (edge, twin index)
  let ends : {e // e ∈ F} × Bool → (Fin t × Bool) × (Fin t × Bool) :=
    fun a => (arcTail π sg a.1.1 a.2, arcHead π sg a.1.1 a.2)
  have hcross : ∀ J : Finset (Fin t × Bool),
      (univ.filter fun a => ((ends a).1 ∈ J) ≠ ((ends a).2 ∈ J)).card = cutCnt π sg J F := by
    intro J
    unfold cutCnt outCnt inCnt outArcs inArcs
    rw [← sum_add_distrib, card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
    rw [← Finset.sum_coe_sort F]
    refine Fintype.sum_congr _ _ fun e => ?_
    simp only [ends, card_filter, Fintype.sum_bool]
    by_cases h1 : arcTail π sg e.1 true ∈ J <;> by_cases h2 : arcHead π sg e.1 true ∈ J <;>
      by_cases h3 : arcTail π sg e.1 false ∈ J <;> by_cases h4 : arcHead π sg e.1 false ∈ J <;>
      simp [h1, h2, h3, h4]
  set μ' : ℕ := ⌊μ⌋₊ with hμ'
  have hμ0 : 0 ≤ μ := by linarith
  have hμ'6 : 6 ≤ μ' := Nat.le_floor (by exact_mod_cast hμ)
  have hμ'le : (μ' : ℝ) ≤ μ := Nat.floor_le hμ0
  have hμ'gt : μ < μ' + 1 := Nat.lt_floor_add_one μ
  have hcut' : ∀ U : Finset (Fin t × Bool), U.Nonempty → U ≠ univ →
      μ' ≤ (univ.filter fun a => ((ends a).1 ∈ U) ≠ ((ends a).2 ∈ U)).card := by
    intro U hU hU'
    rw [hcross U]
    have := hcut U hU hU'
    exact_mod_cast hμ'le.trans this
  have hcc := cut_count ends μ' hμ'6 hcut' (2 * j + 1)
  have hsub : ((univ : Finset (Finset (Fin t × Bool))).filter fun J =>
      (cutCnt π sg J F : ℝ) < (j + 1) * μ) ⊆ (univ : Finset (Finset (Fin t × Bool))).filter
        fun U => (univ.filter fun a => ((ends a).1 ∈ U) ≠ ((ends a).2 ∈ U)).card <
          (2 * j + 1 + 1) * μ' := by
    intro J hJ
    rw [mem_filter] at hJ ⊢
    refine ⟨hJ.1, ?_⟩
    rw [hcross J]
    have h1 : (j + 1 : ℝ) * μ ≤ (2 * j + 1 + 1) * μ' := by
      have : μ ≤ 2 * μ' := by linarith
      have hj : (0 : ℝ) ≤ j + 1 := by positivity
      nlinarith
    have h2 : (cutCnt π sg J F : ℝ) < (2 * j + 1 + 1) * μ' := lt_of_lt_of_le hJ.2 h1
    exact_mod_cast h2
  have hcardV : Fintype.card (Fin t × Bool) = 2 * t := by simp [mul_comm]
  have hcardE : Fintype.card ({e // e ∈ F} × Bool) = 2 * F.card := by simp [mul_comm]
  rw [hcardV, hcardE] at hcc
  have h1 := (card_le_card hsub).trans hcc
  have h2 : (2 * (2 * t + 2 * F.card)) ^ (4 * (2 * j + 1 + 1)) ≤
      (4 * (t + F.card)) ^ (16 * (j + 1)) := by
    have hb : 1 ≤ 4 * (t + F.card) := by omega
    calc (2 * (2 * t + 2 * F.card)) ^ (4 * (2 * j + 1 + 1))
        = (4 * (t + F.card)) ^ (8 * (j + 1)) := by ring_nf
      _ ≤ (4 * (t + F.card)) ^ (16 * (j + 1)) := Nat.pow_le_pow_right hb (by omega)
  have h3 := h1.trans h2
  exact_mod_cast h3

end CutCount


end Connector

end Lovasz
