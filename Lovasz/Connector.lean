/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
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
# Proposition 6.1: the sparse connecting system

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

/-- **Label sampling (6.2).** Retain the inverse label classes of `T` independently with
probability `t₀/d`, `t₀ = A₁ λ L`. For a successful allocation, with probability at least `3/4`
every full-copy vertex has at least `c₂ L = Ω(t₀/λ)` neighbours in the part via retained labels,
and at most `2t₀` classes (so at most `4t₀` labels) are retained. -/
theorem label_sampling (cT A₀ cN : ℝ) (hcT : 0 < cT) (hA₀ : 0 < A₀) (hcN : 0 < cN) :
    ∃ A₁ c₂ : ℝ, 0 < A₁ ∧ 0 < c₂ ∧ ∃ n₀ : ℕ,
      ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S T Ap Am : Finset G)
        (𝒜 : Allocation G) (D σ η ω CN : ℝ),
        n₀ ≤ Fintype.card G → IsConnectionSet S →
        Real.log (Fintype.card G) ^ 12 ≤ S.card → IsTemplate S T Ap Am cT →
        𝒜.Good S T Ap Am (A₀ * Real.log (Fintype.card G)) D σ η ω cN CN →
        (labelLaw G (A₁ * A₀ * Real.log (Fintype.card G) ^ 2 / S.card)).P (fun ξ =>
          ¬ (Sampled62 𝒜 T Ap Am ξ (c₂ * Real.log (Fintype.card G)) ∧
            ((sampled T ξ).card : ℝ) ≤ 4 * A₁ * A₀ * Real.log (Fintype.card G) ^ 2)) ≤ 1 / 4 := by
  sorry

/-! ### Step E6.5: the reservation estimates (6.5)–(6.6) -/

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
  sorry

/-! ### Lemma 6.3: allocation cuts -/

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
  sorry

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

/-- **State cuts in the bipartite case (§6.3).** If `X = Cay(G, S)` is bipartite, the two-state
graph of `Y` splits into two copies of the ordinary contraction (one oriented from the global
positive side to the negative side, one reversed). Hence, if the ordinary contraction has minimum
cut at least `µ ≥ 6`, every state cut has `0` or at least `µ` arcs, and the state cuts with fewer
than `(j+1)µ` arcs number at most `(4 (t + |E(Y)|))^{16(j+1)}`.

Proof sketch: `¬ IsNonbip S` gives a character `χ : G → C₂` with `χ(s) = 1` on `S`; `W = ∅` since
`χ` maps `⟨T⟩` onto `C₂`, so `u` is even. By connectivity of the template, the local sign of `v`
in its part is `ε_{π v} + χ(v)`. Hence the arc of an edge `xy` with tail at `x` joins
`π x, π y` inside the component `χ(x)` of the state graph, where component `c` consists of the
states `(i, c + ε_i)`. Writing `J_c = {i : (i, c + ε_i) ∈ J}`, the state cut of `J` is the sum of
the two ordinary part cuts of `J₀, J₁`, and `J ↦ (J₀, J₁)` is injective; apply (6.4) to the
ordinary contraction. -/
theorem bip_state_cuts (S T Ap Am S₀ : Finset G) (cT : ℝ) (𝒜 : Allocation G)
    (lam D σ η ω cN CN μ : ℝ) (π : G → Fin 𝒜.t) (hS : IsConnectionSet S)
    (hconn : (cayleyGraph S).Connected) (hbip : ¬ IsNonbip S)
    (hT : IsTemplate S T Ap Am cT) (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN)
    (hπ : ∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v)) (hS₀ : S₀ ⊆ S) (hμ : 6 ≤ μ)
    (hcut : ∀ I : Finset (Fin 𝒜.t), I.Nonempty → I ≠ univ →
      μ ≤ ((conY S₀ 𝒜.W).edgeFinset.filter (PartCross π I)).card) :
    (∀ J : Finset (Fin 𝒜.t × Bool),
      cutCnt π (sgnOf 𝒜 Ap π) J (conY S₀ 𝒜.W).edgeFinset = 0 ∨
        μ ≤ cutCnt π (sgnOf 𝒜 Ap π) J (conY S₀ 𝒜.W).edgeFinset) ∧
    ∀ j : ℕ, (((univ : Finset (Finset (Fin 𝒜.t × Bool))).filter fun J =>
      (cutCnt π (sgnOf 𝒜 Ap π) J (conY S₀ 𝒜.W).edgeFinset : ℝ) < (j + 1) * μ).card : ℝ) ≤
        (4 * (𝒜.t + (conY S₀ 𝒜.W).edgeFinset.card)) ^ (16 * (j + 1)) := by
  sorry

end CutCount

/-! ### Step E6.13: the random matching -/

section Matching

variable {G : Type u} [Fintype G] [DecidableEq G]

/-- **The matching `R` and the marks `Z₀` (§6.4, (6.13)–(6.17)).** Apply Lemma 6.4 to `Y` with
edge probability `p` and marking probability `1/128`. Given directional balance, the gap
`s(J) ∈ {0} ∪ [µ, ∞)`, the part-cut bound and cut counting for the state cuts, and endpoint tests
`(A, τ)` with mean `≤ pk|A| ≤ τ/2`, a union bound gives an outcome with
`|δ^±_{D(R)}(J)| ≥ ps/12`, `|δ_{D(R)}(J)| ≤ 2ps`, `|δ_{D(Z₀)}(J)| ≤ ps/64` for every state set
`J` (`s = s(J)`), a marked edge across every nontrivial part cut, at least `256` unmarked
matching edges across every nontrivial part cut (6.15), and `|A ∩ V(R)| ≤ τ` for every test
(6.17).

Proof sketch (constants checked): for a state set `J` with `s = s(J) ≥ µ`, the tails of Lemma 6.4
give failure probabilities at most `e^{-3ps/64}` (each direction, mean `≥ ps/3`), `e^{-3ps/16}`
(`|δ_{D(R)}| > 2ps`, mean `ps`), `e^{-3ps/2048}` (`|δ_{D(Z₀)}| > ps/64`, mean `ps/128`); for a part
cut `I` with `s = s(I × Bool) ≥ µ`, at most `e^{-ps/1024}` (no marked crossing edge, mean `ps/256`)
and `e^{-127ps/4096}` (fewer than `256` unmarked crossing edges, mean `127ps/256 ≥ 512`). All are
`≤ e^{-ps/2048}`, so the cut events cost `≤ ∑_{j ≥ 1} 6 N^{16(j+1)} e^{-jpµ/2048} ≤ 6∑_j e^{-4j}`
by `hcount` and `hpµ₂`; state sets with `s(J) = 0` impose nothing. A test `(A, τ)` fails with
probability `≤ e^{-3τ/40}` (mean `≤ τ/2`), and these sum to `≤ e^{-2}`. The total is `< 1`. -/
theorem exists_matching {t : ℕ} (Y : SimpleGraph G) (π : G → Fin t) (sg : G → Bool) (k : ℕ)
    (hk : ∀ v, Y.degree v ≤ k) (p μ : ℝ) (hp : 0 < p) (hpk : p * k ^ 2 ≤ 1) (hμ : 6 ≤ μ)
    (hpμ₁ : 1100 ≤ p * μ)
    (hpμ₂ : 32 * Real.log (4 * (t + Y.edgeFinset.card)) + 4 ≤ p * μ / 2048)
    (hbal : ∀ J : Finset (Fin t × Bool),
      (cutCnt π sg J Y.edgeFinset : ℝ) ≤ 3 * outCnt π sg J Y.edgeFinset ∧
        (cutCnt π sg J Y.edgeFinset : ℝ) ≤ 3 * inCnt π sg J Y.edgeFinset)
    (hgap : ∀ J : Finset (Fin t × Bool),
      cutCnt π sg J Y.edgeFinset = 0 ∨ μ ≤ cutCnt π sg J Y.edgeFinset)
    (hpart : ∀ I : Finset (Fin t), I.Nonempty → I ≠ univ →
      μ ≤ cutCnt π sg (I ×ˢ univ) Y.edgeFinset)
    (hcount : ∀ j : ℕ, (((univ : Finset (Finset (Fin t × Bool))).filter fun J =>
      (cutCnt π sg J Y.edgeFinset : ℝ) < (j + 1) * μ).card : ℝ) ≤
        (4 * (t + Y.edgeFinset.card)) ^ (16 * (j + 1)))
    (tests : Finset (Finset G × ℝ))
    (htests : ∀ q ∈ tests, p * k * q.1.card ≤ q.2 / 2 ∧
      Real.log tests.card + 2 ≤ 3 / 40 * q.2) :
    ∃ R Z₀ : Finset (Sym2 G), Z₀ ⊆ R ∧ R ⊆ Y.edgeFinset ∧
      (∀ e ∈ R, ∀ f ∈ R, e ≠ f → ∀ v ∈ e, v ∉ f) ∧
      (∀ J : Finset (Fin t × Bool),
        p * cutCnt π sg J Y.edgeFinset / 12 ≤ outCnt π sg J R ∧
        p * cutCnt π sg J Y.edgeFinset / 12 ≤ inCnt π sg J R ∧
        (cutCnt π sg J R : ℝ) ≤ 2 * p * cutCnt π sg J Y.edgeFinset ∧
        (cutCnt π sg J Z₀ : ℝ) ≤ p * cutCnt π sg J Y.edgeFinset / 64) ∧
      (∀ I : Finset (Fin t), I.Nonempty → I ≠ univ → ∃ e ∈ Z₀, PartCross π I e) ∧
      (∀ I : Finset (Fin t), I.Nonempty → I ≠ univ →
        256 ≤ ((R \ Z₀).filter (PartCross π I)).card) ∧
      ∀ q ∈ tests, ((q.1.filter (· ∈ vtx R)).card : ℝ) ≤ q.2 := by
  sorry

end Matching


/-! ### Step E6.int: the reserved-vertex paths and the integral connector -/

section Integral

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

/-- **Inserting the reserved vertices and choosing an integral connector (§6.5).** Given the
matching `R ⊇ Z₀` with the cut estimates (6.13)–(6.15), the endpoint bounds (6.17), and the loop
bound (6.18), choose the paths `a_H w_H b_H`, a feasible circulation (4.6) with the capacities
`[1, 1]` on `Z₀ ∪ P` and `[ε, 1 - ε]` (`ε = 1/256`) on `R \ Z₀`, symmetrize it (Lemma 4.4), and
round it by Lemma 4.1; the resulting `M` is a connecting system. -/
theorem connector_of_matching (S T Ap Am : Finset G) (cT : ℝ) (𝒜 : Allocation G)
    (lam D σ η ω cN CN : ℝ) (hT : IsTemplate S T Ap Am cT)
    (hgood : 𝒜.Good S T Ap Am lam D σ η ω cN CN) (ht : 2 ≤ 𝒜.t) (π ι : G → Fin 𝒜.t)
    (hπ : ∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v))
    (hι : ∀ w ∈ 𝒜.W, w ∈ copyVerts Ap Am (𝒜.g (ι w)))
    (R Z₀ : Finset (Sym2 G)) (hZR : Z₀ ⊆ R)
    (hRadj : ∀ e ∈ R, (cayleyGraph S).Adj e.out.1 e.out.2 ∧ e.out.1 ∉ 𝒜.W ∧ e.out.2 ∉ 𝒜.W)
    (hRmatch : ∀ e ∈ R, ∀ f ∈ R, e ≠ f → ∀ v ∈ e, v ∉ f)
    (s : Finset (Fin 𝒜.t × Bool) → ℝ) (p μ εE εN : ℝ) (hs : ∀ J, 0 ≤ s J) (hμ : 0 < μ)
    (hpμ : 40 ≤ p * μ)
    (hout : ∀ J, p * s J / 12 ≤ outCnt π (sgnOf 𝒜 Ap π) J R)
    (hcutR : ∀ J, (cutCnt π (sgnOf 𝒜 Ap π) J R : ℝ) ≤ 2 * p * s J)
    (hcutZ : ∀ J, (cutCnt π (sgnOf 𝒜 Ap π) J Z₀ : ℝ) ≤ p * s J / 64)
    (hloop : ∀ J, μ * loopCnt ι (loopSgn 𝒜 Am ι) J 𝒜.W ≤ 2 * s J)
    (hconn : ∀ I : Finset (Fin 𝒜.t), I.Nonempty → I ≠ univ → ∃ e ∈ Z₀, PartCross π I e)
    (hslack : ∀ I : Finset (Fin 𝒜.t), I.Nonempty → I ≠ univ →
      256 ≤ ((R \ Z₀).filter (PartCross π I)).card)
    (hfew : ∀ i, (((𝒜.part i).filter (· ∈ vtx R)).card : ℝ) + 2 ≤ εE * (𝒜.part i).card)
    (hsparse : ∀ i, ∀ v ∈ copyVerts Ap Am (𝒜.g i),
      (((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y ∧ y ∈ vtx R).card : ℝ) +
        2 ≤ εN)
    (hεN : εN ≤ cN * S.card / lam) :
    ∃ M : SimpleGraph G, 𝒜.IsConnector S T Ap Am M εE εN := by
  -- basic facts
  have hpartW : ∀ i, ∀ v ∈ 𝒜.part i, v ∉ 𝒜.W := fun i v hv h =>
    disjoint_left.1 (hgood.part_disjoint i) hv h
  have hπeq : ∀ i, ∀ v ∈ 𝒜.part i, π v = i := fun i v hv => pi_eq_of_mem hgood hπ hv
  have hRmem : ∀ r : Sym2 G, ∀ v ∈ r, v = r.out.1 ∨ v = r.out.2 := by
    intro r v hv
    rw [← mk_out r, Sym2.mem_iff] at hv
    exact hv
  have hRW : ∀ r ∈ R, ∀ v ∈ r, v ∉ 𝒜.W := by
    intro r hr v hv
    rcases hRmem r v hv with rfl | rfl
    · exact (hRadj r hr).2.1
    · exact (hRadj r hr).2.2
  have hRne : ∀ r ∈ R, r.out.1 ≠ r.out.2 := fun r hr => (hRadj r hr).1.ne
  have hmatch : ∀ e ∈ R, ∀ f ∈ R, ∀ v, v ∈ e → v ∈ f → e = f := by
    intro e he f hf v hve hvf
    by_contra hne
    exact hRmatch e he f hf hne v hve hvf
  have hιinj : ∀ w ∈ 𝒜.W, ∀ w' ∈ 𝒜.W, ι w = ι w' → w = w' := by
    intro w hw w' hw' h
    refine reserved_unique hgood w w w' hw hw' (by simp) ?_
    exact copy_coset hT _ (hι w hw) (by rw [h]; exact hι w' hw')
  -- the paths `a_H w_H b_H`
  have hpath : ∀ w ∈ 𝒜.W, ∃ x y : G, x ≠ y ∧ x ∈ 𝒜.part (ι w) ∧ y ∈ 𝒜.part (ι w) ∧
      (copyGraph T Ap Am (𝒜.g (ι w))).Adj w x ∧ (copyGraph T Ap Am (𝒜.g (ι w))).Adj w y ∧
      x ∉ vtx R ∧ y ∉ vtx R := by
    intro w hw
    have h1 := hgood.nbhd_lower (ι w) w (hι w hw)
    have h2 := hsparse (ι w) w (hι w hw)
    have hsplit := card_filter_add_card_filter_not (s := (𝒜.part (ι w)).filter fun y =>
      (copyGraph T Ap Am (𝒜.g (ι w))).Adj w y) (fun y => y ∈ vtx R)
    simp only [filter_filter] at hsplit
    have h3 : (1 : ℝ) < ((𝒜.part (ι w)).filter fun y =>
        (copyGraph T Ap Am (𝒜.g (ι w))).Adj w y ∧ y ∉ vtx R).card := by
      have h4 : (((𝒜.part (ι w)).filter fun y => (copyGraph T Ap Am (𝒜.g (ι w))).Adj w y ∧
          y ∈ vtx R).card : ℝ) + ((𝒜.part (ι w)).filter fun y =>
          (copyGraph T Ap Am (𝒜.g (ι w))).Adj w y ∧ y ∉ vtx R).card =
          (((𝒜.part (ι w)).filter fun y => (copyGraph T Ap Am (𝒜.g (ι w))).Adj w y).card : ℝ) := by
        exact_mod_cast hsplit
      linarith
    obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.1 (by exact_mod_cast h3)
    rw [mem_filter] at hx hy
    exact ⟨x, y, hxy, hx.1, hy.1, hx.2.1, hy.2.1, hx.2.2, hy.2.2⟩
  choose! pa pb hpab using hpath
  have hpa_ne : ∀ w ∈ 𝒜.W, pa w ≠ pb w := fun w hw => (hpab w hw).1
  have hpa_part : ∀ w ∈ 𝒜.W, pa w ∈ 𝒜.part (ι w) := fun w hw => (hpab w hw).2.1
  have hpb_part : ∀ w ∈ 𝒜.W, pb w ∈ 𝒜.part (ι w) := fun w hw => (hpab w hw).2.2.1
  have hpa_adj : ∀ w ∈ 𝒜.W, (copyGraph T Ap Am (𝒜.g (ι w))).Adj w (pa w) :=
    fun w hw => (hpab w hw).2.2.2.1
  have hpb_adj : ∀ w ∈ 𝒜.W, (copyGraph T Ap Am (𝒜.g (ι w))).Adj w (pb w) :=
    fun w hw => (hpab w hw).2.2.2.2.1
  have hpa_R : ∀ w ∈ 𝒜.W, pa w ∉ vtx R := fun w hw => (hpab w hw).2.2.2.2.2.1
  have hpb_R : ∀ w ∈ 𝒜.W, pb w ∉ vtx R := fun w hw => (hpab w hw).2.2.2.2.2.2
  have hpa_W : ∀ w ∈ 𝒜.W, pa w ∉ 𝒜.W := fun w hw => hpartW _ _ (hpa_part w hw)
  have hpb_W : ∀ w ∈ 𝒜.W, pb w ∉ 𝒜.W := fun w hw => hpartW _ _ (hpb_part w hw)
  have hend_part : ∀ w ∈ 𝒜.W, ∀ x, (x = pa w ∨ x = pb w) → x ∈ 𝒜.part (ι w) := by
    rintro w hw x (rfl | rfl)
    exacts [hpa_part w hw, hpb_part w hw]
  have hpend : ∀ w ∈ 𝒜.W, ∀ w' ∈ 𝒜.W, ∀ x, (x = pa w ∨ x = pb w) → (x = pa w' ∨ x = pb w') →
      w = w' := by
    intro w hw w' hw' x hx hx'
    exact hιinj w hw w' hw' ((hπeq _ _ (hend_part w hw x hx)).symm.trans
      (hπeq _ _ (hend_part w' hw' x hx')))
  have hsg_nbr : ∀ w ∈ 𝒜.W, ∀ x, x ∈ 𝒜.part (ι w) →
      (copyGraph T Ap Am (𝒜.g (ι w))).Adj w x → sgnOf 𝒜 Ap π x = loopSgn 𝒜 Am ι w := by
    intro w hw x hx hadj
    unfold sgnOf loopSgn
    rw [hπeq _ _ hx]
    rcases hadj.2.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h3 : (𝒜.g (ι w))⁻¹ * x ∉ Ap := fun h => disjoint_left.1 hT.disjoint h h2
      have h4 : (𝒜.g (ι w))⁻¹ * w ∉ Am := fun h => disjoint_left.1 hT.disjoint h1 h
      simp [h3, h4]
    · have h3 : (𝒜.g (ι w))⁻¹ * x ∈ Ap := h2
      simp [h3, h1]
  have hcay : ∀ w ∈ 𝒜.W, ∀ x, (copyGraph T Ap Am (𝒜.g (ι w))).Adj w x →
      (cayleyGraph S).Adj w x := by
    intro w _ x h
    rw [SimpleGraph.mulCayley_adj]
    refine ⟨h.ne, ?_⟩
    rcases copyGraph_adj_label h with h' | h'
    · exact Or.inl (hT.sub h')
    · exact Or.inr (hT.sub h')
  have hp : 0 < p := by
    rcases mul_pos_iff.1 (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 40) hpμ) with h | h
    · exact h.1
    · exact absurd h.2 (not_lt.2 hμ.le)
  -- the signed graph of `R ∪ P` and its capacities
  let Γ : SignedGraph (Fin 𝒜.t) ({r // r ∈ R} ⊕ {w // w ∈ 𝒜.W}) :=
    { fst := Sum.elim (fun r => π r.1.out.1) (fun w => ι w.1)
      snd := Sum.elim (fun r => π r.1.out.2) (fun w => ι w.1)
      sfst := Sum.elim (fun r => sgnOf 𝒜 Ap π r.1.out.1) (fun w => loopSgn 𝒜 Am ι w.1)
      ssnd := Sum.elim (fun r => sgnOf 𝒜 Ap π r.1.out.2) (fun w => loopSgn 𝒜 Am ι w.1) }
  have htR : ∀ r b, Γ.twinTail (Sum.inl r, b) = arcTail π (sgnOf 𝒜 Ap π) r.1 b := by
    intro r b; cases b <;> rfl
  have hhR : ∀ r b, Γ.twinHead (Sum.inl r, b) = arcHead π (sgnOf 𝒜 Ap π) r.1 b := by
    intro r b; cases b <;> rfl
  have htW : ∀ w b, Γ.twinTail (Sum.inr w, b) = (ι w.1, loopSgn 𝒜 Am ι w.1) := by
    intro w b; cases b <;> rfl
  have hhW : ∀ w b, Γ.twinHead (Sum.inr w, b) = (ι w.1, !loopSgn 𝒜 Am ι w.1) := by
    intro w b; cases b <;> rfl
  let lo : {r // r ∈ R} ⊕ {w // w ∈ 𝒜.W} → ℝ :=
    Sum.elim (fun r => if r.1 ∈ Z₀ then 1 else 1 / 256) (fun _ => 1)
  let up : {r // r ∈ R} ⊕ {w // w ∈ 𝒜.W} → ℝ :=
    Sum.elim (fun r => if r.1 ∈ Z₀ then 1 else 1 - 1 / 256) (fun _ => 1)
  have hlu : ∀ a : ({r // r ∈ R} ⊕ {w // w ∈ 𝒜.W}) × Bool, lo a.1 ≤ up a.1 := by
    rintro ⟨r | w, b⟩
    · show (if r.1 ∈ Z₀ then (1 : ℝ) else 1 / 256) ≤ if r.1 ∈ Z₀ then 1 else 1 - 1 / 256
      split_ifs <;> norm_num
    · exact le_refl (1 : ℝ)
  -- the circulation criterion (4.6)
  have hcutJ : ∀ J : Finset (Fin 𝒜.t × Bool),
      ∑ a ∈ univ.filter (fun a => Γ.twinHead a ∈ J ∧ Γ.twinTail a ∉ J), lo a.1 ≤
        ∑ a ∈ univ.filter (fun a => Γ.twinTail a ∈ J ∧ Γ.twinHead a ∉ J), up a.1 := by
    intro J
    have hL : ∑ a ∈ univ.filter (fun a => Γ.twinHead a ∈ J ∧ Γ.twinTail a ∉ J), lo a.1 ≤
        1 / 256 * inCnt π (sgnOf 𝒜 Ap π) J R + cutCnt π (sgnOf 𝒜 Ap π) J Z₀ +
          loopCnt ι (loopSgn 𝒜 Am ι) J 𝒜.W := by
      rw [sum_filter, Fintype.sum_prod_type, Fintype.sum_sum_type]
      simp only [sum_bool_ite]
      have h1 : ∑ r : {r // r ∈ R}, lo (Sum.inl r) * ((univ.filter fun b =>
          Γ.twinHead (Sum.inl r, b) ∈ J ∧ Γ.twinTail (Sum.inl r, b) ∉ J).card : ℝ) =
          ∑ r ∈ R, (if r ∈ Z₀ then 1 else 1 / 256) * (inArcs π (sgnOf 𝒜 Ap π) J r : ℝ) := by
        rw [← Finset.sum_coe_sort R]
        refine Fintype.sum_congr _ _ fun r => ?_
        simp only [htR, hhR]
        rfl
      have h2 : ∑ w : {w // w ∈ 𝒜.W}, lo (Sum.inr w) * ((univ.filter fun b =>
          Γ.twinHead (Sum.inr w, b) ∈ J ∧ Γ.twinTail (Sum.inr w, b) ∉ J).card : ℝ) ≤
          loopCnt ι (loopSgn 𝒜 Am ι) J 𝒜.W := by
        unfold loopCnt
        push_cast
        rw [← Finset.sum_coe_sort 𝒜.W]
        refine Finset.sum_le_sum fun w _ => ?_
        simp only [htW, hhW]
        show (1 : ℝ) * ((univ.filter fun _ : Bool => (ι w.1, !loopSgn 𝒜 Am ι w.1) ∈ J ∧
          (ι w.1, loopSgn 𝒜 Am ι w.1) ∉ J).card : ℝ) ≤ _
        by_cases hc : (ι w.1, !loopSgn 𝒜 Am ι w.1) ∈ J ∧ (ι w.1, loopSgn 𝒜 Am ι w.1) ∉ J
        · rw [if_pos (Or.inr hc)]
          have h5 : (univ.filter fun _ : Bool => (ι w.1, !loopSgn 𝒜 Am ι w.1) ∈ J ∧
              (ι w.1, loopSgn 𝒜 Am ι w.1) ∉ J).card ≤ 2 := (card_filter_le _ _).trans (by simp)
          have h6 : ((univ.filter fun _ : Bool => (ι w.1, !loopSgn 𝒜 Am ι w.1) ∈ J ∧
              (ι w.1, loopSgn 𝒜 Am ι w.1) ∉ J).card : ℝ) ≤ 2 := by exact_mod_cast h5
          linarith
        · rw [Finset.filter_false_of_mem (fun _ _ => hc)]
          simp only [card_empty, Nat.cast_zero, mul_zero]
          split_ifs <;> norm_num
      have h3 : ∑ r ∈ R, (if r ∈ Z₀ then 1 else 1 / 256) * (inArcs π (sgnOf 𝒜 Ap π) J r : ℝ) ≤
          1 / 256 * inCnt π (sgnOf 𝒜 Ap π) J R + cutCnt π (sgnOf 𝒜 Ap π) J Z₀ := by
        have hZ : (cutCnt π (sgnOf 𝒜 Ap π) J Z₀ : ℝ) = ∑ r ∈ R, if r ∈ Z₀ then
            ((outArcs π (sgnOf 𝒜 Ap π) J r : ℝ) + inArcs π (sgnOf 𝒜 Ap π) J r) else 0 := by
          rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.2 hZR]
          unfold cutCnt outCnt inCnt
          push_cast
          rw [sum_add_distrib]
        have hI : (inCnt π (sgnOf 𝒜 Ap π) J R : ℝ) =
            ∑ r ∈ R, (inArcs π (sgnOf 𝒜 Ap π) J r : ℝ) := by
          unfold inCnt
          push_cast
          rfl
        rw [hZ, hI, mul_sum, ← sum_add_distrib]
        refine sum_le_sum fun r _ => ?_
        have h0 : (0 : ℝ) ≤ outArcs π (sgnOf 𝒜 Ap π) J r := Nat.cast_nonneg _
        have h0' : (0 : ℝ) ≤ inArcs π (sgnOf 𝒜 Ap π) J r := Nat.cast_nonneg _
        split_ifs <;> linarith
      linarith [h1, h2, h3]
    have hU : (1 - 1 / 256) * (outCnt π (sgnOf 𝒜 Ap π) J R : ℝ) ≤
        ∑ a ∈ univ.filter (fun a => Γ.twinTail a ∈ J ∧ Γ.twinHead a ∉ J), up a.1 := by
      rw [sum_filter, Fintype.sum_prod_type, Fintype.sum_sum_type]
      simp only [sum_bool_ite]
      have h1 : ∑ r : {r // r ∈ R}, up (Sum.inl r) * ((univ.filter fun b =>
          Γ.twinTail (Sum.inl r, b) ∈ J ∧ Γ.twinHead (Sum.inl r, b) ∉ J).card : ℝ) =
          ∑ r ∈ R, (if r ∈ Z₀ then 1 else 1 - 1 / 256) * (outArcs π (sgnOf 𝒜 Ap π) J r : ℝ) := by
        rw [← Finset.sum_coe_sort R]
        refine Fintype.sum_congr _ _ fun r => ?_
        simp only [htR, hhR]
        rfl
      have h2 : 0 ≤ ∑ w : {w // w ∈ 𝒜.W}, up (Sum.inr w) * ((univ.filter fun b =>
          Γ.twinTail (Sum.inr w, b) ∈ J ∧ Γ.twinHead (Sum.inr w, b) ∉ J).card : ℝ) :=
        sum_nonneg fun w _ => mul_nonneg zero_le_one (Nat.cast_nonneg _)
      have h3 : (1 - 1 / 256) * (outCnt π (sgnOf 𝒜 Ap π) J R : ℝ) ≤
          ∑ r ∈ R, (if r ∈ Z₀ then 1 else 1 - 1 / 256) * (outArcs π (sgnOf 𝒜 Ap π) J r : ℝ) := by
        unfold outCnt
        push_cast
        rw [mul_sum]
        refine sum_le_sum fun r _ => ?_
        have h0 : (0 : ℝ) ≤ outArcs π (sgnOf 𝒜 Ap π) J r := Nat.cast_nonneg _
        split_ifs <;> linarith
      linarith [h1, h2, h3]
    have hloopb : (loopCnt ι (loopSgn 𝒜 Am ι) J 𝒜.W : ℝ) ≤ p * s J / 20 := by
      have h1 := mul_le_mul_of_nonneg_left (hloop J) hp.le
      have h2 := mul_le_mul_of_nonneg_right hpμ
        (Nat.cast_nonneg (loopCnt ι (loopSgn 𝒜 Am ι) J 𝒜.W) : (0 : ℝ) ≤ _)
      linarith
    have hin : (inCnt π (sgnOf 𝒜 Ap π) J R : ℝ) ≤ cutCnt π (sgnOf 𝒜 Ap π) J R := by
      unfold cutCnt
      push_cast
      linarith [(Nat.cast_nonneg (outCnt π (sgnOf 𝒜 Ap π) J R) : (0 : ℝ) ≤ _)]
    have hps : 0 ≤ p * s J := mul_nonneg hp.le (hs J)
    linarith [hL, hU, hout J, hcutR J, hcutZ J, hloopb, hin, hps]
  obtain ⟨g, hgb, hgc⟩ := hoffman_circulation Γ.twinTail Γ.twinHead (fun a => lo a.1)
    (fun a => up a.1) hlu hcutJ
  obtain ⟨f, hflu, hfB⟩ := signed_circulation Γ lo up g (fun e b => hgb (e, b)) hgc
  have hf01 : ∀ e, 0 ≤ f e ∧ f e ≤ 1 := by
    intro e
    obtain ⟨h1, h2⟩ := hflu e
    rcases e with r | w
    · have hl : (0 : ℝ) ≤ lo (Sum.inl r) := by
        show (0 : ℝ) ≤ if r.1 ∈ Z₀ then 1 else 1 / 256
        split_ifs <;> norm_num
      have hu : up (Sum.inl r) ≤ 1 := by
        show (if r.1 ∈ Z₀ then (1 : ℝ) else 1 - 1 / 256) ≤ 1
        split_ifs <;> norm_num
      exact ⟨hl.trans h1, h2.trans hu⟩
    · exact ⟨le_trans (by norm_num : (0 : ℝ) ≤ 1) h1, h2⟩
  -- the slack-cut condition (4.2)
  have hslackU : ∀ U : Finset (Fin 𝒜.t), (∀ v ∈ U, ∀ w ∈ U, Γ.underlying.Reachable v w) →
      (∃ v ∈ U, ∃ w ∉ U, Γ.underlying.Reachable v w) →
      1 ≤ ∑ e ∈ univ.filter (fun e => Γ.crosses (U : Set (Fin 𝒜.t)) e),
        min (f e) (1 - f e) := by
    rintro U - ⟨v, hv, w, hw, -⟩
    have hcnt := hslack U ⟨v, hv⟩ (fun h => hw (h ▸ mem_univ w))
    have hm0 : ∀ e, 0 ≤ min (f e) (1 - f e) := fun e =>
      le_min (hf01 e).1 (by linarith [(hf01 e).2])
    rw [sum_filter, Fintype.sum_sum_type]
    have h2 : 0 ≤ ∑ w : {w // w ∈ 𝒜.W}, (if Γ.crosses (U : Set (Fin 𝒜.t)) (Sum.inr w) then
        min (f (Sum.inr w)) (1 - f (Sum.inr w)) else 0) :=
      sum_nonneg fun w _ => by split_ifs; exacts [hm0 _, le_rfl]
    have hpt : ∀ r : {r // r ∈ R}, (if r.1 ∉ Z₀ ∧ PartCross π U r.1 then (1 : ℝ) / 256 else 0) ≤
        (if Γ.crosses (U : Set (Fin 𝒜.t)) (Sum.inl r) then
          min (f (Sum.inl r)) (1 - f (Sum.inl r)) else 0) := by
      intro r
      by_cases hr : r.1 ∉ Z₀ ∧ PartCross π U r.1
      · rw [if_pos hr]
        have hcr : Γ.crosses (U : Set (Fin 𝒜.t)) (Sum.inl r) := by
          show (π r.1.out.1 ∈ (U : Set (Fin 𝒜.t))) ≠ (π r.1.out.2 ∈ (U : Set (Fin 𝒜.t)))
          simp only [Finset.mem_coe]
          rcases hr.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · intro h
            exact h2 (cast h h1)
          · intro h
            exact h2 (cast h.symm h1)
        rw [if_pos hcr]
        obtain ⟨h1, h2⟩ := hflu (Sum.inl r)
        have hl : lo (Sum.inl r) = 1 / 256 := by
          show (if r.1 ∈ Z₀ then (1 : ℝ) else 1 / 256) = 1 / 256
          rw [if_neg hr.1]
        have hu : up (Sum.inl r) = 1 - 1 / 256 := by
          show (if r.1 ∈ Z₀ then (1 : ℝ) else 1 - 1 / 256) = 1 - 1 / 256
          rw [if_neg hr.1]
        rw [hl] at h1
        rw [hu] at h2
        exact le_min h1 (by linarith)
      · rw [if_neg hr]
        split_ifs
        · exact hm0 _
        · exact le_rfl
    calc (1 : ℝ) ≤ 1 / 256 * ((R \ Z₀).filter (PartCross π U)).card := by
          have : (256 : ℝ) ≤ ((R \ Z₀).filter (PartCross π U)).card := by exact_mod_cast hcnt
          linarith
      _ = ∑ r ∈ R, (if r ∉ Z₀ ∧ PartCross π U r then (1 : ℝ) / 256 else 0) := by
          rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm, sdiff_eq_filter, filter_filter]
      _ = ∑ r : {r // r ∈ R}, (if r.1 ∉ Z₀ ∧ PartCross π U r.1 then (1 : ℝ) / 256 else 0) :=
          (Finset.sum_coe_sort R
            (fun r => if r ∉ Z₀ ∧ PartCross π U r then (1 : ℝ) / 256 else 0)).symm
      _ ≤ _ := sum_le_sum fun r _ => hpt r
      _ ≤ _ := le_add_of_nonneg_right h2
  -- Lemma 4.1 and the choice of an integral point
  have hconv := robust_signed_integrality Γ (fun _ => 0) (fun v => by simp) f hf01
    (fun v => by rw [hfB v]; simp) hslackU
  obtain ⟨z, hz, hz1⟩ := exists_face_point hconv (fun z hz e => by
    rcases hz.1 e with h | h <;> rw [h] <;> norm_num)
  have hzZ : ∀ r (hr : r ∈ R), r ∈ Z₀ → z (Sum.inl ⟨r, hr⟩) = 1 := by
    intro r hr hrZ
    refine hz1 _ ?_
    obtain ⟨h1, h2⟩ := hflu (Sum.inl ⟨r, hr⟩)
    have hl : lo (Sum.inl ⟨r, hr⟩) = 1 := by
      show (if r ∈ Z₀ then (1 : ℝ) else 1 / 256) = 1
      rw [if_pos hrZ]
    have hu : up (Sum.inl ⟨r, hr⟩) = 1 := by
      show (if r ∈ Z₀ then (1 : ℝ) else 1 - 1 / 256) = 1
      rw [if_pos hrZ]
    rw [hl] at h1
    rw [hu] at h2
    exact le_antisymm h2 h1
  have hzW : ∀ w : {w // w ∈ 𝒜.W}, z (Sum.inr w) = 1 := fun w =>
    hz1 _ (le_antisymm (hflu (Sum.inr w)).2 (hflu (Sum.inr w)).1)
  -- the selected edges and the connector
  obtain ⟨Msel, hMsel⟩ : ∃ Msel : Finset (Sym2 G),
      Msel = R.filter (fun r => ∃ h : r ∈ R, z (Sum.inl ⟨r, h⟩) = 1) := ⟨_, rfl⟩
  have hmemM : ∀ r, r ∈ Msel ↔ ∃ h : r ∈ R, z (Sum.inl ⟨r, h⟩) = 1 := by
    intro r
    rw [hMsel, mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  have hMR : Msel ⊆ R := fun r hr => ((hmemM r).1 hr).1
  have hZM : Z₀ ⊆ Msel := fun r hr => (hmemM r).2 ⟨hZR hr, hzZ r (hZR hr) hr⟩
  have hzM : ∀ r : {r // r ∈ R}, z (Sum.inl r) = if r.1 ∈ Msel then 1 else 0 := by
    intro r
    rcases hz.1 (Sum.inl r) with h | h
    · rw [if_neg]
      · exact h
      · intro hm
        obtain ⟨_, h'⟩ := (hmemM r.1).1 hm
        have h'' : z (Sum.inl r) = 1 := h'
        rw [h''] at h
        norm_num at h
    · rw [if_pos ((hmemM r.1).2 ⟨r.2, h⟩)]
      exact h
  obtain ⟨M, hMdef⟩ : ∃ M : SimpleGraph G, M = SimpleGraph.fromEdgeSet ((Msel : Set (Sym2 G)) ∪
      {e | ∃ w ∈ 𝒜.W, e = s(w, pa w) ∨ e = s(w, pb w)}) := ⟨_, rfl⟩
  have hMadj : ∀ x y, M.Adj x y ↔ (s(x, y) ∈ Msel ∨ ∃ w ∈ 𝒜.W, s(x, y) = s(w, pa w) ∨
      s(x, y) = s(w, pb w)) ∧ x ≠ y := by
    intro x y
    rw [hMdef]
    simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq]
  have hvtxM : ∀ r ∈ Msel, ∀ v ∈ r, v ∈ vtx R := fun r hr v hv =>
    mem_vtx.2 ⟨r, hMR hr, hv⟩
  have hcases : ∀ v y, v ∉ 𝒜.W → M.Adj v y →
      s(v, y) ∈ Msel ∨ ∃ w ∈ 𝒜.W, (v = pa w ∨ v = pb w) ∧ y = w := by
    intro v y hv h
    rw [hMadj] at h
    rcases h.1 with h1 | ⟨w, hw, h1 | h1⟩
    · exact Or.inl h1
    · rcases Sym2.eq_iff.1 h1 with ⟨rfl, -⟩ | ⟨h3, h4⟩
      · exact absurd hw hv
      · exact Or.inr ⟨w, hw, Or.inl h3, h4⟩
    · rcases Sym2.eq_iff.1 h1 with ⟨rfl, -⟩ | ⟨h3, h4⟩
      · exact absurd hw hv
      · exact Or.inr ⟨w, hw, Or.inr h3, h4⟩
  have hsub : ∀ v, v ∉ 𝒜.W → ∀ y y', M.Adj v y → M.Adj v y' → y = y' := by
    intro v hv y y' h h'
    rcases hcases v y hv h with h1 | ⟨w, hw, hvw, hyw⟩ <;>
      rcases hcases v y' hv h' with h2 | ⟨w', hw', hvw', hyw'⟩
    · have := hmatch _ (hMR h1) _ (hMR h2) v (Sym2.mem_mk_left v y) (Sym2.mem_mk_left v y')
      exact Sym2.congr_right.1 this
    · exfalso
      have := hvtxM _ h1 v (Sym2.mem_mk_left v y)
      rcases hvw' with rfl | rfl
      exacts [hpa_R w' hw' this, hpb_R w' hw' this]
    · exfalso
      have := hvtxM _ h2 v (Sym2.mem_mk_left v y')
      rcases hvw with rfl | rfl
      exacts [hpa_R w hw this, hpb_R w hw this]
    · rw [hyw, hyw']
      exact hpend w hw w' hw' v hvw hvw'
  have hends : ∀ v, v ∉ 𝒜.W →
      ((∃ y, M.Adj v y) ↔ (v ∈ vtx Msel ∨ ∃ w ∈ 𝒜.W, v = pa w ∨ v = pb w)) := by
    intro v hv
    constructor
    · rintro ⟨y, hy⟩
      rcases hcases v y hv hy with h1 | ⟨w, hw, hvw, -⟩
      · exact Or.inl (mem_vtx.2 ⟨_, h1, Sym2.mem_mk_left v y⟩)
      · exact Or.inr ⟨w, hw, hvw⟩
    · rintro (h | ⟨w, hw, hvw⟩)
      · obtain ⟨r, hr, hvr⟩ := mem_vtx.1 h
        obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 hvr
        refine ⟨y, (hMadj v y).2 ⟨Or.inl hr, fun hvy => ?_⟩⟩
        subst hvy
        exact hRne _ (hMR hr) (by simp)
      · refine ⟨w, (hMadj v w).2 ⟨Or.inr ⟨w, hw, ?_⟩, fun h => hv (by rw [h]; exact hw)⟩⟩
        rcases hvw with rfl | rfl
        · exact Or.inl Sym2.eq_swap
        · exact Or.inr Sym2.eq_swap
  have hdegW : ∀ w ∈ 𝒜.W, M.neighborSet w = {pa w, pb w} := by
    intro w hw
    ext y
    simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [hMadj] at h
      rcases h.1 with h1 | ⟨w', hw', h1 | h1⟩
      · exact absurd hw (hRW _ (hMR h1) w (Sym2.mem_mk_left w y))
      · rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨h3, -⟩
        · exact Or.inl rfl
        · exact absurd (h3 ▸ hw) (hpa_W _ hw')
      · rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨h3, -⟩
        · exact Or.inr rfl
        · exact absurd (h3 ▸ hw) (hpb_W _ hw')
    · rintro (rfl | rfl)
      · exact (hMadj _ _).2 ⟨Or.inr ⟨w, hw, Or.inl rfl⟩,
          fun h => hpa_W w hw (by rw [← h]; exact hw)⟩
      · exact (hMadj _ _).2 ⟨Or.inr ⟨w, hw, Or.inr rfl⟩,
          fun h => hpb_W w hw (by rw [← h]; exact hw)⟩
  have hdeg_le : ∀ v, v ∉ 𝒜.W → (M.neighborSet v).ncard ≤ 1 := fun v hv =>
    (Set.ncard_le_one (Set.toFinite _)).2 fun y hy y' hy' => hsub v hv y y' hy hy'
  have hdeg1 : ∀ v, v ∉ 𝒜.W → ((M.neighborSet v).ncard = 1 ↔
      (v ∈ vtx Msel ∨ ∃ w ∈ 𝒜.W, v = pa w ∨ v = pb w)) := by
    intro v hv
    rw [ncard_eq_one_iff_nonempty (M.neighborSet v) (fun y hy y' hy' => hsub v hv y y' hy hy')]
    exact hends v hv
  -- the path endpoints in a part
  let pathEnds : Fin 𝒜.t → Finset G := fun i =>
    (𝒜.W.filter fun w => ι w = i).biUnion fun w => {pa w, pb w}
  have hWi : ∀ i, (𝒜.W.filter fun w => ι w = i).card ≤ 1 := fun i =>
    card_le_one.2 fun w hw w' hw' => by
      rw [mem_filter] at hw hw'
      exact hιinj w hw.1 w' hw'.1 (hw.2.trans hw'.2.symm)
  have hpathcard : ∀ i, (pathEnds i).card ≤ 2 := by
    intro i
    calc (pathEnds i).card ≤ ∑ w ∈ 𝒜.W.filter (fun w => ι w = i),
          ({pa w, pb w} : Finset G).card := card_biUnion_le
      _ ≤ ∑ w ∈ 𝒜.W.filter (fun w => ι w = i), 2 :=
          sum_le_sum fun w _ => (card_insert_le _ _).trans (by simp)
      _ = 2 * (𝒜.W.filter fun w => ι w = i).card := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 := by have := hWi i; omega
  have hpath_mem : ∀ i v, v ∈ pathEnds i ↔ ∃ w ∈ 𝒜.W, ι w = i ∧ (v = pa w ∨ v = pb w) := by
    intro i v
    simp only [pathEnds, mem_biUnion, mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨w, ⟨hw, hwi⟩, hv⟩
      exact ⟨w, hw, hwi, hv⟩
    · rintro ⟨w, hw, hwi, hv⟩
      exact ⟨w, ⟨hw, hwi⟩, hv⟩
  have hEsub : ∀ i v, v ∈ 𝒜.part i → (M.neighborSet v).ncard = 1 →
      v ∈ vtx R ∨ v ∈ pathEnds i := by
    intro i v hv h1
    rcases (hdeg1 v (hpartW i v hv)).1 h1 with h | ⟨w, hw, hvw⟩
    · obtain ⟨r, hr, hvr⟩ := mem_vtx.1 h
      exact Or.inl (hvtxM r hr v hvr)
    · refine Or.inr ((hpath_mem i v).2 ⟨w, hw, ?_, hvw⟩)
      exact (hπeq _ _ (hend_part w hw v hvw)).symm.trans (hπeq i v hv)
  refine ⟨M, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `M` uses edges of `X`
    intro x y h
    rw [hMadj] at h
    obtain ⟨h1, -⟩ := h
    rw [← SimpleGraph.mem_edgeSet]
    rcases h1 with h1 | ⟨w, hw, h1 | h1⟩
    · have := (hRadj _ (hMR h1)).1
      rw [← SimpleGraph.mem_edgeSet, mk_out] at this
      exact this
    · rw [h1, SimpleGraph.mem_edgeSet]
      exact hcay w hw _ (hpa_adj w hw)
    · rw [h1, SimpleGraph.mem_edgeSet]
      exact hcay w hw _ (hpb_adj w hw)
  · intro w hw
    rw [hdegW w hw, Set.ncard_pair (hpa_ne w hw)]
  · intro w hw y hy
    have : y ∈ M.neighborSet w := hy
    rw [hdegW w hw] at this
    rcases this with rfl | rfl
    exacts [hpa_W w hw, hpb_W w hw]
  · exact hdeg_le
  · -- the contraction is connected
    haveI : Nonempty (Fin 𝒜.t) := ⟨⟨0, by omega⟩⟩
    refine connected_of_forall_cut _ fun I hI hI' => ?_
    obtain ⟨e, he, hcross⟩ := hconn I hI hI'
    have heR := hZR he
    have hadj : M.Adj e.out.1 e.out.2 :=
      (hMadj _ _).2 ⟨Or.inl (by rw [mk_out]; exact hZM he), hRne e heR⟩
    have h1 := hπ _ (hRadj e heR).2.1
    have h2 := hπ _ (hRadj e heR).2.2
    rcases hcross with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · refine ⟨π e.out.1, hi, π e.out.2, hj, ?_⟩
      rw [SimpleGraph.fromRel_adj]
      exact ⟨fun h => hj (h ▸ hi), Or.inl ⟨e.out.1, h1, e.out.2, h2, hRne e heR, hadj.reachable⟩⟩
    · refine ⟨π e.out.2, hi, π e.out.1, hj, ?_⟩
      rw [SimpleGraph.fromRel_adj]
      exact ⟨fun h => hj (h ▸ hi), Or.inr ⟨e.out.1, h1, e.out.2, h2, hRne e heR, hadj.reachable⟩⟩
  · -- the endpoints are balanced (signed balance of `z`)
    intro i
    have hEi : (𝒜.part i).filter (fun v => (M.neighborSet v).ncard = 1) =
        ((𝒜.part i).filter (· ∈ vtx Msel)) ∪ pathEnds i := by
      ext v
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨hv, h1⟩
        rcases (hdeg1 v (hpartW i v hv)).1 h1 with h | ⟨w, hw, hvw⟩
        · exact Or.inl ⟨hv, h⟩
        · refine Or.inr ((hpath_mem i v).2 ⟨w, hw, ?_, hvw⟩)
          exact (hπeq _ _ (hend_part w hw v hvw)).symm.trans (hπeq i v hv)
      · rintro (⟨hv, h⟩ | h)
        · exact ⟨hv, (hdeg1 v (hpartW i v hv)).2 (Or.inl h)⟩
        · obtain ⟨w, hw, hwi, hvw⟩ := (hpath_mem i v).1 h
          have hv : v ∈ 𝒜.part i := hwi ▸ hend_part w hw v hvw
          exact ⟨hv, (hdeg1 v (hpartW i v hv)).2 (Or.inr ⟨w, hw, hvw⟩)⟩
    have hdisj : Disjoint ((𝒜.part i).filter (· ∈ vtx Msel)) (pathEnds i) := by
      rw [disjoint_left]
      intro v hv hv'
      obtain ⟨w, hw, -, hvw⟩ := (hpath_mem i v).1 hv'
      obtain ⟨r, hr, hvr⟩ := mem_vtx.1 (mem_filter.1 hv).2
      have := hvtxM r hr v hvr
      rcases hvw with rfl | rfl
      exacts [hpa_R w hw this, hpb_R w hw this]
    let χ : G → ℝ := fun v => SignedGraph.signVal (sgnOf 𝒜 Ap π v)
    have hsigned : ∀ A : Finset G, A ⊆ 𝒜.part i →
        ∑ v ∈ A, χ v = ((A.filter fun v => (𝒜.g i)⁻¹ * v ∈ Ap).card : ℝ) -
          (A.filter fun v => (𝒜.g i)⁻¹ * v ∈ Am).card := by
      intro A hA
      have hχ : ∀ v ∈ A, χ v = (if (𝒜.g i)⁻¹ * v ∈ Ap then 1 else 0) -
          (if (𝒜.g i)⁻¹ * v ∈ Am then 1 else 0) := by
        intro v hv
        have hvi := hA hv
        have hc : (𝒜.g i)⁻¹ * v ∈ Ap ∪ Am := mem_copyVerts.1 (hgood.part_sub i hvi)
        simp only [χ, sgnOf, hπeq i v hvi, SignedGraph.signVal]
        by_cases h1 : (𝒜.g i)⁻¹ * v ∈ Ap
        · have h2 : (𝒜.g i)⁻¹ * v ∉ Am := fun h => disjoint_left.1 hT.disjoint h1 h
          simp [h1, h2]
        · have h2 : (𝒜.g i)⁻¹ * v ∈ Am := (mem_union.1 hc).resolve_left h1
          simp [h1, h2]
      rw [sum_congr rfl hχ, sum_sub_distrib, sum_boole, sum_boole]
    have happly : Γ.apply z i =
        ∑ v ∈ (𝒜.part i).filter (fun v => (M.neighborSet v).ncard = 1), χ v := by
      rw [hEi, sum_union hdisj]
      unfold SignedGraph.apply
      rw [Fintype.sum_sum_type]
      congr 1
      · have hinc : ∀ r : {r // r ∈ R}, Γ.incidence i (Sum.inl r) * z (Sum.inl r) =
            if r.1 ∈ Msel then ((if π r.1.out.1 = i then χ r.1.out.1 else 0) +
              (if π r.1.out.2 = i then χ r.1.out.2 else 0)) else 0 := by
          intro r
          have hi : Γ.incidence i (Sum.inl r) = (if π r.1.out.1 = i then χ r.1.out.1 else 0) +
              (if π r.1.out.2 = i then χ r.1.out.2 else 0) := by
            unfold SignedGraph.incidence
            congr
          rw [hi, hzM r]
          by_cases hm : r.1 ∈ Msel
          · simp only [hm, if_true, mul_one]
          · simp only [hm, if_false, mul_zero]
        rw [Fintype.sum_congr _ _ hinc, Finset.sum_coe_sort R (fun r => if r ∈ Msel then
          ((if π r.out.1 = i then χ r.out.1 else 0) + (if π r.out.2 = i then χ r.out.2 else 0))
          else 0), ← sum_filter, filter_mem_eq_inter, inter_eq_right.2 hMR]
        have hset : (𝒜.part i).filter (· ∈ vtx Msel) = (Msel.biUnion fun r =>
            ({r.out.1, r.out.2} : Finset G)).filter (fun v => π v = i) := by
          ext v
          simp only [mem_filter, mem_biUnion, mem_insert, mem_singleton]
          constructor
          · rintro ⟨hv, hvM⟩
            obtain ⟨r, hr, hvr⟩ := mem_vtx.1 hvM
            exact ⟨⟨r, hr, hRmem r v hvr⟩, hπeq i v hv⟩
          · rintro ⟨⟨r, hr, hvr⟩, hvi⟩
            have hvr' : v ∈ r := by
              rcases hvr with rfl | rfl
              exacts [Sym2.out_fst_mem r, Sym2.out_snd_mem r]
            refine ⟨?_, mem_vtx.2 ⟨r, hr, hvr'⟩⟩
            have := hπ v (hRW r (hMR hr) v hvr')
            rwa [hvi] at this
        rw [hset, Finset.sum_filter (fun v => π v = i)]
        have hpd : (Msel : Set (Sym2 G)).PairwiseDisjoint
            (fun r => ({r.out.1, r.out.2} : Finset G)) := by
          intro r hr r' hr' hne
          simp only [Function.onFun]
          rw [disjoint_left]
          intro v hv hv'
          have h1 : v ∈ r := by
            simp only [mem_insert, mem_singleton] at hv
            rcases hv with rfl | rfl
            exacts [Sym2.out_fst_mem r, Sym2.out_snd_mem r]
          have h2 : v ∈ r' := by
            simp only [mem_insert, mem_singleton] at hv'
            rcases hv' with rfl | rfl
            exacts [Sym2.out_fst_mem r', Sym2.out_snd_mem r']
          exact hRmatch r (hMR hr) r' (hMR hr') hne v h1 h2
        rw [sum_biUnion hpd]
        refine sum_congr rfl fun r hr => ?_
        rw [sum_pair (hRne r (hMR hr))]
      · have hinc : ∀ w : {w // w ∈ 𝒜.W}, Γ.incidence i (Sum.inr w) * z (Sum.inr w) =
            if ι w.1 = i then 2 * SignedGraph.signVal (loopSgn 𝒜 Am ι w.1) else 0 := by
          intro w
          have hi : Γ.incidence i (Sum.inr w) =
              (if ι w.1 = i then SignedGraph.signVal (loopSgn 𝒜 Am ι w.1) else 0) +
              (if ι w.1 = i then SignedGraph.signVal (loopSgn 𝒜 Am ι w.1) else 0) := by
            unfold SignedGraph.incidence
            congr
          rw [hi, hzW w]
          split_ifs <;> ring
        rw [Fintype.sum_congr _ _ hinc, Finset.sum_coe_sort 𝒜.W (fun w => if ι w = i then
          2 * SignedGraph.signVal (loopSgn 𝒜 Am ι w) else 0), ← sum_filter]
        have hpd : ((𝒜.W.filter fun w => ι w = i : Finset G) : Set G).PairwiseDisjoint
            (fun w => ({pa w, pb w} : Finset G)) := by
          intro w hw w' hw' hne
          simp only [Function.onFun]
          rw [disjoint_left]
          intro v hv hv'
          simp only [mem_insert, mem_singleton] at hv hv'
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hw hw'
          exact hne (hpend w hw.1 w' hw'.1 v hv hv')
        show _ = ∑ v ∈ (𝒜.W.filter fun w => ι w = i).biUnion
          (fun w => ({pa w, pb w} : Finset G)), χ v
        rw [sum_biUnion hpd]
        refine sum_congr rfl fun w hw => ?_
        rw [mem_filter] at hw
        rw [sum_pair (hpa_ne w hw.1)]
        simp only [χ, hsg_nbr w hw.1 (pa w) (hpa_part w hw.1) (hpa_adj w hw.1),
          hsg_nbr w hw.1 (pb w) (hpb_part w hw.1) (hpb_adj w hw.1)]
        ring
    have hzero : ∑ v ∈ (𝒜.part i).filter (fun v => (M.neighborSet v).ncard = 1), χ v = 0 := by
      rw [← happly]
      simpa using hz.2 i
    rw [hsigned _ (filter_subset _ _)] at hzero
    simp only [filter_filter] at hzero
    have : (((𝒜.part i).filter fun v => (M.neighborSet v).ncard = 1 ∧
        (𝒜.g i)⁻¹ * v ∈ Ap).card : ℝ) = ((𝒜.part i).filter fun v =>
        (M.neighborSet v).ncard = 1 ∧ (𝒜.g i)⁻¹ * v ∈ Am).card := by linarith
    exact_mod_cast this
  · -- every part contains an endpoint
    intro i
    have hI' : ({i} : Finset (Fin 𝒜.t)) ≠ univ := by
      intro h
      obtain ⟨j, hj⟩ : ∃ j : Fin 𝒜.t, j ≠ i := by
        by_cases h0 : i.val = 0
        · exact ⟨⟨1, by omega⟩, fun h' => by
            have := congrArg Fin.val h'
            simp only at this
            omega⟩
        · exact ⟨⟨0, by omega⟩, fun h' => by
            have := congrArg Fin.val h'
            simp only at this
            omega⟩
      have := mem_univ j
      rw [← h, mem_singleton] at this
      exact hj this
    obtain ⟨e, he, hcross⟩ := hconn {i} (singleton_nonempty i) hI'
    have heR := hZR he
    have hmem : ∀ v ∈ e, v ∈ vtx Msel := fun v hv => mem_vtx.2 ⟨e, hZM he, hv⟩
    rcases hcross with ⟨hi, -⟩ | ⟨hi, -⟩
    · rw [mem_singleton] at hi
      exact ⟨e.out.1, hi ▸ hπ _ (hRadj e heR).2.1,
        (hdeg1 _ (hRadj e heR).2.1).2 (Or.inl (hmem _ (Sym2.out_fst_mem e)))⟩
    · rw [mem_singleton] at hi
      exact ⟨e.out.2, hi ▸ hπ _ (hRadj e heR).2.2,
        (hdeg1 _ (hRadj e heR).2.2).2 (Or.inl (hmem _ (Sym2.out_snd_mem e)))⟩
  · -- few endpoints in every part
    intro i
    have hsub' : (𝒜.part i).filter (fun v => (M.neighborSet v).ncard = 1) ⊆
        (𝒜.part i).filter (· ∈ vtx R) ∪ pathEnds i := by
      intro v hv
      rw [mem_filter] at hv
      rcases hEsub i v hv.1 hv.2 with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨hv.1, h⟩)
      · exact mem_union_right _ h
    have h1 := (card_le_card hsub').trans (card_union_le _ _)
    have h2 : (((𝒜.part i).filter (fun v => (M.neighborSet v).ncard = 1)).card : ℝ) ≤
        ((𝒜.part i).filter (· ∈ vtx R)).card + 2 := by
      have := h1.trans (Nat.add_le_add_left (hpathcard i) _)
      exact_mod_cast this
    linarith [hfew i]
  · -- few endpoints among the neighbours of any full-copy vertex
    intro i v hv
    have hsub' : ((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y ∧
        (M.neighborSet y).ncard = 1) ⊆ ((𝒜.part i).filter fun y =>
          (copyGraph T Ap Am (𝒜.g i)).Adj v y ∧ y ∈ vtx R) ∪ pathEnds i := by
      intro y hy
      rw [mem_filter] at hy
      rcases hEsub i y hy.1 hy.2.2 with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨hy.1, hy.2.1, h⟩)
      · exact mem_union_right _ h
    have h1 := (card_le_card hsub').trans (card_union_le _ _)
    have h2 : (((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y ∧
        (M.neighborSet y).ncard = 1).card : ℝ) ≤ ((𝒜.part i).filter fun y =>
          (copyGraph T Ap Am (𝒜.g i)).Adj v y ∧ y ∈ vtx R).card + 2 := by
      have := h1.trans (Nat.add_le_add_left (hpathcard i) _)
      exact_mod_cast this
    linarith [hsparse i v hv]

end Integral


/-! ### Assembly of the connector from a good outcome of the joint experiment -/

section Outcome

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

/-- The deterministic and matching part of the proof of Proposition 6.1: from a successful
allocation, added labels `S₁`, retained labels `S_s` satisfying (6.2), (6.6) and Lemma 6.3, and the
parameter regime, construct the connecting system. -/
theorem connector_of_outcome (S T Ap Am S₁ Ss : Finset G) (𝒜 : Allocation G)
    (cT A₀ cN CN cD CD a c₃ CB K P₀ D σ η ω L d : ℝ)
    (hL : Real.log (Fintype.card G) = L) (hd : (S.card : ℝ) = d)
    (hS : IsConnectionSet S) (hconn : (cayleyGraph S).Connected) (hT : IsTemplate S T Ap Am cT)
    (hgood : 𝒜.Good S T Ap Am (A₀ * L) D σ η ω cN CN)
    (hA₀ : 0 < A₀) (hcN : 0 < cN) (ha : 0 < a) (hc₃ : 0 < c₃) (hCB : 0 < CB) (hK : 0 < K)
    (hL3 : 3 ≤ L) (hdpos : 0 < d) (hD₁ : cD * d / L ≤ D) (hD₂ : D ≤ CD * d / L)
    (hS₀conn : IsConnectionSet (S₁ ∪ Ss)) (hS₀S : S₁ ∪ Ss ⊆ S) (hTne : T.Nonempty)
    (hkK : ((S₁ ∪ Ss).card : ℝ) ≤ K * L ^ 2)
    (htwo : CN * d / (A₀ * L) < cT * d - 1)
    (h3B : 3 * (CB * (K * L ^ 2) * L) ≤ c₃ * d / L) (hμ6 : 6 ≤ c₃ * d / L)
    (hpk : P₀ * L / (c₃ * d / L) * (K * L ^ 2) ^ 2 ≤ 1) (hP1100 : 1100 ≤ P₀ * L)
    (hP2048 : 32 * (3 + 2 * L) + 4 ≤ P₀ * L / 2048)
    (hpkE : 4 * (P₀ * L / (c₃ * d / L) * (K * L ^ 2)) ≤ a * Real.log L / L ^ 7)
    (hEV : 4 ≤ a * Real.log L / L ^ 7 * (cN * d / (A₀ * L)))
    (hEVlog : 3 + 2 * L ≤ 3 / 40 * (a * Real.log L / L ^ 7 * (cN * d / (A₀ * L)) - 2))
    (hpkN : 2 * (P₀ * L / (c₃ * d / L) * (K * L ^ 2)) * (CN * d / (A₀ * L)) + 2 ≤
      a * (cD * d / L) / L ^ 6)
    (hNlog : 3 + 2 * L ≤ 3 / 40 * (a * (cD * d / L) / L ^ 6 - 2))
    (hεN : a * (CD * d / L) / L ^ 6 ≤ cN * d / (A₀ * L))
    (hres : Odd (Nat.card (Subgroup.closure (T : Set G))) →
      Res66 T (S₁ ∪ Ss) 𝒜.W (CB * (S₁ ∪ Ss).card * L))
    (hcuts : ∀ π : G → Fin 𝒜.t, (∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v)) →
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
            ((conY (S₁ ∪ Ss) 𝒜.W).edgeFinset.filter (PartCross π I)).card)) :
    ∃ M : SimpleGraph G, 𝒜.IsConnector S T Ap Am M (a * Real.log L / L ^ 7) (a * D / L ^ 6) := by
  subst hd
  simp only [hL] at hcuts
  set n := Fintype.card G
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < n := by linarith only [hn1]
  have hLpos : 0 < L := by linarith only [hL3]
  have hΛpos : 0 < Real.log L := Real.log_pos (by linarith only [hL3])
  have hlam : 0 < A₀ * L := mul_pos hA₀ hLpos
  have hsize : 0 < cN * S.card / (A₀ * L) := div_pos (mul_pos hcN hdpos) hlam
  have ht2 : 2 ≤ 𝒜.t := two_le_t hS hT hgood hlam hTne htwo
  have ht0 : 0 < 𝒜.t := by omega
  -- the part map and the copies of the reserved vertices
  let π : G → Fin 𝒜.t := fun v =>
    if h : ∃ i, v ∈ 𝒜.part i then Classical.choose h else ⟨0, ht0⟩
  have hπ : ∀ v, v ∉ 𝒜.W → v ∈ 𝒜.part (π v) := by
    intro v hv
    have h : ∃ i, v ∈ 𝒜.part i := (hgood.part_unique v hv).exists
    have : π v = Classical.choose h := dif_pos h
    rw [this]
    exact Classical.choose_spec h
  let ι : G → Fin 𝒜.t := fun w =>
    if h : ∃ i, w ∈ copyVerts Ap Am (𝒜.g i) then Classical.choose h else ⟨0, ht0⟩
  have hι : ∀ w ∈ 𝒜.W, w ∈ copyVerts Ap Am (𝒜.g (ι w)) := by
    intro w _
    have h := exists_copy hgood hTne w
    have : ι w = Classical.choose h := dif_pos h
    rw [this]
    exact Classical.choose_spec h
  obtain ⟨hA, hLoc, hBip⟩ := hcuts π hπ
  clear hcuts
  set S₀ := S₁ ∪ Ss
  set μ₀ := c₃ * S.card / L
  have hμ₀pos : 0 < μ₀ := div_pos (mul_pos hc₃ hdpos) hLpos
  set k := S₀.card
  set Y := conY S₀ 𝒜.W
  set sg := sgnOf 𝒜 Ap π
  have hdir := fun J => directional_balance S T Ap Am S₀ cT 𝒜 (A₀ * L) D _ _ ω cN CN μ₀
    (CB * k * L) π ι hT hgood hsize hπ hι hS₀conn
    (by
      have : CB * k * L ≤ CB * (K * L ^ 2) * L :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkK hCB.le) hLpos.le
      linarith only [this, h3B])
    hres hLoc J
  -- the gap, the part cuts and cut counting
  have hB456 : (∀ J, cutCnt π sg J Y.edgeFinset = 0 ∨ μ₀ ≤ cutCnt π sg J Y.edgeFinset) ∧
      (∀ I : Finset (Fin 𝒜.t), I.Nonempty → I ≠ univ →
        μ₀ ≤ cutCnt π sg (I ×ˢ univ) Y.edgeFinset) ∧
      (∀ j : ℕ, (((univ : Finset (Finset (Fin 𝒜.t × Bool))).filter fun J =>
        (cutCnt π sg J Y.edgeFinset : ℝ) < (j + 1) * μ₀).card : ℝ) ≤
          (4 * (𝒜.t + Y.edgeFinset.card)) ^ (16 * (j + 1))) := by
    by_cases hnb : IsNonbip S
    · have hA' := hA hnb
      refine ⟨fun J => ?_, fun I hI hI' => hA' _ (hI.product univ_nonempty) ?_,
        fun j => state_cut_count ht0 π sg _ μ₀ hμ6 hA' j⟩
      · by_cases hJ : J.Nonempty
        · by_cases hJ' : J = univ
          · left
            rw [hJ']
            exact cutCnt_univ _ _ _
          · right
            exact hA' J hJ hJ'
        · left
          rw [not_nonempty_iff_eq_empty.1 hJ]
          exact cutCnt_empty _ _ _
      · intro h
        apply hI'
        ext i
        refine ⟨fun _ => mem_univ _, fun _ => ?_⟩
        have : (i, true) ∈ I ×ˢ (univ : Finset Bool) := by rw [h]; exact mem_univ _
        exact (mem_product.1 this).1
    · have hB' := hBip hnb
      obtain ⟨hgap, hcount⟩ := bip_state_cuts S T Ap Am S₀ cT 𝒜 (A₀ * L) D _ _ ω cN CN μ₀ π hS
        hconn hnb hT hgood hπ hS₀S hμ6 hB'
      refine ⟨hgap, fun I hI hI' => ?_, hcount⟩
      rw [cutCnt_prod_univ]
      push_cast
      have := hB' I hI hI'
      linarith only [this, hμ₀pos]
  -- the random matching
  set p := P₀ * L / μ₀
  have hppos : 0 < p := div_pos (lt_of_lt_of_le (by norm_num) hP1100) hμ₀pos
  have hpμ : p * μ₀ = P₀ * L := div_mul_cancel₀ _ hμ₀pos.ne'
  have htn : (𝒜.t : ℝ) ≤ n := by exact_mod_cast t_le_card hgood hsize
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := le_self_pow₀ hn1 (by norm_num)
  have hEcard : (Y.edgeFinset.card : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h1 := SimpleGraph.card_edgeFinset_le_card_choose_two (G := Y)
    have h2 := Nat.choose_le_pow n 2
    exact_mod_cast h1.trans h2
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith only [this]
  have hlogN : Real.log (4 * ((𝒜.t : ℝ) + Y.edgeFinset.card)) ≤ 3 + 2 * L := by
    have ht0' : (0 : ℝ) < 𝒜.t := by exact_mod_cast ht0
    have hE0 : (0 : ℝ) ≤ Y.edgeFinset.card := Nat.cast_nonneg _
    have hpos : (0 : ℝ) < 4 * ((𝒜.t : ℝ) + Y.edgeFinset.card) := by
      linarith only [ht0', hE0]
    have hle : 4 * ((𝒜.t : ℝ) + Y.edgeFinset.card) ≤ 8 * (n : ℝ) ^ 2 := by
      linarith only [htn, hEcard, hnn]
    have h1 := Real.log_le_log hpos hle
    rw [Real.log_mul (by norm_num) (pow_pos hnpos 2).ne', Real.log_pow, hL] at h1
    have h8 : Real.log 8 < 3 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      linarith only [hlog2]
    push_cast at h1
    linarith only [h1, h8]
  set εE := a * Real.log L / L ^ 7
  set εN := a * D / L ^ 6
  let tests : Finset (Finset G × ℝ) :=
    (univ.image fun i : Fin 𝒜.t => (𝒜.part i, εE * (𝒜.part i).card - 2)) ∪
      univ.biUnion fun i : Fin 𝒜.t => (copyVerts Ap Am (𝒜.g i)).image fun v =>
        ((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y, εN - 2)
  have htests_card : (tests.card : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
    have h1 : tests.card ≤ 𝒜.t + 𝒜.t * n := by
      refine (card_union_le _ _).trans (add_le_add ?_ ?_)
      · exact card_image_le.trans (by simp)
      · refine card_biUnion_le.trans ?_
        calc ∑ i : Fin 𝒜.t, ((copyVerts Ap Am (𝒜.g i)).image fun v =>
              ((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y, εN - 2)).card
            ≤ ∑ _i : Fin 𝒜.t, n := sum_le_sum fun i _ => card_image_le.trans (card_le_univ _)
          _ = 𝒜.t * n := by simp
    have h1' : (tests.card : ℝ) ≤ 𝒜.t + 𝒜.t * n := by exact_mod_cast h1
    have h3 : (𝒜.t : ℝ) * n ≤ (n : ℝ) ^ 2 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right htn hnpos.le
    linarith only [h1', h3, htn, hnn]
  have hlogtests : Real.log tests.card ≤ 1 + 2 * L := by
    rcases Nat.eq_zero_or_pos tests.card with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      linarith only [hLpos]
    · have h := Real.log_le_log (by exact_mod_cast hpos) htests_card
      rw [Real.log_mul (by norm_num) (pow_pos hnpos 2).ne', Real.log_pow, hL] at h
      push_cast at h
      linarith only [h, hlog2]
  have hpk_le : p * k ≤ p * (K * L ^ 2) := mul_le_mul_of_nonneg_left hkK hppos.le
  have hεE0 : 0 ≤ εE := div_nonneg (mul_nonneg ha.le hΛpos.le) (pow_nonneg hLpos.le 7)
  have htests : ∀ q ∈ tests, p * k * q.1.card ≤ q.2 / 2 ∧
      Real.log tests.card + 2 ≤ 3 / 40 * q.2 := by
    intro q hq
    rcases mem_union.1 hq with hq | hq
    · obtain ⟨i, -, rfl⟩ := mem_image.1 hq
      have hV : cN * S.card / (A₀ * L) ≤ (𝒜.part i).card := hgood.size_lower i
      have h2 : εE * (cN * S.card / (A₀ * L)) ≤ εE * (𝒜.part i).card :=
        mul_le_mul_of_nonneg_left hV hεE0
      refine ⟨?_, ?_⟩
      · have h0 : p * k ≤ εE / 4 := by linarith only [hpk_le, hpkE]
        have h1 : p * k * (𝒜.part i).card ≤ εE / 4 * (𝒜.part i).card :=
          mul_le_mul_of_nonneg_right h0 (Nat.cast_nonneg _)
        show p * k * (𝒜.part i).card ≤ (εE * (𝒜.part i).card - 2) / 2
        linarith only [h1, h2, hEV]
      · show Real.log tests.card + 2 ≤ 3 / 40 * (εE * (𝒜.part i).card - 2)
        linarith only [h2, hEVlog, hlogtests]
    · obtain ⟨i, -, hq⟩ := mem_biUnion.1 hq
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hq
      have hA : (((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y).card : ℝ) ≤
          CN * S.card / (A₀ * L) := hgood.nbhd_upper i v hv
      have hεN' : a * (cD * S.card / L) / L ^ 6 ≤ εN :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hD₁ ha.le) (pow_nonneg hLpos.le 6)
      refine ⟨?_, ?_⟩
      · have h1 : p * k * (((𝒜.part i).filter fun y =>
            (copyGraph T Ap Am (𝒜.g i)).Adj v y).card : ℝ) ≤
            (p * (K * L ^ 2)) * (CN * S.card / (A₀ * L)) :=
          mul_le_mul hpk_le hA (Nat.cast_nonneg _)
            (le_trans (mul_nonneg hppos.le (Nat.cast_nonneg _)) hpk_le)
        show p * k * (((𝒜.part i).filter fun y =>
            (copyGraph T Ap Am (𝒜.g i)).Adj v y).card : ℝ) ≤ (εN - 2) / 2
        linarith only [h1, hpkN, hεN']
      · show Real.log tests.card + 2 ≤ 3 / 40 * (εN - 2)
        linarith only [hNlog, hεN', hlogtests]
  obtain ⟨R, Z₀, hZR, hRY, hRmatch, hcutsR, hconnZ, hslackR, htestsR⟩ :=
    exists_matching Y π sg k (fun v => conY_degree_le S₀ 𝒜.W hS₀conn.1 v) p μ₀ hppos
      (by
        have : p * (k : ℝ) ^ 2 ≤ p * (K * L ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hkK 2) hppos.le
        linarith only [this, hpk])
      hμ6 (by rw [hpμ]; linarith only [hP1100])
      (by rw [hpμ]; linarith only [hP2048, hlogN])
      (fun J => ⟨(hdir J).1, (hdir J).2.1⟩) hB456.1 hB456.2.1 hB456.2.2 tests htests
  -- the integral connector
  have hRadj : ∀ e ∈ R, (cayleyGraph S).Adj e.out.1 e.out.2 ∧ e.out.1 ∉ 𝒜.W ∧
      e.out.2 ∉ 𝒜.W := by
    intro e he
    have heY := hRY he
    rw [SimpleGraph.mem_edgeFinset, ← mk_out e, SimpleGraph.mem_edgeSet] at heY
    obtain ⟨h1, h2, h3⟩ := heY
    exact ⟨SimpleGraph.mulCayley_mono (by exact_mod_cast hS₀S) h1, h2, h3⟩
  have hfew : ∀ i, (((𝒜.part i).filter (· ∈ vtx R)).card : ℝ) + 2 ≤
      εE * (𝒜.part i).card := by
    intro i
    have h := htestsR (𝒜.part i, εE * (𝒜.part i).card - 2)
      (mem_union_left _ (mem_image.2 ⟨i, mem_univ _, rfl⟩))
    have h' : (((𝒜.part i).filter (· ∈ vtx R)).card : ℝ) ≤ εE * (𝒜.part i).card - 2 := h
    linarith only [h']
  have hsparse : ∀ i, ∀ v ∈ copyVerts Ap Am (𝒜.g i),
      (((𝒜.part i).filter fun y => (copyGraph T Ap Am (𝒜.g i)).Adj v y ∧
        y ∈ vtx R).card : ℝ) + 2 ≤ εN := by
    intro i v hv
    have h := htestsR _ (mem_union_right _ (mem_biUnion.2 ⟨i, mem_univ _,
      mem_image.2 ⟨v, hv, rfl⟩⟩))
    simp only [filter_filter] at h
    linarith only [h]
  have hεN'' : εN ≤ cN * S.card / (A₀ * L) := by
    have : εN ≤ a * (CD * S.card / L) / L ^ 6 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hD₂ ha.le) (pow_nonneg hLpos.le 6)
    linarith only [this, hεN]
  exact connector_of_matching S T Ap Am cT 𝒜 (A₀ * L) D _ _ ω cN CN hT hgood
    ht2 π ι hπ hι R Z₀ hZR hRadj hRmatch (fun J => (cutCnt π sg J Y.edgeFinset : ℝ)) p μ₀ εE εN
    (fun J => Nat.cast_nonneg _) hμ₀pos (by rw [hpμ]; linarith only [hP1100])
    (fun J => (hcutsR J).1) (fun J => (hcutsR J).2.2.1) (fun J => (hcutsR J).2.2.2)
    (fun J => (hdir J).2.2) hconnZ hslackR hfew hsparse hεN''

end Outcome

end Connector

open Connector

/-- **Proposition 6.1 (Connecting system).** Assume (1.1) with a large constant `C₀`. For a
random allocation as produced by Proposition 5.3 (successful with probability at least `7/8`,
reserved set distributed by (5.7)), some successful outcome admits a connecting system `M`: a
physical matching on `G \ W` plus a path `a_H w_H b_H` through each reserved vertex, with
distinct endpoints, connected contraction on the parts, and endpoint sets `E_i` that are
nonempty, balanced between the local sides, and satisfy (6.1):
`|E_i| ≤ a Λ |V_i| / L⁷` and `|N_{F_i}(v) ∩ V_i ∩ E_i| ≤ a D / L⁶`, where `Λ = log L`. -/
theorem connecting_system (cT ω A₀ cσ cD CD cN CN : ℝ) (hcT : 0 < cT) (hω : 0 < ω)
    (hA₀ : 0 < A₀) (hcσ : 0 < cσ) (hcD : 0 < cD) (hCD : cD ≤ CD) (hcN : 0 < cN) (hCN : cN ≤ CN)
    (a : ℝ) (ha : 0 < a) :
    ∃ C₀ : ℝ, ∃ n₀ : ℕ, 0 < C₀ ∧
      ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S T Ap Am : Finset G) (c₁ D : ℝ)
        (μ : FinDist (Allocation G)),
        IsConnectionSet S → (cayleyGraph S).Connected → n₀ ≤ Fintype.card G →
        C₀ * Real.log (Fintype.card G) ^ 13 / Real.log (Real.log (Fintype.card G)) ≤ S.card →
        IsTemplate S T Ap Am cT →
        cD * S.card / Real.log (Fintype.card G) ≤ D →
        D ≤ CD * S.card / Real.log (Fintype.card G) →
        μ.P (fun 𝒜 => ¬ 𝒜.Good S T Ap Am (A₀ * Real.log (Fintype.card G)) D
          (cσ / Real.log (Fintype.card G) ^ 2)
          (c₁ * (cσ / Real.log (Fintype.card G) ^ 2)) ω cN CN) ≤ 1 / 8 →
        ReservationLaw μ T →
        ∃ 𝒜 ∈ μ.support, 𝒜.Good S T Ap Am (A₀ * Real.log (Fintype.card G)) D
            (cσ / Real.log (Fintype.card G) ^ 2)
            (c₁ * (cσ / Real.log (Fintype.card G) ^ 2)) ω cN CN ∧
          ∃ M : SimpleGraph G, 𝒜.IsConnector S T Ap Am M
            (a * Real.log (Real.log (Fintype.card G)) / Real.log (Fintype.card G) ^ 7)
            (a * D / Real.log (Fintype.card G) ^ 6) := by
  obtain ⟨A₁, c₂, hA₁, hc₂, n₁, hlabel⟩ := label_sampling.{u} cT A₀ cN hcT hA₀ hcN
  obtain ⟨Cres, CB, hCres, hCB, n₂, hres⟩ := reservation_estimates.{u}
  obtain ⟨c₃, hc₃, n₃, hcuts⟩ :=
    allocation_cuts.{u} cT A₀ cN c₂ 8 hcT hA₀ hcN hc₂ (by norm_num)
  set K : ℝ := 8 + 4 * A₁ * A₀ with hK_def
  have hK : 0 < K := by positivity
  set P₀ : ℝ := 2 ^ 19 with hP₀_def
  obtain ⟨L₀, hL₀3, hreg⟩ := regime cT A₀ cN CN cD CD a c₃ Cres CB K P₀ hcT hA₀ hcN
    (hcN.trans_le hCN) hcD (hcD.trans_le hCD) ha hc₃ hCres hCB hK le_rfl
  refine ⟨1, max (max n₁ n₂) (max n₃ ⌈Real.exp L₀⌉₊), one_pos, ?_⟩
  intro G _ _ _ S T Ap Am c₁ D μ hS hconn hn hd hT hD₁ hD₂ hfail hlaw
  have hn₁ : n₁ ≤ Fintype.card G := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂ : n₂ ≤ Fintype.card G := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn₃ : n₃ ≤ Fintype.card G := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnL : ⌈Real.exp L₀⌉₊ ≤ Fintype.card G :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  set n := Fintype.card G with hn_def
  set L := Real.log n with hL_def
  set d : ℝ := (S.card : ℝ) with hd_def
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < n := by linarith
  have hLL₀ : L₀ ≤ L := by
    rw [hL_def, Real.le_log_iff_exp_le hnpos]
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast hnL)
  have hL3 : 3 ≤ L := hL₀3.trans hLL₀
  have hLpos : 0 < L := by linarith
  have hΛpos : 0 < Real.log L := Real.log_pos (by linarith)
  have hdL : L ^ 13 ≤ Real.log L * d := by
    have h := hd
    rw [one_mul, div_le_iff₀ hΛpos] at h
    linarith
  obtain ⟨hL12, htwo, hlog2, hCresK, h3B, hμ6, hpk, hP1100, hP2048, hpkE, hEV, hEVlog,
    hpkN, hNlog, hεN⟩ := hreg L d hLL₀ hdL
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hL12
  have hTcard : cT * d ≤ T.card := hT.card_T
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < T.card := lt_of_lt_of_le (by positivity) hTcard
    exact_mod_cast this
  -- the added labels
  obtain ⟨S₁, hS₁S, hS₁symm, hS₁card, hS₁gen, hS₁nb⟩ := added_labels S hS hconn
  have hS₁L : (S₁.card : ℝ) ≤ 8 * L := by
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : (Nat.log 2 (2 * n) : ℝ) ≤ (Real.log 2 + L) / Real.log 2 := by
      have hpow := Nat.pow_log_le_self 2 (show 2 * n ≠ 0 by positivity)
      rw [le_div_iff₀ hlog2pos]
      have : Real.log ((2 : ℝ) ^ Nat.log 2 (2 * n)) ≤ Real.log (2 * n) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hpow)
      rw [Real.log_pow, Real.log_mul (by norm_num) hnpos.ne'] at this
      linarith
    have h2 : (S₁.card : ℝ) ≤ 2 * ((Nat.log 2 (2 * n) : ℝ) + 1) := by exact_mod_cast hS₁card
    linarith
  -- the label experiment and the joint union bound
  set U := Subgroup.closure (T : Set G) with hU_def
  have hsampT : ∀ ξ, sampled T ξ ⊆ T := fun ξ => filter_subset _ _
  have hS₀conn : ∀ ξ, IsConnectionSet (S₁ ∪ sampled T ξ) := by
    intro ξ
    refine ⟨fun s hs => ?_, fun h1 => ?_⟩
    · rcases mem_union.1 hs with h | h
      · exact mem_union_left _ (hS₁symm s h)
      · exact mem_union_right _ (sampled_symm T hT.symm ξ s h)
    · rcases mem_union.1 h1 with h | h
      · exact hS.2 (hS₁S h)
      · exact hS.2 (hT.sub (hsampT ξ h))
  have hS₀S : ∀ ξ, S₁ ∪ sampled T ξ ⊆ S := fun ξ => union_subset hS₁S ((hsampT ξ).trans hT.sub)
  have hS₀gen : ∀ ξ, Subgroup.closure ((S₁ ∪ sampled T ξ : Finset G) : Set G) = ⊤ := by
    intro ξ
    rw [eq_top_iff, ← hS₁gen]
    exact Subgroup.closure_mono (by rw [Finset.coe_union]; exact Set.subset_union_left)
  have hX₀conn : ∀ ξ, (cayleyGraph (S₁ ∪ sampled T ξ)).Connected :=
    fun ξ => cayley_connected _ (hS₀conn ξ).1 (hS₀gen ξ)
  have hkL : ∀ ξ, ((sampled T ξ).card : ℝ) ≤ 4 * A₁ * A₀ * L ^ 2 →
      ((S₁ ∪ sampled T ξ).card : ℝ) ≤ K * L ^ 2 := by
    intro ξ hξ
    have h' : ((S₁ ∪ sampled T ξ).card : ℝ) ≤ S₁.card + (sampled T ξ).card := by
      exact_mod_cast card_union_le S₁ (sampled T ξ)
    have hL1 : 8 * L ≤ 8 * L ^ 2 := by nlinarith
    rw [hK_def]
    linarith
  have hu : (T.card : ℝ) ≤ Nat.card U := by exact_mod_cast card_le_closure T
  obtain ⟨𝒜, h𝒜, ξ, -, hgood, h62, hKξ, hC⟩ := joint_union_bound μ
    (labelLaw G (A₁ * A₀ * L ^ 2 / S.card))
    (fun 𝒜 => 𝒜.Good S T Ap Am (A₀ * L) D (cσ / L ^ 2) (c₁ * (cσ / L ^ 2)) ω cN CN)
    (fun 𝒜 ξ => Sampled62 𝒜 T Ap Am ξ (c₂ * L))
    (fun ξ => ((sampled T ξ).card : ℝ) ≤ 4 * A₁ * A₀ * L ^ 2)
    (fun 𝒜 ξ => Odd (Nat.card U) → Res65 T (S₁ ∪ sampled T ξ) 𝒜.W ∧
      Res66 T (S₁ ∪ sampled T ξ) 𝒜.W (CB * (S₁ ∪ sampled T ξ).card * L))
    (1 / 4) (1 / 4) hfail
    (fun 𝒜 _ hgood => hlabel G S T Ap Am 𝒜 D _ _ ω CN hn₁ hS hL12 hT hgood)
    (fun ξ _ hξ => by
      by_cases hodd : Odd (Nat.card U)
      · rw [P_congr _ (E' := fun 𝒜 => ¬ (Res65 T (S₁ ∪ sampled T ξ) 𝒜.W ∧
          Res66 T (S₁ ∪ sampled T ξ) 𝒜.W (CB * (S₁ ∪ sampled T ξ).card * L)))
          (fun 𝒜 => by simp only [hodd, true_implies])]
        refine hres G T (S₁ ∪ sampled T ξ) μ _ hn₂ (hS₀conn ξ) (hX₀conn ξ) le_rfl ?_ hlaw hodd
        have hk := hkL ξ hξ
        calc Cres * ((S₁ ∪ sampled T ξ).card : ℝ) * L ≤ Cres * (K * L ^ 2) * L := by gcongr
          _ ≤ cT * d := hCresK
          _ ≤ T.card := hTcard
          _ ≤ Nat.card U := hu
      · rw [P_congr _ (E' := fun _ => False) (fun 𝒜 => by simp only [hodd, false_implies,
          not_true_eq_false]), P_false]
        norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  clear hlabel hres hreg
  refine ⟨𝒜, h𝒜, hgood, connector_of_outcome S T Ap Am S₁ (sampled T ξ) 𝒜 cT A₀ cN CN cD CD a c₃
    CB K P₀ D _ _ ω L d rfl rfl hS hconn hT hgood hA₀ hcN ha hc₃ hCB hK hL3 hdpos hD₁ hD₂
    (hS₀conn ξ) (hS₀S ξ) hTne (hkL ξ hKξ) htwo h3B hμ6 hpk hP1100 hP2048 hpkE hEV hEVlog hpkN
    hNlog hεN (fun hodd => (hC hodd).2) (fun π hπ => hcuts G S T Ap Am S₁ (sampled T ξ) 𝒜 D _ _ ω
      CN π hn₃ hS hconn hL12 hT hgood hπ (hS₀conn ξ) (hS₀S ξ) (hsampT ξ) hS₁gen hS₁nb hS₁L h62
      (fun hodd => (hC hodd).1))⟩

end Lovasz
