/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Challenge

/-!
# Shared definitions for the proof DAG

Definitions used by the intermediate lemmas of the proof of Theorem 1.1 of
`docs/Polylog_Cayley.pdf` (see `docs/BLUEPRINT.md`). None of these is used by the audited
statement in `Challenge.lean`.

* `FinDist`: finitely supported probability distributions (all randomness in the paper is on
  finite spaces).
* `WGraph`: finite weighted graphs (Section 2), with degrees, volumes, edge weights between
  sets, the normalized upper gap in its variational form (2.1), and cut density (Section 2.3).
* Path systems, perfect matchings of a vertex set, matching-absorbing pairs (Definition 3.1),
  comparators and Hamilton routers (Section 3.2).
* Signed incidence systems (Section 4).
-/

universe u

noncomputable section

namespace Lovasz

open Finset

/-! ### Finite probability distributions -/

/-- A finitely supported probability distribution on `α`. -/
structure FinDist (α : Type*) where
  /-- The (finite) support. -/
  support : Finset α
  /-- The probability mass function. -/
  prob : α → ℝ
  prob_nonneg : ∀ a, 0 ≤ prob a
  sum_prob : ∑ a ∈ support, prob a = 1

namespace FinDist

variable {α : Type*}

open Classical in
/-- The probability of an event. -/
noncomputable def P (μ : FinDist α) (E : α → Prop) : ℝ :=
  ∑ a ∈ μ.support, if E a then μ.prob a else 0

/-- The expectation of a real random variable. -/
def expect (μ : FinDist α) (f : α → ℝ) : ℝ :=
  ∑ a ∈ μ.support, μ.prob a * f a

open Classical in
/-- The point mass at `a`. -/
def dirac (a : α) : FinDist α where
  support := {a}
  prob := fun b => if b = a then 1 else 0
  prob_nonneg := fun b => by split_ifs <;> norm_num
  sum_prob := by simp

open Classical in
/-- The mixture `p μ₁ + (1 - p) μ₂` for `p ∈ [0, 1]`. -/
def mix (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (μ₁ μ₂ : FinDist α)
    (h₁ : ∀ a ∉ μ₁.support, μ₁.prob a = 0) (h₂ : ∀ a ∉ μ₂.support, μ₂.prob a = 0) :
    FinDist α where
  support := μ₁.support ∪ μ₂.support
  prob := fun a => p * μ₁.prob a + (1 - p) * μ₂.prob a
  prob_nonneg := fun a => add_nonneg (mul_nonneg hp.1 (μ₁.prob_nonneg a))
    (mul_nonneg (by linarith [hp.2]) (μ₂.prob_nonneg a))
  sum_prob := by
    have e₁ : ∑ a ∈ μ₁.support ∪ μ₂.support, μ₁.prob a = 1 := by
      rw [← Finset.sum_subset Finset.subset_union_left (fun a _ ha => h₁ a ha)]
      exact μ₁.sum_prob
    have e₂ : ∑ a ∈ μ₁.support ∪ μ₂.support, μ₂.prob a = 1 := by
      rw [← Finset.sum_subset Finset.subset_union_right (fun a _ ha => h₂ a ha)]
      exact μ₂.sum_prob
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e₁, e₂]
    ring

/-- The support is exact: the mass vanishes off the support. -/
def IsExact (μ : FinDist α) : Prop := ∀ a ∉ μ.support, μ.prob a = 0

end FinDist

/-- A finite randomized process in `[0,1]^ι` moving along lines (Lemmas 4.2 and 4.3).
`LineProcess ok x μ` means: started at `x`, the process has terminal distribution `μ`. At each
step, conditional on the past, it either stops, or moves to `x + α h` with probability
`β / (α + β)` and to `x - β h` with probability `α / (α + β)` (so the mean is unchanged), where
the direction `h` satisfies `ok h`, and it continues with its own sub-process from each point.
All visited points lie in `[0,1]^ι`. -/
inductive LineProcess {ι : Type*} (ok : (ι → ℝ) → Prop) :
    (ι → ℝ) → FinDist (ι → ℝ) → Prop
  | stop (x : ι → ℝ) : (∀ i, 0 ≤ x i ∧ x i ≤ 1) → LineProcess ok x (FinDist.dirac x)
  | move (x h : ι → ℝ) (α β : ℝ) (μ₁ μ₂ : FinDist (ι → ℝ)) (hα : 0 < α) (hβ : 0 < β)
      (h₁ : μ₁.IsExact) (h₂ : μ₂.IsExact) :
      (∀ i, 0 ≤ x i ∧ x i ≤ 1) → ok h →
      LineProcess ok (x + α • h) μ₁ → LineProcess ok (x - β • h) μ₂ →
      LineProcess ok x (FinDist.mix (β / (α + β))
        ⟨div_nonneg hβ.le (add_pos hα hβ).le,
          (div_le_one (add_pos hα hβ)).2 (le_add_of_nonneg_left hα.le)⟩ μ₁ μ₂ h₁ h₂)

/-! ### Matrices -/

open Matrix

/-- `λ_max(A) ≥ t` for a real symmetric matrix: some unit vector has Rayleigh quotient `≥ t`. -/
def LamMaxGe {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (t : ℝ) : Prop :=
  ∃ v : Fin q → ℝ, v ⬝ᵥ v = 1 ∧ t ≤ v ⬝ᵥ (A *ᵥ v)

/-- `λ_min(A) ≤ t`: some unit vector has Rayleigh quotient `≤ t`. -/
def LamMinLe {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (t : ℝ) : Prop :=
  ∃ v : Fin q → ℝ, v ⬝ᵥ v = 1 ∧ v ⬝ᵥ (A *ᵥ v) ≤ t

/-- The quadratic form of `A` is at most `b |v|²` (for PSD `A`: `‖A‖ ≤ b`). -/
def QuadLe {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (b : ℝ) : Prop :=
  ∀ v : Fin q → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ b * (v ⬝ᵥ v)

/-! ### Weighted graphs -/

/-- A weighted graph on `V`: symmetric nonnegative weights vanishing on the diagonal. The
support edges are the pairs of positive weight (Section 2). -/
structure WGraph (V : Type*) where
  /-- The weight `a_{xy}`. -/
  w : V → V → ℝ
  symm : ∀ x y, w x y = w y x
  nonneg : ∀ x y, 0 ≤ w x y
  loopless : ∀ x, w x x = 0

namespace WGraph

variable {V : Type*} (H : WGraph V)

/-- The support graph `supp H`: `x ∼ y` iff `a_{xy} > 0`. -/
def supp : SimpleGraph V where
  Adj x y := 0 < H.w x y
  symm := ⟨fun x y h => by rwa [H.symm]⟩
  loopless := ⟨fun x h => by simp [H.loopless] at h⟩

/-- The induced weighted graph `H[A]` on the vertex set `A`. -/
def induce (A : Finset V) : WGraph A where
  w x y := H.w x y
  symm x y := H.symm x y
  nonneg x y := H.nonneg x y
  loopless x := H.loopless x

/-- The unit-weight graph of a simple graph. -/
noncomputable def ofSimpleGraph (Γ : SimpleGraph V) : WGraph V := by
  classical
  exact
  { w := fun x y => if Γ.Adj x y then 1 else 0
    symm := fun x y => by simp only [Γ.adj_comm]
    nonneg := fun x y => by split_ifs <;> norm_num
    loopless := fun x => by simp }

/-- `H` is bipartite with respect to the colouring `col`: every support edge joins the two
colour classes. -/
def IsBipartiteWith (col : V → Bool) : Prop :=
  ∀ x y, 0 < H.w x y → col x ≠ col y

/-- All positive weights lie in `[ω, 1]`. -/
def WeightsIn (ω : ℝ) : Prop :=
  ∀ x y, 0 < H.w x y → ω ≤ H.w x y ∧ H.w x y ≤ 1

section Fintype

variable [Fintype V]

/-- Weighted degree `d_H(x) = ∑_y a_{xy}`. -/
def deg (x : V) : ℝ := ∑ y, H.w x y

/-- Weighted degree into a set, `d_H(x, A) = ∑_{y ∈ A} a_{xy}`. -/
def degOn (x : V) (A : Finset V) : ℝ := ∑ y ∈ A, H.w x y

/-- Volume `vol_H(A) = ∑_{x ∈ A} d_H(x)`. -/
def vol (A : Finset V) : ℝ := ∑ x ∈ A, H.deg x

/-- Total weight between two sets, `e_H(A, B) = ∑_{x ∈ A} ∑_{y ∈ B} a_{xy}`. -/
def edgeWeight (A B : Finset V) : ℝ := ∑ x ∈ A, ∑ y ∈ B, H.w x y

/-- The Dirichlet form `∑_{xy ∈ E(H)} a_{xy} (f_x - f_y)^2` (each edge counted once). -/
def dirichlet (f : V → ℝ) : ℝ := (∑ x, ∑ y, H.w x y * (f x - f y) ^ 2) / 2

/-- `H` has normalized upper gap `1 - λ₂(N_H)` at least `σ`, in the variational form (2.1):
for every `f` there is a constant `z` with `σ ∑_x d_H(x) (f_x - z)^2 ≤ ∑_{xy} a_{xy}(f_x-f_y)^2`.
For graphs with positive degrees this is equivalent to `1 - λ₂(D^{-1/2} A D^{-1/2}) ≥ σ`. -/
def HasGap (σ : ℝ) : Prop :=
  ∀ f : V → ℝ, ∃ z : ℝ, σ * ∑ x, H.deg x * (f x - z) ^ 2 ≤ H.dirichlet f

/-- Degrees `(1 ± η) D`. -/
def DegNear (D η : ℝ) : Prop := ∀ x, |H.deg x - D| ≤ η * D

/-- Degrees in `[a, b]`. -/
def DegBetween (a b : ℝ) : Prop := ∀ x, a ≤ H.deg x ∧ H.deg x ≤ b

/-- `ξ`-cut-density (Section 2.3): `e_H(T, Tᶜ) ≥ ξ |T| |Tᶜ|` for every vertex set `T`. -/
def IsCutDense [DecidableEq V] (ξ : ℝ) : Prop :=
  ∀ A : Finset V, ξ * A.card * (univ \ A).card ≤ H.edgeWeight A (univ \ A)

end Fintype

end WGraph

/-! ### Matchings, path systems, absorbers and routers -/

section Paths

variable {V : Type*}

/-- `J` is a perfect matching of the vertex set `E`: its edges lie inside `E` and every vertex
of `E` has exactly one `J`-neighbour. -/
def IsPerfectMatchingOn (J : SimpleGraph V) (E : Set V) : Prop :=
  (∀ x y, J.Adj x y → x ∈ E ∧ y ∈ E) ∧ ∀ x ∈ E, ∃! y, J.Adj x y

/-- `P` is a spanning system of vertex-disjoint paths of the vertex set `A` with endpoint set
`T`: its edges lie in `A`, vertices of `T` have degree one, other vertices of `A` have degree
two, and every component meets `T` (so there are no cycles). Each path joins two vertices of
`T`; which ones is recorded separately with `P.Reachable`. -/
structure IsPathSystem (P : SimpleGraph V) (A T : Set V) : Prop where
  adj_mem : ∀ x y, P.Adj x y → x ∈ A ∧ y ∈ A
  subset : T ⊆ A
  deg_end : ∀ x ∈ T, (P.neighborSet x).ncard = 1
  deg_inner : ∀ x ∈ A, x ∉ T → (P.neighborSet x).ncard = 2
  reach_end : ∀ x ∈ A, ∃ t ∈ T, P.Reachable x t

/-- **Definition 3.1.** `(H, E)` is matching-absorbing: `E` is a finite nonempty set of even
size, and for every perfect matching `J` of `E` the multigraph `H + J` has a Hamilton cycle
containing every edge of `J` (the edges of `J` are formal and kept separate from parallel edges
of `H`). Equivalently: there is a spanning subgraph `P ≤ H` in which the vertices of `E` have
degree one and all other vertices degree two (a spanning path system with endpoint set `E`),
such that `P ∪ J` is connected — then the 2-regular multigraph `P + J` is a single cycle. -/
def IsMatchingAbsorbing (H : SimpleGraph V) (E : Set V) : Prop :=
  E.Finite ∧ E.Nonempty ∧ Even E.ncard ∧
    ∀ J : SimpleGraph V, IsPerfectMatchingOn J E →
      ∃ P : SimpleGraph V, P ≤ H ∧ (∀ x ∈ E, (P.neighborSet x).ncard = 1) ∧
        (∀ x ∉ E, (P.neighborSet x).ncard = 2) ∧ (P ⊔ J).Connected

/-- A comparator (Section 3.2) on the vertex set `A` of the graph `K`, with inputs `x₁, x₂` and
outputs `y₁, y₂`: it has spanning path partitions of `A` into two paths realizing both
input–output bijections. -/
def IsComparator (K : SimpleGraph V) (A : Set V) (x₁ x₂ y₁ y₂ : V) : Prop :=
  [x₁, x₂, y₁, y₂].Nodup ∧
    (∃ P ≤ K, IsPathSystem P A {x₁, x₂, y₁, y₂} ∧ P.Reachable x₁ y₁ ∧ P.Reachable x₂ y₂) ∧
    (∃ P ≤ K, IsPathSystem P A {x₁, x₂, y₁, y₂} ∧ P.Reachable x₁ y₂ ∧ P.Reachable x₂ y₁)

/-- The formal matching `{o, β o}` of a bijection `β : O ≃ I`. -/
def bijMatching {I O : Set V} (β : O ≃ I) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ o : O, e = s((o : V), (β o : V))}

/-- An `I, O`-Hamilton router on the vertex set `A` of `K` (Section 3.2): `I, O ⊆ A` are
disjoint of the same size, and for every bijection `β : O → I` there is a spanning partition of
`A` into paths of `K`, each joining a vertex of `I` to a vertex of `O`, whose union with the
formal matching `{o, β o}` is a Hamilton cycle of `A`. -/
def IsHamRouter (K : SimpleGraph V) (A I O : Set V) : Prop :=
  Disjoint I O ∧ I.ncard = O.ncard ∧ I ∪ O ⊆ A ∧
    ∀ β : O ≃ I, ∃ P ≤ K, IsPathSystem P A (I ∪ O) ∧
      (∀ x ∈ I, ∀ y ∈ I, P.Reachable x y → x = y) ∧
      ((P ⊔ bijMatching β).induce A).Connected

end Paths

/-! ### Signed incidence systems (Section 4) -/

/-- A signed multigraph on the vertex type `V` with edge type `E`: each edge has two ends, each
end a vertex and a sign in `{+1, -1}`. Loops are allowed. -/
structure SignedGraph (V E : Type*) where
  /-- First end of an edge. -/
  fst : E → V
  /-- Second end of an edge. -/
  snd : E → V
  /-- Sign at the first end (`true` = `+1`). -/
  sfst : E → Bool
  /-- Sign at the second end. -/
  ssnd : E → Bool

namespace SignedGraph

variable {V E : Type*} (Γ : SignedGraph V E)

/-- The sign `±1` as a real number. -/
noncomputable def signVal (b : Bool) : ℝ := if b then 1 else -1

open Classical in
/-- The signed incidence matrix `B`: the column of an edge is the sum of the two signed unit
vectors of its ends (so a loop has column `2e_v`, `-2e_v` or `0`). -/
noncomputable def incidence (v : V) (e : E) : ℝ :=
  (if Γ.fst e = v then signVal (Γ.sfst e) else 0) + (if Γ.snd e = v then signVal (Γ.ssnd e) else 0)

/-- `(B x)_v`. -/
noncomputable def apply [Fintype E] (x : E → ℝ) (v : V) : ℝ := ∑ e, Γ.incidence v e * x e

/-- An edge crosses the vertex set `U` if exactly one end lies in `U` (loops never cross). -/
def crosses (U : Set V) (e : E) : Prop := (Γ.fst e ∈ U) ≠ (Γ.snd e ∈ U)

/-- The underlying (unsigned, loopless) simple graph. -/
def underlying : SimpleGraph V :=
  SimpleGraph.fromRel fun v w => ∃ e, Γ.fst e = v ∧ Γ.snd e = w

/-- The set of integral (0/1) solutions of `B z = b`. -/
def integralSolutions [Fintype E] (b : V → ℝ) : Set (E → ℝ) :=
  {z | (∀ e, z e = 0 ∨ z e = 1) ∧ ∀ v, Γ.apply z v = b v}

/-- Twin arcs (4.5) of the two-state directed graph: the edge `ij` with signs `s` at `i` and `t`
at `j` gives the arcs `i^s → j^{-t}` (index `false`) and `j^t → i^{-s}` (index `true`). States
are pairs `(vertex, sign)`. This is the tail of an arc. -/
def twinTail : E × Bool → V × Bool
  | (e, false) => (Γ.fst e, Γ.sfst e)
  | (e, true) => (Γ.snd e, Γ.ssnd e)

/-- The head of a twin arc (4.5). -/
def twinHead : E × Bool → V × Bool
  | (e, false) => (Γ.snd e, !Γ.ssnd e)
  | (e, true) => (Γ.fst e, !Γ.sfst e)

end SignedGraph

/-! ### Cycles and comparator patterns (Section 3.2) -/

section Comparator

variable {V : Type*}

/-- The cycle graph on the (distinct) vertices `c 0, c 1, …, c (m-1)`, `c (m-1) ∼ c 0`. -/
def cycleOn {m : ℕ} (c : Fin m → V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ i : Fin m, e = s(c i, c (finRotate m i))}

/-- Vertex `k mod 2r` of a `2r`-cycle `c`. -/
def cyc {r : ℕ} (hr : 0 < r) (c : Fin (2 * r) → V) (k : ℕ) : V :=
  c ⟨k % (2 * r), Nat.mod_lt _ (by omega)⟩

/-- The pairing (3.4) of the non-terminal vertices of a `2r`-cycle (`r ≥ 3`), as index pairs:
`{c_{2j+1} c_{2j+4} : 1 ≤ j ≤ r-3} ∪ {c_{2r-3} c_{2r-1}}`; empty for the 4-cycle `r = 2`. -/
def comparatorPairs (r : ℕ) : List (ℕ × ℕ) :=
  if r ≤ 2 then [] else
    ((List.range (r - 3)).map fun j => (2 * (j + 1) + 1, 2 * (j + 1) + 4)) ++
      [(2 * r - 3, 2 * r - 1)]

end Comparator

/-! ### Cayley-graph objects (Sections 5 and 6) -/

section Cayley

variable {G : Type u} [Group G]

/-- The bipartite template `Cay(G, T)[A⁺, A⁻]` (Lemma 5.1): vertices `A⁺ ∪ A⁻`, and the edges
`x ∼ x s` (`s ∈ T`) joining `A⁺` to `A⁻`. -/
def templateGraph (T Ap Am : Finset G) : SimpleGraph G where
  Adj x y := x ≠ y ∧ ((x ∈ Ap ∧ y ∈ Am) ∨ (x ∈ Am ∧ y ∈ Ap)) ∧ (x⁻¹ * y ∈ T ∨ y⁻¹ * x ∈ T)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.1.symm.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩),
    h.2.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The label density `f_s(F) = |{x ∈ V(F) : {x, xs} ∈ E(F)}| / m` of Section 5.1. -/
noncomputable def labelDensity [Fintype G] [DecidableEq G] (T Ap Am : Finset G) (s : G) : ℝ := by
  classical
  exact ((Ap ∪ Am).filter fun x => (templateGraph T Ap Am).Adj x (x * s)).card / (Ap ∪ Am).card

end Cayley

/-! ### Interfaces of the top-level nodes -/

section Interfaces

variable {V : Type*}

/-- The connector endpoints `E_i` inside the part `A`: vertices of `A` of `M`-degree one. -/
def connectorEnds (M : SimpleGraph V) (A : Finset V) : Set A :=
  {x | (M.neighborSet (x : V)).ncard = 1}

/-- The hypotheses of **Lemma 3.8** (cycle merging), apart from absorption. The parts
`part i` partition `V \ W`. The graph `M` is the union of the connecting edges and paths: its
vertices in `W` have degree two, all other vertices degree at most one, and every component
meets a part (no cycle inside `W`); thus `M` is a family of paths with mutually distinct
endpoints in the parts whose interiors partition `W`. The local graphs `H i` are subgraphs of
`X` on the parts that use no edge of `M`, and the contraction of `M` on the parts is connected.
-/
structure IsMergingData (X : SimpleGraph V) {ι : Type*} (part : ι → Finset V) (W : Set V)
    (M : SimpleGraph V) (H : ∀ i, SimpleGraph (part i)) : Prop where
  part_unique : ∀ v, v ∉ W → ∃! i, v ∈ part i
  part_disjoint : ∀ i, Disjoint (part i : Set V) W
  le : M ≤ X
  deg_W : ∀ w ∈ W, (M.neighborSet w).ncard = 2
  deg_out : ∀ v ∉ W, (M.neighborSet v).ncard ≤ 1
  meets_part : ∀ v, ∃ x, x ∉ W ∧ M.Reachable v x
  local_le : ∀ i (x y : part i), (H i).Adj x y → X.Adj x y ∧ ¬ M.Adj x y
  contraction_connected : (SimpleGraph.fromRel fun i j : ι =>
    ∃ x ∈ part i, ∃ y ∈ part j, x ≠ y ∧ M.Reachable x y).Connected

/-- The hypotheses of **Theorem 3.2** (local absorption) for `(H, E)`, with the constants
`ω, c, C` of the theorem: `H` is bipartite with classes of size `N`, weights in `[ω, 1]`,
degrees `(1 ± η) D`, normalized upper gap at least `σ ∈ (0, 1/10]`, `η ≤ c σ`,
`L ≥ max {log (2N), 10}`, `g ≥ 4`, (3.1), and `E` has `ℓ ≥ 1` vertices of each class with
(3.2). -/
structure LocalAbsorptionHyp [Fintype V] (ω c C : ℝ) (H : WGraph V) (col : V → Bool)
    (N ℓ : ℕ) (η D σ L g : ℝ) (E : Finset V) : Prop where
  bipartite : H.IsBipartiteWith col
  card_true : (univ.filter fun x => col x = true).card = N
  card_false : (univ.filter fun x => col x = false).card = N
  weights : H.WeightsIn ω
  degrees : H.DegNear D η
  gap : H.HasGap σ
  sigma_pos : 0 < σ
  sigma_le : σ ≤ 1 / 10
  eta_le : η ≤ c * σ
  log_le : Real.log (2 * N) ≤ L
  ten_le : 10 ≤ L
  four_le : 4 ≤ g
  deg_large : C * σ ^ (-(9 / 2 : ℝ)) * L ^ 2 * g ≤ D
  girth_param : C * L / Real.log (2 + σ ^ (5 / 2 : ℝ) * D / L) ≤ g
  ends_true : (E.filter fun x => col x = true).card = ℓ
  ends_false : (E.filter fun x => col x = false).card = ℓ
  one_le : 1 ≤ ℓ
  ends_few : (ℓ : ℝ) ≤ c * σ ^ (5 / 2 : ℝ) * N / (L * g)
  ends_sparse : ∀ x, H.degOn x E ≤ c * σ ^ (5 / 2 : ℝ) * D / L

end Interfaces

end Lovasz
