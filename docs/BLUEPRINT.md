# Blueprint: the proof DAG for Theorem 1.1

This is the lemma DAG for the formal proof of Theorem 1.1 of
[`Polylog_Cayley.pdf`](Polylog_Cayley.pdf). Every node has an id, the informal statement
with its paper reference, the Lean name and file, the ids it depends on, and a status:

* `todo` — not yet stated in Lean;
* `stated` — stated in Lean with a `sorry` proof;
* `proved` — proved in Lean with no `sorry` (its own proof may use its children's statements,
  which may still be `stated`);
* `proved*` — proved and all its descendants are `proved`.

Section references are to the paper. Shared definitions are in `Lovasz/Defs.lean`.

## Modelling choices for the intermediate nodes

* **Weighted graphs** (`WGraph V`): a symmetric nonnegative weight function with zero diagonal on
  a finite type. Degrees, volumes and edge weights between sets are the paper's `d_H`, `vol_H`,
  `e_H`. Induced subgraphs `H.induce A` live on the subtype of a `Finset`.
* **Normalized upper gap** `1 - λ₂(N_H) ≥ σ` is `WGraph.HasGap H σ`, the variational form (2.1):
  `∀ f, ∃ z, σ ∑_x d(x)(f_x - z)^2 ≤ ∑_{xy ∈ E} a_{xy}(f_x - f_y)^2`. For positive degrees this is
  the Courant–Fischer characterization of `1 - λ₂(D^{-1/2} A D^{-1/2})`; using it avoids an
  eigenvalue API in every statement. Nodes whose proofs are spectral (L2.1, L3.3, L2.3, P5.3)
  must connect it to eigenvalues internally.
* **Matching-absorbing** (Definition 3.1): via path systems — for every perfect matching `J` of
  `E` there is `P ≤ H` with degree one on `E`, two elsewhere, and `P ⊔ J` connected (so the
  2-regular multigraph `P + J` is one Hamilton cycle through all edges of `J`). `E` finite,
  nonempty, of even size is part of the definition.
* **Path systems, comparators, routers** (Section 3.2): `IsPathSystem P A T` (spanning
  vertex-disjoint paths of `A` with endpoint set `T`), `IsComparator`, `IsHamRouter`.
* **Connecting systems** (Lemma 3.8): the union `M` of the connecting edges and paths as one
  simple graph: degree two on `W`, at most one elsewhere, no component inside `W`
  (`IsMergingData`).
* **Randomness**: every random experiment in the paper is on a finite space. Probabilities are
  expressed with finitely supported distributions `FinDist` or, for uniform sampling, by
  counting. The dependent rounding process of Section 4 is the inductive predicate
  `LineProcess ok x μ` ("started at `x`, the line-move process has terminal law `μ`").
* **Spectral norms**: statements about `λ_max`, `λ_min` and `‖A‖` of symmetric matrices are
  written with Rayleigh quotients (`LamMaxGe`, `LamMinLe`, `QuadLe`).
* **Matrix Bernstein** (2.5) is *not* used as a node: its only use, the retention step of
  Lemma 2.2, is a sum of independent Bernoulli-weighted PSD matrices, which is the special case
  of Lemma 4.3 (proved in the paper) where every move changes one coordinate. This avoids
  formalizing Lieb's concavity theorem. The constants in Lemma 2.2 change by a fixed factor,
  which Lemma 2.2's statement absorbs into a universal constant.

## The DAG

### Top level

| id | statement (paper) | Lean name — file | depends on | status |
|---|---|---|---|---|
| MAIN | Theorem 1.1 | `Lovasz.main_proof` — `Lovasz/Main.lean` (type is literally that of `Lovasz.hamiltonian_of_polylog_degree`) | GD, T3.2, L3.8 | proved |
| L3.8 | Lemma 3.8 (cycle merging): absorbing parts + connected contraction of the connecting paths ⇒ Hamiltonian | `Lovasz.cycle_merging` — `Lovasz/CycleMerging.lean` | — | stated |
| T3.2 | Theorem 3.2 (local absorption) | `Lovasz.local_absorption` — `Lovasz/LocalAbsorption.lean` | L2.1, E2.2, E2.2c, L2.2, L2.3, L2.4, L2.5, L3.3, L3.4, L3.5, L3.6, L3.7, L3.dfs, K.chernoff | stated |
| GD | Sections 5–7: the weighted partition, the connecting system and the parameter check of §7, packaged as the hypotheses of Lemma 3.8 plus those of Theorem 3.2 for each part | `Lovasz.global_decomposition` — `Lovasz/GlobalDecomposition.lean` | L5.1, P5.3, P6.1, L2.1 | stated |

### Section 2: weighted spectral and matching facts

| id | statement (paper) | Lean name — file | depends on | status |
|---|---|---|---|---|
| E2.2 | (2.2): gap `σ` ⇒ `e(U,Uᶜ) ≥ σ vol(U) vol(Uᶜ)/vol(V)` | `WGraph.edgeWeight_compl_ge_of_hasGap` — `Lovasz/GapCut.lean` | — | stated |
| E2.2c | §2.3: comparable degrees and gap `σ` ⇒ cut-density `cσD/h` | `WGraph.isCutDense_of_hasGap` — `Lovasz/GapCut.lean` | E2.2 | stated |
| K.cheeger | normalized Cheeger inequality `1 - λ₂ ≥ Φ²/2` (§2.1, [1]) | `WGraph.hasGap_of_conductance` — `Lovasz/Cheeger.lean` | — | stated |
| L2.1 | Lemma 2.1: deleting vertices/edges with degree loss `≤ b ≤ c'D` keeps gap `≥ σ - O(b/D)` | `Lovasz.hasGap_of_deletion` — `Lovasz/Perturbation.lean` | — | stated |
| E2.4 | (2.3)–(2.4): the positive part `E₊` of `N_H - uuᵀ` has `(E₊)_vv ≤ C r^{-1/2}` for comparable support degrees `r` | *(inside P5.3)* | — | todo |
| L2.2 | Lemma 2.2 (column sampling): `P(‖F[:,I]‖ > √q‖F‖ + C c√t) ≤ r(s+1)e^{-t}` | *to be stated in* `Lovasz/ColumnSampling.lean` | L4.3, L4.2m | todo |
| L2.3 | Lemma 2.3 (bipartite sampling) | *to be stated in* `Lovasz/BipartiteSampling.lean` | L2.2, K.chernoff, L2.1 | todo |
| L2.4 | Lemma 2.4 (fixed boundary, fresh layer) | *to be stated in* `Lovasz/BipartiteSampling.lean` | L2.2, K.chernoff | todo |
| L2.5 | Lemma 2.5 (robust Hall) | `Lovasz.robust_hall` — `Lovasz/RobustHall.lean` | K.hall | stated |
| K.hall | Hall's marriage theorem | Mathlib `Finset.all_card_le_biUnion_card_iff_exists_injective` | — | proved (Mathlib) |
| K.chernoff | scalar Chernoff bounds, including sampling without replacement and bounded weights (§2.2) | *to be stated in* `Lovasz/Chernoff.lean` | — | todo |

### Section 3: local absorption

| id | statement (paper) | Lean name — file | depends on | status |
|---|---|---|---|---|
| L3.3 | Lemma 3.3 (distances after deletion) | `Lovasz.distances_after_deletion` — `Lovasz/DistanceDeletion.lean` | — | stated |
| K.haxell | Haxell's hypergraph matching theorem [2] | `Lovasz.haxell` — `Lovasz/Haxell.lean` | — | stated |
| L3.4 | Lemma 3.4 (spectral connection) | `Lovasz.spectral_connection` — `Lovasz/SpectralConnection.lean` | L3.3, K.haxell | stated |
| L3.5 | Lemma 3.5 (even-cycle comparator) | `Lovasz.even_cycle_comparator` — `Lovasz/Comparator.lean` | — | stated |
| L3.6 | Lemma 3.6 (linear-size router) | `Lovasz.router_of_comparators` — `Lovasz/Router.lean` | — | stated |
| L3.7 | Lemma 3.7 (many disjoint short cycles) | `Lovasz.many_short_cycles` — `Lovasz/ShortCycles.lean` | — | stated |
| L3.dfs | §3.2 (end): comparable degrees and gap `σ` ⇒ a path with `cσM` vertices | `Lovasz.exists_long_path` — `Lovasz/LongPath.lean` | E2.2 | stated |

The proof of T3.2 (Section 3.3) is decomposed further as follows; these sub-nodes will receive
Lean statements when T3.2 is attacked (they share one large data structure, the random partition
of §3.3, which is best designed together with its proof).

| id | step of §3.3 | depends on |
|---|---|---|
| T3.2a | delete `E`; `H₀` keeps degrees `(1 ± c'σ)D` and gap `cσ` | L2.1 |
| T3.2b | the initial random partition (`R₁, R₂, Z, I, O, U, V`, ports, `C ⊆ R₂`) satisfies all events (degrees, gaps (Lemma 2.3), one-sided events (2.9), (3.9), (3.10)) simultaneously | L2.3, K.chernoff |
| T3.2c | router: `≥ w-1` short cycles in `C` (L3.7), comparators (L3.5), arrangement (L3.6), all connections via L3.4 in `Q`; `S` is balanced | L3.4, L3.5, L3.6, L3.7 |
| T3.2d | attachments of `E` to the ports via L3.4 in `R₁`; the formal matching `J'` | L3.4 |
| T3.2e | divisibility: a path of length `2r+1` in `Z` | L3.dfs |
| T3.2f | fresh equipartition into layers; perfect matchings between consecutive layers | L2.1, L2.3, L2.4, L2.5, E2.2c |
| T3.2g | assembly: layers + router + expansion of formal edges = Hamilton cycle of `H + J` through `J` | T3.2a–f |

### Section 4: signed rounding

| id | statement (paper) | Lean name — file | depends on | status |
|---|---|---|---|---|
| K.bmatch | unit-capacitated perfect b-matching polytope (4.1) [5] | `Lovasz.bmatching_polytope` — `Lovasz/BMatchingPolytope.lean` | — | stated |
| L4.1 | Lemma 4.1 (robust signed integrality) | `Lovasz.robust_signed_integrality` — `Lovasz/SignedIntegrality.lean` | K.bmatch | stated |
| L4.2 | Lemma 4.2 (signed swap rounding) | `Lovasz.signed_swap_rounding` — `Lovasz/SwapRounding.lean` | — | stated |
| L4.2m | line processes preserve the mean and have exact support | `Lovasz.LineProcess.expect_eq`, `Lovasz.LineProcess.isExact` — `Lovasz/SwapRounding.lean` | — | stated |
| L4.3 | Lemma 4.3 (bounded-support concentration) | `Lovasz.bounded_support_concentration` — `Lovasz/TraceConcentration.lean` | — | stated |
| L4.4 | Lemma 4.4 (signed fractional circulations) | `Lovasz.signed_circulation` — `Lovasz/SignedCirculation.lean` | — | stated |
| K.hoffman | circulation criterion (4.6), from max-flow/min-cut | `Lovasz.hoffman_circulation` — `Lovasz/Circulation.lean` | — | stated |

### Section 5: a balanced weighted partition

| id | statement (paper) | Lean name — file | depends on | status |
|---|---|---|---|---|
| L5.1 | Lemma 5.1 (penalized extraction of the template) | `Lovasz.penalized_extraction` — `Lovasz/Template.lean` | K.cheeger | stated |
| K.watkins | Watkins: vertex connectivity of a connected vertex-transitive graph of degree `k` is `≥ k/2` [8] (applied to components of Cayley graphs) | `Lovasz.watkins_cayley` — `Lovasz/Watkins.lean` | — | stated |
| L5.2 | Lemma 5.2 (incidence cuts) | `Lovasz.incidence_cut` — `Lovasz/IncidenceCuts.lean` | K.watkins | stated |
| E5.2 | (5.2): translate cover with every vertex in `≤ 2λ` copies and `c_e ∈ [λf_s/2, 2λf_s]` | *(inside P5.3)* | K.chernoff | todo |
| P5.3 | Proposition 5.3 (weighted partition), including the law (5.7) of the reserved vertices | *to be stated in* `Lovasz/WeightedPartition.lean` | E5.2, L5.2, L4.1, L4.2, L4.2m, L4.3, E2.4, L2.1, K.chernoff | todo |

### Section 6: a sparse connecting system

| id | statement (paper) | Lean name — file | depends on | status |
|---|---|---|---|---|
| L6.2 | Lemma 6.2 (coset cuts) | `Lovasz.coset_cut` — `Lovasz/CosetCuts.lean` | — | stated |
| K.trees | Nash-Williams–Tutte tree packing [4] | `Lovasz.tree_packing` — `Lovasz/TreePacking.lean` | — | stated |
| E6.4 | (6.4): cut counting | `Lovasz.cut_count` — `Lovasz/TreePacking.lean` | K.trees | stated |
| E6.1 | §6.1: label sampling (6.2), `O(L)` generating labels whose lifts generate `G × C₂`, `X₀` (6.3) | *(inside P6.1)* | K.chernoff | todo |
| E6.5 | (6.5)–(6.6): reservation estimates | *(inside P6.1)* | L6.2, E6.4, K.chernoff | todo |
| L6.3 | Lemma 6.3 (allocation cuts) | *to be stated in* `Lovasz/AllocationCuts.lean` | K.watkins, L6.2, E6.5 | todo |
| E6.9 | (6.9): directional balance | *(inside P6.1)* | L6.3, E6.5 | todo |
| L6.4 | Lemma 6.4 (mutual nominations; negative association and Chernoff) | *to be stated in* `Lovasz/MutualNominations.lean` | K.chernoff | todo |
| P6.1 | Proposition 6.1 (connecting system) | *to be stated in* `Lovasz/Connector.lean` | E6.1, E6.5, L6.3, E6.9, L6.4, E6.4, L4.4, K.hoffman, L4.1 | todo |

## Review of the paper's argument

The paper is an unverified draft. While building the DAG we checked the arguments of the
nodes above at the level of detail needed to state them. Findings so far:

* **No definite gap found yet.** The parameter chain of Sections 6–7 is consistent: the text
  extraction of (6.12) is garbled, but the page reads `p = A₂L/µ = O(L²/d)` with `µ = cd/L`, so
  `pk² = O(L⁶/d) = o(1)` and `pk = O(L⁴/d)` as claimed.
* **Lemma 2.5**: the extracted text reads `x ≤ 10α(m - |T|)`; the correct inequality from the
  counting is `x ≤ (α/10)(m - |T|)`, which is what the final contradiction
  `h < (α/10)(h + u) ≤ ((α+1)/10) h` uses (a typesetting issue, not a gap).
* **Risk areas** (not yet formalized, highest review priority): the conditioning in Lemma 2.4 and
  the fresh-layer union bound of §3.3; the use of the dependent rounding (Lemma 4.3) for the
  matrix estimate of §5.3; negative-association Chernoff bounds in §6.4.
