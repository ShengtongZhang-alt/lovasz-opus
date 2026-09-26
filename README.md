# Hamilton cycles in Cayley graphs of polylogarithmic degree

> **Theorem 1.1.** There are absolute constants $C, n_0 > 0$ such that every connected Cayley
> graph on $n \ge n_0$ vertices and of degree at least $C(\log n)^{13}/\log\log n$ contains a
> Hamilton cycle.

This theorem is proven in the research draft
[`docs/Polylog_Cayley.pdf`](docs/Polylog_Cayley.pdf). 
Its authors are Domagoj Bradač, Matija Bucić, Micha Christoph, Zach Hunter,
Oliver Janzer and Alp Müyesser; the draft was prepared by GPT 6 Pro, with significant input from the authors, including
several unpublished human manuscripts that were identified in the bibliography. The authors are working on a more readable exposition of the proof.


In Lean this is `Lovasz.hamiltonian_of_polylog_degree`. It is stated in
[`Challenge.lean`](Challenge.lean), which imports only Mathlib, and proved in
[`Solution.lean`](Solution.lean). The proof depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## The result and its context

A Cayley graph $\mathrm{Cay}(G,S)$ of a finite group $G$ with respect to $S = S^{-1}$,
$1 \notin S$ has the edges $x \sim xs$ ($s \in S$); it is $|S|$-regular and connected exactly
when $S$ generates $G$. Lovász asked (1969) whether every connected vertex-transitive graph has
a Hamilton path [1]; the Cayley-graph form of the question, going back to Rapaport-Strasser [2],
asks whether every connected Cayley graph on at least three vertices is Hamiltonian. For
arbitrary connected Cayley graphs this was previously known for linear degree (Christofides,
Hladký and Máthé [3]) and for degree at least $n^{1-c}$ (Bedert, Draganić, Müyesser and
Pavez-Signé [4]); Theorem 1.1 lowers the degree threshold to $C(\log n)^{13}/\log\log n$.
Related recent work: Hamiltonicity of regular sublinear expanders [5], of random Cayley graphs
of degree $C \log n$ [6], long cycles in vertex-transitive graphs [7], and almost Hamilton
cycles (length $(1-o(1))n$) in connected vertex-transitive graphs of polylogarithmic degree
[8]. The full references are listed [below](#references).

The source manuscript is an unpublished research draft dated 25 September 2026. It calls its
proof "a consolidated proposed proof, not an independently verified theorem". This
formalization checks that proof in full; no gap was found.

## What is formalized

The statement and every modelling decision are explained in
[`FORMALIZATION.md`](FORMALIZATION.md). In brief:

* `Lovasz.IsConnectionSet S` is the paper's convention $S = S^{-1}$, $1 \notin S$;
  `Lovasz.cayleyGraph S` is Mathlib's `SimpleGraph.mulCayley`;
* the degree is `S.card`, the graph's degree at every vertex; connectivity is
  `SimpleGraph.Connected`, equivalent to `Subgroup.closure S = ⊤`;
* `log` is `Real.log`; the conclusion is Mathlib's `SimpleGraph.IsHamiltonian`.

[`Lovasz/Sanity.lean`](Lovasz/Sanity.lean) proves that these definitions mean what the paper
says: the graph degree is `|S|`, connectivity is equivalent to generation, the threshold is a
genuine positive real for $n \ge 3$, the hypotheses are satisfiable for every $C$ and $n_0$
(also by non-complete graphs), and `K₂` shows that some $n_0$ is needed.

The whole proof of the paper is formalized, as a DAG of about 55 lemmas recorded in
[`docs/BLUEPRINT.md`](docs/BLUEPRINT.md) with its Lean names and files. The development is in
`Lovasz/` (about 36,500 lines in 49 modules):

| Paper | Lean |
|---|---|
| Section 2: spectral and matching facts (Lemmas 2.1–2.5, (2.2)) | `Lovasz/Perturbation.lean`, `ColumnSampling.lean`, `BipartiteSampling.lean`, `RobustHall.lean`, `GapCut.lean` |
| Section 3: local absorption (Theorem 3.2, Lemmas 3.3–3.8) | `Lovasz/LocalAbsorption.lean`, `Lovasz/Absorption/`, `DistanceDeletion.lean`, `SpectralConnection.lean`, `Comparator.lean`, `Router.lean`, `ShortCycles.lean`, `LongPath.lean`, `CycleMerging.lean` |
| Section 4: signed rounding (Lemmas 4.1–4.4) | `Lovasz/SignedIntegrality.lean`, `SwapRounding.lean`, `TraceConcentration.lean`, `SignedCirculation.lean` |
| Section 5: weighted partition (Lemmas 5.1–5.2, Proposition 5.3) | `Lovasz/Template.lean`, `IncidenceCuts.lean`, `WeightedPartition.lean` |
| Section 6: connecting system (Lemmas 6.2–6.4, Proposition 6.1) | `Lovasz/CosetCuts.lean`, `MutualNominations.lean`, `Connector.lean`, `Lovasz/Connecting/` |
| Section 7: parameter check | `Lovasz/GlobalDecomposition.lean`, `Lovasz/Main.lean` |
| Classical inputs used without proof by the paper | `Lovasz/Cheeger.lean`, `Haxell.lean`, `BMatchingPolytope.lean`, `Watkins.lean`, `TreePacking.lean`, `Circulation.lean`, `Chernoff.lean` |

The proof takes a different route from the paper's text in a few places, without weakening
Theorem 1.1 or any hypothesis it relies on. For example, Lemma 2.2 is derived from the paper's
own Lemma 4.3 instead of matrix Bernstein, so the term `c√t` of Lemma 2.2 (`c` the largest column
norm) gains a universal factor and becomes `6c√t`; the later steps absorb the factor. These points are
listed at the end of `docs/BLUEPRINT.md`.

## Provenance and roles

* **Mathematics.** The source manuscript is by the six researchers named above; the PDF itself
  carries no author line. As stated above, the draft was prepared by GPT 6 Pro (OpenAI) with
  significant input from the authors, including several unpublished human manuscripts
  identified in its bibliography [10, 11, 12]; the draft itself is [9].
* **Formalization.** All the Lean code was written by Claude Opus 5.5 (Anthropic) agents
  running in Grok Build: a coordinating agent wrote the statement, the sanity lemmas and the
  lemma DAG, and 38 parallel subagents proved the nodes. The file headers name the agent and
  the human who directed it. The toolchain smoke test `Lovasz/Basic.lean` (no proof content)
  was written by the maintainer during project setup.
* **Direction and maintenance.** Shengtong Zhang directed the formalization and takes
  responsibility for it; he is listed as its author in `formalization.yaml` for that role and is
  the responsible maintainer of this repository. He set up the project and the task
  specification [`AGENTS.md`](AGENTS.md) and instructed the agents, but wrote no Lean code, and
  he is not an author of the source manuscript.
* **Review.** The proof is checked by Lean's kernel, and Comparator's independent kernels
  replay it. The statement was audited against the paper by the formalizing agent and by
  independent agent runs of the Palomar review policy. No human has reviewed the Lean statement
  or proof, and the manuscript has not been refereed.

`formalization.yaml` records the structured provenance, automation and review metadata.

## Verifying

Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`.

```bash
lake exe cache get
lake build                     # Lovasz, Challenge, Solution
./scripts/verify-comparator.sh # Comparator: Solution against Challenge (needs bubblewrap)
```

[`VERIFICATION.md`](VERIFICATION.md) records the commands run and their results. The CI workflow
`.github/workflows/palomar.yml` runs the same checks.

## Palomar

The repository is laid out for the [Palomar registry](https://palomar-registry.org) of
Lean-verified results: `Challenge.lean`, `Solution.lean`, `comparator.json` and
`formalization.yaml` at the root. Submissions go through the Palomar submission form at
<https://submit.palomar-registry.org/>.

## Layout

| Path | Contents |
|---|---|
| `Challenge.lean` | Mathlib-only statement: the two definitions and the theorem (`sorry`). |
| `Solution.lean` | Restates the theorem and proves it from `Lovasz.main_proof`. |
| `comparator.json` | Comparator configuration. |
| `formalization.yaml` | Palomar / formalization.yaml v0.4 metadata. |
| `Lovasz/` | The proof development; `Lovasz/Statement.lean` holds the statement definitions (copied verbatim from `Challenge.lean`), `Lovasz/Main.lean` the main proof. |
| `FORMALIZATION.md` | Paper-to-Lean correspondence and modelling decisions. |
| `VERIFICATION.md` | Verification record. |
| `docs/BLUEPRINT.md` | The lemma DAG with per-node status, and a review of the paper's argument. |
| `docs/Polylog_Cayley.pdf` | The source manuscript. It is the authors' work, included for reference; the repository's Apache-2.0 licence does not cover it. |
| `AGENTS.md` | The task specification given to the formalizing agent. |

## References

The result and its context:

1. L. Lovász, Problem 11, in *Combinatorial Structures and Their Applications* (Proc. Calgary
   Internat. Conf., Calgary, Alberta, 1969), Gordon and Breach, New York, 1970, p. 497.
2. E. Rapaport-Strasser, Cayley color groups and Hamilton lines, *Scripta Math.* **24** (1959),
   51–58.
3. D. Christofides, J. Hladký and A. Máthé, Hamilton cycles in dense vertex-transitive graphs,
   *J. Combin. Theory Ser. B* **109** (2014), 34–72.
   [doi:10.1016/j.jctb.2014.05.001](https://doi.org/10.1016/j.jctb.2014.05.001)
4. B. Bedert, N. Draganić, A. Müyesser and M. Pavez-Signé, The Lovász conjecture holds for
   moderately dense Cayley graphs, preprint (2026).
   [arXiv:2603.08675](https://arxiv.org/abs/2603.08675)
5. D. Bradač and O. Janzer, Hamiltonicity of regular sublinear expanders, preprint (2026).
   [arXiv:2605.15043](https://arxiv.org/abs/2605.15043)
6. N. Draganić, R. Montgomery, D. Munhá Correia, A. Pokrovskiy and B. Sudakov, Hamiltonicity of
   expanders: optimal bounds and applications, preprint (2024).
   [arXiv:2402.06603](https://arxiv.org/abs/2402.06603)
7. M. Bucić, M. Christoph, A. Pokrovskiy and R. Steiner, Towards the Lovász conjecture via
   sublinear expanders, preprint (2026). [arXiv:2606.09742](https://arxiv.org/abs/2606.09742)
8. M. Christoph, Z. Hunter and B. Sudakov, Thinning and sprinkling: from robust sampling to
   almost Hamiltonicity, preprint (2026). [arXiv:2609.30165](https://arxiv.org/abs/2609.30165)

The source manuscript and the unpublished manuscripts it builds on (from its bibliography; not
publicly available):

9. D. Bradač, M. Bucić, M. Christoph, Z. Hunter, O. Janzer and A. Müyesser, Hamilton cycles in
   Cayley graphs of polylogarithmic degree, research draft, 25 September 2026
   ([`docs/Polylog_Cayley.pdf`](docs/Polylog_Cayley.pdf)).
10. A. Müyesser, Hamiltonicity of mildly pseudorandom regular graphs, unpublished manuscript,
    2026 (reference [6] of the draft).
11. *Hamilton cycles in bipartite Cayley graphs: a proof draft via balanced allocation*,
    unpublished research draft, 2026 (reference [9] of the draft).
12. *A candidate logarithmic exponent of thirteen: weighted allocation and Hamilton routers*,
    unpublished research draft, 2026 (reference [10] of the draft).

Classical results used by the proof (all proved in `Lovasz/` except Hall's theorem, from
Mathlib, and matrix Bernstein, which the formalization avoids):

13. F. R. K. Chung, *Spectral Graph Theory*, CBMS Regional Conference Series in Mathematics 92,
    American Mathematical Society, Providence, RI, 1997.
    [doi:10.1090/cbms/092](https://doi.org/10.1090/cbms/092) — normalized Cheeger inequality.
14. P. E. Haxell, A condition for matchability in hypergraphs, *Graphs Combin.* **11** (1995),
    245–248. [doi:10.1007/BF01793010](https://doi.org/10.1007/BF01793010)
15. M. E. Watkins, Connectivity of transitive graphs, *J. Combin. Theory* **8** (1970), 23–29.
    [doi:10.1016/S0021-9800(70)80005-9](https://doi.org/10.1016/S0021-9800(70)80005-9)
16. C. St. J. A. Nash-Williams, Edge-disjoint spanning trees of finite graphs,
    *J. London Math. Soc.* **36** (1961), 445–450.
    [doi:10.1112/jlms/s1-36.1.445](https://doi.org/10.1112/jlms/s1-36.1.445)
17. W. T. Tutte, On the problem of decomposing a graph into *n* connected factors,
    *J. London Math. Soc.* **36** (1961), 221–230.
    [doi:10.1112/jlms/s1-36.1.221](https://doi.org/10.1112/jlms/s1-36.1.221)
18. T. Kaiser, A short proof of the tree-packing theorem, *Discrete Math.* **312** (2012),
    1689–1691. [doi:10.1016/j.disc.2012.01.020](https://doi.org/10.1016/j.disc.2012.01.020)
    — the proof of [16, 17] formalized in `Lovasz/TreePacking.lean`.
19. A. N. Letchford, G. Reinelt and D. O. Theis, A faster exact separation algorithm for blossom
    inequalities, in *Integer Programming and Combinatorial Optimization (IPCO 2004)*, Lecture
    Notes in Comput. Sci. 3064, Springer, 2004, 196–205.
    [doi:10.1007/978-3-540-25960-2_15](https://doi.org/10.1007/978-3-540-25960-2_15) — the
    capacitated b-matching polytope.
20. A. J. Hoffman, Some recent applications of the theory of linear inequalities to extremal
    combinatorial analysis, in *Combinatorial Analysis*, Proc. Sympos. Appl. Math. 10, American
    Mathematical Society, 1960, 113–127.
    [doi:10.1090/psapm/010/0114759](https://doi.org/10.1090/psapm/010/0114759) — the
    circulation criterion.
21. K. Joag-Dev and F. Proschan, Negative association of random variables with applications,
    *Ann. Statist.* **11** (1983), 286–295.
    [doi:10.1214/aos/1176346079](https://doi.org/10.1214/aos/1176346079)
22. J. A. Tropp, User-friendly tail bounds for sums of random matrices, *Found. Comput. Math.*
    **12** (2012), 389–434.
    [doi:10.1007/s10208-011-9099-z](https://doi.org/10.1007/s10208-011-9099-z) — matrix
    Bernstein, cited by the draft and avoided by the formalization.

## Licence

The Lean code, scripts and documentation are released under the Apache License 2.0
([`LICENSE`](LICENSE)). This does not extend to `docs/Polylog_Cayley.pdf`.
