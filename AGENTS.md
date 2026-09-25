# Agent instructions

## Task

Formalize in Lean 4 / Mathlib Theorem 1.1 of `docs/Polylog_Cayley.pdf` ("Hamilton cycles in
Cayley graphs of polylogarithmic degree"): first a faithful **statement**, then its **proof**,
decomposed into a DAG of intermediate lemmas (see *Recommended workflow*).

The theorem, verbatim:

> **Theorem 1.1 (Proposed theorem).** There are absolute constants $C, n_0 > 0$ such that every
> connected Cayley graph on $n \ge n_0$ vertices and of degree at least
> $C (\log n)^{13} / \log\log n$ contains a Hamilton cycle.

The conventions the paper fixes (Section 2): natural logarithms; $X = \mathrm{Cay}(G, S)$,
$n = |G|$, $d = |S|$, $L = \log n$, where $S = S^{-1} \subseteq G \setminus \{1\}$ and
$\langle S \rangle = G$; edges have the form $x \sim xs$; graphs are simple. Read the whole
paper for anything else the statement depends on.

The statement must mean exactly what the paper means: not weaker, not stronger, and not
vacuous. Where the paper leaves something implicit, choose the reading the paper intends and
record the choice and the reason in `FORMALIZATION.md`. The paper is an unverified draft: if a
step of its proof is wrong, record the gap in `docs/BLUEPRINT.md` and report it rather than
weakening the statement to route around it.

## Recommended workflow

1. **Statement first.** Formalize the statement in `Challenge.lean` with its sanity lemmas and
   `FORMALIZATION.md` (deliverables 1–3 below), check it, and commit. From then on the
   statement is frozen; change it only to fix a genuine error, and document the change.
2. **Decompose into a DAG.** Before proving anything, break the theorem into a DAG of
   intermediate lemmas, each small enough to formalize on its own, and record it in
   `docs/BLUEPRINT.md`. For every node give: an id, the informal statement with its paper
   reference (section, lemma, equation), the Lean name and file, the ids of the nodes it depends
   on, and a status (`todo` / `stated` / `proved`). The classical results the paper uses
   without proof (normalized Cheeger inequality, matrix Bernstein, Hall's and Haxell's matching
   theorems, the capacitated matching-polytope description, Watkins's connectivity bound, the
   tree-packing theorem, max-flow/min-cut) are nodes too; search Mathlib for each before
   planning to prove it.
3. **State the whole DAG in Lean.** Write every node's Lean statement with a `sorry` proof, and
   derive the main theorem from its children, so the entire DAG type-checks end to end before
   any leaf is proved. This catches mis-stated interfaces early.
4. **Formalize along the DAG**, leaves first, keeping `lake build` green and the statuses in
   `docs/BLUEPRINT.md` current. If a node turns out false or much harder than planned, revise
   the DAG rather than forcing it.

## Parallelism

Time is pivotal: deploy as many subagents as possible in parallel (10 at once is fine). The
agent that owns the DAG coordinates; each subagent gets one node or a small cluster of nodes
whose dependencies are already stated in Lean. Give each subagent the paper reference, the
exact Lean statement it must prove, the file it owns, and these rules:

- Edit only the files you own, usually one file `Lovasz/<Node>.lean` per node. Only the
  coordinator edits shared files: `Challenge.lean`, `Lovasz.lean`, `docs/BLUEPRINT.md`,
  `FORMALIZATION.md`, `README.md`.
- Never change the statement of a node you were given. If it is false, unprovable as stated, or
  needs an extra hypothesis, stop and report back so the coordinator revises the DAG.
- Check your own file with `lake env lean Lovasz/<Node>.lean` (the coordinator builds its
  imports first with `lake build`). Do not run `lake build` concurrently with other agents.
- Commit only your own files (`git add <your paths>`), or leave commits to the coordinator.

Each Lean process that imports Mathlib holds several GB of memory. If the machine starts
swapping, reduce the number of agents compiling at the same time.

## Deliverables

1. **`Challenge.lean`** — imports only `Mathlib`. Contains every definition the statement uses
   and the main theorem, in namespace `Lovasz`, with a docstring that restates the theorem in
   words, proved by `sorry`. It stays the audited statement surface once the proof exists.
2. **Sanity lemmas in `Lovasz/`** (e.g. `Lovasz/Sanity.lean`, imported from `Lovasz.lean`;
   these files may `import Challenge`), fully proved. They should show that the definitions
   and hypotheses mean what the paper says, for example that the formal notion of degree is
   the paper's $d$, that the connectivity hypothesis is the intended one, and that the
   hypotheses are satisfiable, so the theorem is not vacuous.
3. **`FORMALIZATION.md`** — a paper-to-Lean correspondence: each ingredient of the statement,
   its Lean rendering, every modelling decision with its justification, hypotheses deliberately
   absent, and any known discrepancy.
4. **`docs/BLUEPRINT.md`** — the lemma DAG with per-node status, kept current.
5. **The proof**, in `Lovasz/`, ending in `Lovasz/Main.lean` with a theorem whose type is
   literally the Challenge statement, e.g. `theorem main_proof : type_of% @Lovasz.<main> := ...`.
6. Keep the **Status** section of `README.md` current.

Things that commonly make a formal statement wrong without failing to compile: truncated
subtraction and division in `ℕ`, junk values of `Real.log` and of division by zero, Mathlib
conventions for degenerate cases (read the docstrings of the definitions you use), quantifier
order, universe levels, and `Fintype`/`Finite`/decidability instance choices in the statement.

## Acceptance checks

- `lake build` succeeds.
- Until the proof is complete, `sorry` appears only in `Challenge.lean`'s main theorem and in
  DAG nodes whose status in `docs/BLUEPRINT.md` is not `proved`. When it is complete,
  `rg -n 'sorry' --glob '*.lean'` shows only `Challenge.lean`.
- No `axiom` declarations, no `native_decide`, no `set_option` that weakens checking.
- `#print axioms` on every sanity lemma, every `proved` node, and (at the end) the main proof
  reports at most `propext`, `Classical.choice`, `Quot.sound`:

  ```bash
  printf 'import Lovasz\n#print axioms Lovasz.some_lemma\n' > /tmp/axioms.lean
  lake env lean /tmp/axioms.lean
  ```

## Rules

- Work only inside this repository. Do not read, list, or reference any other `lovasz-*`
  directory or any other formalization attempt of this paper. Mathlib sources under
  `.lake/packages/mathlib` and public documentation are fine.
- Do not change `lean-toolchain`, the Mathlib `rev`, or `lake-manifest.json`. Never run
  `lake update` or `lake clean`, and never delete `.lake`: Mathlib is prebuilt locally and
  rebuilding it takes hours.
- Commit your work with git in this repository at meaningful checkpoints.

## Useful commands and API

```bash
lake build                     # whole project (Mathlib is prebuilt)
lake env lean Challenge.lean   # check one file
```

Relevant Mathlib files (under `.lake/packages/mathlib/Mathlib/`):

- `Combinatorics/SimpleGraph/Cayley.lean` — `SimpleGraph.mulCayley`.
- `Combinatorics/SimpleGraph/Hamiltonian.lean` — `SimpleGraph.Walk.IsHamiltonianCycle`,
  `SimpleGraph.IsHamiltonian`.
- `Combinatorics/SimpleGraph/Connectivity/` — `SimpleGraph.Connected`.
- `Algebra/Group/Subgroup/` — `Subgroup.closure`.
- `Analysis/SpecialFunctions/Log/Basic.lean` — `Real.log`.
