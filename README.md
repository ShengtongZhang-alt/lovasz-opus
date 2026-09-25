# Hamilton cycles in Cayley graphs of polylogarithmic degree — Lean formalization

A Lean 4 / Mathlib formalization of Theorem 1.1 of the research draft
[`docs/Polylog_Cayley.pdf`](docs/Polylog_Cayley.pdf):

> There are absolute constants $C, n_0 > 0$ such that every connected Cayley graph on
> $n \ge n_0$ vertices and of degree at least $C(\log n)^{13}/\log\log n$ contains a Hamilton
> cycle.

This is a special case of the open conjecture, a variant of Lovász's question on
vertex-transitive graphs, that every connected Cayley graph on at least three vertices is
Hamiltonian. The draft itself says its proof has not been independently verified.

## Layout

| Path | Contents |
|---|---|
| `Challenge.lean` | Mathlib-only statement module: the definitions the statement needs and the main theorem (`sorry`). |
| `Lovasz/` | The development: toolchain smoke test, sanity lemmas about the definitions, and the proof along the lemma DAG, ending in `Lovasz/Main.lean`. |
| `FORMALIZATION.md` | Paper-to-Lean correspondence and modelling decisions. |
| `docs/BLUEPRINT.md` | The DAG of intermediate lemmas and their status. |
| `docs/Polylog_Cayley.pdf` | The source draft. |
| `AGENTS.md` | Instructions for agents working in this repository. |

## Building

Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` are pinned in `lean-toolchain` and
`lakefile.toml`.

```bash
lake exe cache get   # only needed on a fresh clone
lake build
```

## Status

Toolchain set up; statement not yet formalized.
