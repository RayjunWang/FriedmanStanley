# Verification record

The main theorem is `FSCofinality.theorem1_2` in `Solutions/Main.lean`.
Its statement matches the mission's published main target, including all three
requirements: tower cofinality, failure of graph-isomorphism reducibility, and
cofinality for the original bounded rooted-tree relations.

## Local environment

- Lean: `leanprover/lean4:v4.30.0`.
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- The Mathlib Git checkout was checked at this exact commit with a clean
  `git status --porcelain` result.
- `lake build` completed successfully with 3188 jobs.
- `lake build Solutions.Main` completed successfully.
- `lake env lean AuditAll.lean` checked all five mission statements.

Each of the five declarations reports exactly these axiom dependencies:

```text
[propext, Classical.choice, Quot.sound]
```

The declarations are:

```text
FSCofinality.bounded_tree_isomorphism_borel
FSCofinality.invariant_real_parameters
FSCofinality.coset_cofinality
FSCofinality.original_tree_comparison
FSCofinality.theorem1_2
```

No solution imports its own unproved target. A source scan of `Definitions/`,
`FSCofinalityProof/`, and `Solutions/` found no `sorry`, `admit`, `axiom`,
`unsafe`, or `native_decide` declarations or uses.

## Reproduction

```sh
lake exe cache get
lake build
lake build Solutions.Main
lake env lean AuditAll.lean
```

The four fixed `Definitions/` bundles are the actual mission definitions.
No target stubs belong to the proof project.

## Source and platform

Source manuscript: `FriedmanStanleyQuestion.tex`, dated 2 November 2026.
SHA-256:
`10d9e37ebf19c1d873fbc7ccf45ac57e42b7c023f275e9ec8ff3209f9a577624`.

Public OpenProblem proposal:
[Friedman Stanley cofinality without Borel completeness](https://prove2.me/my-missions/5bb9ccfa-5ab5-4a6c-9918-5352b107d179).

Main published target: `b774fd72-07d9-402c-a4df-1a2a2c2f9242`.
The proposal was read back as `In review` for mission moderation. Prove2Me
accepted the main proof and all four supporting proofs; all five published
targets were read back with status `Proved`. Every accepted server source
matched the exact locally compiled upload's SHA-256 and byte count.

| Target | Accepted submission |
|---|---|
| Main theorem | `2c3159c6-54cc-4bf5-bc17-bf35571ed5de` |
| Coset cofinality | `e3d98e2e-abfd-47c2-8063-f4cc71ed5441` |
| Bounded-tree Borelness | `7aaab607-cd8a-4912-a577-71af345bd6be` |
| Invariant real parameters | `2a76de34-92be-400e-af2b-6e1d79717d8b` |
| Original-tree comparison | `9f2620e0-6b8b-4e09-801e-b2c73a37a137` |

The final standalone main and coset proofs compiled locally in 34.50 and
31.36 seconds respectively. Lean verified that their `solution` types are
definitionally equal to the exact published target types and that their
axiom dependencies contain only the standard three axioms listed above.

Machine-readable acceptance evidence is in `prove2me-acceptance.json`.
Exact accepted standalone proof files are in `../Prove2Me/`.

## Source archive

Run `python tools/package_project.py` to create the source-only archive
`../fs-cofinality-lean-github.zip`. Its explicit file list excludes dependency
caches, temporary upload files, and account credentials. The archive includes
`docs/source-manifest.json` with a SHA-256 for every packaged source file.
