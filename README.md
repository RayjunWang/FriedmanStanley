# Friedman–Stanley cofinality without Borel completeness

The exact main Theorem 1.2 from `FriedmanStanleyQuestion.tex` is fully proved
and kernel checked locally in [Solutions/Main.lean](Solutions/Main.lean).
Prove2Me accepted the main proof and all four supporting milestones. All five
targets have status **Proved**. The exact accepted standalone files are in
[`Prove2Me/`](Prove2Me/README.md), with submission identifiers and verified hashes
in [`docs/prove2me-acceptance.json`](docs/prove2me-acceptance.json).

The theorem exhibits one invariant Borel class of countable structures whose
isomorphism relation receives every countable product-limit Friedman–Stanley
tower stage and every countably bounded rooted-tree isomorphism relation,
while graph isomorphism does not Borel reduce to it.

The proof uses the exact four definition bundles uploaded with the mission.
It imports no target placeholders. Its transitive axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Reproduce the proof

- Lean: `leanprover/lean4:v4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

This Mathlib revision is supported by Prove2Me. With `elan` and Git installed:

```sh
lake exe cache get
lake build
lake build Solutions.Main
lake env lean AuditMain.lean
lake env lean AuditAll.lean
```

The last command checks the canonical main declaration and prints its complete
axiom dependencies. `AuditParameterSequences.lean` contains additional audits
of the supporting constructions. The package files pin both versions; the
local `.lake` cache and credentials are excluded from Git.

## Files

- `Definitions/`: exact structure, hierarchy, tree, and coset definitions.
- `FSCofinalityProof/`: verified mathematical constructions and reductions.
- `Solutions/Main.lean`: exact main theorem.
- `Solutions/CosetCofinality.lean`: exact coset-cofinality theorem.
- `Solutions/InvariantRealParameters.lean`, `BoundedTreeIsomorphismBorel.lean`,
  and `OriginalTreeComparison.lean`: exact supporting mission statements.
- `docs/progress.md`: proof route and verification status.
- `docs/proof-outline.md`: explanation of the mathematical construction.
- `docs/readbacks/`: independent statement read-backs and source comparison.
- `Prove2Me/`: exact accepted standalone proof files.

The source manuscript is dated 2 November 2026, with SHA-256
`10d9e37ebf19c1d873fbc7ccf45ac57e42b7c023f275e9ec8ff3209f9a577624`.

## Prove2Me

Public `OpenProblem` proposal:
[Friedman Stanley cofinality without Borel completeness](https://prove2.me/my-missions/5bb9ccfa-5ab5-4a6c-9918-5352b107d179).

The proposal has public visibility and type `OpenProblem`. Its moderation
status remains **In review**, separately from the five accepted proof
verifications. Main proof submission:
`2c3159c6-54cc-4bf5-bc17-bf35571ed5de`.

The proof submission workflow followed the
[Prove2Me skill](https://github.com/prove2me/prove2me_workspace/blob/main/SKILL.md).
