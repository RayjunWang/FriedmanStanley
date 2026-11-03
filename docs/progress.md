# Verification status

`FSCofinality.theorem1_2` is fully proved locally in `Solutions/Main.lean`.
Its declaration type matches the exact Prove2Me draft statement after whitespace
normalization. `lake build Solutions.Main` passed, and `lake env lean AuditMain.lean`
reported exactly `[propext, Classical.choice, Quot.sound]`.

Prove2Me accepted the main proof and all four supporting milestones. Each
target was read back with status `Proved`, and every accepted server source
matched the exact locally checked upload bytes. Submission identifiers and
hashes are recorded in `prove2me-acceptance.json`; exact standalone source
files are in `../Prove2Me/`.

The public OpenProblem proposal remains `In review` for mission moderation.
This is separate from the completed proof verifications.

## Exact statements

The following solution modules contain complete proofs and import no placeholder
for their own target:

- `Solutions/Main.lean`: the exact main Theorem 1.2.
- `Solutions/CosetCofinality.lean`: the actual closed-group, continuous injective
  homomorphism, Borel image, and tower-to-image-coset reduction.
- `Solutions/InvariantRealParameters.lean`: the invariant-real fiber principle.
- `Solutions/BoundedTreeIsomorphismBorel.lean`: Borelness at every countable bound.
- `Solutions/OriginalTreeComparison.lean`: comparison with some countable tower stage.

The four `Definitions/` bundles remain the exact uploaded definitions.

## Proof route

1. `Hierarchy*`, `Multiset*`, `TreeChildClassification`, and `TreeClassifiers`
   establish native tower regularity, monotonicity, countable sum/product
   absorption, the occurrence-tag multiset reduction, and actual bounded-tree
   cofinality. The tree classifier uses total Borel codes and actual node
   isomorphisms, including empty and finitely branching trees.
2. `RawObjects*` construct the actual Type-0 semantic universe as a quotient of
   tree codes evaluated in Mathlib's `ZFSet`, together with typed layers,
   canonical injective lifts, countable source pools, dedicated columns,
   finite birth supports, profiles, and cross-pool semantic naturality.
   No composition law for the canonical lifts is assumed.
3. `GenericTables*`, `Token*`, and `CosetConstruction*` supply genuine generic
   Boolean tables, bottom maps, all one-point extension cases, exact token
   recovery, common-model isomorphisms, Borel countable presentations, and the
   final continuous injective automorphism-restriction image. The raw semantic
   universe is not assigned an artificial measurable structure.
4. `ParameterClass*`, `TwoSort*`, and `ClosedGraphCapture` construct one actual
   invariant Borel class, with named Cantor parameters, canonical orbit
   structures, Borel copy tests, marker enumerations, and Borel isomorphism in
   each fixed parameter fiber. Every continuous closed-group homomorphic-image
   coset relation reduces to this same class.
5. `PartialIsomorphism*`, `Boundedness`, `Padding*`, and `Noncomplete*` prove
   analytic boundedness, the invariant-real principle, graph-isomorphism
   non-Borelness, and failure of a graph-isomorphism reduction to the fixed class.
   `Solutions/Main.lean` composes these proved reductions and obstructions.

## Reproduce the final checks

```sh
lake exe cache get
lake build
lake build Solutions.Main
lake env lean AuditMain.lean
lake env lean AuditAll.lean
```

Pinned environment: Lean `4.30.0`, Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

Additional component audits are in `AuditParameterSequences.lean`. The main
audit is transitive, so its three reported standard axioms cover the entire
proof dependency closure.

Source manuscript:
`C:/Users/1/Documents/ChatGPT/Reduction/fs-cofinality-paper-20261102/FriedmanStanleyQuestion.tex`.
SHA-256: `10d9e37ebf19c1d873fbc7ccf45ac57e42b7c023f275e9ec8ff3209f9a577624`.

Mission proposal: `5bb9ccfa-5ab5-4a6c-9918-5352b107d179`.
