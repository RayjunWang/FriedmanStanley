# Exact standalone submissions

The Lean files in this directory preserve the exact bytes submitted to
Prove2Me. Their target identifiers, submission identifiers, SHA-256 hashes,
and verification results are recorded in
[`docs/prove2me-acceptance.json`](../docs/prove2me-acceptance.json).

The normal modular proof is in `Solutions/Main.lean`; these standalone files
retain the required complete source modules for the platform's import layout.
Each uses the same four fixed `Definitions/` bundles as the modular project.
Compile a standalone file individually, for example:

```sh
lake env lean Prove2Me/Main.lean
```

Each file declares its own top-level `theorem solution`, so they are independent
submission files and should not be imported together.

The transformation used Lean's parser and the official Prove2Me sketch oracle.
Complete module bodies were retained. Namespace and section scopes were closed
between modules, and the target proof was exposed as the required top-level
`solution`. Exact upload bytes were compiled and compared with the published
target type before submission. The modular theorem's transitive axiom audit is
reproducible with `lake env lean AuditAll.lean`.
