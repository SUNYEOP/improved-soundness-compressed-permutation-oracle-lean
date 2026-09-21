# Third-party notices

Original Quantum Oracle project code is licensed under the [MIT license](LICENSE).
That license does not replace the licenses of the third-party material identified
below. In particular, `QuantumOracle/Proof/HookLengthFormula.lean` is an adapted
Apache-2.0 source file, even though it is inside the project source directory.
Preserved upstream license, notice, copyright, and author headers continue to
apply to their respective files.

## Etingof representation theory formalization

- Repository: [mathlib-initiative/Etingof-RepresentationTheory-draft1](https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1).
- Commit: `9587adb8833ebd14d6f3c586a39fac0241c9df63`.
- Upstream subtree: `clean-code/release`.
- Included at: `vendor/etingof-representation-theory/`.
- License: [Apache License 2.0](vendor/etingof-representation-theory/LICENSE).
- Upstream [NOTICE](vendor/etingof-representation-theory/NOTICE):

```text
EtingofRepresentationTheory
Copyright 2026 mathlib-initiative

Licensed under the Apache License, Version 2.0.
```

The 835 upstream files are preserved unchanged. The accompanying
[source manifest](vendor/etingof-representation-theory/_provenance/source-manifest.json)
records their original paths, source URLs, Git blob identifiers, SHA-256 hashes,
and sizes. File-specific attribution remains in the original sources.

## ProofAtlas hook-length formula formalization

- Theorem: [Hook-length formula](https://www.proofatlas.ai/formalizations/hook-length-formula/).
- Published source package: [ProofAtlas source](https://www.proofatlas.ai/sources/hook-length-formula/).
- Commit: `7e628b6361f20e33d6b8214adc608685b9d4da2d`.
- Original path: `AtlasKnownTheorems/HookLengthFormula/Basic.lean`.
- Original source retained at: `vendor/proofatlas/hook-length-formula/Basic.lean`.
- Adapted source used in the build: `QuantumOracle/Proof/HookLengthFormula.lean`.
- License: [Apache License 2.0](vendor/proofatlas/hook-length-formula/LICENSE).
- Upstream [NOTICE](vendor/proofatlas/hook-length-formula/NOTICE):

```text
Hook-length formula formalization package
Copyright 2026 Advameg, Inc.

This product includes software developed for ProofAtlas.
```

The original source is preserved unchanged. The adapted source retains its
upstream SPDX copyright and Apache-2.0 license identifiers and explicitly records
the Lean version adaptations. The project's separately proved
`QuantumOracle/Proof/HookLengthCompat.lean` supplies a compatibility lemma used by this
adaptation. The project MIT license does not relicense the adapted ProofAtlas
source or its preserved upstream copy.

## Dependencies downloaded by Lake

The source distribution records these packages in
[lake-manifest.json](lake-manifest.json); it does not include their downloaded
`.lake/packages` directories. The following license designations were checked
against the local `LICENSE` files at the pinned revisions. Each upstream
package's own license files and file-specific notices govern that package.
Exact revisions are listed in [Dependencies](docs/DEPENDENCIES.md).

| Package | Upstream | License |
| --- | --- | --- |
| mathlib | [mathlib4](https://github.com/leanprover-community/mathlib4) | Apache-2.0 |
| plausible | [plausible](https://github.com/leanprover-community/plausible) | Apache-2.0 |
| LeanSearchClient | [LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient) | Apache-2.0 |
| importGraph | [import-graph](https://github.com/leanprover-community/import-graph) | Apache-2.0 |
| proofwidgets | [ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4) | Apache-2.0 |
| aesop | [aesop](https://github.com/leanprover-community/aesop) | Apache-2.0 |
| Qq | [quote4](https://github.com/leanprover-community/quote4) | Apache-2.0 |
| batteries | [batteries](https://github.com/leanprover-community/batteries) | Apache-2.0 |
| Cli | [lean4-cli](https://github.com/leanprover/lean4-cli) | MIT; Copyright (c) 2021 mhuisi |

The Lean toolchain is downloaded separately and is not included in the source
distribution. Its release includes its own licenses and third-party notices;
the inspected Lean 4.32.2 distribution's top-level `LICENSE` is Apache-2.0.
