# Dependencies and source provenance

The build has two direct Lake dependencies: pinned mathlib and a local path
package containing the Etingof representation theory formalization. ProofAtlas
is used through an adapted source file in `QuantumOracle/`, not through a third
Lake dependency. See [Third-party notices](../THIRD_PARTY_NOTICES.md) for the
licenses and preserved attribution.

## Toolchain and package pins

[lean-toolchain](../lean-toolchain) selects `leanprover/lean4:v4.32.2`.
[lakefile.toml](../lakefile.toml) pins mathlib to a full commit and selects
`vendor/etingof-representation-theory` as the path dependency.
[lake-manifest.json](../lake-manifest.json) records the resolved package graph.
Keep this lockfile in a source release; branch names in inherited `inputRev`
fields are not substitutes for the resolved commit hashes below.

| Package | Dependency form | Resolved revision |
| --- | --- | --- |
| mathlib | Direct Git dependency | `905b95818eb32af7874a58b427f50c1711a5e96c` |
| RepresentationTheoryFormalization | Direct local path dependency | Upstream `9587adb8833ebd14d6f3c586a39fac0241c9df63`, subtree `clean-code/release` |
| plausible | Inherited Git dependency | `e12c1910fe855cbfc38803cd4e55543906d5fa62` |
| LeanSearchClient | Inherited Git dependency | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
| importGraph | Inherited Git dependency | `7e9612bf0b9ee66db3cb5b9988a35afc706f5a12` |
| proofwidgets | Inherited Git dependency | `6e311e2a844da9b2cc3971187df2fe0066947b93` |
| aesop | Inherited Git dependency | `a7dbf0c63b694e47f425f3dcddbc0e178bb432d3` |
| Qq | Inherited Git dependency | `38d591e778f100aec9762bb582f9c7f55f50e9dc` |
| batteries | Inherited Git dependency | `023ce7d62a0531e22a5331e20b587817a80d49ff` |
| Cli | Inherited Git dependency | `88679d088c9720c27ebdf2ba4dafe17341747f94` |

The Etingof package's own toolchain is also Lean 4.32.2. Its mathlib requirement
names `v4.32.2`; its preserved lockfile resolves to the same mathlib commit as
the parent project. Its package name is `RepresentationTheoryFormalization`,
while its Lean module prefix is `RepresentationTheory`.

## Active external sources

### Etingof representation theory

The source comes from
[Etingof-RepresentationTheory-draft1](https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1),
commit `9587adb8833ebd14d6f3c586a39fac0241c9df63`, subtree
`clean-code/release`. All 835 original files are retained, including the upstream
package configuration, license, notice, and source headers. The added
[source manifest](../vendor/etingof-representation-theory/_provenance/source-manifest.json)
records per-file provenance and hashes. The path package is compiled together
with the project against the parent's pinned mathlib.

This dependency supplies the actual representation theory used by the local
Specht, restriction, and spectral arguments. Keeping the complete upstream
source subtree does not mean that all its modules occur in the proof's import
closure.

### ProofAtlas hook-length formula

The original package is pinned at commit
`7e628b6361f20e33d6b8214adc608685b9d4da2d`. Its original
`AtlasKnownTheorems/HookLengthFormula/Basic.lean` is preserved as
`vendor/proofatlas/hook-length-formula/Basic.lean`, with SHA-256
`bfcd609759bb37494f274922f11b212beaae2dce56da4e197912ced7915089a6`.
The original checker evidence records Lean 4.29.1.

The active module is `QuantumOracle/Proof/HookLengthFormula.lean`, adapted for
Lean/mathlib 4.32.2. It imports the project's proved Lagrange coefficient
compatibility lemma from `QuantumOracle/Proof/HookLengthCompat.lean`.
The original `Basic.lean` is retained for provenance and is not itself imported
by the build.

The upstream proof supplies the general hook-length identity and tableau corner
recurrence. Connections to actual Specht dimensions, the oracle Gram operator,
and the final error estimate are separate local proofs. Upstream checker
evidence is provenance, not a replacement for compiling and auditing the local
adaptation.

## Import scope and source verification

`scripts/audit-source-closure.py` follows the aggregate's project imports,
checks that local imports resolve, rejects proof placeholders and bypass tokens,
and verifies the preserved Etingof sources against their recorded SHA-256 hashes.
Its report lists the imported project and representation-theory modules.
`scripts/export-source.py` also verifies the Etingof manifest and the preserved
ProofAtlas `Basic.lean` hash before creating a source release. These are
source-integrity checks; the separate Lean axiom audit checks the dependencies
of the audited declarations.

The compatibility import `QuantumOracle/ImprovedSoundness.lean` is outside the
aggregate closure. The independent statement target imports the model and
canonical statement, without the representation-theory or adapted hook-length
proof modules. The layer audit enforces these import boundaries.

The [proof checker](REPRODUCIBILITY.md) runs both source and axiom audits.
[Source releases](PUBLISHING.md) retain the pinned toolchain and Lake lockfile,
preserved upstream sources and licenses, and the scripts needed to repeat the
checks. Toolchains and build caches are downloaded separately.

## Toolchain setup

The Windows setup verifies the SHA-256 of the official Lean archive against
[toolchain-windows.json](../toolchain-windows.json), resolves the pinned Lake
dependencies, fetches the selected Mathlib cache, and builds the project.
The supplied download and wrapper scripts require PowerShell, Git, `curl.exe`,
`tar.exe`, and network access.

The [reproduction instructions](REPRODUCIBILITY.md) also provide commands using
elan on Linux or macOS. The included GitHub Actions workflow runs the proof
checker on Ubuntu. All setups use the same Lean version and Lake dependency
manifest.
