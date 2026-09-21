# Reproducing the Lean proof checks

Run all commands below from the repository root, which contains
`lakefile.toml`, `lean-toolchain`, and `AxiomAudit.lean`. The proof checker
requires Python 3.10 or later.

## Pinned inputs

- Lean: `leanprover/lean4:v4.32.2`, selected by `lean-toolchain`.
- Mathlib: commit `905b95818eb32af7874a58b427f50c1711a5e96c`; other Git
  dependencies are pinned in `lake-manifest.json`.
- Representation theory: the included path dependency
  `vendor/etingof-representation-theory`, from commit
  `9587adb8833ebd14d6f3c586a39fac0241c9df63` of
  [Etingof-RepresentationTheory-draft1](https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1),
  subtree `clean-code/release`. The source-integrity check verifies the SHA-256
  hashes of all 835 original files against the included provenance manifest.

Keep the committed Lake manifest; `lake update` changes dependency resolution
and is not part of reproduction. Downloaded dependencies and build caches are
not included in the source release.

The committed `.gitattributes` disables Git newline conversion for all files.
This preserves the exact bytes recorded in source and review SHA-256 manifests
when cloning on either Windows or Unix. Lean accepts both LF and CRLF sources.

## Linux or macOS with elan

Install [elan, the official Lean version manager](https://github.com/leanprover/elan#installation),
and make its `elan`, `lean`, and `lake` executables available on `PATH`. Then run:

```sh
elan toolchain install "$(tr -d '\r\n' < lean-toolchain)"
MATHLIB_NO_CACHE_ON_UPDATE=1 lake --no-cache exe cache get --cache-from=legacy Mathlib
python3 scripts/check-proof.py
```

The Mathlib cache fetch saves compilation time; it does not replace the checks.
The selected representation-theory modules import the full Mathlib umbrella,
so the command requests the `Mathlib` cache. The build uses `--no-cache` to
disable Lake's additional package artifact downloads; Mathlib's cache is fetched
explicitly in the preceding command. A first run needs network access and enough
disk space for Lean, Mathlib, and their build artifacts.

## Windows

The setup script installs the pinned Lean release, verifies its
archive checksum, fetches the Mathlib cache, and builds the project:

```powershell
.\setup.ps1
python scripts/check-proof.py --lake-wrapper ./lake-local.ps1
```

The checker invokes the wrapper through PowerShell without shell interpolation.
An existing elan installation can instead use `python scripts/check-proof.py`
with `lake` available on `PATH`.

## What a successful check establishes

`scripts/check-proof.py` runs these stages in order:

1. `scripts/audit-layers.py` checks every project import and the complete
   `Statement.Soundness` dependency closure. Model and Statement cannot import
   Proof, the public endpoint, compatibility imports, or representation-theory
   packages. Mathlib, Lean's standard libraries, and pinned Aesop are allowed.
2. `lake build QuantumOracle.Statement.Soundness` compiles the canonical
   proposition and model without the main soundness proof.
3. `lake build` compiles the `QuantumOracle` aggregate and its dependencies.
4. `lake lean AxiomAudit.lean` asks Lean for the dependencies of each
   explicitly audited declaration and checks the endpoint theorem signatures.
   The checker requires exactly one output for every unique `#print axioms`
   declaration. Duplicate, missing, or unlisted outputs fail. Only `propext`,
   `Classical.choice`, and `Quot.sound` are allowed; any `sorryAx` fails.
5. `lake lean review/Statement.lean` checks the specification-only entrypoint;
   `lake lean review/VerifyStatement.lean` checks its connection to the proof.
6. `scripts/audit-source-closure.py` follows the aggregate's first-party import
   closure, rejects placeholder and bypass tokens outside comments and strings,
   checks that local imports resolve, and verifies the original vendored Etingof
   files against their source manifest.

The audit uses `lake lean` so Lake supplies the complete import setup, including
dependencies kept in its local artifact store. In Lean 4.32, a successful build
need not place every dependency's `.olean` in its package build directory;
invoking `lake env lean` directly can therefore miss valid build artifacts.

The checker also rejects changes to the toolchain, Lake configuration, manifest,
or audit list during its run. The audited count is derived from the current
`AxiomAudit.lean`. The static source scan supplements Lean's checks. An axiom audit does
not by itself remove hypotheses from a theorem: the endpoint statements in
`AxiomAudit.lean` and the source declarations specify the mathematical result.

The exit code is zero only when all stages pass. `logs/proof-check.json` records
the current result, input hashes, declaration counts, allowed axioms, source
counts, and stage exit codes. Paths in that summary are relative to the source
root. Detailed build and audit output stays in `logs/proof-check-*.log`, and the
import-closure report is `logs/import-closure-audit.json`. The layer graph and
statement closure are in `logs/layer-audit.json`. These files are local,
ignored outputs and are excluded from the public source bundle. Raw logs may
contain machine-specific paths; review them before sharing.

## GitHub Actions

[The included workflow](../.github/workflows/lean.yml) runs the same checker on
Ubuntu 24.04 for pushes, pull requests, and manual runs. It grants read-only
repository permissions and does not retain checkout credentials. The sole
action is official
[`actions/checkout` v4.2.2](https://github.com/actions/checkout/releases/tag/v4.2.2),
pinned to its full commit SHA. Elan is installed from the official
[v4.2.4 release](https://github.com/leanprover/elan/releases/tag/v4.2.4), using a
versioned archive URL and its fixed SHA-256 checksum. The workflow does not run
an installer fetched from an unpinned branch.

CI prints the JSON summary and does not upload raw verification logs.
