# Source releases

The source exporter creates a standalone Lean package containing the theorem,
proofs, exact dependency pins, third-party sources and licenses, documentation,
and verification workflow. Its explicit file allowlist excludes build artifacts
and caches.

Run the proof checker and regenerate the statement review before exporting:

```sh
python scripts/check-proof.py
lake --no-cache lean review/tools/ExtractDependencies.lean
python review/tools/build-review.py
python scripts/export-source.py
```

With the local Windows toolchain, use
`python scripts/check-proof.py --lake-wrapper ./lake-local.ps1` and replace
`lake --no-cache` with `.\lake-local.ps1` for extraction. Regenerate the review
after source changes so its excerpts, locations, and hashes match the export.

The exporter creates `release/quantum-oracle-lean/` and
`release/quantum-oracle-lean.zip`. It refuses to replace existing exports;
use `--name another-source-directory` for a new snapshot.
`SOURCE_MANIFEST.json` records the exported files, byte sizes, and SHA-256 hashes.
The ZIP contains source, without precompiled proof artifacts.

See [reproduction instructions](REPRODUCIBILITY.md) for verification commands
and [dependencies](DEPENDENCIES.md) for source provenance. Original project
code is covered by the [MIT license](../LICENSE); third-party licenses and
notices are preserved as described in [third-party notices](../THIRD_PARTY_NOTICES.md).
