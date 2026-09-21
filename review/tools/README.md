# Declaration-level statement review extractor

Run from the Lean source root:

```powershell
.\lake-local.ps1 lean review/tools/ExtractDependencies.lean
python review/tools/build-review.py
```

With elan on another platform, use
`lake --no-cache lean review/tools/ExtractDependencies.lean`, followed by
`python review/tools/build-review.py`.
The extractor reads the loaded Lean environment and writes
`review/semantic-dependencies.json`. It does not change proof
sources or the public source release.

The source of the proposition is `QuantumOracle/Statement/Soundness.lean`.
It imports only the model. The extractor imports the completed original theorem
to inspect its full type; `QuantumOracle/Soundness.lean` checks that this type is
definitionally equal to the canonical proposition. The review manifest hashes
both the canonical statement and the separate verification entrypoint.

The root is **only the type** of
`QuantumOracle.ImprovedSoundness.soundness`. For every reached non-boundary
declaration, the traversal follows its type, its non-Prop value if present,
inductive constructor relationships, and recursor rules. It records ordinary
constant references and the structure names stored in kernel projection
expressions. `Lean.Meta.isProp` identifies proof-valued declarations: their
propositions are followed, but their proof values are never visited. In
particular, the final soundness proof is never visited.

The explicit trusted-library boundary consists of declarations originating in
`Mathlib`, `Lean`, `Std`, or `Init` modules. Boundary names and originating modules
are listed individually in the JSON. Classification is by originating module,
not by a declaration's namespace. Non-boundary dependencies are followed even
if they do not use the `QuantumOracle` namespace.

Each local node contains its name, kernel declaration kind, proof/type/instance
classification, pretty-printed type, source module, direct dependency edges,
and source range when present. Generated declarations without their own range
fall back to a named parent's range; `sourceOwner` and
`rangeInheritedFromParent` expose that mapping. Lines are 1-based and columns
are 0-based Unicode codepoint offsets; ends are exclusive. Ranges can include
documentation comments. Pretty-printed types can elide implicit arguments;
dependency edges are computed from the elaborated expressions themselves.

This is a **conservative syntactic semantic slice**, not a mathematically
minimal set of definitions. Inline proof expressions inside non-Prop values
are conservatively traversed, so they can introduce additional named proof
obligations; the bodies of those named obligations remain excluded. Source
commands may define several generated declarations together, so a source-based
review should deduplicate by source ranges and distinguish proof signatures
from computational definitions. A collection of such excerpts is a reading
artifact, not a replacement standalone Lean proof. `build-review.py` renders
the source excerpts, proof-obligation signatures, and source SHA-256 manifest.
The human reading order is selected in `reading-order.json`; every selection
must occur in the extracted non-proof dependency set.

The extractor assumes the project's imported environment is the one being
reviewed. It is an inspection tool, not independent kernel replay, an axiom
audit, a manuscript-to-code equivalence proof, or a new soundness proof.
