# Improved soundness for compressed permutation oracles

This repository contains a Lean 4 formalization of improved soundness for
compressed permutation oracles. It specifies the exact and compressed oracle
experiments, states their soundness relation, and proves it using harmonic
decomposition and symmetric-group representation theory.

The main result is [`QuantumOracle.soundness`](QuantumOracle/Soundness.lean).
Its full statement is defined and annotated in
[`QuantumOracle/Statement/Soundness.lean`](QuantumOracle/Statement/Soundness.lean).

## Repository layout

```text
QuantumOracle/
  Model/                      oracle experiments and their mathematical definitions
  Statement/
    Soundness.lean            quantified soundness statement
  Proof/                      spectral, branching, and query-comparison arguments
  Soundness.lean              main theorem
QuantumOracle.lean            aggregate import
AxiomAudit.lean               declaration-level axiom checks
review/                       statement review and generated definition excerpts
docs/                         theorem correspondence, proof map, and build details
vendor/                       pinned third-party proof sources
```

`Model/` defines partial-injection databases, oracle operations, finite quantum
algorithms, output states, purifications, and the comparison isometry. It also
contains the foundational proofs needed to construct these objects.
`Statement/` imports this model independently of the main soundness proof.
`Proof/` develops the comparison argument, and `Soundness.lean` connects the
completed proof to the stated proposition.

## Main theorem

The formalization runs the same finite quantum algorithm against an exact
random-permutation oracle and its compressed database oracle. The algorithm
includes a normalized initial workspace state, unitary workspace operations,
a query schedule, coherent query controls, and a final output/discard split.

The soundness theorem bounds the distance between the specified common
purifications, the worst-case output distance over the algorithm class, and
the difference of projected norms for every final output projection. The output
distance is defined by a supremum over algorithms and an infimum over finite
normalized common purifications of their output states.

```lean
import QuantumOracle.Soundness

#check QuantumOracle.soundness
-- QuantumOracle.soundness : QuantumOracle.SoundnessStatement
```

For the complete assumptions and inequalities, read the
[annotated statement](QuantumOracle/Statement/Soundness.lean) and the
[correspondence with the manuscript](docs/THEOREM_STATEMENT.md).
The [statement review guide](review/README.md) provides a reading order through
the definitions used by the theorem. Its excerpts are generated from the source.

## Proof structure

The proof follows four stages:

1. Construct consistency vectors and their harmonic layers, and define the
   comparison isometry between the permutation and database registers.
2. Identify the Gram spectra through symmetric-group representations, and use
   branching and hook-length identities to obtain the required overlap estimates.
3. Bound the discrepancy between exact and compressed queries, including coherent
   controls and an arbitrary finite workspace.
4. Accumulate the query errors by a hybrid argument and derive the purification,
   output-distance, and final-projection conclusions.

The [proof map](docs/PROOF_MAP.md) describes the modules implementing each part.

## Verification

The project uses the Lean version in [`lean-toolchain`](lean-toolchain), with
dependencies pinned in [`lake-manifest.json`](lake-manifest.json). With
[elan](https://lean-lang.org/install/) and Python 3.10 or later installed, run:

```sh
lake --no-cache exe cache get --cache-from=legacy Mathlib
python3 scripts/check-proof.py
```

The checker builds the specification and full proof, verifies the statement
entrypoints, checks declaration dependencies against `propext`,
`Classical.choice`, and `Quot.sound`, and checks the source import boundaries
and vendored file hashes. The GitHub Actions workflow runs the same checker.
Platform-specific setup instructions are in
[Reproducibility](docs/REPRODUCIBILITY.md).

To build the specification alone:

```sh
lake --no-cache build QuantumOracle.Statement.Soundness
```

To inspect the main theorem's axiom dependencies in Lean:

```lean
import QuantumOracle.Soundness

#print axioms QuantumOracle.soundness
```

## Dependencies

The development uses [mathlib](https://github.com/leanprover-community/mathlib4),
the [Etingof representation-theory formalization](https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1)
for Specht modules and branching, and the
[ProofAtlas hook-length formalization](https://www.proofatlas.ai/formalizations/hook-length-formula/).
Exact revisions and integration details are recorded in
[Dependencies](docs/DEPENDENCIES.md).

## License

Original project code is licensed under [MIT](LICENSE). The vendored Etingof and
ProofAtlas sources, including the adapted hook-length proof, retain their
Apache-2.0 licenses and notices. See [Third-party notices](THIRD_PARTY_NOTICES.md).
