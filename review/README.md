# Statement review guide

This directory provides a reading path for the proposition
`QuantumOracle.SoundnessStatement`, proved by `QuantumOracle.soundness`.
It collects the statement and the definitions of its objects, with generated
source excerpts for reviewing their correspondence with the manuscript.

## Reading order

1. [Annotated statement](../QuantumOracle/Statement/Soundness.lean): the complete
   assumptions and conclusions. [Statement.lean](Statement.lean) imports this
   specification alone; [VerifyStatement.lean](VerifyStatement.lean) separately
   imports the proof and checks its connection to the specification.
2. [Core definitions](CORE_DEFINITIONS.md): selected source excerpts, ordered from
   states and algorithms through oracle executions, output distance, the
   comparison isometry, common purifications, and final projections.
3. [Definition dependencies](DEFINITIONS.md): further project definitions,
   compiler-generated declarations, and the propositions of named proof
   obligations.
4. [Dependency data](semantic-dependencies.json): the extracted declaration graph,
   library boundaries, and extraction policy.
5. [Source manifest](SOURCE_MANIFEST.json): source locations and SHA-256 hashes for
   the files and excerpts.

## Definitions and scope

The definitions describe a finite purified query model: the initial state and
workspace gates, ordinary/marked query schedule, coherent query controls and
directions, actual oracle operations, and final output/discard decomposition.
`reducedState` implements the partial trace. `CommonPurification` requires
normalized vectors with the specified reduced states, and `Dist` takes a
supremum over algorithms and an infimum over their finite common purifications.
The constructed isometry `W` supplies the explicit purification pair, and the
final projector acts on the output register. The
[manuscript correspondence](../docs/THEOREM_STATEMENT.md) explains these objects
and the theorem's assumptions and conclusions.

The canonical source is organized into `Model/`, `Statement/`, and `Proof/`.
The statement imports model definitions and foundational proofs without
importing the main soundness proof. [audit-layers.py](../scripts/audit-layers.py)
checks this import boundary. The public
[Soundness.lean](../QuantumOracle/Soundness.lean) checks that the existing theorem
has exactly the canonical proposition's type.

## Extraction

The extractor starts from the theorem's **type**, not its proof body. It follows
project declaration types and data definitions; for named proof declarations it
retains their propositions without traversing their proof bodies. References
to proofs within data definitions are retained conservatively. This is a
mechanically tracked review scope, not a claim of mathematical minimality.
Structure fields and generated auxiliary declarations are grouped with their
original source commands.

Library definitions are listed as extraction boundaries. The current boundary
contains `Mathlib` and `Init`; the Etingof and ProofAtlas proof sources do not
occur in this definition subset. They remain dependencies of the complete
soundness proof. Definitions using choice include database lookup, inverse
maps, finite coordinate enumerations, orthogonal projections, and positive
square roots; their constraints and library dependencies are recorded with the
other definitions.

`CORE_DEFINITIONS.md` is a selection for navigation. The fuller dependency data
is in `DEFINITIONS.md` and the JSON extraction. Excerpts retain their original
module's namespace, variable, and instance context; they are not standalone
Lean programs. Definitions that construct values using `by` blocks are retained.
Proof fields required to construct normalized states, isometries, and databases
remain part of the actual source.

The review files are generated views of a single implementation. This directory
is not an independent Lean project; its checks use the complete repository's
pinned Lake environment.

## Verification

After the setup in [REPRODUCIBILITY.md](../docs/REPRODUCIBILITY.md), run from the
proof repository root:

```sh
lake --no-cache build QuantumOracle.Statement.Soundness
lake --no-cache lean review/Statement.lean
lake --no-cache lean review/VerifyStatement.lean
```

On Windows, the repository wrapper provides the same commands:

```powershell
.\lake-local.ps1 build QuantumOracle.Statement.Soundness
.\lake-local.ps1 lean review/Statement.lean
.\lake-local.ps1 lean review/VerifyStatement.lean
```

The first two commands check the specification without the main proof. The last
checks that the proved theorem supplies the specified proposition. These checks
complement the mathematical review of the correspondence with the manuscript.
See the [tool documentation](tools/README.md) for regeneration commands and
extraction details.

The review documentation and tools use the project's [MIT license](LICENSE).
Source excerpts retain the attribution and license of their original files.
