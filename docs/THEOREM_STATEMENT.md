# Reading the improved soundness theorem

`QuantumOracle.soundness : QuantumOracle.SoundnessStatement` proves the three conclusions of the
manuscript's `thm:soundness` in its adopted purified finite query model.

## The declaration

The canonical, annotated proposition is
[`SoundnessStatement`](../QuantumOracle/Statement/Soundness.lean#L61).
It imports the model and foundational proofs only. The public endpoint is:

```lean
theorem soundness : SoundnessStatement := @ImprovedSoundness.soundness
```

This direct assignment checks the complete original type against the canonical
proposition. The original declaration below remains available as
[`ImprovedSoundness.soundness`](../QuantumOracle/Proof/ImprovedSoundness.lean#L76).
Here `N w : ℕ` are implicit parameters, and `outputPurification` and `project`
are opened from `FiniteSoundnessWitness` and `ProjectorPurification`.

```lean
theorem soundness
    (encode : BasisLookup.Encoding N w) (hN : 0 < N) (q : ℕ) (hq : 4 * q ≤ N)
    (a : OutputExperiment.Algorithm N w) (ha : a.base.queries ≤ q) :
    let p := outputPurification encode a
    p.distance ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) ∧
      OutputExperiment.Dist encode q ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) ∧
      ∀ P : Submodule ℂ (EuclideanSpace ℂ (Fin (Fintype.card a.Output))),
        |‖project P p.exactVector‖ - ‖project P p.compressedVector‖| ≤
          OutputExperiment.Dist encode q
```

All displayed norms are Euclidean vector norms. The casts `(q : ℝ)` and
`(N : ℝ)` make the numerical bound a real expression.

| Parameter | Meaning in the manuscript and implementation |
| --- | --- |
| `N : ℕ` | Number of permutation points. Lean uses `Fin N`, numbered `0,…,N−1`, for the manuscript's `[N] = {1,…,N}`. This is not the bit length. |
| `w : ℕ` | Fixed bit length of each encoded permutation value. The marker bit used by marked answers is a separate register. |
| `encode : BasisLookup.Encoding N w` | An injection `Fin N ↪ (Fin w → Bool)`: the distinct fixed-length encodings required by the query model. It is supplied once and used by both oracle experiments. |
| `hN : 0 < N` | The manuscript's positive-domain assumption. |
| `q : ℕ` | A common upper bound on the number of queries; it can be zero. |
| `hq : 4 * q ≤ N` | The integer form of the manuscript's real inequality `q ≤ N/4`. It avoids ambiguity from natural-number division. |
| `a : OutputExperiment.Algorithm N w` | One finite algorithm, together with its chosen final output and discarded workspace factor. |
| `ha : a.base.queries ≤ q` | This particular algorithm uses at most `q` queries. Taking its count equal to `q` recovers the manuscript's particular `q`-query algorithm. |

The encoding definition is in
[`Database.lean`](../QuantumOracle/Model/Database.lean#L451). The theorem has no
additional hypothesis supplying a Gram spectrum, branching support, an overlap
formula, or a query-error estimate. Those facts are established by the imported
project proofs.

## Correspondence with the manuscript

The corresponding manuscript statement is Section 3, the theorem titled
"Improved soundness" (label `thm:soundness`). Its distance is defined in Section 2,
"Distance between the oracle experiments" (subsection `sec:oracle-distance`,
equation `eq:dist-definition`). These labels identify the manuscript statements;
the manuscript source is not included in this proof repository.

| Manuscript conclusion | Conjunct in `soundness` | Supporting declaration |
| --- | --- | --- |
| `Dist(q) ≤ 4q/√N` | **2.** The numerical bound on `OutputExperiment.Dist encode q`. | [`FiniteSoundness.dist_le_four_mul_div_sqrt`](../QuantumOracle/Proof/FiniteSoundness.lean#L37) |
| The specified embedded exact and compressed vectors are common purifications, at distance at most `4q/√N`. | **1.** The bound on the constructed `p.distance`; its type already supplies normalization and reduced-state equalities. | [`FiniteSoundnessWitness.outputPurification`](../QuantumOracle/Model/SoundnessPurification.lean#L53) and [`outputPurification_distance_le`](../QuantumOracle/Proof/FiniteSoundnessWitness.lean#L63) |
| For every final projector `G`, the absolute difference of projected norms is at most `Dist(q) ≤ 4q/√N`. | **3.** The bound for every `P`, followed by conjunct **2**. | [`ImprovedSoundness.projected_norm_difference_le_dist_le_four_mul_div_sqrt`](../QuantumOracle/Proof/ImprovedSoundness.lean#L48) |

The Lean conjunction puts the explicit pair first. This changes only the order
of the conclusions. The standalone numerical theorem does not require choosing
an algorithm `a`; the bundled theorem takes `a` because it also describes that
algorithm's particular pair and final projections.

## What the algorithm contains

[`ConcreteExperiment.Algorithm`](../QuantumOracle/Model/ConcreteAlgorithm.lean#L19)
contains a finite private-memory dimension, a query count, an ordinary/marked
schedule, arbitrary complex linear isometry equivalences on the workspace, and
a normalized pure initial workspace vector. The same record drives the exact
and compressed executions. It does not supply final states or error bounds.

The [query arguments](../QuantumOracle/Model/ExactCoherentQuery.lean#L22) contain a
coherent enable bit, a forward/inverse direction bit, a point in `Fin N`, a
marker bit, and a `w`-bit answer. Workspace gates can act jointly on private
memory and these arguments. Ordinary/marked selection is the algorithm's
Boolean schedule, and each scheduled query counts once.

The exact [initial state](../QuantumOracle/Model/ExactExecution.lean#L22) is the
workspace input tensored with the normalized uniform permutation register.
This implements oracle-independent initial advice. The algorithm has no gate
acting directly on that hidden permutation register.

[`OutputExperiment.Algorithm`](../QuantumOracle/Model/OutputExperiment.lean#L27)
adds finite basis types `Output` and `Discard` and a bijection
`a.base.Workspace ≃ a.Output × a.Discard`. The actual final reduction traces out
both the oracle and `Discard`. Choosing `keepAll` retains the entire workspace;
[`dist_eq_retained`](../QuantumOracle/Model/OutputExperiment.lean#L159) proves that
allowing all these output choices preserves the worst-case distance.

## The constructed `p` and its reductions

`let p := outputPurification encode a` names a constructed witness, not a caller
assumption or a selected minimizer. Its type is

```lean
CommonPurification
  (OutputExperiment.exactFinal encode a)
  (OutputExperiment.compressedFinal encode a)
```

The [record definition](../QuantumOracle/Model/PurificationDistance.lean#L28) contains:

- A finite common ancilla dimension and two vectors in that same ambient space.
- Proofs that both vectors have norm one.
- `exact_reduction : reducedState exactVector = OutputExperiment.exactFinal encode a`.
- `compressed_reduction : reducedState compressedVector = OutputExperiment.compressedFinal encode a`.

The exact vector is the actual exact execution transported by the constructed
[`PolarEmbedding.candidate`](../QuantumOracle/Model/PolarEmbedding.lean#L50), the
project's harmonic comparison isometry `W`. The other vector is the actual
compressed execution. The discarded output factor joins the database register,
so the common ancilla is indexed by `a.Discard × Database N`.

[`coordinateState`](../QuantumOracle/Model/FinitePurification.lean#L32) renumbers
finite basis types as `Fin` indices by an isometry. Thus `p.distance` is the
actual vector distance after this shared coordinate change. The construction
proves both reduced-state equalities; neither is an assumption about an abstract
pair of matrices.

## The supremum, infimum, and final projector

[`OutputExperiment.dist_def`](../QuantumOracle/Model/OutputExperiment.lean#L124)
expands `Dist encode q` into the supremum over all implemented algorithms with
at most `q` queries and all their finite output decompositions. For each one,
[`purificationDistance`](../QuantumOracle/Model/PurificationDistance.lean#L51) is the
infimum of vector distances over **all** normalized common purifications of
its actual two reduced states, allowing every finite common ancilla dimension.
The definitions contain no proposed soundness upper bound. The implementation
also proves the witness sets and admissible algorithm class are nonempty in
the required positive-domain setting and supplies the needed boundedness facts.

In the final conjunct, `P` is a complex subspace of the numbered output Hilbert
space `EuclideanSpace ℂ (Fin (Fintype.card a.Output))`. It specifies the range of
the final orthogonal projector. [`project P`](../QuantumOracle/Model/ProjectorPurification.lean#L27)
uses `P.starProjection` on the output and the identity on the common ancilla;
`P` does not choose or act on hidden oracle data. The `Fin` numbering is only a
choice of basis labels and does not restrict the output subspaces quantified over.

The quantity is the **absolute difference of projected norms**, equivalently
the difference of square roots of the associated success probabilities. It is
not a claim equating `Dist` to trace distance. The proof shows projected norms
depend only on the reduced states, bounds their difference by every valid
pair's distance, and then takes the infimum. Consequently it proves the
intermediate inequality through `Dist`, not only a bound through `p.distance`.
No attainment of the infimum is required.

## Scope and dependencies

The formal interface adopts the manuscript's purified finite query model:
Section 2, "Query model" (label `sec:query-model`), retains auxiliary registers
to purify the initial state and defer measurements until the end.
A standalone syntax for arbitrary CPTP or intermediate-measurement programs
and a theorem translating that syntax into this interface are outside the
selected theorem scope. Equality with an infimum over arbitrary Hilbert-space
purifications is also outside this scope and is not claimed as proved.
These choices do not add assumptions to the Lean theorem. Later sparse-search
and sponge application theorems are separate from this endpoint.

The proof uses more than mathlib. External source code supplies established
representation and tableau results; the project supplies their connection to
the actual oracle operators.

The independent specification target imports 50 `Model/` modules and one
`Statement/` module. Its external imports are Mathlib and the pinned Aesop tactic
dependency; it does not import the following Etingof or ProofAtlas proof sources.
The model contains definitions together with genuine normalization/isometry
proofs and elementary semantic facts. The [generated review](../review/README.md)
separates definition excerpts from named proof obligations for human reading.

| Source | Role in this proof | How it is included |
| --- | --- | --- |
| Lean and mathlib | Foundational logic, finite groups and modules, linear algebra, finite Hilbert spaces, projections, sums, and real inequalities. | Toolchain and mathlib revision are pinned in [`lean-toolchain`](../lean-toolchain) and [`lakefile.toml`](../lakefile.toml). |
| Pinned Etingof representation-theory release | Actual Young-symmetrizer Specht modules, irreducibility, dimensions/tableau counts, and restriction characters, exposed by [`SpechtFoundation`](../QuantumOracle/Proof/SpechtFoundation.lean). | A local Lake dependency under `vendor/etingof-representation-theory`, preserving the original source and Apache-2.0 license. Its [source manifest](../vendor/etingof-representation-theory/_provenance/source-manifest.json) records the revision and original file hashes. |
| ProofAtlas hook-length formalization | The hook-length formula and tableau corner recurrence, adapted in [`HookLengthFormula`](../QuantumOracle/Proof/HookLengthFormula.lean). | Compiled project source with compatibility proofs. See the [dependency guide](DEPENDENCIES.md) and [third-party notices](../THIRD_PARTY_NOTICES.md) for the pinned source and Apache-2.0 attribution. The preserved original `Basic.lean` is not a second imported copy. |
| This project's `QuantumOracle` modules | Actual databases and executions, Gram spectrum, multiplicities, harmonic embedding, conditioning and overlap estimates, coherent-query comparison, hybrid argument, and purification/projector conclusions. | Locally proved Lean modules. [`SpechtHookBridge`](../QuantumOracle/Proof/SpechtHookBridge.lean) connects the two sources' actual hook products and tableau counts. |

The external results are compiled Lean dependencies, not added mathematical
axioms or a supplied oracle-soundness hypothesis. The local kernel axiom audit
and source-integrity evidence are described in the [main README](../README.md)
and [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md); those records distinguish imported source
from the larger preserved upstream release.

After the setup described in [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md), run
these commands from the proof repository root:

```sh
lake --no-cache build QuantumOracle.Statement.Soundness
lake --no-cache build QuantumOracle.Soundness
```

For a module-by-module correspondence with the rest of the manuscript proof,
see [`PROOF_MAP.md`](PROOF_MAP.md).
