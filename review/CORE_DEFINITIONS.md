# Core definitions: suggested reading order

The following selection provides a reading order through the theorem's definitions. Each code block is an exact source excerpt.
Additional auxiliary definitions appear in the [complete definition list](DEFINITIONS.md).
The canonical theorem statement is defined in [Statement/Soundness.lean](../QuantumOracle/Statement/Soundness.lean).

## States, partial traces, and common purifications

These definitions give coordinate representations of state vectors and density matrices, the partial-trace sum, and a common-purification type requiring normalization and the specified reduced states.

<a id="source-98"></a>
### `QuantumOracle.PureState`

Source: `QuantumOracle/Model/PurificationDistance.lean:19–19`. Classification: `type`.

```lean
abbrev PureState (d n : ℕ) := EuclideanSpace ℂ (Fin d × Fin n)
```

[Continue in the complete list](DEFINITIONS.md#source-98)

<a id="source-99"></a>
### `QuantumOracle.ReducedState`

Source: `QuantumOracle/Model/PurificationDistance.lean:20–20`. Classification: `type`.

```lean
abbrev ReducedState (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
```

[Continue in the complete list](DEFINITIONS.md#source-99)

<a id="source-100"></a>
### `QuantumOracle.reducedState`

Source: `QuantumOracle/Model/PurificationDistance.lean:22–24`. Classification: `definition`.

```lean
/-- Partial trace of the rank-one matrix `|ψ⟩⟨ψ|` over the common ancilla. -/
def reducedState {d n : ℕ} (ψ : PureState d n) : ReducedState d :=
  fun i j => ∑ a : Fin n, ψ (i, a) * star (ψ (j, a))
```

[Continue in the complete list](DEFINITIONS.md#source-100)

<a id="source-101"></a>
### `QuantumOracle.CommonPurification`

Source: `QuantumOracle/Model/PurificationDistance.lean:26–35`. Classification: `type`.

```lean
/-- An actual pair of normalized purifications of the given reduced states.
The common ambient space is part of the witness. -/
structure CommonPurification {d : ℕ} (ρ σ : ReducedState d) where
  ancillaDim : ℕ
  exactVector : PureState d ancillaDim
  compressedVector : PureState d ancillaDim
  exact_normalized : ‖exactVector‖ = 1
  compressed_normalized : ‖compressedVector‖ = 1
  exact_reduction : reducedState exactVector = ρ
  compressed_reduction : reducedState compressedVector = σ
```

<details>
<summary>Corresponding declarations, including generated declarations and fields</summary>

- `QuantumOracle.CommonPurification`
- `QuantumOracle.CommonPurification.ancillaDim`
- `QuantumOracle.CommonPurification.compressedVector`
- `QuantumOracle.CommonPurification.exactVector`
- `QuantumOracle.CommonPurification.mk`

</details>

[Continue in the complete list](DEFINITIONS.md#source-101)

<a id="source-102"></a>
### `QuantumOracle.CommonPurification.distance`

Source: `QuantumOracle/Model/PurificationDistance.lean:37–39`. Classification: `definition`.

```lean
def CommonPurification.distance {d : ℕ} {ρ σ : ReducedState d}
    (p : CommonPurification ρ σ) : ℝ :=
  ‖p.exactVector - p.compressedVector‖
```

[Continue in the complete list](DEFINITIONS.md#source-102)

<a id="source-103"></a>
### `QuantumOracle.purificationDistance`

Source: `QuantumOracle/Model/PurificationDistance.lean:50–52`. Classification: `definition`.

```lean
/-- The infimum is over purifications, and is independent of any proposed bound. -/
def purificationDistance {d : ℕ} (ρ σ : ReducedState d) : ℝ :=
  sInf (Set.range (CommonPurification.distance (ρ := ρ) (σ := σ)))
```

[Continue in the complete list](DEFINITIONS.md#source-103)

## Permutations and databases

Permutations act on Fin N, and databases are finite graphs of partial injections. Encoding distinguishes distinct answers. Auxiliary lookup and update definitions appear in the complete definition list.

<a id="source-37"></a>
### `QuantumOracle.Database`

Source: `QuantumOracle/Model/Database.lean:19–24`. Classification: `type`.

```lean
/-- A finite graph representing a partial injective function on `Fin N`. -/
structure Database (N : ℕ) where
  edges : Finset (Fin N × Fin N)
  functional : ∀ ⦃e f⦄, e ∈ edges → f ∈ edges → e.1 = f.1 → e.2 = f.2
  injective : ∀ ⦃e f⦄, e ∈ edges → f ∈ edges → e.2 = f.2 → e.1 = f.1
  deriving DecidableEq
```

<details>
<summary>Corresponding declarations, including generated declarations and fields</summary>

- `QuantumOracle.Database`
- `QuantumOracle.Database.casesOn`
- `QuantumOracle.Database.edges`
- `QuantumOracle.Database.mk`
- `QuantumOracle.Database.rec`
- `QuantumOracle.instDecidableEqDatabase`
- `QuantumOracle.instDecidableEqDatabase.decEq`
- `QuantumOracle.instDecidableEqDatabase.decEq.match_1`

</details>

[Continue in the complete list](DEFINITIONS.md#source-37)

<a id="source-43"></a>
### `QuantumOracle.Database.lookup`

Source: `QuantumOracle/Model/Database.lean:84–86`. Classification: `definition`.

```lean
/-- The option-valued partial function encoded by the edge graph. -/
noncomputable def lookup (I : Database N) (x : Fin N) : Option (Fin N) :=
  if h : ∃ y, (x, y) ∈ I.edges then some h.choose else none
```

[Continue in the complete list](DEFINITIONS.md#source-43)

<a id="source-93"></a>
### `QuantumOracle.PermutationExtensions.Perm`

Source: `QuantumOracle/Model/PermutationExtensions.lean:11–11`. Classification: `type`.

```lean
abbrev Perm (N : ℕ) := Equiv.Perm (Fin N)
```

[Continue in the complete list](DEFINITIONS.md#source-93)

<a id="source-48"></a>
### `QuantumOracle.BasisLookup.Bits`

Source: `QuantumOracle/Model/Database.lean:403–404`. Classification: `type`.

```lean
/-- A fixed-length bit string. -/
abbrev Bits (w : ℕ) := Fin w → Bool
```

[Continue in the complete list](DEFINITIONS.md#source-48)

<a id="source-53"></a>
### `QuantumOracle.BasisLookup.Encoding`

Source: `QuantumOracle/Model/Database.lean:450–451`. Classification: `type`.

```lean
/-- A representation by distinct bit strings, as required in Section 2.1. -/
abbrev Encoding (N w : ℕ) := Fin N ↪ Bits w
```

[Continue in the complete list](DEFINITIONS.md#source-53)

## Admissible algorithms and their two executions

Algorithm specifies finite private memory, an initial state, unitary gates, a query count, and an ordinary/marked query schedule. The exact and compressed executions use the same algorithm data.

<a id="source-60"></a>
### `QuantumOracle.ExactCoherentQuery.Args`

Source: `QuantumOracle/Model/ExactCoherentQuery.lean:21–22`. Classification: `type`.

```lean
/-- Enable, direction/point, and marker/output registers. -/
abbrev Args (N w : ℕ) := Bool × ((Bool × Fin N) × (Bool × Bits w))
```

[Continue in the complete list](DEFINITIONS.md#source-60)

<a id="source-31"></a>
### `QuantumOracle.ConcreteExperiment.Algorithm`

Source: `QuantumOracle/Model/ConcreteAlgorithm.lean:18–26`. Classification: `type`.

```lean
/-- Finite algorithms in the implemented pure/unitary query model. -/
structure Algorithm (N w : ℕ) where
  auxDim : ℕ
  queries : ℕ
  marked : ℕ → Bool
  gates : ℕ → EuclideanSpace ℂ (Workspace (Fin auxDim) N w) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ (Workspace (Fin auxDim) N w)
  initial : EuclideanSpace ℂ (Workspace (Fin auxDim) N w)
  normalized : ‖initial‖ = 1
```

<details>
<summary>Corresponding declarations, including generated declarations and fields</summary>

- `QuantumOracle.ConcreteExperiment.Algorithm`
- `QuantumOracle.ConcreteExperiment.Algorithm.auxDim`
- `QuantumOracle.ConcreteExperiment.Algorithm.gates`
- `QuantumOracle.ConcreteExperiment.Algorithm.initial`
- `QuantumOracle.ConcreteExperiment.Algorithm.marked`
- `QuantumOracle.ConcreteExperiment.Algorithm.mk`
- `QuantumOracle.ConcreteExperiment.Algorithm.queries`

</details>

[Continue in the complete list](DEFINITIONS.md#source-31)

<a id="source-64"></a>
### `QuantumOracle.ExactExecution.initial`

Source: `QuantumOracle/Model/ExactExecution.lean:21–24`. Classification: `definition`.

```lean
/-- An arbitrary workspace state tensored with the actual uniform permutation state. -/
def initial (N : ℕ) (φ : EuclideanSpace ℂ A) :
    EuclideanSpace ℂ (A × Perm N) :=
  WithLp.toLp 2 (fun aπ => φ aπ.1 * ConsistentState.vector Database.empty aπ.2)
```

[Continue in the complete list](DEFINITIONS.md#source-64)

<a id="source-66"></a>
### `QuantumOracle.ExactExecution.run`

Source: `QuantumOracle/Model/ExactExecution.lean:71–81`. Classification: `definition`.

```lean
/-- Actual execution with an arbitrary workspace unitary before the first query and
after each subsequent query. The Boolean schedule chooses ordinary or marked
queries; enable, direction, point, marker, and answer remain coherent registers. -/
def run (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) :
    ℕ → EuclideanSpace ℂ (Workspace Aux N w × Perm N)
  | 0 => onWorkspace (Perm N) (gates 0).toLinearEquiv.toLinearMap (initial N φ)
  | q + 1 => onWorkspace (Perm N) (gates (q + 1)).toLinearEquiv.toLinearMap
      (liftedQuery Aux encode (marked q) (run encode marked gates φ q))
```

<details>
<summary>Corresponding declarations, including generated declarations and fields</summary>

- `QuantumOracle.ExactExecution.run`
- `QuantumOracle.ExactExecution.run._f`
- `QuantumOracle.ExactExecution.run.match_1`

</details>

[Continue in the complete list](DEFINITIONS.md#source-66)

<a id="source-12"></a>
### `QuantumOracle.CompressedExecution.initial`

Source: `QuantumOracle/Model/CompressedExecution.lean:23–25`. Classification: `definition`.

```lean
/-- An arbitrary workspace vector tensored with the actual empty database ket. -/
def initial (N : ℕ) (φ : EuclideanSpace ℂ A) :
    EuclideanSpace ℂ (A × Database N) := BlockSupport.emptyState φ
```

[Continue in the complete list](DEFINITIONS.md#source-12)

<a id="source-14"></a>
### `QuantumOracle.CompressedExecution.run`

Source: `QuantumOracle/Model/CompressedExecution.lean:100–109`. Classification: `definition`.

```lean
/-- Actual compressed execution, with a workspace unitary before its first query
and after every query. No support-growth hypothesis is part of this definition. -/
def run (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) :
    ℕ → EuclideanSpace ℂ (Workspace Aux N w × Database N)
  | 0 => onWorkspace (Database N) (gates 0).toLinearEquiv.toLinearMap (initial N φ)
  | q + 1 => onWorkspace (Database N) (gates (q + 1)).toLinearEquiv.toLinearMap
      (liftedQuery Aux encode (marked q) (run encode marked gates φ q))
```

<details>
<summary>Corresponding declarations, including generated declarations and fields</summary>

- `QuantumOracle.CompressedExecution.run`
- `QuantumOracle.CompressedExecution.run._f`
- `QuantumOracle.CompressedExecution.run.match_1`

</details>

[Continue in the complete list](DEFINITIONS.md#source-14)

<a id="source-33"></a>
### `QuantumOracle.ConcreteExperiment.exactVector`

Source: `QuantumOracle/Model/ConcreteExperiment.lean:24–26`. Classification: `definition`.

```lean
def exactVector (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    EuclideanSpace ℂ (a.Workspace × Perm N) :=
  ExactExecution.run encode a.marked a.gates a.initial a.queries
```

[Continue in the complete list](DEFINITIONS.md#source-33)

<a id="source-34"></a>
### `QuantumOracle.ConcreteExperiment.compressedVector`

Source: `QuantumOracle/Model/ConcreteExperiment.lean:28–30`. Classification: `definition`.

```lean
def compressedVector (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    EuclideanSpace ℂ (a.Workspace × Database N) :=
  CompressedExecution.run encode a.marked a.gates a.initial a.queries
```

[Continue in the complete list](DEFINITIONS.md#source-34)

## Query and compression operators

These definitions specify the exact query's action on basis states, the compression–lookup–compression construction of compressed queries, inverse queries, and coherent control. The complete list also includes the definitions underlying compression and lookup.

<a id="source-61"></a>
### `QuantumOracle.ExactCoherentQuery.argumentBasis`

Source: `QuantumOracle/Model/ExactCoherentQuery.lean:56–62`. Classification: `definition`.

```lean
/-- For one fixed permutation, the enable and input registers coherently control
the reversible output update. -/
def argumentBasis (encode : Encoding N w) (marked : Bool)
    (π : Equiv.Perm (Fin N)) : Equiv.Perm (Args N w) :=
  BasisLookup.controlled (Query.indexedBasis fun ix : Bool × Fin N =>
    Equiv.prodCongr (bitXorPerm marked)
      (xorPerm (encode (permutationAnswer ix.1 π ix.2))))
```

[Continue in the complete list](DEFINITIONS.md#source-61)

<a id="source-62"></a>
### `QuantumOracle.ExactCoherentQuery.queryBasis`

Source: `QuantumOracle/Model/ExactCoherentQuery.lean:78–81`. Classification: `definition`.

```lean
/-- The concrete permutation-query basis map, with an unchanged oracle register. -/
def queryBasis (encode : Encoding N w) (marked : Bool) :
    Equiv.Perm (Args N w × Equiv.Perm (Fin N)) :=
  Query.registerBasis (argumentBasis encode marked)
```

[Continue in the complete list](DEFINITIONS.md#source-62)

<a id="source-63"></a>
### `QuantumOracle.ExactCoherentQuery.query`

Source: `QuantumOracle/Model/ExactCoherentQuery.lean:108–113`. Classification: `definition`.

```lean
/-- Exact ordinary (`marked = false`) and marked (`marked = true`) queries on
the same complete coherent argument space. -/
def query (encode : Encoding N w) (marked : Bool) :
    EuclideanSpace ℂ (Args N w × Equiv.Perm (Fin N)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Args N w × Equiv.Perm (Fin N)) :=
  Query.linearLift (queryBasis encode marked)
```

[Continue in the complete list](DEFINITIONS.md#source-63)

<a id="source-22"></a>
### `QuantumOracle.Compression.pC`

Source: `QuantumOracle/Model/Compression.lean:34–37`. Classification: `definition`.

```lean
/-- Carolan's actual permutation compression, on the entire database space. -/
def pC (x : Fin N) : State N ≃ₗᵢ[ℂ] State N :=
  BlockOperator.transport (databaseEquiv x)
    (fun J => CompressionBlock.compression (Fresh J.val))
```

[Continue in the complete list](DEFINITIONS.md#source-22)

<a id="source-16"></a>
### `QuantumOracle.CompressedQuery.ordinary`

Source: `QuantumOracle/Model/CompressedQuery.lean:37–42`. Classification: `definition`.

```lean
/-- The exact forward compressed ordinary query in Section 2.2. -/
@[irreducible] def ordinary (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ (Bits w × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Bits w × Database N) :=
  (compression (Bits w) x).trans
    ((Query.ordinaryLookup encode x).trans (compression (Bits w) x))
```

[Continue in the complete list](DEFINITIONS.md#source-16)

<a id="source-17"></a>
### `QuantumOracle.CompressedQuery.marked`

Source: `QuantumOracle/Model/CompressedQuery.lean:44–49`. Classification: `definition`.

```lean
/-- The exact forward compressed marked query in Section 2.3. -/
@[irreducible] def marked (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ ((Bool × Bits w) × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Bool × Bits w) × Database N) :=
  (compression (Bool × Bits w) x).trans
    ((Query.markedLookup encode x).trans (compression (Bool × Bits w) x))
```

[Continue in the complete list](DEFINITIONS.md#source-17)

<a id="source-19"></a>
### `QuantumOracle.CompressedQuery.inverseOrdinary`

Source: `QuantumOracle/Model/CompressedQuery.lean:70–73`. Classification: `definition`.

```lean
def inverseOrdinary (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ (Bits w × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Bits w × Database N) :=
  (flip (Bits w)).trans ((ordinary encode x).trans (flip (Bits w)))
```

[Continue in the complete list](DEFINITIONS.md#source-19)

<a id="source-20"></a>
### `QuantumOracle.CompressedQuery.inverseMarked`

Source: `QuantumOracle/Model/CompressedQuery.lean:75–78`. Classification: `definition`.

```lean
def inverseMarked (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ ((Bool × Bits w) × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Bool × Bits w) × Database N) :=
  (flip (Bool × Bits w)).trans ((marked encode x).trans (flip (Bool × Bits w)))
```

[Continue in the complete list](DEFINITIONS.md#source-20)

<a id="source-8"></a>
### `QuantumOracle.CompressedCoherentQuery.branch`

Source: `QuantumOracle/Model/CompressedCoherentQuery.lean:39–45`. Classification: `definition`.

```lean
/-- A fixed direction and point, on the common marked-answer workspace. -/
def branch (encode : Encoding N w) (marked inverse : Bool) (x : Fin N) :
    State (Bool × Bits w) N ≃ₗᵢ[ℂ] State (Bool × Bits w) N :=
  if marked then
    if inverse then CompressedQuery.inverseMarked encode x
    else CompressedQuery.marked encode x
  else ordinaryWithMarker encode inverse x
```

[Continue in the complete list](DEFINITIONS.md#source-8)

<a id="source-10"></a>
### `QuantumOracle.CompressedCoherentQuery.query`

Source: `QuantumOracle/Model/CompressedCoherentQuery.lean:75–81`. Classification: `definition`.

```lean
/-- Actual controlled compressed oracle on precisely the exact query workspace. -/
def query (encode : Encoding N w) (marked : Bool) :
    State (Args N w) N ≃ₗᵢ[ℂ] State (Args N w) N :=
  let R := Query.linearLift (controlsEquiv (N := N) (w := w))
  R.trans ((BlockOperator.family (fun c : Bool × (Bool × Fin N) =>
    if c.1 then branch encode marked c.2.1 c.2.2
    else LinearIsometryEquiv.refl ℂ _)).trans R.symm)
```

[Continue in the complete list](DEFINITIONS.md#source-10)

## Output, discarded registers, and distance quantifiers

The two executions are partially traced after splitting the workspace into output and discarded registers. Dist takes a supremum over admissible algorithms and, for each algorithm, an infimum over all finite normalized common purifications of the resulting states.

<a id="source-86"></a>
### `QuantumOracle.OutputExperiment.Algorithm`

Source: `QuantumOracle/Model/OutputExperiment.lean:24–33`. Classification: `type`.

```lean
/-- An implemented finite unitary algorithm together with its chosen final
output factor. Both finite basis types are data, allowing the entire original
workspace as a special case without changing its coordinate convention. -/
structure Algorithm (N w : ℕ) where
  base : ConcreteExperiment.Algorithm N w
  Output : Type
  Discard : Type
  outputFintype : Fintype Output
  discardFintype : Fintype Discard
  split : base.Workspace ≃ Output × Discard
```

<details>
<summary>Corresponding declarations, including generated declarations and fields</summary>

- `QuantumOracle.OutputExperiment.Algorithm`
- `QuantumOracle.OutputExperiment.Algorithm.Discard`
- `QuantumOracle.OutputExperiment.Algorithm.Output`
- `QuantumOracle.OutputExperiment.Algorithm.base`
- `QuantumOracle.OutputExperiment.Algorithm.discardFintype`
- `QuantumOracle.OutputExperiment.Algorithm.mk`
- `QuantumOracle.OutputExperiment.Algorithm.outputFintype`
- `QuantumOracle.OutputExperiment.Algorithm.split`

</details>

[Continue in the complete list](DEFINITIONS.md#source-86)

<a id="source-85"></a>
### `QuantumOracle.OutputDiscard.discardVector`

Source: `QuantumOracle/Model/OutputDiscard.lean:24–25`. Classification: `definition`.

```lean
def discardVector (e : A ≃ B × D) (ψ : EuclideanSpace ℂ (A × O)) :
    EuclideanSpace ℂ (B × (D × O)) := discardIsometry e ψ
```

[Continue in the complete list](DEFINITIONS.md#source-85)

<a id="source-89"></a>
### `QuantumOracle.OutputExperiment.exactFinal`

Source: `QuantumOracle/Model/OutputExperiment.lean:62–63`. Classification: `definition`.

```lean
def exactFinal (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    ReducedState (Fintype.card a.Output) := reducedFin (exactVector encode a)
```

[Continue in the complete list](DEFINITIONS.md#source-89)

<a id="source-90"></a>
### `QuantumOracle.OutputExperiment.compressedFinal`

Source: `QuantumOracle/Model/OutputExperiment.lean:65–66`. Classification: `definition`.

```lean
def compressedFinal (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    ReducedState (Fintype.card a.Output) := reducedFin (compressedVector encode a)
```

[Continue in the complete list](DEFINITIONS.md#source-90)

<a id="source-104"></a>
### `QuantumOracle.ExperimentFamily`

Source: `QuantumOracle/Model/PurificationDistance.lean:71–78`. Classification: `type`.

```lean
/-- An interface for a family of final reduced states and query counts.
`ConcreteExperiment.family` instantiates it with algorithms and oracle runs. -/
structure ExperimentFamily (Algorithm : Type*) where
  queries : Algorithm → ℕ
  workspaceDim : Algorithm → ℕ
  exactFinal : (a : Algorithm) → ReducedState (workspaceDim a)
  compressedFinal : (a : Algorithm) → ReducedState (workspaceDim a)
  hasPurifications : ∀ a, Nonempty (CommonPurification (exactFinal a) (compressedFinal a))
```

<details>
<summary>Corresponding declarations, including generated declarations and fields</summary>

- `QuantumOracle.ExperimentFamily`
- `QuantumOracle.ExperimentFamily.compressedFinal`
- `QuantumOracle.ExperimentFamily.exactFinal`
- `QuantumOracle.ExperimentFamily.mk`
- `QuantumOracle.ExperimentFamily.queries`
- `QuantumOracle.ExperimentFamily.workspaceDim`

</details>

[Continue in the complete list](DEFINITIONS.md#source-104)

<a id="source-91"></a>
### `QuantumOracle.OutputExperiment.family`

Source: `QuantumOracle/Model/OutputExperiment.lean:114–119`. Classification: `definition`.

```lean
def family (encode : BasisLookup.Encoding N w) : ExperimentFamily (Algorithm N w) where
  queries a := a.base.queries
  workspaceDim a := Fintype.card a.Output
  exactFinal := exactFinal encode
  compressedFinal := compressedFinal encode
  hasPurifications a := ⟨purification encode a⟩
```

[Continue in the complete list](DEFINITIONS.md#source-91)

<a id="source-105"></a>
### `QuantumOracle.ExperimentFamily.Dist`

Source: `QuantumOracle/Model/PurificationDistance.lean:80–84`. Classification: `definition`.

```lean
/-- Section 2.4's supremum/infimum construction for a supplied experiment family.
No soundness upper bound appears in this definition. -/
def ExperimentFamily.Dist {Algorithm : Type*} (F : ExperimentFamily Algorithm) (q : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ a, F.queries a ≤ q ∧
    r = purificationDistance (F.exactFinal a) (F.compressedFinal a)}
```

[Continue in the complete list](DEFINITIONS.md#source-105)

<a id="source-92"></a>
### `QuantumOracle.OutputExperiment.Dist`

Source: `QuantumOracle/Model/OutputExperiment.lean:121–122`. Classification: `definition`.

```lean
/-- The supremum now also ranges over all finite final output decompositions. -/
def Dist (encode : BasisLookup.Encoding N w) (q : ℕ) : ℝ := (family encode).Dist q
```

[Continue in the complete list](DEFINITIONS.md#source-92)

## The explicit isometry W and the theorem's purification pair

W is defined by the polar normalization A*(sqrt(A†A))⁻¹, where A combines the extension maps on the harmonic layers. The final outputPurification pairs the exact execution transformed by W with the compressed execution. The implementation supplies the isometry and normalization proofs.

<a id="source-71"></a>
### `QuantumOracle.ExtensionOperator.T`

Source: `QuantumOracle/Model/ExtensionOperator.lean:35–38`. Classification: `definition`.

```lean
/-- The manuscript's `T_{N,t}` as a concrete complex linear map. -/
def T (N t : ℕ) :
    EuclideanSpace ℂ (Level N t) →ₗ[ℂ] EuclideanSpace ℂ (Perm N) :=
  (matrix N t).toEuclideanLin
```

[Continue in the complete list](DEFINITIONS.md#source-71)

<a id="source-78"></a>
### `QuantumOracle.KnowledgeSpace.K`

Source: `QuantumOracle/Model/KnowledgeSpace.lean:21–23`. Classification: `definition`.

```lean
/-- The manuscript's span of size-t consistent-permutation states. -/
def K (N t : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Perm N)) :=
  Submodule.span ℂ (Set.range (fun I : ExtensionOperator.Level N t => vector I.val))
```

[Continue in the complete list](DEFINITIONS.md#source-78)

<a id="source-75"></a>
### `QuantumOracle.HarmonicLayers.H`

Source: `QuantumOracle/Model/HarmonicLayers.lean:19–23`. Classification: `definition`.

```lean
/-- Degree zero is the uniform line; each later degree is the orthogonal
increment of the actual consistent-state filtration. -/
def H (N : ℕ) : ℕ → Submodule ℂ (EuclideanSpace ℂ (Perm N))
  | 0 => K N 0
  | t + 1 => K N (t + 1) ⊓ (K N t)ᗮ
```

<details>
<summary>Corresponding declarations, including generated declarations and fields</summary>

- `QuantumOracle.HarmonicLayers.H`
- `QuantumOracle.HarmonicLayers.H.match_1`

</details>

[Continue in the complete list](DEFINITIONS.md#source-75)

<a id="source-113"></a>
### `QuantumOracle.RawHarmonic.raw`

Source: `QuantumOracle/Model/RawHarmonic.lean:24–27`. Classification: `definition`.

```lean
/-- The actual extension adjoint, placed at its exact physical database size. -/
def raw (N t : ℕ) :
    EuclideanSpace ℂ (Perm N) →ₗ[ℂ] Compression.State N :=
  (LevelEmbedding.embed N t).toLinearMap.comp (T N t).adjoint
```

[Continue in the complete list](DEFINITIONS.md#source-113)

<a id="source-112"></a>
### `QuantumOracle.RawEmbedding.total`

Source: `QuantumOracle/Model/RawEmbedding.lean:24–26`. Classification: `definition`.

```lean
/-- Assemble all actual degree components into their physical database levels. -/
def total (N : ℕ) : EuclideanSpace ℂ (Perm N) →ₗ[ℂ] Compression.State N :=
  ∑ i : Fin (N + 1), (raw N i.val).comp (H N i.val).starProjection.toLinearMap
```

[Continue in the complete list](DEFINITIONS.md#source-112)

<a id="source-80"></a>
### `QuantumOracle.MatrixPolar.gramSqrt`

Source: `QuantumOracle/Model/MatrixPolar.lean:22–23`. Classification: `definition`.

```lean
/-- The canonical positive square root of the domain Gram matrix. -/
def gramSqrt (A : Matrix R C ℂ) : Matrix C C ℂ := CFC.sqrt (Aᴴ * A)
```

[Continue in the complete list](DEFINITIONS.md#source-80)

<a id="source-81"></a>
### `QuantumOracle.MatrixPolar.normalize`

Source: `QuantumOracle/Model/MatrixPolar.lean:25–26`. Classification: `definition`.

```lean
/-- Actual positive polar normalization, defined using the inverse square root. -/
def normalize (A : Matrix R C ℂ) : Matrix R C ℂ := A * (gramSqrt A)⁻¹
```

[Continue in the complete list](DEFINITIONS.md#source-81)

<a id="source-96"></a>
### `QuantumOracle.PolarEmbedding.candidate`

Source: `QuantumOracle/Model/PolarEmbedding.lean:49–52`. Classification: `definition`.

```lean
/-- Canonical positive polar normalization of the actual assembled map. -/
def candidate (N : ℕ) :
    EuclideanSpace ℂ (Perm N) →ₗᵢ[ℂ] Compression.State N :=
  MatrixPolar.isometry (matrix N) (matrix_mulVec_injective N)
```

[Continue in the complete list](DEFINITIONS.md#source-96)

<a id="source-114"></a>
### `QuantumOracle.FiniteSoundnessWitness.outputPurification`

Source: `QuantumOracle/Model/SoundnessPurification.lean:52–70`. Classification: `definition`.

```lean
/-- The discarded coordinates join the actual common database ancilla. -/
def outputPurification (encode : BasisLookup.Encoding N w)
    (a : OutputExperiment.Algorithm N w) :
    CommonPurification (OutputExperiment.exactFinal encode a)
      (OutputExperiment.compressedFinal encode a) where
  ancillaDim := Fintype.card (a.Discard × Database N)
  exactVector := coordinateState (discardVector a.split
    (onOracle a.base.Workspace (PolarEmbedding.candidate N)
      (ConcreteExperiment.exactVector encode a.base)))
  compressedVector := coordinateState (OutputExperiment.compressedVector encode a)
  exact_normalized := by
    rw [coordinateState_norm, norm_discardVector, norm_onOracle,
      ConcreteExperiment.exactVector_normalized]
  compressed_normalized := by
    rw [coordinateState_norm, OutputExperiment.compressedVector_normalized]
  exact_reduction := by
    rw [reducedState_coordinateState, reducedFin_discardVector, reducedFin_onOracle]
    exact (OutputExperiment.exactFinal_eq_discardMatrix encode a).symm
  compressed_reduction := reducedState_coordinateState _
```

[Continue in the complete list](DEFINITIONS.md#source-114)

## Orthogonal projection on the final output

project extends an orthogonal projection on the output by the identity on the common ancillary space. The theorem bounds the difference of projected norms, equivalently the difference of square roots of success probabilities.

<a id="source-97"></a>
### `QuantumOracle.ProjectorPurification.project`

Source: `QuantumOracle/Model/ProjectorPurification.lean:26–29`. Classification: `definition`.

```lean
/-- Lift the output's Hilbert orthogonal projection to the actual joint vector. -/
def project (P : Submodule ℂ (EuclideanSpace ℂ (Fin d))) :
    PureState d n →ₗ[ℂ] PureState d n :=
  onWorkspace (Fin n) P.starProjection.toLinearMap
```

[Continue in the complete list](DEFINITIONS.md#source-97)

