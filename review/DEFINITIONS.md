# Complete definition dependencies

This report starts from the final theorem's **type** and follows the types and data definitions of project declarations.
For named proof declarations, it records the propositions without traversing the proof bodies.
Proof fields and inline proof references within data definitions are included conservatively; the result is not a mathematically minimal dependency set.

Of the 233 project declarations, 154 non-proof declarations are collected into the 119 source excerpts below.
The excerpts come from 36 source files. The propositions for 79 proof obligations appear separately below.
Each excerpt depends on the namespace, variable, and instance context of its source file and is not a standalone compilation unit.
Generated fields, constructors, and recursive auxiliary declarations are grouped with their source structure or definition.

## Source definitions

## `QuantumOracle/Model/BlockOperator.lean`

<a id="source-1"></a>
### `QuantumOracle.BlockOperator.diagonal`

Source: `QuantumOracle/Model/BlockOperator.lean:14–19`. Classification: `definition`.

```lean
/-- Apply a genuine linear isometry independently on each orthogonal block. -/
def diagonal (U : ∀ i, EuclideanSpace ℂ (κ i) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (κ i)) :
    EuclideanSpace ℂ (Sigma κ) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Sigma κ) :=
  (LinearIsometryEquiv.piLpCurry ℂ 2 (fun _ _ => ℂ)).trans
    ((LinearIsometryEquiv.piLpCongrRight 2 U).trans
      (LinearIsometryEquiv.piLpCurry ℂ 2 (fun _ _ => ℂ)).symm)
```

<a id="source-2"></a>
### `QuantumOracle.BlockOperator.transport`

Source: `QuantumOracle/Model/BlockOperator.lean:49–54`. Classification: `definition`.

```lean
/-- Reindexing a block direct sum back into a physical basis. -/
def transport {α : Type*} [Fintype α] (e : α ≃ Sigma κ)
    (U : ∀ i, EuclideanSpace ℂ (κ i) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (κ i)) :
    EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α :=
  let R := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  R.trans ((diagonal U).trans R.symm)
```

<a id="source-3"></a>
### `QuantumOracle.BlockOperator.family`

Source: `QuantumOracle/Model/BlockOperator.lean:73–77`. Classification: `definition`.

```lean
/-- A family of operators controlled by an unchanged finite register. -/
def family {C Y : Type*} [Fintype C] [Fintype Y]
    (U : C → EuclideanSpace ℂ Y ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y) :
    EuclideanSpace ℂ (C × Y) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (C × Y) :=
  transport (Equiv.sigmaEquivProd C Y).symm U
```

<a id="source-4"></a>
### `QuantumOracle.BlockOperator.onRight`

Source: `QuantumOracle/Model/BlockOperator.lean:89–93`. Classification: `definition`.

```lean
/-- Tensoring with an identity register, in finite product coordinates. -/
def onRight (C : Type*) {Y : Type*} [Fintype C] [Fintype Y]
    (U : EuclideanSpace ℂ Y ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y) :
    EuclideanSpace ℂ (C × Y) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (C × Y) :=
  family (fun _ : C => U)
```

## `QuantumOracle/Model/BlockSupport.lean`

<a id="source-5"></a>
### `QuantumOracle.BlockSupport.State`

Source: `QuantumOracle/Model/BlockSupport.lean:19–20`. Classification: `type`.

```lean
abbrev State (Y : Type*) [Fintype Y] (N : ℕ) :=
  EuclideanSpace ℂ (Y × Database N)
```

<a id="source-6"></a>
### `QuantumOracle.BlockSupport.emptyState`

Source: `QuantumOracle/Model/BlockSupport.lean:108–110`. Classification: `definition`.

```lean
/-- Arbitrary initial workspace amplitudes tensored with the empty database. -/
def emptyState (ψ : EuclideanSpace ℂ Y) : State Y N :=
  WithLp.toLp 2 (fun p => if p.2 = Database.empty then ψ p.1 else 0)
```

## `QuantumOracle/Model/CompressedCoherentQuery.lean`

<a id="source-7"></a>
### `QuantumOracle.CompressedCoherentQuery.ordinaryWithMarker`

Source: `QuantumOracle/Model/CompressedCoherentQuery.lean:22–28`. Classification: `definition`.

```lean
/-- The ordinary compressed query, with its unused marker register retained. -/
def ordinaryWithMarker (encode : Encoding N w) (inverse : Bool) (x : Fin N) :
    State (Bool × Bits w) N ≃ₗᵢ[ℂ] State (Bool × Bits w) N :=
  let R := Query.linearLift (Equiv.prodAssoc Bool (Bits w) (Database N))
  R.trans ((BlockOperator.onRight Bool
    (if inverse then CompressedQuery.inverseOrdinary encode x
      else CompressedQuery.ordinary encode x)).trans R.symm)
```

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

<a id="source-9"></a>
### `QuantumOracle.CompressedCoherentQuery.controlsEquiv`

Source: `QuantumOracle/Model/CompressedCoherentQuery.lean:66–73`. Classification: `definition`.

```lean
/-- Regroup the unchanged controls independently of the answer/database block. -/
def controlsEquiv :
    (Args N w × Database N) ≃
      ((Bool × (Bool × Fin N)) × ((Bool × Bits w) × Database N)) where
  toFun p := ((p.1.1, p.1.2.1), (p.1.2.2, p.2))
  invFun p := ((p.1.1, (p.1.2, p.2.1)), p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
```

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

<a id="source-11"></a>
### `QuantumOracle.CompressedCoherentQuery.liftedQuery`

Source: `QuantumOracle/Model/CompressedCoherentQuery.lean:157–161`. Classification: `definition`.

```lean
/-- An arbitrary finite auxiliary register is retained coherently. -/
def liftedQuery (Aux : Type*) [Fintype Aux] (encode : Encoding N w) (marked : Bool) :
    State (Aux × Args N w) N ≃ₗᵢ[ℂ] State (Aux × Args N w) N :=
  let R := Query.linearLift (Equiv.prodAssoc Aux (Args N w) (Database N))
  R.trans ((BlockOperator.onRight Aux (query encode marked)).trans R.symm)
```

## `QuantumOracle/Model/CompressedExecution.lean`

<a id="source-12"></a>
### `QuantumOracle.CompressedExecution.initial`

Source: `QuantumOracle/Model/CompressedExecution.lean:23–25`. Classification: `definition`.

```lean
/-- An arbitrary workspace vector tensored with the actual empty database ket. -/
def initial (N : ℕ) (φ : EuclideanSpace ℂ A) :
    EuclideanSpace ℂ (A × Database N) := BlockSupport.emptyState φ
```

<a id="source-13"></a>
### `QuantumOracle.CompressedExecution.Workspace`

Source: `QuantumOracle/Model/CompressedExecution.lean:97–98`. Classification: `type`.

```lean
/-- Exactly the same private and coherent query workspace as the exact execution. -/
abbrev Workspace (Aux : Type*) (N w : ℕ) := ExactExecution.Workspace Aux N w
```

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

## `QuantumOracle/Model/CompressedQuery.lean`

<a id="source-15"></a>
### `QuantumOracle.CompressedQuery.compression`

Source: `QuantumOracle/Model/CompressedQuery.lean:18–21`. Classification: `definition`.

```lean
/-- Compression leaves an arbitrary answer register unchanged. -/
@[irreducible] def compression (Y : Type*) [Fintype Y] (x : Fin N) :
    EuclideanSpace ℂ (Y × Database N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Y × Database N) :=
  BlockOperator.onRight Y (Compression.pC x)
```

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

<a id="source-18"></a>
### `QuantumOracle.CompressedQuery.flip`

Source: `QuantumOracle/Model/CompressedQuery.lean:65–68`. Classification: `definition`.

```lean
/-- Actual database inversion as a complex linear isometry equivalence. -/
def flip (Y : Type*) [Fintype Y] :
    EuclideanSpace ℂ (Y × Database N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Y × Database N) :=
  Query.linearLift BasisLookup.flip
```

<a id="source-19"></a>
### `QuantumOracle.CompressedQuery.inverseOrdinary`

Source: `QuantumOracle/Model/CompressedQuery.lean:70–73`. Classification: `definition`.

```lean
def inverseOrdinary (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ (Bits w × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Bits w × Database N) :=
  (flip (Bits w)).trans ((ordinary encode x).trans (flip (Bits w)))
```

<a id="source-20"></a>
### `QuantumOracle.CompressedQuery.inverseMarked`

Source: `QuantumOracle/Model/CompressedQuery.lean:75–78`. Classification: `definition`.

```lean
def inverseMarked (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ ((Bool × Bits w) × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Bool × Bits w) × Database N) :=
  (flip (Bool × Bits w)).trans ((marked encode x).trans (flip (Bool × Bits w)))
```

## `QuantumOracle/Model/Compression.lean`

<a id="source-21"></a>
### `QuantumOracle.Compression.State`

Source: `QuantumOracle/Model/Compression.lean:21–21`. Classification: `type`.

```lean
abbrev State (N : ℕ) := EuclideanSpace ℂ (Database N)
```

<a id="source-22"></a>
### `QuantumOracle.Compression.pC`

Source: `QuantumOracle/Model/Compression.lean:34–37`. Classification: `definition`.

```lean
/-- Carolan's actual permutation compression, on the entire database space. -/
def pC (x : Fin N) : State N ≃ₗᵢ[ℂ] State N :=
  BlockOperator.transport (databaseEquiv x)
    (fun J => CompressionBlock.compression (Fresh J.val))
```

## `QuantumOracle/Model/CompressionBlock.lean`

<a id="source-23"></a>
### `QuantumOracle.CompressionBlock.compression`

Source: `QuantumOracle/Model/CompressionBlock.lean:21–24`. Classification: `definition`.

```lean
/-- The local compression map, as an actual complex linear isometry equivalence. -/
def compression (α : Type*) [Fintype α] :
    EuclideanSpace ℂ (Option α) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Option α) :=
  orthonormalSwap (emptyKet α) (extensionUniform α)
```

## `QuantumOracle/Model/CompressionIndex.lean`

<a id="source-24"></a>
### `QuantumOracle.CompressionIndex.Base`

Source: `QuantumOracle/Model/CompressionIndex.lean:19–20`. Classification: `type`.

```lean
/-- A base database for compression at input `x`. -/
abbrev Base (x : Fin N) := {J : Database N // x ∉ J.domain}
```

<a id="source-25"></a>
### `QuantumOracle.CompressionIndex.Fresh`

Source: `QuantumOracle/Model/CompressionIndex.lean:22–23`. Classification: `type`.

```lean
/-- Unused output values of an actual partial-injective database. -/
abbrev Fresh (J : Database N) := {y : Fin N // y ∉ J.image}
```

<a id="source-26"></a>
### `QuantumOracle.CompressionIndex.baseFintype`

Source: `QuantumOracle/Model/CompressionIndex.lean:25–26`. Classification: `instance`.

```lean
noncomputable instance baseFintype (x : Fin N) : Fintype (Base x) :=
  Fintype.ofFinite _
```

<a id="source-27"></a>
### `QuantumOracle.CompressionIndex.freshFintype`

Source: `QuantumOracle/Model/CompressionIndex.lean:28–29`. Classification: `instance`.

```lean
noncomputable instance freshFintype (J : Database N) : Fintype (Fresh J) :=
  Fintype.ofFinite _
```

<a id="source-28"></a>
### `QuantumOracle.CompressionIndex.Index`

Source: `QuantumOracle/Model/CompressionIndex.lean:31–32`. Classification: `type`.

```lean
/-- One undefined basis vector, followed by one vector for each fresh output. -/
abbrev Index (x : Fin N) := Σ J : Base x, Option (Fresh J.val)
```

<a id="source-29"></a>
### `QuantumOracle.CompressionIndex.decode`

Source: `QuantumOracle/Model/CompressionIndex.lean:54–57`. Classification: `definition`.

```lean
/-- Interpret block coordinates as actual databases. -/
def decode (x : Fin N) : Index x → Database N
  | ⟨J, none⟩ => J.val
  | ⟨J, some y⟩ => J.val.set x y.val
```

<details>
<summary>Corresponding declarations, including generated declarations and fields</summary>

- `QuantumOracle.CompressionIndex.decode`
- `QuantumOracle.CompressionIndex.decode.match_1`

</details>

<a id="source-30"></a>
### `QuantumOracle.CompressionIndex.databaseEquiv`

Source: `QuantumOracle/Model/CompressionIndex.lean:108–110`. Classification: `definition`.

```lean
/-- The genuine database basis is partitioned into its compression blocks. -/
noncomputable def databaseEquiv (x : Fin N) : Database N ≃ Index x :=
  (Equiv.ofBijective (decode x) ⟨decode_injective x, decode_surjective x⟩).symm
```

## `QuantumOracle/Model/ConcreteAlgorithm.lean`

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

<a id="source-32"></a>
### `QuantumOracle.ConcreteExperiment.Algorithm.Workspace`

Source: `QuantumOracle/Model/ConcreteAlgorithm.lean:28–29`. Classification: `type`.

```lean
abbrev Algorithm.Workspace {N w : ℕ} (a : Algorithm N w) :=
  ExactExecution.Workspace (Fin a.auxDim) N w
```

## `QuantumOracle/Model/ConcreteExperiment.lean`

<a id="source-33"></a>
### `QuantumOracle.ConcreteExperiment.exactVector`

Source: `QuantumOracle/Model/ConcreteExperiment.lean:24–26`. Classification: `definition`.

```lean
def exactVector (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    EuclideanSpace ℂ (a.Workspace × Perm N) :=
  ExactExecution.run encode a.marked a.gates a.initial a.queries
```

<a id="source-34"></a>
### `QuantumOracle.ConcreteExperiment.compressedVector`

Source: `QuantumOracle/Model/ConcreteExperiment.lean:28–30`. Classification: `definition`.

```lean
def compressedVector (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    EuclideanSpace ℂ (a.Workspace × Database N) :=
  CompressedExecution.run encode a.marked a.gates a.initial a.queries
```

## `QuantumOracle/Model/ConsistentState.lean`

<a id="source-35"></a>
### `QuantumOracle.ConsistentState.amplitude`

Source: `QuantumOracle/Model/ConsistentState.lean:30–32`. Classification: `definition`.

```lean
/-- The manuscript's exact factorial amplitude. -/
def amplitude (I : Database N) : ℝ :=
  (Real.sqrt ((N - I.size).factorial : ℝ))⁻¹
```

<a id="source-36"></a>
### `QuantumOracle.ConsistentState.vector`

Source: `QuantumOracle/Model/ConsistentState.lean:49–52`. Classification: `definition`.

```lean
/-- Uniform superposition over the genuine permutations extending `I`. -/
def vector (I : Database N) : EuclideanSpace ℂ (Perm N) := by
  classical
  exact WithLp.toLp 2 (fun π => if Extends I π then (amplitude I : ℂ) else 0)
```

## `QuantumOracle/Model/Database.lean`

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

<a id="source-38"></a>
### `QuantumOracle.Database.instFintype`

Source: `QuantumOracle/Model/Database.lean:40–40`. Classification: `instance`.

```lean
noncomputable instance : Fintype (Database N) := Fintype.ofFinite _
```

<a id="source-39"></a>
### `QuantumOracle.Database.empty`

Source: `QuantumOracle/Model/Database.lean:42–46`. Classification: `definition`.

```lean
/-- The empty database, denoted `⊥_I` in the manuscript. -/
def empty : Database N where
  edges := ∅
  functional := by simp
  injective := by simp
```

<a id="source-40"></a>
### `QuantumOracle.Database.domain`

Source: `QuantumOracle/Model/Database.lean:48–49`. Classification: `definition`.

```lean
/-- The input points on which a database is defined. -/
def domain (I : Database N) : Finset (Fin N) := I.edges.image Prod.fst
```

<a id="source-41"></a>
### `QuantumOracle.Database.image`

Source: `QuantumOracle/Model/Database.lean:51–52`. Classification: `definition`.

```lean
/-- The values attained by a database. -/
def image (I : Database N) : Finset (Fin N) := I.edges.image Prod.snd
```

<a id="source-42"></a>
### `QuantumOracle.Database.size`

Source: `QuantumOracle/Model/Database.lean:54–55`. Classification: `definition`.

```lean
/-- Database size is its domain cardinality, as in the manuscript. -/
def size (I : Database N) : ℕ := I.domain.card
```

<a id="source-43"></a>
### `QuantumOracle.Database.lookup`

Source: `QuantumOracle/Model/Database.lean:84–86`. Classification: `definition`.

```lean
/-- The option-valued partial function encoded by the edge graph. -/
noncomputable def lookup (I : Database N) (x : Fin N) : Option (Fin N) :=
  if h : ∃ y, (x, y) ∈ I.edges then some h.choose else none
```

<a id="source-44"></a>
### `QuantumOracle.Database.inverse`

Source: `QuantumOracle/Model/Database.lean:124–136`. Classification: `definition`.

```lean
/-- Inversion exchanges input and output coordinates. -/
def inverse (I : Database N) : Database N where
  edges := I.edges.image Prod.swap
  functional := by
    intro e f he hf h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
    exact I.injective ha hb h
  injective := by
    intro e f he hf h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
    exact I.functional ha hb h
```

<a id="source-45"></a>
### `QuantumOracle.Database.set`

Source: `QuantumOracle/Model/Database.lean:201–222`. Classification: `definition`.

```lean
/-- Set the edge at `x` to `y`, deleting the former edge at `x` and
any conflicting preimage of `y`, exactly as in Section 2.2. -/
def set (I : Database N) (x y : Fin N) : Database N where
  edges := insert (x, y) (I.edges.filter (fun e => e.1 ≠ x ∧ e.2 ≠ y))
  functional := by
    intro e f he hf h
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · rfl
      · exact False.elim ((Finset.mem_filter.mp hf).2.1 h.symm)
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact False.elim ((Finset.mem_filter.mp he).2.1 h)
      · exact I.functional (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 h
  injective := by
    intro e f he hf h
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · rfl
      · exact False.elim ((Finset.mem_filter.mp hf).2.2 h.symm)
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact False.elim ((Finset.mem_filter.mp he).2.2 h)
      · exact I.injective (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 h
```

<a id="source-46"></a>
### `QuantumOracle.Database.update`

Source: `QuantumOracle/Model/Database.lean:224–227`. Classification: `definition`.

```lean
/-- The manuscript's update, including deletion for an undefined value. -/
def update (I : Database N) (x : Fin N) : Option (Fin N) → Database N
  | none => I.erase x
  | some y => I.set x y
```

<a id="source-47"></a>
### `QuantumOracle.Database.level`

Source: `QuantumOracle/Model/Database.lean:384–385`. Classification: `type`.

```lean
/-- The databases at a fixed level of the manuscript's direct sum. -/
def level (N t : ℕ) := {I : Database N // I.size = t}
```

<a id="source-48"></a>
### `QuantumOracle.BasisLookup.Bits`

Source: `QuantumOracle/Model/Database.lean:403–404`. Classification: `type`.

```lean
/-- A fixed-length bit string. -/
abbrev Bits (w : ℕ) := Fin w → Bool
```

<a id="source-49"></a>
### `QuantumOracle.BasisLookup.xor`

Source: `QuantumOracle/Model/Database.lean:406–406`. Classification: `definition`.

```lean
def xor (z a : Bits w) : Bits w := fun i => Bool.xor (z i) (a i)
```

<a id="source-50"></a>
### `QuantumOracle.BasisLookup.xorPerm`

Source: `QuantumOracle/Model/Database.lean:418–423`. Classification: `definition`.

```lean
/-- XOR with a fixed bit string is an actual permutation. -/
def xorPerm (a : Bits w) : Equiv.Perm (Bits w) where
  toFun := fun z => xor z a
  invFun := fun z => xor z a
  left_inv := fun z => xor_twice z a
  right_inv := fun z => xor_twice z a
```

<a id="source-51"></a>
### `QuantumOracle.BasisLookup.bitXorPerm`

Source: `QuantumOracle/Model/Database.lean:425–429`. Classification: `definition`.

```lean
def bitXorPerm (a : Bool) : Equiv.Perm Bool where
  toFun := fun z => Bool.xor z a
  invFun := fun z => Bool.xor z a
  left_inv := by intro z; cases z <;> cases a <;> rfl
  right_inv := by intro z; cases z <;> cases a <;> rfl
```

<a id="source-52"></a>
### `QuantumOracle.BasisLookup.liftLookup`

Source: `QuantumOracle/Model/Database.lean:431–437`. Classification: `definition`.

```lean
/-- Apply a database-dependent output permutation, keeping the database. -/
def liftLookup {Y : Type*} (action : Database N → Equiv.Perm Y) :
    Equiv.Perm (Y × Database N) where
  toFun := fun zI => (action zI.2 zI.1, zI.2)
  invFun := fun zI => ((action zI.2).symm zI.1, zI.2)
  left_inv := by rintro ⟨z, I⟩; simp
  right_inv := by rintro ⟨z, I⟩; simp
```

<a id="source-53"></a>
### `QuantumOracle.BasisLookup.Encoding`

Source: `QuantumOracle/Model/Database.lean:450–451`. Classification: `type`.

```lean
/-- A representation by distinct bit strings, as required in Section 2.1. -/
abbrev Encoding (N w : ℕ) := Fin N ↪ Bits w
```

<a id="source-54"></a>
### `QuantumOracle.BasisLookup.ordinaryAnswer`

Source: `QuantumOracle/Model/Database.lean:453–457`. Classification: `definition`.

```lean
noncomputable def ordinaryAnswer (encode : Encoding N w) (I : Database N)
    (x : Fin N) : Bits w :=
  match I.lookup x with
  | none => fun _ => false
  | some y => encode y
```

<a id="source-55"></a>
### `QuantumOracle.BasisLookup.markedAnswer`

Source: `QuantumOracle/Model/Database.lean:459–465`. Classification: `definition`.

```lean
/-- Marked answers encode a defined value as `(true, encode y)` and
an undefined value as `(false, 0)`. -/
noncomputable def markedAnswer (encode : Encoding N w) (I : Database N)
    (x : Fin N) : Bool × Bits w :=
  match I.lookup x with
  | none => (false, fun _ => false)
  | some y => (true, encode y)
```

<a id="source-56"></a>
### `QuantumOracle.BasisLookup.ordinary`

Source: `QuantumOracle/Model/Database.lean:467–470`. Classification: `definition`.

```lean
/-- The manuscript's ordinary extended lookup `P_x` on basis states. -/
noncomputable def ordinary (encode : Encoding N w) (x : Fin N) :
    Equiv.Perm (Bits w × Database N) :=
  liftLookup (fun I => xorPerm (ordinaryAnswer encode I x))
```

<a id="source-57"></a>
### `QuantumOracle.BasisLookup.marked`

Source: `QuantumOracle/Model/Database.lean:472–477`. Classification: `definition`.

```lean
/-- The marked extended lookup, including an arbitrary marker-qubit value. -/
noncomputable def marked (encode : Encoding N w) (x : Fin N) :
    Equiv.Perm ((Bool × Bits w) × Database N) :=
  liftLookup (fun I =>
    Equiv.prodCongr (bitXorPerm (markedAnswer encode I x).1)
      (xorPerm (markedAnswer encode I x).2))
```

<a id="source-58"></a>
### `QuantumOracle.BasisLookup.flip`

Source: `QuantumOracle/Model/Database.lean:522–527`. Classification: `definition`.

```lean
/-- Database inversion, with an arbitrary unchanged output register. -/
def flip {Y : Type*} : Equiv.Perm (Y × Database N) where
  toFun := fun zI => (zI.1, zI.2.inverse)
  invFun := fun zI => (zI.1, zI.2.inverse)
  left_inv := by intro zI; simp
  right_inv := by intro zI; simp
```

<a id="source-59"></a>
### `QuantumOracle.BasisLookup.controlled`

Source: `QuantumOracle/Model/Database.lean:552–557`. Classification: `definition`.

```lean
/-- A coherent-control basis permutation. Its linear lift remains to be proved. -/
def controlled {Y : Type*} (e : Equiv.Perm Y) : Equiv.Perm (Bool × Y) where
  toFun := fun cy => (cy.1, if cy.1 then e cy.2 else cy.2)
  invFun := fun cy => (cy.1, if cy.1 then e.symm cy.2 else cy.2)
  left_inv := by rintro ⟨b, y⟩; cases b <;> simp
  right_inv := by rintro ⟨b, y⟩; cases b <;> simp
```

## `QuantumOracle/Model/ExactCoherentQuery.lean`

<a id="source-60"></a>
### `QuantumOracle.ExactCoherentQuery.Args`

Source: `QuantumOracle/Model/ExactCoherentQuery.lean:21–22`. Classification: `type`.

```lean
/-- Enable, direction/point, and marker/output registers. -/
abbrev Args (N w : ℕ) := Bool × ((Bool × Fin N) × (Bool × Bits w))
```

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

<a id="source-62"></a>
### `QuantumOracle.ExactCoherentQuery.queryBasis`

Source: `QuantumOracle/Model/ExactCoherentQuery.lean:78–81`. Classification: `definition`.

```lean
/-- The concrete permutation-query basis map, with an unchanged oracle register. -/
def queryBasis (encode : Encoding N w) (marked : Bool) :
    Equiv.Perm (Args N w × Equiv.Perm (Fin N)) :=
  Query.registerBasis (argumentBasis encode marked)
```

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

## `QuantumOracle/Model/ExactExecution.lean`

<a id="source-64"></a>
### `QuantumOracle.ExactExecution.initial`

Source: `QuantumOracle/Model/ExactExecution.lean:21–24`. Classification: `definition`.

```lean
/-- An arbitrary workspace state tensored with the actual uniform permutation state. -/
def initial (N : ℕ) (φ : EuclideanSpace ℂ A) :
    EuclideanSpace ℂ (A × Perm N) :=
  WithLp.toLp 2 (fun aπ => φ aπ.1 * ConsistentState.vector Database.empty aπ.2)
```

<a id="source-65"></a>
### `QuantumOracle.ExactExecution.Workspace`

Source: `QuantumOracle/Model/ExactExecution.lean:68–69`. Classification: `type`.

```lean
/-- The adversary can jointly manipulate private memory and every query argument. -/
abbrev Workspace (Aux : Type*) (N w : ℕ) := Aux × Args N w
```

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

## `QuantumOracle/Model/ExactQueryGrowth.lean`

<a id="source-67"></a>
### `QuantumOracle.ExactQueryGrowth.liftedQuery`

Source: `QuantumOracle/Model/ExactQueryGrowth.lean:40–47`. Classification: `definition`.

```lean
/-- The actual coherent query, tensored with the identity on an auxiliary register.
The reassociation keeps the full workspace on the left of the oracle register. -/
def liftedQuery (Aux : Type*) [Fintype Aux] (encode : BasisLookup.Encoding N w)
    (marked : Bool) :
    EuclideanSpace ℂ ((Aux × Args N w) × Perm N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Aux × Args N w) × Perm N) :=
  let R := Query.linearLift (Equiv.prodAssoc Aux (Args N w) (Perm N))
  R.trans ((BlockOperator.onRight Aux (query encode marked)).trans R.symm)
```

## `QuantumOracle/Model/ExtensionOperator.lean`

<a id="source-68"></a>
### `QuantumOracle.ExtensionOperator.Level`

Source: `QuantumOracle/Model/ExtensionOperator.lean:21–21`. Classification: `type`.

```lean
abbrev Level (N t : ℕ) := Database.level N t
```

<a id="source-69"></a>
### `QuantumOracle.ExtensionOperator.levelFintype`

Source: `QuantumOracle/Model/ExtensionOperator.lean:23–26`. Classification: `instance`.

```lean
noncomputable instance levelFintype (N t : ℕ) : Fintype (Level N t) := by
  classical
  unfold Level Database.level
  infer_instance
```

<a id="source-70"></a>
### `QuantumOracle.ExtensionOperator.matrix`

Source: `QuantumOracle/Model/ExtensionOperator.lean:31–33`. Classification: `definition`.

```lean
/-- Columns are the actual normalized consistent-permutation vectors. -/
def matrix (N t : ℕ) : Matrix (Perm N) (Level N t) ℂ :=
  fun π I => ConsistentState.vector I.val π
```

<a id="source-71"></a>
### `QuantumOracle.ExtensionOperator.T`

Source: `QuantumOracle/Model/ExtensionOperator.lean:35–38`. Classification: `definition`.

```lean
/-- The manuscript's `T_{N,t}` as a concrete complex linear map. -/
def T (N t : ℕ) :
    EuclideanSpace ℂ (Level N t) →ₗ[ℂ] EuclideanSpace ℂ (Perm N) :=
  (matrix N t).toEuclideanLin
```

## `QuantumOracle/Model/FinitePurification.lean`

<a id="source-72"></a>
### `QuantumOracle.FinitePurification.reducedFin`

Source: `QuantumOracle/Model/FinitePurification.lean:21–24`. Classification: `definition`.

```lean
/-- Actual workspace reduction, expressed in a numbered finite basis. -/
def reducedFin (ψ : EuclideanSpace ℂ (A × O)) : ReducedState (Fintype.card A) :=
  fun a b => HiddenIsometry.reduced ψ ((Fintype.equivFin A).symm a)
    ((Fintype.equivFin A).symm b)
```

<a id="source-73"></a>
### `QuantumOracle.FinitePurification.coordinateIsometry`

Source: `QuantumOracle/Model/FinitePurification.lean:26–30`. Classification: `definition`.

```lean
/-- A change of basis labels only, on both actual registers. -/
def coordinateIsometry (A O : Type*) [Fintype A] [Fintype O] :
    EuclideanSpace ℂ (A × O) ≃ₗᵢ[ℂ]
      PureState (Fintype.card A) (Fintype.card O) :=
  Query.linearLift (Equiv.prodCongr (Fintype.equivFin A) (Fintype.equivFin O))
```

<a id="source-74"></a>
### `QuantumOracle.FinitePurification.coordinateState`

Source: `QuantumOracle/Model/FinitePurification.lean:32–33`. Classification: `definition`.

```lean
def coordinateState (ψ : EuclideanSpace ℂ (A × O)) :
    PureState (Fintype.card A) (Fintype.card O) := coordinateIsometry A O ψ
```

## `QuantumOracle/Model/HarmonicLayers.lean`

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

## `QuantumOracle/Model/HiddenIsometry.lean`

<a id="source-76"></a>
### `QuantumOracle.HiddenIsometry.reduced`

Source: `QuantumOracle/Model/HiddenIsometry.lean:22–24`. Classification: `definition`.

```lean
/-- Finite partial trace over the hidden register, on any finite basis types. -/
def reduced (ψ : EuclideanSpace ℂ (A × O)) : Matrix A A ℂ :=
  fun a b => ∑ o : O, ψ (a, o) * star (ψ (b, o))
```

<a id="source-77"></a>
### `QuantumOracle.HiddenIsometry.onOracle`

Source: `QuantumOracle/Model/HiddenIsometry.lean:44–65`. Classification: `definition`.

```lean
/-- Apply an actual hidden-register isometry independently at each workspace coordinate. -/
def onOracle (A : Type*) [Fintype A]
    (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ P) :
    EuclideanSpace ℂ (A × O) →ₗᵢ[ℂ] EuclideanSpace ℂ (A × P) where
  toFun ψ := WithLp.toLp 2 (fun p => W (slice ψ p.1) p.2)
  map_add' ψ φ := by
    ext ⟨a, p⟩
    change W (slice (ψ + φ) a) p = W (slice ψ a) p + W (slice φ a) p
    rw [slice_add, map_add]
    rfl
  map_smul' c ψ := by
    ext ⟨a, p⟩
    change W (slice (c • ψ) a) p = c • W (slice ψ a) p
    rw [slice_smul, map_smul]
    rfl
  norm_map' ψ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_eq_sum_slices, norm_sq_eq_sum_slices]
    apply Finset.sum_congr rfl
    intro a _
    change ‖W (slice ψ a)‖ ^ 2 = ‖slice ψ a‖ ^ 2
    rw [W.norm_map]
```

## `QuantumOracle/Model/KnowledgeSpace.lean`

<a id="source-78"></a>
### `QuantumOracle.KnowledgeSpace.K`

Source: `QuantumOracle/Model/KnowledgeSpace.lean:21–23`. Classification: `definition`.

```lean
/-- The manuscript's span of size-t consistent-permutation states. -/
def K (N t : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Perm N)) :=
  Submodule.span ℂ (Set.range (fun I : ExtensionOperator.Level N t => vector I.val))
```

## `QuantumOracle/Model/LevelEmbedding.lean`

<a id="source-79"></a>
### `QuantumOracle.LevelEmbedding.embed`

Source: `QuantumOracle/Model/LevelEmbedding.lean:20–51`. Classification: `definition`.

```lean
/-- Actual zero padding from one database size to the full database register. -/
def embed (N t : ℕ) :
    EuclideanSpace ℂ (Level N t) →ₗᵢ[ℂ] EuclideanSpace ℂ (Database N) := by
  classical
  exact
    { toFun := fun v => WithLp.toLp 2
        (fun I => if hI : I.size = t then v ⟨I, hI⟩ else 0)
      map_add' := by
        intro v w
        ext I
        by_cases hI : I.size = t <;> simp [hI]
      map_smul' := by
        intro c v
        ext I
        by_cases hI : I.size = t <;> simp [hI]
      norm_map' := by
        intro v
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        rw [← Fintype.sum_subtype_add_sum_subtype (fun I : Database N => I.size = t)]
        have hpos : (∑ I : {I : Database N // I.size = t},
            ‖(if hI : I.val.size = t then v ⟨I.val, hI⟩ else 0)‖ ^ 2) =
            ∑ I : Level N t, ‖v I‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro I _
          simp [I.property]
        have hneg : (∑ I : {I : Database N // ¬ I.size = t},
            ‖(if hI : I.val.size = t then v ⟨I.val, hI⟩ else 0)‖ ^ 2) = 0 := by
          apply Finset.sum_eq_zero
          intro I _
          simp [I.property]
        exact (congrArg₂ (· + ·) hpos hneg).trans (add_zero _) }
```

## `QuantumOracle/Model/MatrixPolar.lean`

<a id="source-80"></a>
### `QuantumOracle.MatrixPolar.gramSqrt`

Source: `QuantumOracle/Model/MatrixPolar.lean:22–23`. Classification: `definition`.

```lean
/-- The canonical positive square root of the domain Gram matrix. -/
def gramSqrt (A : Matrix R C ℂ) : Matrix C C ℂ := CFC.sqrt (Aᴴ * A)
```

<a id="source-81"></a>
### `QuantumOracle.MatrixPolar.normalize`

Source: `QuantumOracle/Model/MatrixPolar.lean:25–26`. Classification: `definition`.

```lean
/-- Actual positive polar normalization, defined using the inverse square root. -/
def normalize (A : Matrix R C ℂ) : Matrix R C ℂ := A * (gramSqrt A)⁻¹
```

<a id="source-82"></a>
### `QuantumOracle.MatrixPolar.isometry`

Source: `QuantumOracle/Model/MatrixPolar.lean:105–108`. Classification: `definition`.

```lean
/-- The bundled Euclidean isometry is exactly the positive polar matrix. -/
def isometry (A : Matrix R C ℂ) (hA : Function.Injective A.mulVec) :
    EuclideanSpace ℂ C →ₗᵢ[ℂ] EuclideanSpace ℂ R :=
  (normalize A).toEuclideanLin.isometryOfInner (normalize_inner A hA)
```

## `QuantumOracle/Model/OrthonormalSwap.lean`

<a id="source-83"></a>
### `QuantumOracle.orthonormalSwap`

Source: `QuantumOracle/Model/OrthonormalSwap.lean:19–22`. Classification: `definition`.

```lean
/-- Reflection in the hyperplane perpendicular to `e - u`.
No unproved isometry hypothesis is part of this definition. -/
def orthonormalSwap (e u : E) : E ≃ₗᵢ[ℂ] E :=
  (ℂ ∙ (e - u))ᗮ.reflection
```

## `QuantumOracle/Model/OutputDiscard.lean`

<a id="source-84"></a>
### `QuantumOracle.OutputDiscard.discardIsometry`

Source: `QuantumOracle/Model/OutputDiscard.lean:19–22`. Classification: `definition`.

```lean
/-- Reassociate an actual workspace factor into the hidden register. -/
def discardIsometry (e : A ≃ B × D) :
    EuclideanSpace ℂ (A × O) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (B × (D × O)) :=
  Query.linearLift ((Equiv.prodCongr e (Equiv.refl O)).trans (Equiv.prodAssoc B D O))
```

<a id="source-85"></a>
### `QuantumOracle.OutputDiscard.discardVector`

Source: `QuantumOracle/Model/OutputDiscard.lean:24–25`. Classification: `definition`.

```lean
def discardVector (e : A ≃ B × D) (ψ : EuclideanSpace ℂ (A × O)) :
    EuclideanSpace ℂ (B × (D × O)) := discardIsometry e ψ
```

## `QuantumOracle/Model/OutputExperiment.lean`

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

<a id="source-87"></a>
### `QuantumOracle.OutputExperiment.exactVector`

Source: `QuantumOracle/Model/OutputExperiment.lean:46–48`. Classification: `definition`.

```lean
def exactVector (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    EuclideanSpace ℂ (a.Output × (a.Discard × Perm N)) :=
  discardVector a.split (ConcreteExperiment.exactVector encode a.base)
```

<a id="source-88"></a>
### `QuantumOracle.OutputExperiment.compressedVector`

Source: `QuantumOracle/Model/OutputExperiment.lean:50–52`. Classification: `definition`.

```lean
def compressedVector (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    EuclideanSpace ℂ (a.Output × (a.Discard × Database N)) :=
  discardVector a.split (ConcreteExperiment.compressedVector encode a.base)
```

<a id="source-89"></a>
### `QuantumOracle.OutputExperiment.exactFinal`

Source: `QuantumOracle/Model/OutputExperiment.lean:62–63`. Classification: `definition`.

```lean
def exactFinal (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    ReducedState (Fintype.card a.Output) := reducedFin (exactVector encode a)
```

<a id="source-90"></a>
### `QuantumOracle.OutputExperiment.compressedFinal`

Source: `QuantumOracle/Model/OutputExperiment.lean:65–66`. Classification: `definition`.

```lean
def compressedFinal (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    ReducedState (Fintype.card a.Output) := reducedFin (compressedVector encode a)
```

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

<a id="source-92"></a>
### `QuantumOracle.OutputExperiment.Dist`

Source: `QuantumOracle/Model/OutputExperiment.lean:121–122`. Classification: `definition`.

```lean
/-- The supremum now also ranges over all finite final output decompositions. -/
def Dist (encode : BasisLookup.Encoding N w) (q : ℕ) : ℝ := (family encode).Dist q
```

## `QuantumOracle/Model/PermutationExtensions.lean`

<a id="source-93"></a>
### `QuantumOracle.PermutationExtensions.Perm`

Source: `QuantumOracle/Model/PermutationExtensions.lean:11–11`. Classification: `type`.

```lean
abbrev Perm (N : ℕ) := Equiv.Perm (Fin N)
```

<a id="source-94"></a>
### `QuantumOracle.PermutationExtensions.Extends`

Source: `QuantumOracle/Model/PermutationExtensions.lean:15–17`. Classification: `type`.

```lean
/-- A genuine permutation agrees with every recorded edge of the database. -/
def Extends (I : Database N) (π : Perm N) : Prop :=
  ∀ x y, (x, y) ∈ I.edges → π x = y
```

## `QuantumOracle/Model/PolarEmbedding.lean`

<a id="source-95"></a>
### `QuantumOracle.PolarEmbedding.matrix`

Source: `QuantumOracle/Model/PolarEmbedding.lean:25–27`. Classification: `definition`.

```lean
/-- The matrix of the actual assembled degree map in the Euclidean bases. -/
def matrix (N : ℕ) : Matrix (Database N) (Perm N) ℂ :=
  Matrix.toEuclideanLin.symm (RawEmbedding.total N)
```

<a id="source-96"></a>
### `QuantumOracle.PolarEmbedding.candidate`

Source: `QuantumOracle/Model/PolarEmbedding.lean:49–52`. Classification: `definition`.

```lean
/-- Canonical positive polar normalization of the actual assembled map. -/
def candidate (N : ℕ) :
    EuclideanSpace ℂ (Perm N) →ₗᵢ[ℂ] Compression.State N :=
  MatrixPolar.isometry (matrix N) (matrix_mulVec_injective N)
```

## `QuantumOracle/Model/ProjectorPurification.lean`

<a id="source-97"></a>
### `QuantumOracle.ProjectorPurification.project`

Source: `QuantumOracle/Model/ProjectorPurification.lean:26–29`. Classification: `definition`.

```lean
/-- Lift the output's Hilbert orthogonal projection to the actual joint vector. -/
def project (P : Submodule ℂ (EuclideanSpace ℂ (Fin d))) :
    PureState d n →ₗ[ℂ] PureState d n :=
  onWorkspace (Fin n) P.starProjection.toLinearMap
```

## `QuantumOracle/Model/PurificationDistance.lean`

<a id="source-98"></a>
### `QuantumOracle.PureState`

Source: `QuantumOracle/Model/PurificationDistance.lean:19–19`. Classification: `type`.

```lean
abbrev PureState (d n : ℕ) := EuclideanSpace ℂ (Fin d × Fin n)
```

<a id="source-99"></a>
### `QuantumOracle.ReducedState`

Source: `QuantumOracle/Model/PurificationDistance.lean:20–20`. Classification: `type`.

```lean
abbrev ReducedState (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
```

<a id="source-100"></a>
### `QuantumOracle.reducedState`

Source: `QuantumOracle/Model/PurificationDistance.lean:22–24`. Classification: `definition`.

```lean
/-- Partial trace of the rank-one matrix `|ψ⟩⟨ψ|` over the common ancilla. -/
def reducedState {d n : ℕ} (ψ : PureState d n) : ReducedState d :=
  fun i j => ∑ a : Fin n, ψ (i, a) * star (ψ (j, a))
```

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

<a id="source-102"></a>
### `QuantumOracle.CommonPurification.distance`

Source: `QuantumOracle/Model/PurificationDistance.lean:37–39`. Classification: `definition`.

```lean
def CommonPurification.distance {d : ℕ} {ρ σ : ReducedState d}
    (p : CommonPurification ρ σ) : ℝ :=
  ‖p.exactVector - p.compressedVector‖
```

<a id="source-103"></a>
### `QuantumOracle.purificationDistance`

Source: `QuantumOracle/Model/PurificationDistance.lean:50–52`. Classification: `definition`.

```lean
/-- The infimum is over purifications, and is independent of any proposed bound. -/
def purificationDistance {d : ℕ} (ρ σ : ReducedState d) : ℝ :=
  sInf (Set.range (CommonPurification.distance (ρ := ρ) (σ := σ)))
```

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

## `QuantumOracle/Model/Query.lean`

<a id="source-106"></a>
### `QuantumOracle.Query.linearLift`

Source: `QuantumOracle/Model/Query.lean:21–25`. Classification: `definition`.

```lean
/-- A basis reindexing extended linearly to the finite complex Hilbert space.
The direction is `|i⟩ ↦ |e i⟩`, proved by `linearLift_single`. -/
def linearLift {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ β :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
```

<a id="source-107"></a>
### `QuantumOracle.Query.ordinaryLookup`

Source: `QuantumOracle/Model/Query.lean:46–50`. Classification: `definition`.

```lean
/-- Ordinary extended database lookup `P_x`, as a genuine Hilbert-space map. -/
def ordinaryLookup (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ (Bits w × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Bits w × Database N) :=
  linearLift (BasisLookup.ordinary encode x)
```

<a id="source-108"></a>
### `QuantumOracle.Query.markedLookup`

Source: `QuantumOracle/Model/Query.lean:52–56`. Classification: `definition`.

```lean
/-- Marked lookup shifts both marker and output bits, for arbitrary inputs. -/
def markedLookup (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ ((Bool × Bits w) × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Bool × Bits w) × Database N) :=
  linearLift (BasisLookup.marked encode x)
```

<a id="source-109"></a>
### `QuantumOracle.Query.registerBasis`

Source: `QuantumOracle/Model/Query.lean:100–106`. Classification: `definition`.

```lean
/-- A read-only oracle register controls a reversible answer-register operation. -/
def registerBasis {R Y : Type*} (action : R → Equiv.Perm Y) :
    Equiv.Perm (Y × R) where
  toFun := fun yr => (action yr.2 yr.1, yr.2)
  invFun := fun yr => ((action yr.2).symm yr.1, yr.2)
  left_inv := by rintro ⟨y, r⟩; simp
  right_inv := by rintro ⟨y, r⟩; simp
```

<a id="source-110"></a>
### `QuantumOracle.Query.permutationAnswer`

Source: `QuantumOracle/Model/Query.lean:112–114`. Classification: `definition`.

```lean
/-- `false` is the forward direction; `true` is inverse. -/
def permutationAnswer (inverse : Bool) (π : Equiv.Perm (Fin N)) (x : Fin N) : Fin N :=
  if inverse then π.symm x else π x
```

<a id="source-111"></a>
### `QuantumOracle.Query.indexedBasis`

Source: `QuantumOracle/Model/Query.lean:182–188`. Classification: `definition`.

```lean
/-- Coherent selection of point, direction, or both. The index remains intact. -/
def indexedBasis {C Y : Type*} (action : C → Equiv.Perm Y) :
    Equiv.Perm (C × Y) where
  toFun := fun cy => (cy.1, action cy.1 cy.2)
  invFun := fun cy => (cy.1, (action cy.1).symm cy.2)
  left_inv := by rintro ⟨c, y⟩; simp
  right_inv := by rintro ⟨c, y⟩; simp
```

## `QuantumOracle/Model/RawEmbedding.lean`

<a id="source-112"></a>
### `QuantumOracle.RawEmbedding.total`

Source: `QuantumOracle/Model/RawEmbedding.lean:24–26`. Classification: `definition`.

```lean
/-- Assemble all actual degree components into their physical database levels. -/
def total (N : ℕ) : EuclideanSpace ℂ (Perm N) →ₗ[ℂ] Compression.State N :=
  ∑ i : Fin (N + 1), (raw N i.val).comp (H N i.val).starProjection.toLinearMap
```

## `QuantumOracle/Model/RawHarmonic.lean`

<a id="source-113"></a>
### `QuantumOracle.RawHarmonic.raw`

Source: `QuantumOracle/Model/RawHarmonic.lean:24–27`. Classification: `definition`.

```lean
/-- The actual extension adjoint, placed at its exact physical database size. -/
def raw (N t : ℕ) :
    EuclideanSpace ℂ (Perm N) →ₗ[ℂ] Compression.State N :=
  (LevelEmbedding.embed N t).toLinearMap.comp (T N t).adjoint
```

## `QuantumOracle/Model/SoundnessPurification.lean`

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

## `QuantumOracle/Model/UniformState.lean`

<a id="source-115"></a>
### `QuantumOracle.UniformState.amplitude`

Source: `QuantumOracle/Model/UniformState.lean:19–21`. Classification: `definition`.

```lean
/-- The common real amplitude of a uniform state on a finite set. -/
def amplitude (α : Type*) [Fintype α] : ℝ :=
  (Real.sqrt (Fintype.card α : ℝ))⁻¹
```

<a id="source-116"></a>
### `QuantumOracle.UniformState.emptyKet`

Source: `QuantumOracle/Model/UniformState.lean:46–49`. Classification: `definition`.

```lean
/-- The empty database basis vector in a local extension block. -/
def emptyKet (α : Type*) [Fintype α] : EuclideanSpace ℂ (Option α) := by
  classical
  exact EuclideanSpace.single none 1
```

<a id="source-117"></a>
### `QuantumOracle.UniformState.extensionUniform`

Source: `QuantumOracle/Model/UniformState.lean:64–66`. Classification: `definition`.

```lean
/-- Uniform vector on the extensions, with zero empty-database amplitude. -/
def extensionUniform (α : Type*) [Fintype α] : EuclideanSpace ℂ (Option α) :=
  WithLp.toLp 2 (fun a => a.elim 0 (fun _ => (amplitude α : ℂ)))
```

## `QuantumOracle/Model/WorkspaceKnowledge.lean`

<a id="source-118"></a>
### `QuantumOracle.WorkspaceKnowledge.slice`

Source: `QuantumOracle/Model/WorkspaceKnowledge.lean:19–21`. Classification: `definition`.

```lean
/-- Oracle vector at one workspace coordinate. -/
def slice (ψ : EuclideanSpace ℂ (A × O)) (a : A) : EuclideanSpace ℂ O :=
  WithLp.toLp 2 (fun o => ψ (a, o))
```

<a id="source-119"></a>
### `QuantumOracle.WorkspaceKnowledge.onWorkspace`

Source: `QuantumOracle/Model/WorkspaceKnowledge.lean:83–98`. Classification: `definition`.

```lean
/-- Apply `U` to the workspace at each unchanged oracle coordinate. -/
def onWorkspace (O : Type*) [Fintype O]
    (U : EuclideanSpace ℂ A →ₗ[ℂ] EuclideanSpace ℂ A) :
    EuclideanSpace ℂ (A × O) →ₗ[ℂ] EuclideanSpace ℂ (A × O) where
  toFun ψ := WithLp.toLp 2 (fun p => U (WithLp.toLp 2 (fun a => ψ (a, p.2))) p.1)
  map_add' ψ φ := by
    ext ⟨a, o⟩
    change U ((WithLp.toLp 2 (fun b => ψ (b, o))) +
      (WithLp.toLp 2 (fun b => φ (b, o)))) a = _
    rw [map_add]
    rfl
  map_smul' c ψ := by
    ext ⟨a, o⟩
    change U (c • (WithLp.toLp 2 (fun b => ψ (b, o)))) a = _
    rw [map_smul]
    rfl
```

## Propositions of proof obligations

The following are printed types from the extraction, with proof bodies omitted. They are reading material, not Lean declarations introducing new assumptions.
The compiled implementation supplies proofs of these propositions. The final theorem is also included in this list.

### `QuantumOracle.BasisLookup.bitXorPerm._proof_1`

```text
∀ (a z : Bool), (z ^^ a ^^ a) = z
```

### `QuantumOracle.BasisLookup.controlled._proof_1`

```text
∀ {Y : Type u_1} (e : Equiv.Perm Y) (x : Bool × Y),
  ((x.1, if x.1 = true then e x.2 else x.2).1,
      if (x.1, if x.1 = true then e x.2 else x.2).1 = true then
        (Equiv.symm e) (x.1, if x.1 = true then e x.2 else x.2).2
      else (x.1, if x.1 = true then e x.2 else x.2).2) =
    x
```

### `QuantumOracle.BasisLookup.controlled._proof_2`

```text
∀ {Y : Type u_1} (e : Equiv.Perm Y) (x : Bool × Y),
  ((x.1, if x.1 = true then (Equiv.symm e) x.2 else x.2).1,
      if (x.1, if x.1 = true then (Equiv.symm e) x.2 else x.2).1 = true then
        e (x.1, if x.1 = true then (Equiv.symm e) x.2 else x.2).2
      else (x.1, if x.1 = true then (Equiv.symm e) x.2 else x.2).2) =
    x
```

### `QuantumOracle.BasisLookup.flip._proof_1`

```text
∀ {N : ℕ} {Y : Type u_1} (zI : Y × QuantumOracle.Database N),
  ((zI.1, zI.2.inverse).1, (zI.1, zI.2.inverse).2.inverse) = zI
```

### `QuantumOracle.BasisLookup.liftLookup._proof_1`

```text
∀ {N : ℕ} {Y : Type u_1} (action : QuantumOracle.Database N → Equiv.Perm Y) (x : Y × QuantumOracle.Database N),
  ((Equiv.symm (action ((action x.2) x.1, x.2).2)) ((action x.2) x.1, x.2).1, ((action x.2) x.1, x.2).2) = x
```

### `QuantumOracle.BasisLookup.liftLookup._proof_2`

```text
∀ {N : ℕ} {Y : Type u_1} (action : QuantumOracle.Database N → Equiv.Perm Y) (x : Y × QuantumOracle.Database N),
  ((action ((Equiv.symm (action x.2)) x.1, x.2).2) ((Equiv.symm (action x.2)) x.1, x.2).1,
      ((Equiv.symm (action x.2)) x.1, x.2).2) =
    x
```

### `QuantumOracle.BasisLookup.xor_twice`

```text
∀ {w : ℕ} (z a : QuantumOracle.BasisLookup.Bits w),
  QuantumOracle.BasisLookup.xor (QuantumOracle.BasisLookup.xor z a) a = z
```

### `QuantumOracle.BlockOperator.diagonal._proof_1`

```text
RingHomCompTriple (RingHom.id ℂ) (RingHom.id ℂ) (RingHom.id ℂ)
```

### `QuantumOracle.BlockOperator.restrict._proof_1`

```text
(1 + 1).AtLeastTwo
```

### `QuantumOracle.BlockSupport.inverseState._proof_1`

```text
(1 + 1).AtLeastTwo
```

### `QuantumOracle.CompressedCoherentQuery.controlsEquiv._proof_1`

```text
∀ {N w : ℕ} (x : QuantumOracle.ExactCoherentQuery.Args N w × QuantumOracle.Database N),
  ((((x.1.1, x.1.2.1), x.1.2.2, x.2).1.1, ((x.1.1, x.1.2.1), x.1.2.2, x.2).1.2, ((x.1.1, x.1.2.1), x.1.2.2, x.2).2.1),
      ((x.1.1, x.1.2.1), x.1.2.2, x.2).2.2) =
    ((((x.1.1, x.1.2.1), x.1.2.2, x.2).1.1, ((x.1.1, x.1.2.1), x.1.2.2, x.2).1.2, ((x.1.1, x.1.2.1), x.1.2.2, x.2).2.1),
      ((x.1.1, x.1.2.1), x.1.2.2, x.2).2.2)
```

### `QuantumOracle.CompressedCoherentQuery.controlsEquiv._proof_2`

```text
∀ {N w : ℕ} (x : (Bool × Bool × Fin N) × (Bool × QuantumOracle.BasisLookup.Bits w) × QuantumOracle.Database N),
  ((((x.1.1, x.1.2, x.2.1), x.2.2).1.1, ((x.1.1, x.1.2, x.2.1), x.2.2).1.2.1), ((x.1.1, x.1.2, x.2.1), x.2.2).1.2.2,
      ((x.1.1, x.1.2, x.2.1), x.2.2).2) =
    ((((x.1.1, x.1.2, x.2.1), x.2.2).1.1, ((x.1.1, x.1.2, x.2.1), x.2.2).1.2.1), ((x.1.1, x.1.2, x.2.1), x.2.2).1.2.2,
      ((x.1.1, x.1.2, x.2.1), x.2.2).2)
```

### `QuantumOracle.CompressedCoherentQuery.ordinaryWithMarker._proof_1`

```text
RingHomCompTriple (RingHom.id ℂ) (RingHom.id ℂ) (RingHom.id ℂ)
```

### `QuantumOracle.CompressedQuery.ordinary._proof_1`

```text
RingHomCompTriple (RingHom.id ℂ) (RingHom.id ℂ) (RingHom.id ℂ)
```

### `QuantumOracle.CompressionIndex.baseFintype._proof_1`

```text
∀ {N : ℕ} (x : Fin N), Finite { x_1 // x ∉ x_1.domain }
```

### `QuantumOracle.CompressionIndex.databaseEquiv._proof_1`

```text
∀ {N : ℕ} (x : Fin N),
  Function.Injective (QuantumOracle.CompressionIndex.decode x) ∧
    Function.Surjective (QuantumOracle.CompressionIndex.decode x)
```

### `QuantumOracle.CompressionIndex.freshFintype._proof_1`

```text
∀ {N : ℕ} (J : QuantumOracle.Database N), Finite { x // x ∉ J.image }
```

### `QuantumOracle.ConsistentState.vector._proof_1`

```text
(1 + 1).AtLeastTwo
```

### `QuantumOracle.Database.empty._proof_1`

```text
∀ {N : ℕ} (a a_1 : Fin N × Fin N), a ∈ ∅ → a_1 ∈ ∅ → a.1 = a_1.1 → a.2 = a_1.2
```

### `QuantumOracle.Database.empty._proof_2`

```text
∀ {N : ℕ} (a a_1 : Fin N × Fin N), a ∈ ∅ → a_1 ∈ ∅ → a.2 = a_1.2 → a.1 = a_1.1
```

### `QuantumOracle.Database.instFinite`

```text
∀ {N : ℕ}, Finite (QuantumOracle.Database N)
```

### `QuantumOracle.Database.inverse._proof_1`

```text
∀ {N : ℕ} (I : QuantumOracle.Database N) ⦃e f : Fin N × Fin N⦄,
  e ∈ Finset.image Prod.swap I.edges → f ∈ Finset.image Prod.swap I.edges → e.1 = f.1 → e.2 = f.2
```

### `QuantumOracle.Database.inverse._proof_2`

```text
∀ {N : ℕ} (I : QuantumOracle.Database N) ⦃e f : Fin N × Fin N⦄,
  e ∈ Finset.image Prod.swap I.edges → f ∈ Finset.image Prod.swap I.edges → e.2 = f.2 → e.1 = f.1
```

### `QuantumOracle.Database.set._proof_1`

```text
∀ {N : ℕ} (I : QuantumOracle.Database N) (x y : Fin N) ⦃e f : Fin N × Fin N⦄,
  e ∈ insert (x, y) ({e ∈ I.edges | e.1 ≠ x ∧ e.2 ≠ y}) →
    f ∈ insert (x, y) ({e ∈ I.edges | e.1 ≠ x ∧ e.2 ≠ y}) → e.1 = f.1 → e.2 = f.2
```

### `QuantumOracle.Database.set._proof_2`

```text
∀ {N : ℕ} (I : QuantumOracle.Database N) (x y : Fin N) ⦃e f : Fin N × Fin N⦄,
  e ∈ insert (x, y) ({e ∈ I.edges | e.1 ≠ x ∧ e.2 ≠ y}) →
    f ∈ insert (x, y) ({e ∈ I.edges | e.1 ≠ x ∧ e.2 ≠ y}) → e.2 = f.2 → e.1 = f.1
```

### `QuantumOracle.ExactExecution.initial._proof_1`

```text
(1 + 1).AtLeastTwo
```

### `QuantumOracle.ExactQueryGrowth.liftedQuery._proof_1`

```text
RingHomCompTriple (RingHom.id ℂ) (RingHom.id ℂ) (RingHom.id ℂ)
```

### `QuantumOracle.ExtensionOperator.T._proof_1`

```text
RingHomInvPair (RingHom.id ℂ) (RingHom.id ℂ)
```

### `QuantumOracle.ExtensionOperator.T._proof_2`

```text
∀ (N : ℕ), SMulCommClass ℂ ℂ (WithLp 2 (QuantumOracle.PermutationExtensions.Perm N → ℂ))
```

### `QuantumOracle.FiniteSoundnessWitness.outputPurification._proof_1`

```text
∀ {N w : ℕ} (encode : QuantumOracle.BasisLookup.Encoding N w) (a : QuantumOracle.OutputExperiment.Algorithm N w),
  ‖QuantumOracle.FinitePurification.coordinateState
        (QuantumOracle.OutputDiscard.discardVector a.split
          ((QuantumOracle.HiddenIsometry.onOracle a.base.Workspace (QuantumOracle.PolarEmbedding.candidate N))
            (QuantumOracle.ConcreteExperiment.exactVector encode a.base)))‖ =
    1
```

### `QuantumOracle.FiniteSoundnessWitness.outputPurification._proof_2`

```text
∀ {N w : ℕ} (encode : QuantumOracle.BasisLookup.Encoding N w) (a : QuantumOracle.OutputExperiment.Algorithm N w),
  ‖QuantumOracle.FinitePurification.coordinateState (QuantumOracle.OutputExperiment.compressedVector encode a)‖ = 1
```

### `QuantumOracle.FiniteSoundnessWitness.outputPurification._proof_3`

```text
∀ {N w : ℕ} (encode : QuantumOracle.BasisLookup.Encoding N w) (a : QuantumOracle.OutputExperiment.Algorithm N w),
  QuantumOracle.reducedState
      (QuantumOracle.FinitePurification.coordinateState
        (QuantumOracle.OutputDiscard.discardVector a.split
          ((QuantumOracle.HiddenIsometry.onOracle a.base.Workspace (QuantumOracle.PolarEmbedding.candidate N))
            (QuantumOracle.ConcreteExperiment.exactVector encode a.base)))) =
    QuantumOracle.OutputExperiment.exactFinal encode a
```

### `QuantumOracle.FiniteSoundnessWitness.outputPurification._proof_4`

```text
∀ {N w : ℕ} (encode : QuantumOracle.BasisLookup.Encoding N w) (a : QuantumOracle.OutputExperiment.Algorithm N w),
  QuantumOracle.reducedState
      (QuantumOracle.FinitePurification.coordinateState (QuantumOracle.OutputExperiment.compressedVector encode a)) =
    QuantumOracle.FinitePurification.reducedFin (QuantumOracle.OutputExperiment.compressedVector encode a)
```

### `QuantumOracle.HiddenIsometry.onOracle._proof_1`

```text
(1 + 1).AtLeastTwo
```

### `QuantumOracle.HiddenIsometry.onOracle._proof_2`

```text
∀ {O : Type u_1} {P : Type u_3} [inst : Fintype O] [inst_1 : Fintype P] (A : Type u_2) [inst_2 : Fintype A]
  (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ P) (ψ φ : EuclideanSpace ℂ (A × O)),
  (WithLp.toLp 2 fun p => (W (QuantumOracle.WorkspaceKnowledge.slice (ψ + φ) p.1)).ofLp p.2) =
    (WithLp.toLp 2 fun p => (W (QuantumOracle.WorkspaceKnowledge.slice ψ p.1)).ofLp p.2) +
      WithLp.toLp 2 fun p => (W (QuantumOracle.WorkspaceKnowledge.slice φ p.1)).ofLp p.2
```

### `QuantumOracle.HiddenIsometry.onOracle._proof_3`

```text
∀ {O : Type u_1} {P : Type u_3} [inst : Fintype O] [inst_1 : Fintype P] (A : Type u_2) [inst_2 : Fintype A]
  (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ P) (c : ℂ) (ψ : EuclideanSpace ℂ (A × O)),
  (WithLp.toLp 2 fun p => (W (QuantumOracle.WorkspaceKnowledge.slice (c • ψ) p.1)).ofLp p.2) =
    (RingHom.id ℂ) c • WithLp.toLp 2 fun p => (W (QuantumOracle.WorkspaceKnowledge.slice ψ p.1)).ofLp p.2
```

### `QuantumOracle.HiddenIsometry.onOracle._proof_4`

```text
∀ {O : Type u_1} {P : Type u_3} [inst : Fintype O] [inst_1 : Fintype P] (A : Type u_2) [inst_2 : Fintype A]
  (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ P) (ψ : EuclideanSpace ℂ (A × O)),
  ‖{ toFun := fun ψ => WithLp.toLp 2 fun p => (W (QuantumOracle.WorkspaceKnowledge.slice ψ p.1)).ofLp p.2,
          map_add' := ⋯, map_smul' := ⋯ }
        ψ‖ =
    ‖ψ‖
```

### `QuantumOracle.ImprovedSoundness.soundness`

```text
∀ {N w : ℕ} (encode : QuantumOracle.BasisLookup.Encoding N w),
  0 < N →
    ∀ (q : ℕ),
      4 * q ≤ N →
        ∀ (a : QuantumOracle.OutputExperiment.Algorithm N w),
          a.base.queries ≤ q →
            have p := QuantumOracle.FiniteSoundnessWitness.outputPurification encode a;
            p.distance ≤ 4 * ↑q / √↑N ∧
              QuantumOracle.OutputExperiment.Dist encode q ≤ 4 * ↑q / √↑N ∧
                ∀ (P : Submodule ℂ (EuclideanSpace ℂ (Fin (Fintype.card a.Output)))),
                  |‖(QuantumOracle.ProjectorPurification.project P) p.exactVector‖ -
                        ‖(QuantumOracle.ProjectorPurification.project P) p.compressedVector‖| ≤
                    QuantumOracle.OutputExperiment.Dist encode q
```

### `QuantumOracle.LevelEmbedding.embed._proof_1`

```text
(1 + 1).AtLeastTwo
```

### `QuantumOracle.LevelEmbedding.embed._proof_2`

```text
∀ (N t : ℕ) (v w : EuclideanSpace ℂ (QuantumOracle.ExtensionOperator.Level N t)),
  (WithLp.toLp 2 fun I => if hI : I.size = t then (v + w).ofLp ⟨I, hI⟩ else 0) =
    (WithLp.toLp 2 fun I => if hI : I.size = t then v.ofLp ⟨I, hI⟩ else 0) +
      WithLp.toLp 2 fun I => if hI : I.size = t then w.ofLp ⟨I, hI⟩ else 0
```

### `QuantumOracle.LevelEmbedding.embed._proof_3`

```text
∀ (N t : ℕ) (c : ℂ) (v : EuclideanSpace ℂ (QuantumOracle.ExtensionOperator.Level N t)),
  (WithLp.toLp 2 fun I => if hI : I.size = t then (c • v).ofLp ⟨I, hI⟩ else 0) =
    (RingHom.id ℂ) c • WithLp.toLp 2 fun I => if hI : I.size = t then v.ofLp ⟨I, hI⟩ else 0
```

### `QuantumOracle.LevelEmbedding.embed._proof_4`

```text
∀ (N t : ℕ) (v : EuclideanSpace ℂ (QuantumOracle.ExtensionOperator.Level N t)),
  ‖{ toFun := fun v => WithLp.toLp 2 fun I => if hI : I.size = t then v.ofLp ⟨I, hI⟩ else 0, map_add' := ⋯,
          map_smul' := ⋯ }
        v‖ =
    ‖v‖
```

### `QuantumOracle.MatrixPolar.gramSqrt._proof_1`

```text
∀ {C : Type u_1} [inst : Fintype C] [inst_1 : DecidableEq C], SMulCommClass ℝ (Matrix C C ℂ) (Matrix C C ℂ)
```

### `QuantumOracle.MatrixPolar.gramSqrt._proof_2`

```text
∀ {C : Type u_1} [inst : Fintype C] [inst_1 : DecidableEq C], IsScalarTower ℝ (Matrix C C ℂ) (Matrix C C ℂ)
```

### `QuantumOracle.MatrixPolar.gramSqrt._proof_3`

```text
Nontrivial ℝ
```

### `QuantumOracle.MatrixPolar.gramSqrt._proof_4`

```text
IsTopologicalSemiring ℝ
```

### `QuantumOracle.MatrixPolar.gramSqrt._proof_5`

```text
∀ {C : Type u_1} [inst : Fintype C] [inst_1 : DecidableEq C], IsScalarTower ℝ (Matrix C C ℂ) (Matrix C C ℂ)
```

### `QuantumOracle.MatrixPolar.gramSqrt._proof_6`

```text
∀ {C : Type u_1} [inst : Fintype C] [inst_1 : DecidableEq C], SMulCommClass ℝ (Matrix C C ℂ) (Matrix C C ℂ)
```

### `QuantumOracle.MatrixPolar.gramSqrt._proof_7`

```text
∀ {C : Type u_1} [inst : Fintype C] [inst_1 : DecidableEq C],
  NonUnitalContinuousFunctionalCalculus ℝ (Matrix C C ℂ) IsSelfAdjoint
```

### `QuantumOracle.MatrixPolar.isometry._proof_1`

```text
RingHomInvPair (RingHom.id ℂ) (RingHom.id ℂ)
```

### `QuantumOracle.MatrixPolar.isometry._proof_2`

```text
∀ {R : Type u_1}, SMulCommClass ℂ ℂ (WithLp 2 (R → ℂ))
```

### `QuantumOracle.MatrixPolar.normalize_inner`

```text
∀ {R : Type u_1} {C : Type u_2} [inst : Fintype R] [inst_1 : Fintype C] [inst_2 : DecidableEq C] [DecidableEq R]
  (A : Matrix R C ℂ),
  Function.Injective A.mulVec →
    ∀ (v z : EuclideanSpace ℂ C),
      inner ℂ ((Matrix.toEuclideanLin (QuantumOracle.MatrixPolar.normalize A)) v)
          ((Matrix.toEuclideanLin (QuantumOracle.MatrixPolar.normalize A)) z) =
        inner ℂ v z
```

### `QuantumOracle.OutputExperiment.family._proof_1`

```text
∀ {N w : ℕ} (encode : QuantumOracle.BasisLookup.Encoding N w) (a : QuantumOracle.OutputExperiment.Algorithm N w),
  Nonempty
    (QuantumOracle.CommonPurification (QuantumOracle.OutputExperiment.exactFinal encode a)
      (QuantumOracle.OutputExperiment.compressedFinal encode a))
```

### `QuantumOracle.PolarEmbedding.matrix._proof_1`

```text
RingHomInvPair (RingHom.id ℂ) (RingHom.id ℂ)
```

### `QuantumOracle.PolarEmbedding.matrix._proof_2`

```text
∀ (N : ℕ), SMulCommClass ℂ ℂ (WithLp 2 (QuantumOracle.Database N → ℂ))
```

### `QuantumOracle.PolarEmbedding.matrix_mulVec_injective`

```text
∀ (N : ℕ), Function.Injective (QuantumOracle.PolarEmbedding.matrix N).mulVec
```

### `QuantumOracle.ProjectorPurification.project._proof_1`

```text
∀ {d : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin d))), P.HasOrthogonalProjection
```

### `QuantumOracle.Query.indexedBasis._proof_1`

```text
∀ {C : Type u_1} {Y : Type u_2} (action : C → Equiv.Perm Y) (x : C × Y),
  ((x.1, (action x.1) x.2).1, (Equiv.symm (action (x.1, (action x.1) x.2).1)) (x.1, (action x.1) x.2).2) = x
```

### `QuantumOracle.Query.indexedBasis._proof_2`

```text
∀ {C : Type u_1} {Y : Type u_2} (action : C → Equiv.Perm Y) (x : C × Y),
  ((x.1, (Equiv.symm (action x.1)) x.2).1,
      (action (x.1, (Equiv.symm (action x.1)) x.2).1) (x.1, (Equiv.symm (action x.1)) x.2).2) =
    x
```

### `QuantumOracle.Query.linearLift._proof_1`

```text
(1 + 1).AtLeastTwo
```

### `QuantumOracle.Query.registerBasis._proof_1`

```text
∀ {R : Type u_2} {Y : Type u_1} (action : R → Equiv.Perm Y) (x : Y × R),
  ((Equiv.symm (action ((action x.2) x.1, x.2).2)) ((action x.2) x.1, x.2).1, ((action x.2) x.1, x.2).2) = x
```

### `QuantumOracle.Query.registerBasis._proof_2`

```text
∀ {R : Type u_2} {Y : Type u_1} (action : R → Equiv.Perm Y) (x : Y × R),
  ((action ((Equiv.symm (action x.2)) x.1, x.2).2) ((Equiv.symm (action x.2)) x.1, x.2).1,
      ((Equiv.symm (action x.2)) x.1, x.2).2) =
    x
```

### `QuantumOracle.RawEmbedding.total._proof_1`

```text
RingHomCompTriple (RingHom.id ℂ) (RingHom.id ℂ) (RingHom.id ℂ)
```

### `QuantumOracle.RawEmbedding.total._proof_2`

```text
∀ (N : ℕ) (i : Fin (N + 1)), (QuantumOracle.HarmonicLayers.H N ↑i).HasOrthogonalProjection
```

### `QuantumOracle.RawHarmonic.raw._proof_1`

```text
RingHomCompTriple (RingHom.id ℂ) (RingHom.id ℂ) (RingHom.id ℂ)
```

### `QuantumOracle.RawHarmonic.raw._proof_2`

```text
RingHomInvPair (starRingEnd ℂ) (starRingEnd ℂ)
```

### `QuantumOracle.RawHarmonic.raw._proof_3`

```text
∀ (N : ℕ), SMulCommClass ℂ ℂ (EuclideanSpace ℂ (QuantumOracle.PermutationExtensions.Perm N))
```

### `QuantumOracle.RawHarmonic.raw._proof_4`

```text
∀ (N t : ℕ), SMulCommClass ℂ ℂ (EuclideanSpace ℂ (QuantumOracle.ExtensionOperator.Level N t))
```

### `QuantumOracle.RawHarmonic.raw._proof_5`

```text
∀ (N t : ℕ), Module.Finite ℂ (WithLp 2 (QuantumOracle.ExtensionOperator.Level N t → ℂ))
```

### `QuantumOracle.RawHarmonic.raw._proof_6`

```text
∀ (N : ℕ), Module.Finite ℂ (WithLp 2 (QuantumOracle.PermutationExtensions.Perm N → ℂ))
```

### `QuantumOracle.UniformState.uniform._proof_1`

```text
(1 + 1).AtLeastTwo
```

### `QuantumOracle.WorkspaceKnowledge.onWorkspace._proof_1`

```text
∀ {A : Type u_2} (O : Type u_1) (U : EuclideanSpace ℂ A →ₗ[ℂ] EuclideanSpace ℂ A) (ψ φ : EuclideanSpace ℂ (A × O)),
  (WithLp.toLp 2 fun p => (U (WithLp.toLp 2 fun a => (ψ + φ).ofLp (a, p.2))).ofLp p.1) =
    (WithLp.toLp 2 fun p => (U (WithLp.toLp 2 fun a => ψ.ofLp (a, p.2))).ofLp p.1) +
      WithLp.toLp 2 fun p => (U (WithLp.toLp 2 fun a => φ.ofLp (a, p.2))).ofLp p.1
```

### `QuantumOracle.WorkspaceKnowledge.onWorkspace._proof_2`

```text
∀ {A : Type u_2} (O : Type u_1) (U : EuclideanSpace ℂ A →ₗ[ℂ] EuclideanSpace ℂ A) (c : ℂ)
  (ψ : EuclideanSpace ℂ (A × O)),
  (WithLp.toLp 2 fun p => (U (WithLp.toLp 2 fun a => (c • ψ).ofLp (a, p.2))).ofLp p.1) =
    (RingHom.id ℂ) c • WithLp.toLp 2 fun p => (U (WithLp.toLp 2 fun a => ψ.ofLp (a, p.2))).ofLp p.1
```

### `QuantumOracle.WorkspaceKnowledge.slice._proof_1`

```text
(1 + 1).AtLeastTwo
```

### `QuantumOracle.instDecidableEqDatabase.decEq._proof_1`

```text
∀ {N : ℕ} (a : Finset (Fin N × Fin N)) (a_1 : ∀ ⦃e f : Fin N × Fin N⦄, e ∈ a → f ∈ a → e.1 = f.1 → e.2 = f.2), a_1 = a_1
```

### `QuantumOracle.instDecidableEqDatabase.decEq._proof_2`

```text
∀ {N : ℕ} (a : Finset (Fin N × Fin N)) (a_1 : ∀ ⦃e f : Fin N × Fin N⦄, e ∈ a → f ∈ a → e.2 = f.2 → e.1 = f.1), a_1 = a_1
```

### `QuantumOracle.instDecidableEqDatabase.decEq._proof_3`

```text
∀ {N : ℕ} (a : Finset (Fin N × Fin N)) (a_1 : ∀ ⦃e f : Fin N × Fin N⦄, e ∈ a → f ∈ a → e.1 = f.1 → e.2 = f.2)
  (a_2 : ∀ ⦃e f : Fin N × Fin N⦄, e ∈ a → f ∈ a → e.2 = f.2 → e.1 = f.1),
  { edges := a, functional := a_1, injective := a_2 } = { edges := a, functional := a_1, injective := a_2 }
```

### `QuantumOracle.instDecidableEqDatabase.decEq._proof_4`

```text
∀ {N : ℕ} (a : Finset (Fin N × Fin N)) (a_1 : ∀ ⦃e f : Fin N × Fin N⦄, e ∈ a → f ∈ a → e.1 = f.1 → e.2 = f.2)
  (a_2 : ∀ ⦃e f : Fin N × Fin N⦄, e ∈ a → f ∈ a → e.2 = f.2 → e.1 = f.1) (b : Finset (Fin N × Fin N))
  (b_1 : ∀ ⦃e f : Fin N × Fin N⦄, e ∈ b → f ∈ b → e.1 = f.1 → e.2 = f.2)
  (b_2 : ∀ ⦃e f : Fin N × Fin N⦄, e ∈ b → f ∈ b → e.2 = f.2 → e.1 = f.1),
  ¬a = b →
    { edges := a, functional := a_1, injective := a_2 } = { edges := b, functional := b_1, injective := b_2 } → False
```

### `QuantumOracle.orthonormalSwap._proof_1`

```text
∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℂ E] (e u : E),
  (ℂ ∙ (e - u))ᗮ.HasOrthogonalProjection
```

## Library boundary

The library implementations of the following declarations are not reproduced in this bundle.
This boundary includes complex numbers, Euclidean norms, finite sums, orthogonal projections, and positive matrix square roots.
Choice functions, coordinate enumerations, and instances remain recorded as their actual dependencies, without substituting other definitions.

| Declaration | Module |
| --- | --- |
| `AddCommGroup.toAddCommMonoid` | `Mathlib.Algebra.Group.Defs` |
| `AddCommGroup.toAddGroup` | `Mathlib.Algebra.Group.Defs` |
| `AddCommMagma.toAdd` | `Mathlib.Algebra.Group.Defs` |
| `AddCommMonoid.toAddCommSemigroup` | `Mathlib.Algebra.Group.Defs` |
| `AddCommMonoid.toAddMonoid` | `Mathlib.Algebra.Group.Defs` |
| `AddCommMonoidWithOne.toAddMonoidWithOne` | `Mathlib.Data.Nat.Cast.Defs` |
| `AddCommSemigroup.toAddCommMagma` | `Mathlib.Algebra.Group.Defs` |
| `AddGroup.toSubNegMonoid` | `Mathlib.Algebra.Group.Defs` |
| `AddHom.mk` | `Mathlib.Algebra.Group.Hom.Defs` |
| `AddMonoid.toAddZeroClass` | `Mathlib.Algebra.Group.Defs` |
| `AddMonoidWithOne.toNatCast` | `Mathlib.Data.Nat.Cast.Defs` |
| `AddZero.toZero` | `Mathlib.Algebra.Group.Defs` |
| `AddZeroClass.toAddZero` | `Mathlib.Algebra.Group.Defs` |
| `Algebra.id` | `Mathlib.Algebra.Algebra.Defs` |
| `Algebra.toModule` | `Mathlib.Algebra.Algebra.Defs` |
| `Algebra.toSMul` | `Mathlib.Algebra.Algebra.Defs` |
| `Algebra.to_smulCommClass` | `Mathlib.Algebra.Algebra.Basic` |
| `And` | `Init.Prelude` |
| `Bool` | `Init.Prelude` |
| `Bool.false` | `Init.Prelude` |
| `Bool.fintype` | `Mathlib.Data.Fintype.Defs` |
| `Bool.true` | `Init.Prelude` |
| `Bool.xor` | `Init.Data.Bool` |
| `CFC.sqrt` | `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic` |
| `Classical.propDecidable` | `Init.Classical` |
| `CommCStarAlgebra.toNormedCommRing` | `Mathlib.Analysis.CStarAlgebra.Classes` |
| `CommMonoid.toMonoid` | `Mathlib.Algebra.Group.Defs` |
| `CommRing.toCommMonoid` | `Mathlib.Algebra.Ring.Defs` |
| `CommRing.toNonUnitalCommRing` | `Mathlib.Algebra.Ring.Defs` |
| `CommSemiring.toSemiring` | `Mathlib.Algebra.Ring.Defs` |
| `Complex` | `Mathlib.Data.Complex.Basic` |
| `Complex.addCommGroup` | `Mathlib.Data.Complex.Basic` |
| `Complex.commRing` | `Mathlib.Data.Complex.Basic` |
| `Complex.instAddCommMonoid` | `Mathlib.Data.Complex.Basic` |
| `Complex.instMul` | `Mathlib.Data.Complex.Basic` |
| `Complex.instNonUnitalCommRing` | `Mathlib.Data.Complex.Basic` |
| `Complex.instNorm` | `Mathlib.Analysis.Complex.Norm` |
| `Complex.instNormedAddCommGroup` | `Mathlib.Analysis.Complex.Norm` |
| `Complex.instNormedField` | `Mathlib.Analysis.Complex.Basic` |
| `Complex.instOne` | `Mathlib.Data.Complex.Basic` |
| `Complex.instRCLike` | `Mathlib.Analysis.Complex.Basic` |
| `Complex.instRing` | `Mathlib.Data.Complex.Basic` |
| `Complex.instSemiring` | `Mathlib.Data.Complex.Basic` |
| `Complex.instStarRing` | `Mathlib.Data.Complex.Basic` |
| `Complex.instZero` | `Mathlib.Data.Complex.Basic` |
| `Complex.ofReal` | `Mathlib.Data.Complex.Basic` |
| `ContinuousLinearMap.toLinearMap` | `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic` |
| `DFinsupp.instEquivLikeLinearEquiv` | `Mathlib.LinearAlgebra.DFinsupp` |
| `DFunLike.coe` | `Mathlib.Data.FunLike.Basic` |
| `Decidable` | `Init.Prelude` |
| `Decidable.isFalse` | `Init.Prelude` |
| `Decidable.isTrue` | `Init.Prelude` |
| `DecidableEq` | `Init.Prelude` |
| `DenselyNormedField.toNormedField` | `Mathlib.Analysis.Normed.Field.Basic` |
| `Distrib.toMul` | `Mathlib.Algebra.Ring.Defs` |
| `DistribMulAction.toDistribSMul` | `Mathlib.Algebra.GroupWithZero.Action.Defs` |
| `DistribMulAction.toMulAction` | `Mathlib.Algebra.GroupWithZero.Action.Defs` |
| `DistribSMul.toSMulZeroClass` | `Mathlib.Algebra.GroupWithZero.Action.Defs` |
| `DivInvMonoid.toDiv` | `Mathlib.Algebra.Group.Defs` |
| `DivisionRing.toDivisionSemiring` | `Mathlib.Algebra.Field.Defs` |
| `DivisionRing.toRing` | `Mathlib.Algebra.Field.Defs` |
| `DivisionSemiring.toSemiring` | `Mathlib.Algebra.Field.Defs` |
| `ENNReal` | `Mathlib.Data.ENNReal.Basic` |
| `ENNReal.instAddCommMonoidWithOne` | `Mathlib.Data.ENNReal.Basic` |
| `EmptyCollection.emptyCollection` | `Init.Core` |
| `Eq` | `Init.Prelude` |
| `Eq.ndrec` | `Init.Prelude` |
| `Equiv` | `Mathlib.Logic.Equiv.Defs` |
| `Equiv.Perm` | `Mathlib.Logic.Equiv.Defs` |
| `Equiv.instEquivLike` | `Mathlib.Logic.Equiv.Defs` |
| `Equiv.instFintype` | `Mathlib.Data.Fintype.Perm` |
| `Equiv.mk` | `Mathlib.Logic.Equiv.Defs` |
| `Equiv.ofBijective` | `Mathlib.Logic.Equiv.Defs` |
| `Equiv.prodAssoc` | `Mathlib.Logic.Equiv.Prod` |
| `Equiv.prodCongr` | `Mathlib.Logic.Equiv.Prod` |
| `Equiv.refl` | `Mathlib.Logic.Equiv.Defs` |
| `Equiv.sigmaEquivProd` | `Mathlib.Logic.Equiv.Defs` |
| `Equiv.symm` | `Mathlib.Logic.Equiv.Defs` |
| `Equiv.trans` | `Mathlib.Logic.Equiv.Defs` |
| `EquivLike.toFunLike` | `Mathlib.Data.FunLike.Equiv` |
| `EuclideanSpace` | `Mathlib.Analysis.InnerProductSpace.PiL2` |
| `EuclideanSpace.single` | `Mathlib.Analysis.InnerProductSpace.PiL2` |
| `Exists` | `Init.Core` |
| `Exists.choose` | `Init.Classical` |
| `False` | `Init.Prelude` |
| `Field.toCommRing` | `Mathlib.Algebra.Field.Defs` |
| `Field.toDivisionRing` | `Mathlib.Algebra.Field.Defs` |
| `Field.toSemifield` | `Mathlib.Algebra.Field.Defs` |
| `Fin` | `Init.Prelude` |
| `Fin.fintype` | `Mathlib.Data.Fintype.Basic` |
| `Fin.val` | `Init.Prelude` |
| `Finite` | `Mathlib.Data.Finite.Defs` |
| `Finset` | `Mathlib.Data.Finset.Defs` |
| `Finset.card` | `Mathlib.Data.Finset.Card` |
| `Finset.decidableEq` | `Mathlib.Data.Finset.Defs` |
| `Finset.decidableMem` | `Mathlib.Data.Finset.Defs` |
| `Finset.filter` | `Mathlib.Data.Finset.Filter` |
| `Finset.image` | `Mathlib.Data.Finset.Image` |
| `Finset.instEmptyCollection` | `Mathlib.Data.Finset.Empty` |
| `Finset.instInsert` | `Mathlib.Data.Finset.Insert` |
| `Finset.instSetLike` | `Mathlib.Data.Finset.Defs` |
| `Finset.sum` | `Mathlib.Algebra.BigOperators.Group.Finset.Defs` |
| `Finset.univ` | `Mathlib.Data.Fintype.Defs` |
| `Fintype` | `Mathlib.Data.Fintype.Defs` |
| `Fintype.card` | `Mathlib.Data.Fintype.Card` |
| `Fintype.decidableEqEquivFintype` | `Mathlib.Data.Fintype.Defs` |
| `Fintype.equivFin` | `Mathlib.Data.Fintype.EquivFin` |
| `Fintype.ofFinite` | `Mathlib.Data.Fintype.EquivFin` |
| `Function.Embedding` | `Mathlib.Logic.Embedding.Basic` |
| `Function.Injective` | `Init.Data.Function` |
| `Function.Surjective` | `Init.Data.Function` |
| `Function.instFunLikeEmbedding` | `Mathlib.Logic.Embedding.Basic` |
| `Function.smulCommClass` | `Mathlib.Algebra.Group.Action.Pi` |
| `HAdd.hAdd` | `Init.Prelude` |
| `HDiv.hDiv` | `Init.Prelude` |
| `HMul.hMul` | `Init.Prelude` |
| `HSMul.hSMul` | `Init.Prelude` |
| `HSub.hSub` | `Init.Prelude` |
| `InfSet.sInf` | `Mathlib.Order.SetNotation` |
| `Inner.inner` | `Mathlib.Analysis.InnerProductSpace.Defs` |
| `InnerProductSpace` | `Mathlib.Analysis.InnerProductSpace.Defs` |
| `InnerProductSpace.toInner` | `Mathlib.Analysis.InnerProductSpace.Defs` |
| `InnerProductSpace.toNormedSpace` | `Mathlib.Analysis.InnerProductSpace.Defs` |
| `Insert.insert` | `Init.Core` |
| `Inv.inv` | `Init.Prelude` |
| `InvolutiveStar.toStar` | `Mathlib.Algebra.Star.Basic` |
| `IsScalarTower` | `Mathlib.Algebra.Group.Action.Defs` |
| `IsSelfAdjoint` | `Mathlib.Algebra.Star.SelfAdjoint` |
| `IsTopologicalSemiring` | `Mathlib.Topology.Algebra.Ring.Basic` |
| `LE.le` | `Init.Prelude` |
| `LT.lt` | `Init.Prelude` |
| `LinearEquiv` | `Mathlib.Algebra.Module.Equiv.Defs` |
| `LinearEquiv.symm` | `Mathlib.Algebra.Module.Equiv.Defs` |
| `LinearEquiv.toLinearMap` | `Mathlib.Algebra.Module.Equiv.Defs` |
| `LinearIsometry` | `Mathlib.Analysis.Normed.Operator.LinearIsometry` |
| `LinearIsometry.instFunLike` | `Mathlib.Analysis.Normed.Operator.LinearIsometry` |
| `LinearIsometry.mk` | `Mathlib.Analysis.Normed.Operator.LinearIsometry` |
| `LinearIsometry.toLinearMap` | `Mathlib.Analysis.Normed.Operator.LinearIsometry` |
| `LinearIsometryEquiv` | `Mathlib.Analysis.Normed.Operator.LinearIsometry` |
| `LinearIsometryEquiv.instEquivLike` | `Mathlib.Analysis.Normed.Operator.LinearIsometry` |
| `LinearIsometryEquiv.piLpCongrLeft` | `Mathlib.Analysis.Normed.Lp.PiLp` |
| `LinearIsometryEquiv.piLpCongrRight` | `Mathlib.Analysis.Normed.Lp.PiLp` |
| `LinearIsometryEquiv.piLpCurry` | `Mathlib.Analysis.Normed.Lp.PiLp` |
| `LinearIsometryEquiv.refl` | `Mathlib.Analysis.Normed.Operator.LinearIsometry` |
| `LinearIsometryEquiv.symm` | `Mathlib.Analysis.Normed.Operator.LinearIsometry` |
| `LinearIsometryEquiv.toLinearEquiv` | `Mathlib.Analysis.Normed.Operator.LinearIsometry` |
| `LinearIsometryEquiv.trans` | `Mathlib.Analysis.Normed.Operator.LinearIsometry` |
| `LinearMap` | `Mathlib.Algebra.Module.LinearMap.Defs` |
| `LinearMap.addCommMonoid` | `Mathlib.Algebra.Module.LinearMap.Defs` |
| `LinearMap.adjoint` | `Mathlib.Analysis.InnerProductSpace.Adjoint` |
| `LinearMap.comp` | `Mathlib.Algebra.Module.LinearMap.Defs` |
| `LinearMap.instFunLike` | `Mathlib.Algebra.Module.LinearMap.Defs` |
| `LinearMap.isometryOfInner` | `Mathlib.Analysis.InnerProductSpace.LinearMap` |
| `LinearMap.mk` | `Mathlib.Algebra.Module.LinearMap.Defs` |
| `LinearMap.module` | `Mathlib.Algebra.Module.LinearMap.Defs` |
| `Matrix` | `Mathlib.LinearAlgebra.Matrix.Defs` |
| `Matrix.addCommMonoid` | `Mathlib.LinearAlgebra.Matrix.Defs` |
| `Matrix.conjTranspose` | `Mathlib.LinearAlgebra.Matrix.ConjTranspose` |
| `Matrix.instAlgebra` | `Mathlib.Data.Matrix.Basic` |
| `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid` | `Mathlib.Data.Matrix.Mul` |
| `Matrix.instNonUnitalRing` | `Mathlib.Data.Matrix.Mul` |
| `Matrix.instNonnegSpectrumClass` | `Mathlib.Analysis.Matrix.Order` |
| `Matrix.instPartialOrder` | `Mathlib.Analysis.Matrix.Order` |
| `Matrix.instRing` | `Mathlib.Data.Matrix.Mul` |
| `Matrix.instStar` | `Mathlib.LinearAlgebra.Matrix.ConjTranspose` |
| `Matrix.instStarOrderedRing` | `Mathlib.Analysis.Matrix.Order` |
| `Matrix.instStarRing` | `Mathlib.LinearAlgebra.Matrix.ConjTranspose` |
| `Matrix.inv` | `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` |
| `Matrix.module` | `Mathlib.LinearAlgebra.Matrix.Defs` |
| `Matrix.mulVec` | `Mathlib.Data.Matrix.Mul` |
| `Matrix.semiring` | `Mathlib.Data.Matrix.Mul` |
| `Matrix.toEuclideanLin` | `Mathlib.Analysis.InnerProductSpace.PiL2` |
| `Membership.mem` | `Init.Prelude` |
| `MetricSpace.toPseudoMetricSpace` | `Mathlib.Topology.MetricSpace.Defs` |
| `Min.min` | `Init.Prelude` |
| `Module.Finite` | `Mathlib.RingTheory.Finiteness.Defs` |
| `Module.toDistribMulAction` | `Mathlib.Algebra.Module.Defs` |
| `Monoid.toSemigroup` | `Mathlib.Algebra.Group.Defs` |
| `MulAction.toSemigroupAction` | `Mathlib.Algebra.Group.Action.Defs` |
| `Nat` | `Init.Prelude` |
| `Nat.AtLeastTwo` | `Mathlib.Data.Nat.Init` |
| `Nat.below` | `Init.Prelude` |
| `Nat.brecOn` | `Init.Prelude` |
| `Nat.casesOn` | `Init.Prelude` |
| `Nat.cast` | `Init.Data.Cast` |
| `Nat.decidableExistsFin` | `Init.Data.Nat.Lemmas` |
| `Nat.factorial` | `Mathlib.Data.Nat.Factorial.Basic` |
| `Nat.instAtLeastTwoHAddOfNat` | `Mathlib.Data.Nat.Init` |
| `Nat.instNeZeroSucc` | `Init.Data.Nat.Basic` |
| `Nat.succ` | `Init.Prelude` |
| `Ne` | `Init.Core` |
| `NonUnitalCommRing.toNonUnitalNonAssocCommRing` | `Mathlib.Algebra.Ring.Defs` |
| `NonUnitalCommRing.toNonUnitalRing` | `Mathlib.Algebra.Ring.Defs` |
| `NonUnitalContinuousFunctionalCalculus` | `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital` |
| `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing` | `Mathlib.Algebra.Ring.Defs` |
| `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring` | `Mathlib.Algebra.Ring.Defs` |
| `NonUnitalNonAssocSemiring.toAddCommMonoid` | `Mathlib.Algebra.Ring.Defs` |
| `NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing` | `Mathlib.Analysis.Normed.Ring.Basic` |
| `NonUnitalSeminormedRing.toSeminormedAddCommGroup` | `Mathlib.Analysis.Normed.Ring.Basic` |
| `Nonempty` | `Init.Prelude` |
| `Nontrivial` | `Mathlib.Logic.Nontrivial.Defs` |
| `Norm.norm` | `Mathlib.Analysis.Normed.Group.Defs` |
| `NormedAddCommGroup` | `Mathlib.Analysis.Normed.Group.Defs` |
| `NormedAddCommGroup.toAddCommGroup` | `Mathlib.Analysis.Normed.Group.Defs` |
| `NormedAddCommGroup.toSeminormedAddCommGroup` | `Mathlib.Analysis.Normed.Group.Defs` |
| `NormedAlgebra.toAlgebra` | `Mathlib.Analysis.Normed.Module.Basic` |
| `NormedCommRing.toSeminormedCommRing` | `Mathlib.Analysis.Normed.Ring.Basic` |
| `NormedField.toField` | `Mathlib.Analysis.Normed.Field.Basic` |
| `NormedField.toNormedCommRing` | `Mathlib.Analysis.Normed.Field.Basic` |
| `NormedSpace.toModule` | `Mathlib.Analysis.Normed.Module.Basic` |
| `Not` | `Init.Prelude` |
| `OfNat.ofNat` | `Init.Prelude` |
| `One.toOfNat1` | `Init.Data.Zero` |
| `Option` | `Init.Prelude` |
| `Option.casesOn` | `Init.Prelude` |
| `Option.elim` | `Init.Data.Option.Basic` |
| `Option.instDecidableEq` | `Init.Data.Option.Basic` |
| `Option.none` | `Init.Prelude` |
| `Option.some` | `Init.Prelude` |
| `PProd` | `Init.Prelude` |
| `Pi.Function.module` | `Mathlib.Algebra.Module.Pi` |
| `Pi.addCommGroup` | `Mathlib.Algebra.Group.Pi.Basic` |
| `Pi.instFintype` | `Mathlib.Data.Fintype.Pi` |
| `Pi.module` | `Mathlib.Algebra.Module.Pi` |
| `PiLp` | `Mathlib.Analysis.Normed.Lp.PiLp` |
| `PiLp.innerProductSpace` | `Mathlib.Analysis.InnerProductSpace.PiL2` |
| `PiLp.innerProductSpace._proof_1` | `Mathlib.Analysis.InnerProductSpace.PiL2` |
| `PiLp.instNorm` | `Mathlib.Analysis.Normed.Lp.PiLp` |
| `PiLp.normedAddCommGroup` | `Mathlib.Analysis.Normed.Lp.PiLp` |
| `PiLp.seminormedAddCommGroup` | `Mathlib.Analysis.Normed.Lp.PiLp` |
| `Prod` | `Init.Prelude` |
| `Prod.fst` | `Init.Prelude` |
| `Prod.mk` | `Init.Prelude` |
| `Prod.snd` | `Init.Prelude` |
| `Prod.swap` | `Init.Data.Prod` |
| `PseudoMetricSpace.toUniformSpace` | `Mathlib.Topology.MetricSpace.Pseudo.Defs` |
| `RCLike.innerProductSpace` | `Mathlib.Analysis.InnerProductSpace.Basic` |
| `RCLike.toDenselyNormedField` | `Mathlib.Analysis.RCLike.Basic` |
| `RCLike.toNormedAlgebra` | `Mathlib.Analysis.RCLike.Basic` |
| `RCLike.toStarRing` | `Mathlib.Analysis.RCLike.Basic` |
| `Real` | `Mathlib.Data.Real.Basic` |
| `Real.commRing` | `Mathlib.Data.Real.Basic` |
| `Real.instAddGroup` | `Mathlib.Data.Real.Basic` |
| `Real.instCommSemiring` | `Mathlib.Data.Real.Basic` |
| `Real.instDivInvMonoid` | `Mathlib.Data.Real.Basic` |
| `Real.instField` | `Mathlib.Data.Real.Basic` |
| `Real.instInfSet` | `Mathlib.Algebra.Order.Archimedean.Real.Basic` |
| `Real.instInv` | `Mathlib.Data.Real.Basic` |
| `Real.instLE` | `Mathlib.Data.Real.Basic` |
| `Real.instMul` | `Mathlib.Data.Real.Basic` |
| `Real.instNatCast` | `Mathlib.Data.Real.Basic` |
| `Real.instOne` | `Mathlib.Data.Real.Basic` |
| `Real.instRCLike` | `Mathlib.Analysis.RCLike.Basic` |
| `Real.instSub` | `Mathlib.Data.Real.Basic` |
| `Real.instSupSet` | `Mathlib.Algebra.Order.Archimedean.Real.Basic` |
| `Real.lattice` | `Mathlib.Data.Real.Basic` |
| `Real.metricSpace` | `Mathlib.Topology.MetricSpace.Basic` |
| `Real.normedField` | `Mathlib.Analysis.Normed.Field.Basic` |
| `Real.semiring` | `Mathlib.Data.Real.Basic` |
| `Real.sqrt` | `Mathlib.Analysis.Real.Sqrt` |
| `Ring.toAddCommGroup` | `Mathlib.Algebra.Ring.Defs` |
| `Ring.toNonUnitalRing` | `Mathlib.Algebra.Ring.Defs` |
| `Ring.toSemiring` | `Mathlib.Algebra.Ring.Defs` |
| `RingHom` | `Mathlib.Algebra.Ring.Hom.Defs` |
| `RingHom.id` | `Mathlib.Algebra.Ring.Hom.Defs` |
| `RingHom.instFunLike` | `Mathlib.Algebra.Ring.Hom.Defs` |
| `RingHomCompTriple` | `Mathlib.Algebra.Ring.CompTypeclasses` |
| `RingHomInvPair` | `Mathlib.Algebra.Ring.CompTypeclasses` |
| `RingHomInvPair.ids` | `Mathlib.Algebra.Ring.CompTypeclasses` |
| `SMulCommClass` | `Mathlib.Algebra.Group.Action.Defs` |
| `SMulZeroClass.toSMul` | `Mathlib.Algebra.GroupWithZero.Action.Defs` |
| `Semifield.toCommSemiring` | `Mathlib.Algebra.Field.Defs` |
| `Semifield.toDivisionSemiring` | `Mathlib.Algebra.Field.Defs` |
| `SemigroupAction.toSMul` | `Mathlib.Algebra.Group.Action.Defs` |
| `SeminormedAddCommGroup.toAddCommGroup` | `Mathlib.Analysis.Normed.Group.Defs` |
| `SeminormedAddCommGroup.toPseudoMetricSpace` | `Mathlib.Analysis.Normed.Group.Defs` |
| `SeminormedAddCommGroup.toSeminormedAddGroup` | `Mathlib.Analysis.Normed.Group.Defs` |
| `SeminormedAddGroup.toNorm` | `Mathlib.Analysis.Normed.Group.Defs` |
| `SeminormedCommRing.toNonUnitalSeminormedCommRing` | `Mathlib.Analysis.Normed.Ring.Basic` |
| `SeminormedCommRing.toSeminormedRing` | `Mathlib.Analysis.Normed.Ring.Basic` |
| `SeminormedRing.toPseudoMetricSpace` | `Mathlib.Analysis.Normed.Ring.Basic` |
| `SeminormedRing.toRing` | `Mathlib.Analysis.Normed.Ring.Basic` |
| `Semiring.toAddCommMonoid` | `Mathlib.Algebra.Ring.Defs` |
| `Semiring.toModule` | `Mathlib.Algebra.Module.Defs` |
| `Semiring.toMonoid` | `Mathlib.Algebra.Ring.Defs` |
| `Semiring.toNonAssocSemiring` | `Mathlib.Algebra.Ring.Defs` |
| `Set` | `Mathlib.Data.Set.Defs` |
| `Set.instSingletonSet` | `Mathlib.Data.Set.Defs` |
| `Set.range` | `Mathlib.Data.Set.Operations` |
| `SetLike.instMembership` | `Mathlib.Data.SetLike.Basic` |
| `Sigma` | `Init.Core` |
| `Sigma.casesOn` | `Init.Core` |
| `Sigma.instFintype` | `Mathlib.Data.Fintype.Sigma` |
| `Sigma.mk` | `Init.Core` |
| `Singleton.singleton` | `Init.Core` |
| `Star.star` | `Mathlib.Algebra.Notation.Defs` |
| `StarAddMonoid.toInvolutiveStar` | `Mathlib.Algebra.Star.Basic` |
| `StarRing.toStarAddMonoid` | `Mathlib.Algebra.Star.Basic` |
| `SubNegMonoid.toAddMonoid` | `Mathlib.Algebra.Group.Defs` |
| `SubNegMonoid.toSub` | `Mathlib.Algebra.Group.Defs` |
| `Submodule` | `Mathlib.Algebra.Module.Submodule.Defs` |
| `Submodule.HasOrthogonalProjection` | `Mathlib.Analysis.InnerProductSpace.Projection.Basic` |
| `Submodule.instMin` | `Mathlib.Algebra.Module.Submodule.Lattice` |
| `Submodule.orthogonal` | `Mathlib.Analysis.InnerProductSpace.Orthogonal` |
| `Submodule.reflection` | `Mathlib.Analysis.InnerProductSpace.Projection.Reflection` |
| `Submodule.span` | `Mathlib.LinearAlgebra.Span.Defs` |
| `Submodule.starProjection` | `Mathlib.Analysis.InnerProductSpace.Projection.Basic` |
| `Subtype` | `Init.Prelude` |
| `Subtype.fintype` | `Mathlib.Data.Fintype.Sets` |
| `Subtype.mk` | `Init.Prelude` |
| `Subtype.val` | `Init.Prelude` |
| `SupSet.sSup` | `Mathlib.Order.SetNotation` |
| `UniformSpace.toTopologicalSpace` | `Mathlib.Topology.UniformSpace.Defs` |
| `Unit` | `Init.Prelude` |
| `Unit.unit` | `Init.Prelude` |
| `WithLp` | `Mathlib.Analysis.Normed.Lp.WithLp` |
| `WithLp.instAddCommGroup` | `Mathlib.Analysis.Normed.Lp.WithLp` |
| `WithLp.instModule` | `Mathlib.Analysis.Normed.Lp.WithLp` |
| `WithLp.instSMul` | `Mathlib.Analysis.Normed.Lp.WithLp` |
| `WithLp.instSMulCommClass` | `Mathlib.Analysis.Normed.Lp.WithLp` |
| `WithLp.ofLp` | `Mathlib.Analysis.Normed.Lp.WithLp` |
| `WithLp.toLp` | `Mathlib.Analysis.Normed.Lp.WithLp` |
| `Zero.toOfNat0` | `Init.Data.Zero` |
| `abs` | `Mathlib.Algebra.Order.Group.Unbundled.Abs` |
| `dite` | `Init.Prelude` |
| `fact_one_le_two_ennreal` | `Mathlib.Data.ENNReal.Basic` |
| `id` | `Init.Prelude` |
| `inferInstance` | `Init.Prelude` |
| `instAddNat` | `Init.Prelude` |
| `instCommCStarAlgebraComplex` | `Mathlib.Analysis.CStarAlgebra.Classes` |
| `instContinuousStarReal` | `Mathlib.Topology.Algebra.Star.Real` |
| `instDecidableAnd` | `Init.Prelude` |
| `instDecidableEqBool` | `Init.Prelude` |
| `instDecidableEqFin` | `Init.Prelude` |
| `instDecidableEqNat` | `Init.Prelude` |
| `instDecidableEqProd` | `Init.Core` |
| `instDecidableNot` | `Init.Prelude` |
| `instDistribOfSemiring` | `Mathlib.Algebra.Ring.Defs` |
| `instFintypeOption` | `Mathlib.Data.Fintype.Option` |
| `instFintypeProd` | `Mathlib.Data.Fintype.Prod` |
| `instHAdd` | `Init.Prelude` |
| `instHDiv` | `Init.Prelude` |
| `instHMul` | `Init.Prelude` |
| `instHSMul` | `Init.Prelude` |
| `instHSub` | `Init.Prelude` |
| `instInnerProductSpaceRealComplex` | `Mathlib.Analysis.InnerProductSpace.Basic` |
| `instLENat` | `Init.Prelude` |
| `instLTNat` | `Init.Prelude` |
| `instMulNat` | `Init.Prelude` |
| `instOfNatAtLeastTwo` | `Mathlib.Data.Nat.Cast.Defs` |
| `instOfNatNat` | `Init.Prelude` |
| `instSMulOfMul` | `Init.Prelude` |
| `instStarRingReal` | `Mathlib.Data.Real.Star` |
| `instSubNat` | `Init.Prelude` |
| `instTopologicalSpaceMatrix` | `Mathlib.Topology.Instances.Matrix` |
| `ite` | `Init.Prelude` |
| `setOf` | `Mathlib.Data.Set.Defs` |
| `starRingEnd` | `Mathlib.Algebra.Star.Basic` |
