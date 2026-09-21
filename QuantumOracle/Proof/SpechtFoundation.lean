import RepresentationTheory.PartitionAuxiliary
import RepresentationTheory.PartitionFinrank
import RepresentationTheory.Auxiliary.PartitionPermutationRelations

/-!
# Actual Specht modules and their dimension and branching identities

These names expose the concrete constructions in the pinned Etingof release:
the Young-symmetrizer left ideal in the complex symmetric-group algebra, its
actual permutation action and trace character, standard tableaux, and the
dimension and character-branching theorems.

This module does not identify these modules with the QuantumOracle harmonic
layers or Gram eigenspaces. The branching theorem is a character identity;
no particular branching isometry is constructed here.
-/

noncomputable section

namespace QuantumOracle.SpechtFoundation

open scoped BigOperators Classical

/-- The complex group algebra of the actual symmetric group on `Fin N`. -/
abbrev GroupAlgebra (N : ℕ) := MonoidAlgebra ℂ (Equiv.Perm (Fin N))

/-- The sum over the row stabilizer of the canonical tableau. -/
abbrev rowSymmetrizer (N : ℕ) (la : Nat.Partition N) : GroupAlgebra N :=
  RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB N la

/-- The sign-weighted sum over the column stabilizer of the canonical tableau. -/
abbrev columnAntisymmetrizer (N : ℕ) (la : Nat.Partition N) : GroupAlgebra N :=
  RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA N la

/-- The actual Young symmetrizer, with column-times-row convention. -/
abbrev youngSymmetrizer (N : ℕ) (la : Nat.Partition N) : GroupAlgebra N :=
  RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC N la

theorem youngSymmetrizer_eq (N : ℕ) (la : Nat.Partition N) :
    youngSymmetrizer N la = columnAntisymmetrizer N la * rowSymmetrizer N la := rfl

/-- The actual Specht module as a left ideal, rather than an abstract model. -/
abbrev specht (N : ℕ) (la : Nat.Partition N) :
    Submodule (GroupAlgebra N) (GroupAlgebra N) :=
  RepresentationTheory.PartitionAuxiliary.partitionSubmodule N la

theorem specht_eq_span (N : ℕ) (la : Nat.Partition N) :
    specht N la = Submodule.span (GroupAlgebra N) {youngSymmetrizer N la} := rfl

/-- The actual left ideal is an irreducible complex symmetric-group module. -/
theorem specht_simple (N : ℕ) (la : Nat.Partition N) :
    IsSimpleModule (GroupAlgebra N) (specht N la) :=
  RepresentationTheory.PartitionAuxiliary.partitionSubmodule_isSimpleModule N la

/-- The Young diagram formed from the partition's decreasing row lengths. -/
abbrev diagram {N : ℕ} (la : Nat.Partition N) : YoungDiagram :=
  RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la

/-- Bijective fillings by `Fin N`, strictly increasing along rows and columns. -/
abbrev StandardTableau (N : ℕ) (la : Nat.Partition N) : Type :=
  RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource N la

/-- The cardinality of the actual standard-tableau type. -/
def tableauCount (N : ℕ) (la : Nat.Partition N) : ℕ := Nat.card (StandardTableau N la)

/-- The usual arm-plus-leg-plus-one hook statistic at an actual diagram cell. -/
abbrev hookLength (mu : YoungDiagram) (i j : ℕ) : ℕ :=
  RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellStatistic mu i j

theorem hookLength_eq (mu : YoungDiagram) (i j : ℕ) :
    hookLength mu i j = mu.rowLen i + mu.colLen j - i - j - 1 := rfl

/-- Product of the actual hook lengths over all cells. -/
abbrev hookProduct (mu : YoungDiagram) : ℕ :=
  RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic mu

theorem hookProduct_eq_prod (mu : YoungDiagram) :
    hookProduct mu = mu.cells.prod (fun c => hookLength mu c.1 c.2) := rfl

theorem hookProduct_pos (mu : YoungDiagram) : 0 < hookProduct mu :=
  RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic_pos mu

/-- The concrete Specht module has dimension equal to the actual tableau count. -/
theorem dimension_eq_tableauCount (N : ℕ) (la : Nat.Partition N) :
    Module.finrank ℂ (specht N la) = tableauCount N la :=
  RepresentationTheory.PartitionFinrank.finrank_eq_card_auxiliaryType N la

/-- Exact multiplicative hook identity; no natural-division truncation is involved. -/
theorem tableauCount_mul_hookProduct (N : ℕ) (la : Nat.Partition N) :
    tableauCount N la * hookProduct (diagram la) = N.factorial :=
  RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.auxiliaryCard_mul_hookLengthProduct_eq_factorial N la

theorem hookProduct_dvd_factorial (N : ℕ) (la : Nat.Partition N) :
    hookProduct (diagram la) ∣ N.factorial :=
  RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.hookLengthProduct_dvd_factorial N la

/-- The dimension hook formula is a theorem about the constructed Specht module. -/
theorem dimension_eq_factorial_div_hookProduct (N : ℕ) (la : Nat.Partition N) :
    Module.finrank ℂ (specht N la) = N.factorial / hookProduct (diagram la) :=
  RepresentationTheory.PartitionFinrank.finrank_eq_factorial_div_hookLengthProduct N la

theorem dimension_mul_hookProduct (N : ℕ) (la : Nat.Partition N) :
    Module.finrank ℂ (specht N la) * hookProduct (diagram la) = N.factorial := by
  rw [dimension_eq_tableauCount]
  exact tableauCount_mul_hookProduct N la

/-- Actual left multiplication by a permutation on the constructed Specht ideal. -/
abbrev action (N : ℕ) (la : Nat.Partition N) (sigma : Equiv.Perm (Fin N)) :
    ↥(specht N la) →ₗ[ℂ] ↥(specht N la) :=
  RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliarySubtypePermutationEndomorphism N la sigma

theorem action_apply_val (N : ℕ) (la : Nat.Partition N) (sigma : Equiv.Perm (Fin N))
    (v : specht N la) :
    (action N la sigma v).val = MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) sigma * v.val := rfl

/-- The actual permutation action packaged as a complex representation. -/
abbrev representation (N : ℕ) (la : Nat.Partition N) :
    Representation ℂ (Equiv.Perm (Fin N)) (specht N la) :=
  RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation N la

theorem representation_apply (N : ℕ) (la : Nat.Partition N) (sigma : Equiv.Perm (Fin N)) :
    representation N la sigma = action N la sigma := rfl

/-- The trace of the actual permutation action, not a prescribed scalar formula. -/
abbrev character (N : ℕ) (la : Nat.Partition N) (sigma : Equiv.Perm (Fin N)) : ℂ :=
  RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue N la sigma

theorem character_eq_trace (N : ℕ) (la : Nat.Partition N) (sigma : Equiv.Perm (Fin N)) :
    character N la sigma = LinearMap.trace ℂ (specht N la) (action N la sigma) := rfl

/-- The actual inclusion fixing the last point. -/
abbrev includePerm (N : ℕ) : Equiv.Perm (Fin N) →* Equiv.Perm (Fin (N + 1)) :=
  RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.permutation_hom_succ N

theorem includePerm_eq (N : ℕ) :
    includePerm N = Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb := rfl

/-- All partitions obtained by removing one corner, encoded by diagram containment. -/
abbrev removeCorners {N : ℕ} (mu : Nat.Partition (N + 1)) : Finset (Nat.Partition N) :=
  RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred mu

theorem mem_removeCorners {N : ℕ} (la : Nat.Partition N) (mu : Nat.Partition (N + 1)) :
    la ∈ removeCorners mu ↔ diagram la ≤ diagram mu := by
  simp only [removeCorners,
    RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.partition_finset_pred,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- Character-level branching for the actual restriction to the last-point stabilizer. -/
theorem character_restrict (N : ℕ) (mu : Nat.Partition (N + 1))
    (sigma : Equiv.Perm (Fin N)) :
    character (N + 1) mu (includePerm N sigma) =
      ∑ la ∈ removeCorners mu, character N la sigma :=
  RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.value_permutation_hom_succ_eq_sum_partition_finset_pred N mu sigma

/-- The actual finite-group character pairing, using inverse permutations. -/
abbrev characterPairing (N : ℕ) (chi psi : Equiv.Perm (Fin N) → ℂ) : ℂ :=
  RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.complex_function_operation N chi psi

theorem characterPairing_eq_sum (N : ℕ) (chi psi : Equiv.Perm (Fin N) → ℂ) :
    characterPairing N chi psi =
      (Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ * ∑ sigma, chi sigma * psi sigma⁻¹ := rfl

/-- The actual restriction pairing is multiplicity-free, with exactly the
one-corner containment condition. -/
theorem branching_multiplicity (N : ℕ) (la : Nat.Partition N) (mu : Nat.Partition (N + 1)) :
    characterPairing N (character N la)
        (fun sigma => character (N + 1) mu (includePerm N sigma)) =
      if diagram la ≤ diagram mu then 1 else 0 :=
  RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.complex_function_operation_eq_indicator_le N la mu

end QuantumOracle.SpechtFoundation
