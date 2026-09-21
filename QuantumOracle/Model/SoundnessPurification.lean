import QuantumOracle.Model.OutputExperiment
import QuantumOracle.Model.PolarEmbedding

/-! # The concrete common purifications in the soundness statement

The exact final vector is transported by the actual positive polar embedding
into the database register of the compressed final vector. Any discarded output
coordinates become part of that shared ancilla. The normalization and reduction
proofs below certify that these explicit vectors are purifications of the actual
outputs; no quantitative soundness estimate is imported or assumed.

The namespace is retained for compatibility with the original public theorem.
-/

noncomputable section

namespace QuantumOracle.FiniteSoundnessWitness

open PermutationExtensions HiddenIsometry FinitePurification OutputDiscard

attribute [local irreducible] PolarEmbedding.candidate

variable {N w : ℕ}

/-- Explicit common purifications retaining the entire final workspace. -/
def retainedPurification (encode : BasisLookup.Encoding N w)
    (a : ConcreteExperiment.Algorithm N w) :
    CommonPurification (ConcreteExperiment.exactFinal encode a)
      (ConcreteExperiment.compressedFinal encode a) where
  ancillaDim := Fintype.card (Database N)
  exactVector := coordinateState
    (onOracle a.Workspace (PolarEmbedding.candidate N) (ConcreteExperiment.exactVector encode a))
  compressedVector := coordinateState (ConcreteExperiment.compressedVector encode a)
  exact_normalized := by
    rw [coordinateState_norm, norm_onOracle, ConcreteExperiment.exactVector_normalized]
  compressed_normalized := by
    rw [coordinateState_norm, ConcreteExperiment.compressedVector_normalized]
  exact_reduction := by
    rw [reducedState_coordinateState, reducedFin_onOracle]
    rfl
  compressed_reduction := reducedState_coordinateState _

theorem retainedPurification_distance (encode : BasisLookup.Encoding N w)
    (a : ConcreteExperiment.Algorithm N w) :
    (retainedPurification encode a).distance =
      ‖onOracle a.Workspace (PolarEmbedding.candidate N)
        (ConcreteExperiment.exactVector encode a) - ConcreteExperiment.compressedVector encode a‖ := by
  change ‖coordinateIsometry a.Workspace (Database N) _ -
    coordinateIsometry a.Workspace (Database N) _‖ = _
  rw [← map_sub, LinearIsometryEquiv.norm_map]

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

/-- Discarding any output factor preserves the distance of this concrete
purification pair because both vectors undergo the same coordinate isometry. -/
theorem outputPurification_distance (encode : BasisLookup.Encoding N w)
    (a : OutputExperiment.Algorithm N w) :
    (outputPurification encode a).distance = (retainedPurification encode a.base).distance := by
  change ‖coordinateIsometry a.Output (a.Discard × Database N) _ -
    coordinateIsometry a.Output (a.Discard × Database N) _‖ = _
  rw [← map_sub, LinearIsometryEquiv.norm_map, retainedPurification_distance]
  exact norm_discardVector_sub a.split _ _

end QuantumOracle.FiniteSoundnessWitness
