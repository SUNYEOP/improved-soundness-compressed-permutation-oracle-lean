import QuantumOracle.Model.CompressionIndex
import QuantumOracle.Model.CompressionBlock
import QuantumOracle.Model.BlockOperator

/-!
# Actual permutation compression

This is `pC_x` from manuscript Section 2.2: the orthogonal direct sum, over
actual erased databases, of the swap between the base and its uniform extensions.
The swap's normalization and isometry are proved, not supplied as hypotheses.
-/

noncomputable section

namespace QuantumOracle.Compression

open CompressionIndex

variable {N : ℕ}

abbrev State (N : ℕ) := EuclideanSpace ℂ (Database N)

/-- Actual complex database basis expressed in its unique compression blocks. -/
def reindex (x : Fin N) : State N ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Index x) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (databaseEquiv x)

def coordinates (x : Fin N) (ψ : State N) (J : Base x) :
    EuclideanSpace ℂ (Option (Fresh J.val)) :=
  BlockOperator.restrict (reindex x ψ) J

@[simp] theorem coordinates_apply (x : Fin N) (ψ : State N) (J : Base x)
    (o : Option (Fresh J.val)) : coordinates x ψ J o = ψ (decode x ⟨J, o⟩) := rfl

/-- Carolan's actual permutation compression, on the entire database space. -/
def pC (x : Fin N) : State N ≃ₗᵢ[ℂ] State N :=
  BlockOperator.transport (databaseEquiv x)
    (fun J => CompressionBlock.compression (Fresh J.val))

theorem pC_isometry (x : Fin N) : Isometry (pC x) := (pC x).isometry

@[simp] theorem pC_involutive (x : Fin N) (ψ : State N) : pC x (pC x ψ) = ψ :=
  BlockOperator.transport_involutive (databaseEquiv x)
    (fun J : Base x => CompressionBlock.compression (Fresh J.val))
    (fun J v => CompressionBlock.compression_involutive (Fresh J.val) v) ψ

/-- The actual global operator acts exactly as the proved swap in each block. -/
@[simp] theorem coordinates_pC (x : Fin N) (ψ : State N) (J : Base x) :
    coordinates x (pC x ψ) J =
      CompressionBlock.compression (Fresh J.val) (coordinates x ψ J) := by
  unfold coordinates reindex pC
  rw [BlockOperator.reindex_transport, BlockOperator.restrict_diagonal]

theorem pC_zero_block (x : Fin N) (ψ : State N) (J : Base x)
    (h : coordinates x ψ J = 0) : coordinates x (pC x ψ) J = 0 := by
  rw [coordinates_pC, h, map_zero]

/-- An exact coordinate formula for an empty database block. -/
theorem pC_empty_block (x : Fin N) (ψ : State N) (J : Base x)
    (h : coordinates x ψ J = UniformState.emptyKet (Fresh J.val)) :
    coordinates x (pC x ψ) J = UniformState.extensionUniform (Fresh J.val) := by
  letI := fresh_nonempty J
  rw [coordinates_pC, h, CompressionBlock.compression_empty]

/-- The converse swap on the uniform extension block. -/
theorem pC_uniform_block (x : Fin N) (ψ : State N) (J : Base x)
    (h : coordinates x ψ J = UniformState.extensionUniform (Fresh J.val)) :
    coordinates x (pC x ψ) J = UniformState.emptyKet (Fresh J.val) := by
  letI := fresh_nonempty J
  rw [coordinates_pC, h, CompressionBlock.compression_uniform]

end QuantumOracle.Compression
