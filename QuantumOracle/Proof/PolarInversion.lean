import QuantumOracle.Proof.InversionSymmetry
import QuantumOracle.Model.PolarEmbedding
import QuantumOracle.Proof.PolarIntertwining

/-!
# Inversion symmetry of the actual polar isometry

The involutive isometries are the concrete permutation and database inversion
maps. Their self-adjointness is proved here, so positive polar normalization
preserves the actual raw intertwining without any assumed symmetry operators.
-/

noncomputable section

namespace QuantumOracle.PolarInversion

open PermutationExtensions InversionSymmetry
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable

def oracleMatrix (N : ℕ) : Matrix (Perm N) (Perm N) ℂ :=
  Matrix.toEuclideanLin.symm (oracle N).toLinearEquiv.toLinearMap

def databaseMatrix (N : ℕ) : Matrix (Database N) (Database N) ℂ :=
  Matrix.toEuclideanLin.symm (database N).toLinearEquiv.toLinearMap

@[simp] theorem oracleMatrix_operator (N : ℕ) :
    (oracleMatrix N).toEuclideanLin = (oracle N).toLinearEquiv.toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

@[simp] theorem databaseMatrix_operator (N : ℕ) :
    (databaseMatrix N).toEuclideanLin = (database N).toLinearEquiv.toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

theorem oracle_isSymmetric (N : ℕ) : (oracle N).toLinearEquiv.toLinearMap.IsSymmetric := by
  intro h k
  exact (oracle_inner_right N h k).symm

theorem database_isSymmetric (N : ℕ) :
    (database N).toLinearEquiv.toLinearMap.IsSymmetric := by
  intro ψ φ
  change ⟪database N ψ, φ⟫_ℂ = ⟪ψ, database N φ⟫_ℂ
  have hi := (database N).inner_map_map ψ (database N φ)
  simpa only [database_involutive] using hi

theorem oracleMatrix_isHermitian (N : ℕ) : (oracleMatrix N).IsHermitian := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  rw [oracleMatrix_operator]
  exact oracle_isSymmetric N

theorem databaseMatrix_isHermitian (N : ℕ) : (databaseMatrix N).IsHermitian := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  rw [databaseMatrix_operator]
  exact database_isSymmetric N

theorem matrix_intertwines (N : ℕ) :
    PolarEmbedding.matrix N * oracleMatrix N = databaseMatrix N * PolarEmbedding.matrix N := by
  apply Matrix.toEuclideanLin.injective
  simp only [FiniteIncidence.toEuclideanLin_mul, PolarEmbedding.matrix_operator,
    oracleMatrix_operator, databaseMatrix_operator]
  apply LinearMap.ext
  intro h
  exact total_intertwines N h

/-- The normalized map intertwines actual inversion as a linear-map identity. -/
theorem candidate_intertwines_linearMap (N : ℕ) :
    (PolarEmbedding.candidate N).toLinearMap.comp (oracle N).toLinearEquiv.toLinearMap =
      (database N).toLinearEquiv.toLinearMap.comp (PolarEmbedding.candidate N).toLinearMap := by
  have h := PolarIntertwining.normalize_intertwines (PolarEmbedding.matrix N)
    (PolarEmbedding.matrix_mulVec_injective N) (oracleMatrix N) (databaseMatrix N)
    (oracleMatrix_isHermitian N) (databaseMatrix_isHermitian N) (matrix_intertwines N)
  have hlin := congrArg Matrix.toEuclideanLin h
  simpa only [FiniteIncidence.toEuclideanLin_mul, oracleMatrix_operator,
    databaseMatrix_operator, ← PolarEmbedding.candidate_toLinearMap] using hlin

/-- Exact inversion symmetry of the constructed polar comparison isometry. -/
theorem candidate_intertwines (N : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    PolarEmbedding.candidate N (oracle N h) = database N (PolarEmbedding.candidate N h) :=
  LinearMap.congr_fun (candidate_intertwines_linearMap N) h

/-- The actual inverted image satisfies the same fresh-extension cancellation. -/
theorem candidate_cancels_inverse {N : ℕ} (x : Fin N) (h : EuclideanSpace ℂ (Perm N)) :
    CompressionCancellation.Cancels x (database N (PolarEmbedding.candidate N h)) := by
  rw [← candidate_intertwines]
  exact PolarEmbedding.candidate_cancels x (oracle N h)

/-- Actual compression fixes the defined part after database inversion as well. -/
theorem pC_definedPart_candidate_inverse {N : ℕ} (x : Fin N)
    (h : EuclideanSpace ℂ (Perm N)) :
    Compression.pC x
      (CompressionCancellation.definedPart x (database N (PolarEmbedding.candidate N h))) =
      CompressionCancellation.definedPart x (database N (PolarEmbedding.candidate N h)) :=
  CompressionCancellation.pC_definedPart x _ (candidate_cancels_inverse x h)

end QuantumOracle.PolarInversion
