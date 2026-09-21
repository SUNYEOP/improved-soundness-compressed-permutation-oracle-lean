import QuantumOracle.Model.RawEmbedding
import QuantumOracle.Model.MatrixPolar

/-!
# The actual positive polar isometry of the assembled degree map

The concrete injective map `RawEmbedding.total` is normalized by its positive
domain Gram square root. This gives an actual isometry with precisely the raw
image, so the proved physical database cancellation survives normalization.

The uniform initialization identity is proved for this normalized map.
`PolarSpectrum` proves its scalar spectral form, and `FiniteSoundnessWitness`
uses it to bound the discrepancy between the two oracle executions.
-/

noncomputable section

namespace QuantumOracle.PolarEmbedding

open PermutationExtensions
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable

/-- The matrix of the actual assembled degree map in the Euclidean bases. -/
def matrix (N : ℕ) : Matrix (Database N) (Perm N) ℂ :=
  Matrix.toEuclideanLin.symm (RawEmbedding.total N)

@[simp] theorem matrix_operator (N : ℕ) :
    (matrix N).toEuclideanLin = RawEmbedding.total N :=
  Matrix.toEuclideanLin.apply_symm_apply _

/-- Each column is the actual raw image of the corresponding permutation ket. -/
theorem matrix_entry (N : ℕ) (I : Database N) (π : Perm N) :
    matrix N I π = RawEmbedding.total N (EuclideanSpace.single π 1) I := by
  classical
  rw [← matrix_operator N]
  change matrix N I π = Matrix.mulVec (matrix N) (Pi.single π 1) I
  rw [Matrix.mulVec_single_one]
  rfl

theorem matrix_mulVec_injective (N : ℕ) : Function.Injective (matrix N).mulVec := by
  intro v z hvz
  have h : (matrix N).toEuclideanLin (WithLp.toLp 2 v) =
      (matrix N).toEuclideanLin (WithLp.toLp 2 z) := congrArg (WithLp.toLp 2) hvz
  rw [matrix_operator N] at h
  exact congrArg WithLp.ofLp (RawEmbedding.total_injective N h)

/-- Canonical positive polar normalization of the actual assembled map. -/
def candidate (N : ℕ) :
    EuclideanSpace ℂ (Perm N) →ₗᵢ[ℂ] Compression.State N :=
  MatrixPolar.isometry (matrix N) (matrix_mulVec_injective N)

theorem candidate_toLinearMap (N : ℕ) :
    (candidate N).toLinearMap = (MatrixPolar.normalize (matrix N)).toEuclideanLin := rfl

@[simp] theorem candidate_norm (N : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    ‖candidate N h‖ = ‖h‖ := (candidate N).norm_map h

theorem candidate_inner (N : ℕ) (h k : EuclideanSpace ℂ (Perm N)) :
    ⟪candidate N h, candidate N k⟫_ℂ = ⟪h, k⟫_ℂ :=
  (candidate N).inner_map_map h k

/-- Normalization preserves the concrete physical database image exactly. -/
theorem range_candidate (N : ℕ) :
    LinearMap.range (candidate N).toLinearMap = LinearMap.range (RawEmbedding.total N) := by
  rw [candidate, MatrixPolar.range_isometry, matrix_operator]

/-- Positive polar normalization preserves the actual uniform initialization. -/
theorem candidate_uniform (N : ℕ) :
    candidate N (ConsistentState.vector Database.empty) =
      EuclideanSpace.single (Database.empty : Database N) 1 := by
  let u := ConsistentState.vector (Database.empty : Database N)
  have hg : ((matrix N).conjTranspose * matrix N).toEuclideanLin u = u := by
    rw [FiniteIncidence.toEuclideanLin_mul,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, matrix_operator]
    exact RawEmbedding.total_gram_uniform N
  have hcoords : ((matrix N).conjTranspose * matrix N).mulVec (WithLp.ofLp u) =
      WithLp.ofLp u := congrArg WithLp.ofLp hg
  have hn := MatrixPolar.normalize_mulVec_of_gram_fixed (matrix N)
    (matrix_mulVec_injective N) (WithLp.ofLp u) hcoords
  have heq : candidate N u = RawEmbedding.total N u := by
    change (MatrixPolar.normalize (matrix N)).toEuclideanLin u = _
    rw [← matrix_operator N]
    exact congrArg (WithLp.toLp 2) hn
  exact heq.trans (RawEmbedding.total_uniform N)

/-- Every vector of the normalized image still has cancelling fresh-extension sums. -/
theorem candidate_cancels {N : ℕ} (x : Fin N) (h : EuclideanSpace ℂ (Perm N)) :
    CompressionCancellation.Cancels x (candidate N h) := by
  apply RawEmbedding.cancels_of_mem_range
  rw [← range_candidate N]
  exact ⟨h, rfl⟩

/-- Actual compression fixes the defined part of the normalized image. -/
theorem pC_definedPart_candidate {N : ℕ} (x : Fin N)
    (h : EuclideanSpace ℂ (Perm N)) :
    Compression.pC x (CompressionCancellation.definedPart x (candidate N h)) =
      CompressionCancellation.definedPart x (candidate N h) :=
  CompressionCancellation.pC_definedPart x _ (candidate_cancels x h)

/-- The normalized image also has no undefined-base amplitude after compression. -/
theorem pC_candidate_apply_base {N : ℕ} (x : Fin N)
    (h : EuclideanSpace ℂ (Perm N)) (J : CompressionIndex.Base x) :
    Compression.pC x (candidate N h) J.val = 0 :=
  CompressionCancellation.pC_apply_base x _ (candidate_cancels x h) J

end QuantumOracle.PolarEmbedding
