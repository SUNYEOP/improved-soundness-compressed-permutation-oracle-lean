import QuantumOracle.Model.FiniteIncidence
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# The positive polar normalization of an injective matrix

The map is the actual matrix `A * (sqrt (A† * A))⁻¹`. Its norm preservation
is proved from the positive square root identity, with no choice of an
unrelated isometric embedding.
-/

noncomputable section

namespace QuantumOracle.MatrixPolar

open Matrix
open scoped MatrixOrder ComplexOrder

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]

/-- The canonical positive square root of the domain Gram matrix. -/
def gramSqrt (A : Matrix R C ℂ) : Matrix C C ℂ := CFC.sqrt (Aᴴ * A)

/-- Actual positive polar normalization, defined using the inverse square root. -/
def normalize (A : Matrix R C ℂ) : Matrix R C ℂ := A * (gramSqrt A)⁻¹

theorem gramSqrt_posDef (A : Matrix R C ℂ) (hA : Function.Injective A.mulVec) :
    (gramSqrt A).PosDef :=
  Matrix.isStrictlyPositive_iff_posDef.mp <|
    IsStrictlyPositive.sqrt _ (Matrix.PosDef.conjTranspose_mul_self A hA).isStrictlyPositive

theorem gramSqrt_mul_self (A : Matrix R C ℂ) :
    gramSqrt A * gramSqrt A = Aᴴ * A :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self A).nonneg

/-- The positive square root preserves every actual Gram commutation relation. -/
theorem commute_gramSqrt (A : Matrix R C ℂ) (B : Matrix C C ℂ)
    (h : Commute (Aᴴ * A) B) : Commute (gramSqrt A) B :=
  h.cfcₙ_nnreal NNReal.sqrt

theorem normalize_mul_gramSqrt (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) : normalize A * gramSqrt A = A := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (gramSqrt_posDef A hA).isUnit
  exact Matrix.nonsing_inv_mul_cancel_right _ _ hdet

/-- A Gram eigenvector of eigenvalue one is fixed by its positive square root. -/
theorem gramSqrt_mulVec_of_gram_fixed (A : Matrix R C ℂ) (v : C → ℂ)
    (hv : (Aᴴ * A) *ᵥ v = v) : gramSqrt A *ᵥ v = v := by
  have hS : (gramSqrt A).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hpos : (gramSqrt A + 1).PosDef := by
    simpa only [add_comm] using (Matrix.PosDef.one : (1 : Matrix C C ℂ).PosDef).add_posSemidef hS
  apply Matrix.mulVec_injective_of_isUnit hpos.isUnit
  simp only [Matrix.add_mulVec, Matrix.one_mulVec]
  rw [Matrix.mulVec_mulVec, gramSqrt_mul_self, hv]
  exact add_comm _ _

/-- The normalization agrees with the original matrix on its Gram-one sector. -/
theorem normalize_mulVec_of_gram_fixed (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) (v : C → ℂ)
    (hv : (Aᴴ * A) *ᵥ v = v) : normalize A *ᵥ v = A *ᵥ v := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (gramSqrt_posDef A hA).isUnit
  have h := congrArg ((gramSqrt A)⁻¹ *ᵥ ·) (gramSqrt_mulVec_of_gram_fixed A v hv)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec] at h
  rw [normalize, ← Matrix.mulVec_mulVec, ← h]

/-- The normalized rectangular matrix has orthonormal columns. -/
theorem normalize_conjTranspose_mul (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) : (normalize A)ᴴ * normalize A = 1 := by
  have hS := gramSqrt_posDef A hA
  have hdet : IsUnit (gramSqrt A).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
  rw [normalize, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
    hS.isHermitian.eq]
  calc
    ((gramSqrt A)⁻¹ * Aᴴ) * (A * (gramSqrt A)⁻¹) =
        (gramSqrt A)⁻¹ * (Aᴴ * A) * (gramSqrt A)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (gramSqrt A)⁻¹ * (gramSqrt A * gramSqrt A) * (gramSqrt A)⁻¹ := by
      rw [gramSqrt_mul_self]
    _ = ((gramSqrt A)⁻¹ * gramSqrt A) *
        (gramSqrt A * (gramSqrt A)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet, one_mul]

variable [DecidableEq R]

theorem normalize_adjoint_comp (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) :
    (normalize A).toEuclideanLin.adjoint.comp (normalize A).toEuclideanLin =
      LinearMap.id := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    ← FiniteIncidence.toEuclideanLin_mul, normalize_conjTranspose_mul A hA]
  ext v i
  change ((1 : Matrix C C ℂ) *ᵥ (WithLp.ofLp v)) i = v i
  simp

theorem normalize_inner (A : Matrix R C ℂ) (hA : Function.Injective A.mulVec)
    (v z : EuclideanSpace ℂ C) :
    inner ℂ ((normalize A).toEuclideanLin v) ((normalize A).toEuclideanLin z) =
      inner ℂ v z := by
  rw [← LinearMap.adjoint_inner_right]
  have h := congrArg (fun f : EuclideanSpace ℂ C →ₗ[ℂ] EuclideanSpace ℂ C => f z)
    (normalize_adjoint_comp A hA)
  exact congrArg (inner ℂ v) h

/-- The bundled Euclidean isometry is exactly the positive polar matrix. -/
def isometry (A : Matrix R C ℂ) (hA : Function.Injective A.mulVec) :
    EuclideanSpace ℂ C →ₗᵢ[ℂ] EuclideanSpace ℂ R :=
  (normalize A).toEuclideanLin.isometryOfInner (normalize_inner A hA)

@[simp] theorem isometry_toLinearMap (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) :
    (isometry A hA).toLinearMap = (normalize A).toEuclideanLin := rfl

/-- Positive normalization does not change the actual image subspace. -/
theorem range_isometry (A : Matrix R C ℂ) (hA : Function.Injective A.mulVec) :
    LinearMap.range (isometry A hA).toLinearMap = LinearMap.range A.toEuclideanLin := by
  rw [isometry_toLinearMap]
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    refine ⟨((gramSqrt A)⁻¹).toEuclideanLin v, ?_⟩
    rw [normalize, FiniteIncidence.toEuclideanLin_mul]
    rfl
  · rintro _ ⟨v, rfl⟩
    refine ⟨(gramSqrt A).toEuclideanLin v, ?_⟩
    have h := FiniteIncidence.toEuclideanLin_mul (normalize A) (gramSqrt A)
    rw [normalize_mul_gramSqrt A hA] at h
    exact (congrArg (fun f : EuclideanSpace ℂ C →ₗ[ℂ] EuclideanSpace ℂ R => f v) h).symm

end QuantumOracle.MatrixPolar
