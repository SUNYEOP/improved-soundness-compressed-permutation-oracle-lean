import QuantumOracle.Model.MatrixPolar

/-!
# Intertwining preserved by positive polar normalization

Self-adjoint intertwiners commute with the actual Gram matrix and its positive
inverse square root. Consequently the concrete polar isometry preserves the
intertwining relation, including the ranges and fixed spaces of projections.
-/

noncomputable section

namespace QuantumOracle.PolarIntertwining

open Matrix
open scoped ComplexOrder

variable {R C : Type*} [Fintype R] [Fintype C]

/-- A self-adjoint intertwining relation makes the domain Gram matrix commute. -/
theorem gram_commute_of_intertwines (A : Matrix R C ℂ)
    (P : Matrix C C ℂ) (Q : Matrix R R ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hAP : A * P = Q * A) :
    Commute (Aᴴ * A) P := by
  have hadj : P * Aᴴ = Aᴴ * Q := by
    have h := congrArg Matrix.conjTranspose hAP
    simpa only [Matrix.conjTranspose_mul, hP.eq, hQ.eq] using h
  show (Aᴴ * A) * P = P * (Aᴴ * A)
  calc
    (Aᴴ * A) * P = Aᴴ * (A * P) := Matrix.mul_assoc _ _ _
    _ = Aᴴ * (Q * A) := by rw [hAP]
    _ = (Aᴴ * Q) * A := (Matrix.mul_assoc _ _ _).symm
    _ = (P * Aᴴ) * A := by rw [hadj]
    _ = P * (Aᴴ * A) := Matrix.mul_assoc _ _ _

variable [DecidableEq C]

/-- Every actual Gram commutation relation survives inverse square root. -/
theorem inverse_gramSqrt_commute (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) (P : Matrix C C ℂ)
    (hGram : Commute (Aᴴ * A) P) : Commute (MatrixPolar.gramSqrt A)⁻¹ P := by
  have hS := MatrixPolar.commute_gramSqrt A P hGram
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp
    (MatrixPolar.gramSqrt_posDef A hA).isUnit
  have hleft := Matrix.nonsing_inv_mul _ hdet
  have hright := Matrix.mul_nonsing_inv _ hdet
  show (MatrixPolar.gramSqrt A)⁻¹ * P = P * (MatrixPolar.gramSqrt A)⁻¹
  calc
    (MatrixPolar.gramSqrt A)⁻¹ * P =
        ((MatrixPolar.gramSqrt A)⁻¹ * P) *
          (MatrixPolar.gramSqrt A * (MatrixPolar.gramSqrt A)⁻¹) := by rw [hright, mul_one]
    _ = (MatrixPolar.gramSqrt A)⁻¹ * (P * MatrixPolar.gramSqrt A) *
        (MatrixPolar.gramSqrt A)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (MatrixPolar.gramSqrt A)⁻¹ * (MatrixPolar.gramSqrt A * P) *
        (MatrixPolar.gramSqrt A)⁻¹ := by rw [hS.eq]
    _ = ((MatrixPolar.gramSqrt A)⁻¹ * MatrixPolar.gramSqrt A) * P *
        (MatrixPolar.gramSqrt A)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = P * (MatrixPolar.gramSqrt A)⁻¹ := by rw [hleft, one_mul]

/-- Gram commutation is enough to preserve an arbitrary intertwining relation. -/
theorem normalize_intertwines_of_gram_commute (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) (P : Matrix C C ℂ) (Q : Matrix R R ℂ)
    (hGram : Commute (Aᴴ * A) P) (hAP : A * P = Q * A) :
    MatrixPolar.normalize A * P = Q * MatrixPolar.normalize A := by
  have hS := inverse_gramSqrt_commute A hA P hGram
  unfold MatrixPolar.normalize
  calc
    (A * (MatrixPolar.gramSqrt A)⁻¹) * P =
        A * ((MatrixPolar.gramSqrt A)⁻¹ * P) := Matrix.mul_assoc _ _ _
    _ = A * (P * (MatrixPolar.gramSqrt A)⁻¹) := by rw [hS.eq]
    _ = (A * P) * (MatrixPolar.gramSqrt A)⁻¹ := (Matrix.mul_assoc _ _ _).symm
    _ = (Q * A) * (MatrixPolar.gramSqrt A)⁻¹ := by rw [hAP]
    _ = Q * (A * (MatrixPolar.gramSqrt A)⁻¹) := Matrix.mul_assoc _ _ _

/-- Positive polar normalization preserves self-adjoint intertwining relations. -/
theorem normalize_intertwines (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) (P : Matrix C C ℂ) (Q : Matrix R R ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hAP : A * P = Q * A) :
    MatrixPolar.normalize A * P = Q * MatrixPolar.normalize A :=
  normalize_intertwines_of_gram_commute A hA P Q
    (gram_commute_of_intertwines A P Q hP hQ hAP) hAP

variable [DecidableEq R]

theorem normalize_intertwines_toEuclideanLin (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) (P : Matrix C C ℂ) (Q : Matrix R R ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hAP : A * P = Q * A) :
    (MatrixPolar.normalize A).toEuclideanLin.comp P.toEuclideanLin =
      Q.toEuclideanLin.comp (MatrixPolar.normalize A).toEuclideanLin := by
  rw [← FiniteIncidence.toEuclideanLin_mul, ← FiniteIncidence.toEuclideanLin_mul,
    normalize_intertwines A hA P Q hP hQ hAP]

theorem isometry_intertwines (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) (P : Matrix C C ℂ) (Q : Matrix R R ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hAP : A * P = Q * A) :
    (MatrixPolar.isometry A hA).toLinearMap.comp P.toEuclideanLin =
      Q.toEuclideanLin.comp (MatrixPolar.isometry A hA).toLinearMap :=
  normalize_intertwines_toEuclideanLin A hA P Q hP hQ hAP

/-- In particular the polar isometry takes a projector's fixed space to the
fixed space of the matching output projector. -/
theorem isometry_fixed (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) (P : Matrix C C ℂ) (Q : Matrix R R ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hAP : A * P = Q * A)
    (v : EuclideanSpace ℂ C) (hv : P.toEuclideanLin v = v) :
    Q.toEuclideanLin (MatrixPolar.isometry A hA v) = MatrixPolar.isometry A hA v := by
  have h := congrArg (fun f : EuclideanSpace ℂ C →ₗ[ℂ] EuclideanSpace ℂ R => f v)
    (isometry_intertwines A hA P Q hP hQ hAP)
  simpa only [LinearMap.comp_apply, hv, LinearIsometry.coe_toLinearMap] using h.symm

/-- The range of a self-adjoint input map is taken into the matching output
range; this applies directly to orthogonal projectors. -/
theorem isometry_maps_range (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) (P : Matrix C C ℂ) (Q : Matrix R R ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hAP : A * P = Q * A) :
    (LinearMap.range P.toEuclideanLin).map (MatrixPolar.isometry A hA).toLinearMap ≤
      LinearMap.range Q.toEuclideanLin := by
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  refine ⟨MatrixPolar.isometry A hA v, ?_⟩
  exact (congrArg (fun f : EuclideanSpace ℂ C →ₗ[ℂ] EuclideanSpace ℂ R => f v)
    (isometry_intertwines A hA P Q hP hQ hAP)).symm

end QuantumOracle.PolarIntertwining
