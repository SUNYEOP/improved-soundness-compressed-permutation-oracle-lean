import QuantumOracle.Proof.PolarIntertwining

/-!
# Unitary symmetries of positive polar normalization

The input and output symmetry need not be involutions. Their actual unitarity
and a raw intertwining identity imply the same identity for the positive polar
isometry. Matrices of bundled Euclidean isometry equivalences supply the
unitarity identities internally.
-/

noncomputable section

namespace QuantumOracle.PolarUnitary

open Matrix
open scoped InnerProductSpace

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

theorem gram_commute_of_unitary_intertwines (A : Matrix R C ℂ)
    (P : Matrix C C ℂ) (Q : Matrix R R ℂ)
    (hP : P * Pᴴ = 1) (hQ : Qᴴ * Q = 1) (hAP : A * P = Q * A) :
    Commute (Aᴴ * A) P := by
  have hadj : Pᴴ * Aᴴ = Aᴴ * Qᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hAP
  have hback : Aᴴ * Q = P * Aᴴ := by
    calc
      Aᴴ * Q = (P * Pᴴ) * Aᴴ * Q := by rw [hP, Matrix.one_mul]
      _ = P * (Pᴴ * Aᴴ) * Q := by simp only [Matrix.mul_assoc]
      _ = P * (Aᴴ * Qᴴ) * Q := by rw [hadj]
      _ = P * Aᴴ * (Qᴴ * Q) := by simp only [Matrix.mul_assoc]
      _ = P * Aᴴ := by rw [hQ, Matrix.mul_one]
  show (Aᴴ * A) * P = P * (Aᴴ * A)
  calc
    (Aᴴ * A) * P = Aᴴ * (A * P) := Matrix.mul_assoc _ _ _
    _ = Aᴴ * (Q * A) := by rw [hAP]
    _ = (Aᴴ * Q) * A := (Matrix.mul_assoc _ _ _).symm
    _ = (P * Aᴴ) * A := by rw [hback]
    _ = P * (Aᴴ * A) := Matrix.mul_assoc _ _ _

theorem normalize_intertwines (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) (P : Matrix C C ℂ) (Q : Matrix R R ℂ)
    (hP : P * Pᴴ = 1) (hQ : Qᴴ * Q = 1) (hAP : A * P = Q * A) :
    MatrixPolar.normalize A * P = Q * MatrixPolar.normalize A :=
  PolarIntertwining.normalize_intertwines_of_gram_commute A hA P Q
    (gram_commute_of_unitary_intertwines A P Q hP hQ hAP) hAP

/-- The matrix of an actual Euclidean isometry equivalence. -/
def matrix (e : EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C) : Matrix C C ℂ :=
  Matrix.toEuclideanLin.symm e.toLinearEquiv.toLinearMap

@[simp] theorem matrix_operator (e : EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C) :
    (matrix e).toEuclideanLin = e.toLinearEquiv.toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

omit [DecidableEq C] in
theorem adjoint_equiv (e : EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C) :
    e.toLinearEquiv.toLinearMap.adjoint = e.symm.toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro v
  apply ext_inner_right ℂ
  intro w
  rw [LinearMap.adjoint_inner_left]
  change ⟪v, e w⟫_ℂ = ⟪e.symm v, w⟫_ℂ
  simpa only [LinearIsometryEquiv.apply_symm_apply] using e.inner_map_map (e.symm v) w

@[simp] theorem matrix_conjTranspose_operator
    (e : EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C) :
    (matrix e)ᴴ.toEuclideanLin = e.symm.toLinearEquiv.toLinearMap := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, matrix_operator, adjoint_equiv]

theorem matrix_mul_conjTranspose (e : EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C) :
    matrix e * (matrix e)ᴴ = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [FiniteIncidence.toEuclideanLin_mul, matrix_operator, matrix_conjTranspose_operator]
  apply LinearMap.ext
  intro v
  ext i
  change e (e.symm v) i = ((1 : Matrix C C ℂ) *ᵥ WithLp.ofLp v) i
  simp

theorem matrix_conjTranspose_mul (e : EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C) :
    (matrix e)ᴴ * matrix e = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [FiniteIncidence.toEuclideanLin_mul, matrix_operator, matrix_conjTranspose_operator]
  apply LinearMap.ext
  intro v
  ext i
  change e.symm (e v) i = ((1 : Matrix C C ℂ) *ᵥ WithLp.ofLp v) i
  simp

/-- A raw intertwiner between actual unitary symmetries survives normalization. -/
theorem isometry_intertwines (A : Matrix R C ℂ) (hA : Function.Injective A.mulVec)
    (p : EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (q : EuclideanSpace ℂ R ≃ₗᵢ[ℂ] EuclideanSpace ℂ R)
    (h : A.toEuclideanLin.comp p.toLinearEquiv.toLinearMap =
      q.toLinearEquiv.toLinearMap.comp A.toEuclideanLin) :
    (MatrixPolar.isometry A hA).toLinearMap.comp p.toLinearEquiv.toLinearMap =
      q.toLinearEquiv.toLinearMap.comp (MatrixPolar.isometry A hA).toLinearMap := by
  have hmatrix : A * matrix p = matrix q * A := by
    apply Matrix.toEuclideanLin.injective
    simpa only [FiniteIncidence.toEuclideanLin_mul, matrix_operator] using h
  have hn := normalize_intertwines A hA (matrix p) (matrix q)
    (matrix_mul_conjTranspose p) (matrix_conjTranspose_mul q) hmatrix
  have hlin := congrArg Matrix.toEuclideanLin hn
  simpa only [FiniteIncidence.toEuclideanLin_mul, matrix_operator,
    MatrixPolar.isometry_toLinearMap] using hlin

end QuantumOracle.PolarUnitary
