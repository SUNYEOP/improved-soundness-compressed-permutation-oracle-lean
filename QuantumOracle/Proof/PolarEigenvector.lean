import QuantumOracle.Model.MatrixPolar

/-!
# Actual polar normalization on a positive Gram eigenspace

These generic identities assume an explicitly stated eigenvector relation for
the actual Gram matrix. They do not identify its eigenvalues with any
representation-theoretic formula or prove a query-error estimate.
-/

noncomputable section

namespace QuantumOracle.PolarEigenvector

open Matrix
open scoped MatrixOrder ComplexOrder

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]

/-- The actual positive square root acts by the positive scalar square root on
an explicitly given positive Gram eigenvector. -/
theorem gramSqrt_mulVec_of_eigenvector (A : Matrix R C ℂ) (v : C → ℂ)
    (μ : ℝ) (hμ : 0 < μ) (hv : (Aᴴ * A) *ᵥ v = (μ : ℂ) • v) :
    MatrixPolar.gramSqrt A *ᵥ v = (Real.sqrt μ : ℂ) • v := by
  have hsqrt : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hscalar : ((Real.sqrt μ : ℂ) • (1 : Matrix C C ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast hsqrt)
  have hS : (MatrixPolar.gramSqrt A).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hpos : (MatrixPolar.gramSqrt A + (Real.sqrt μ : ℂ) • (1 : Matrix C C ℂ)).PosDef := by
    simpa only [add_comm] using hscalar.add_posSemidef hS
  have hsq : (Real.sqrt μ : ℂ) * (Real.sqrt μ : ℂ) = (μ : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hμ.le
  apply Matrix.mulVec_injective_of_isUnit hpos.isUnit
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul]
  rw [Matrix.mulVec_mulVec, MatrixPolar.gramSqrt_mul_self, hv, smul_add, smul_smul, hsq]
  exact add_comm _ _

/-- The inverse square root acts by the reciprocal square root on a positive
Gram eigenspace of an injective matrix. -/
theorem inverse_gramSqrt_mulVec_of_eigenvector (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) (v : C → ℂ)
    (μ : ℝ) (hμ : 0 < μ) (hv : (Aᴴ * A) *ᵥ v = (μ : ℂ) • v) :
    (MatrixPolar.gramSqrt A)⁻¹ *ᵥ v = (((Real.sqrt μ)⁻¹ : ℝ) : ℂ) • v := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp
    (MatrixPolar.gramSqrt_posDef A hA).isUnit
  have hsqrt : (Real.sqrt μ : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hμ).ne'
  have h := congrArg ((MatrixPolar.gramSqrt A)⁻¹ *ᵥ ·)
    (gramSqrt_mulVec_of_eigenvector A v μ hμ hv)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec,
    Matrix.mulVec_smul] at h
  have h' := congrArg (fun z : C → ℂ => (Real.sqrt μ : ℂ)⁻¹ • z) h
  simpa only [smul_smul, inv_mul_cancel₀ hsqrt, one_smul, Complex.ofReal_inv] using h'.symm

/-- On a known positive Gram eigenspace, actual polar normalization is the
original matrix multiplied by the reciprocal square root of its eigenvalue. -/
theorem normalize_mulVec_of_eigenvector (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) (v : C → ℂ)
    (μ : ℝ) (hμ : 0 < μ) (hv : (Aᴴ * A) *ᵥ v = (μ : ℂ) • v) :
    MatrixPolar.normalize A *ᵥ v = (((Real.sqrt μ)⁻¹ : ℝ) : ℂ) • (A *ᵥ v) := by
  rw [MatrixPolar.normalize, ← Matrix.mulVec_mulVec,
    inverse_gramSqrt_mulVec_of_eigenvector A hA v μ hμ hv, Matrix.mulVec_smul]

variable [DecidableEq R]

/-- The same identity for the bundled Euclidean isometry. The hypothesis is
the eigenvector equation for the actual Euclidean Gram operator. -/
theorem isometry_apply_of_gram_eigenvector (A : Matrix R C ℂ)
    (hA : Function.Injective A.mulVec) (v : EuclideanSpace ℂ C)
    (μ : ℝ) (hμ : 0 < μ)
    (hv : (Aᴴ * A).toEuclideanLin v = (μ : ℂ) • v) :
    MatrixPolar.isometry A hA v =
      (((Real.sqrt μ)⁻¹ : ℝ) : ℂ) • A.toEuclideanLin v := by
  have hcoeff : (Aᴴ * A) *ᵥ WithLp.ofLp v = (μ : ℂ) • WithLp.ofLp v :=
    congrArg WithLp.ofLp hv
  change (MatrixPolar.normalize A).toEuclideanLin v = _
  rw [Matrix.toLpLin_apply,
    normalize_mulVec_of_eigenvector A hA (WithLp.ofLp v) μ hμ hcoeff,
    WithLp.toLp_smul]
  rfl

end QuantumOracle.PolarEigenvector
