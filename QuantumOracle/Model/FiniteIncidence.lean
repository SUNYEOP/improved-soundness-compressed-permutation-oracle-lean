import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Fintype.Card

/-! Finite incidence matrices and their actual Euclidean adjoints. These are
general algebraic counting identities, to be instantiated by permutation extensions. -/

noncomputable section

namespace QuantumOracle.FiniteIncidence

attribute [local instance] Classical.propDecidable

variable {R C : Type*} [Fintype R] [Fintype C]

def matrix (a : ℂ) (p : R → C → Prop) : Matrix R C ℂ := by
  classical
  exact fun r c => if p r c then a else 0

omit [Fintype R] in
theorem kernel_entry (a : ℂ) (p : R → C → Prop) (r s : R) :
    (matrix a p * (matrix a p).conjTranspose) r s =
      (Fintype.card {c : C // p r c ∧ p s c} : ℂ) * (a * star a) := by
  classical
  rw [Matrix.mul_apply]
  calc
    _ = ∑ c : C, if p r c ∧ p s c then a * star a else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases hr : p r c <;> by_cases hs : p s c <;>
        simp [matrix, Matrix.conjTranspose_apply, hr, hs]
    _ = _ := by
      simp [Fintype.card_subtype, Finset.sum_ite]

omit [Fintype R] in
theorem toEuclideanLin_mul {D : Type*} [Fintype D] [DecidableEq C] [DecidableEq D]
    (A : Matrix R C ℂ) (B : Matrix C D ℂ) :
    (A * B).toEuclideanLin = A.toEuclideanLin.comp B.toEuclideanLin := by
  ext ψ r
  change Matrix.mulVec (A * B) (WithLp.ofLp ψ) r =
    Matrix.mulVec A (Matrix.mulVec B (WithLp.ofLp ψ)) r
  rw [Matrix.mulVec_mulVec]

/-- The matrix product here is the actual operator composed with its adjoint. -/
theorem gram_operator [DecidableEq R] [DecidableEq C] (A : Matrix R C ℂ) :
    (A * A.conjTranspose).toEuclideanLin =
      A.toEuclideanLin.comp A.toEuclideanLin.adjoint := by
  rw [toEuclideanLin_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

end QuantumOracle.FiniteIncidence
