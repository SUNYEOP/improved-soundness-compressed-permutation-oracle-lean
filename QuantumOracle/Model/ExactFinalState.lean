import QuantumOracle.Model.ExactExecution
import QuantumOracle.Model.HiddenIsometry
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Actual final reduced states of exact executions

The workspace density matrix is obtained by the concrete finite partial trace
of the previously constructed exact execution. Its Hermitian, positive
semidefinite, and unit-trace properties are proved, rather than included as
assumptions about an externally supplied matrix.
-/

noncomputable section

namespace QuantumOracle.ExactFinalState

open HiddenIsometry WorkspaceKnowledge ExactExecution
open scoped BigOperators ComplexOrder

section Reduction

variable {A O : Type*} [Fintype A] [Fintype O]

/-- The actual amplitudes, arranged as workspace rows and hidden-register columns. -/
def coefficientMatrix (ψ : EuclideanSpace ℂ (A × O)) : Matrix A O ℂ :=
  fun a o => ψ (a, o)

omit [Fintype A] in
/-- The finite partial trace is exactly the Gram matrix of the amplitudes. -/
theorem reduced_eq_gram (ψ : EuclideanSpace ℂ (A × O)) :
    reduced ψ = coefficientMatrix ψ * (coefficientMatrix ψ).conjTranspose := by
  ext a b
  rfl

theorem reduced_posSemidef (ψ : EuclideanSpace ℂ (A × O)) :
    (reduced ψ).PosSemidef := by
  rw [reduced_eq_gram]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem reduced_isHermitian (ψ : EuclideanSpace ℂ (A × O)) :
    (reduced ψ).IsHermitian := (reduced_posSemidef ψ).isHermitian

/-- The partial trace has total weight equal to the joint state's norm squared. -/
theorem trace_reduced (ψ : EuclideanSpace ℂ (A × O)) :
    Matrix.trace (reduced ψ) = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, reduced_eq_inner, inner_self_eq_norm_sq_to_K]
  rw [norm_sq_eq_sum_slices]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow]
  rfl

theorem trace_reduced_of_normalized (ψ : EuclideanSpace ℂ (A × O))
    (hψ : ‖ψ‖ = 1) : Matrix.trace (reduced ψ) = 1 := by
  rw [trace_reduced, hψ]
  norm_num

end Reduction

section ExactRun

variable {N w : ℕ} {Aux : Type*} [Fintype Aux]

/-- The exact algorithm's actual final workspace density matrix after `q` queries. -/
def finalReduced (encode : BasisLookup.Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) :
    Matrix (Workspace Aux N w) (Workspace Aux N w) ℂ :=
  reduced (run encode marked gates φ q)

@[simp] theorem finalReduced_apply (encode : BasisLookup.Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) (a b : Workspace Aux N w) :
    finalReduced encode marked gates φ q a b =
      ∑ π : PermutationExtensions.Perm N,
        run encode marked gates φ q (a, π) * star (run encode marked gates φ q (b, π)) :=
  rfl

theorem finalReduced_posSemidef (encode : BasisLookup.Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) :
    (finalReduced encode marked gates φ q).PosSemidef :=
  reduced_posSemidef _

theorem finalReduced_isHermitian (encode : BasisLookup.Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) :
    (finalReduced encode marked gates φ q).IsHermitian :=
  reduced_isHermitian _

theorem finalReduced_trace (encode : BasisLookup.Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) :
    Matrix.trace (finalReduced encode marked gates φ q) = ((‖φ‖ ^ 2 : ℝ) : ℂ) := by
  rw [finalReduced, trace_reduced, run_norm]

/-- Every normalized actual exact execution produces a genuine density matrix. -/
theorem finalReduced_trace_one (encode : BasisLookup.Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (hφ : ‖φ‖ = 1) (q : ℕ) :
    Matrix.trace (finalReduced encode marked gates φ q) = 1 := by
  rw [finalReduced_trace, hφ]
  norm_num

end ExactRun

end QuantumOracle.ExactFinalState
