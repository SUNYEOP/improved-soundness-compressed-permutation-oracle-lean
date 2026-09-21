import QuantumOracle.Model.ConsistentState
import QuantumOracle.Model.CommonDatabases
import QuantumOracle.Model.FiniteIncidence

/-!
# The actual extension operator and its central kernel

`T` sends each size-t database ket to its normalized consistent-permutation
vector. The kernel calculation is the combinatorial first step of Appendix A;
it does not assert the irreducible eigenvalues or construct the harmonic W map.
-/

noncomputable section

namespace QuantumOracle.ExtensionOperator

open PermutationExtensions

attribute [local instance] Classical.propDecidable

abbrev Level (N t : ℕ) := Database.level N t

noncomputable instance levelFintype (N t : ℕ) : Fintype (Level N t) := by
  classical
  unfold Level Database.level
  infer_instance

def amplitude (N t : ℕ) : ℂ :=
  (((Real.sqrt ((N - t).factorial : ℝ))⁻¹ : ℝ) : ℂ)

/-- Columns are the actual normalized consistent-permutation vectors. -/
def matrix (N t : ℕ) : Matrix (Perm N) (Level N t) ℂ :=
  fun π I => ConsistentState.vector I.val π

/-- The manuscript's `T_{N,t}` as a concrete complex linear map. -/
def T (N t : ℕ) :
    EuclideanSpace ℂ (Level N t) →ₗ[ℂ] EuclideanSpace ℂ (Perm N) :=
  (matrix N t).toEuclideanLin

theorem matrix_eq_incidence (N t : ℕ) :
    matrix N t = FiniteIncidence.matrix (amplitude N t)
      (fun π (I : Level N t) => Extends I.val π) := by
  classical
  ext π I
  simp [matrix, FiniteIncidence.matrix, ConsistentState.vector_apply,
    ConsistentState.amplitude, amplitude, I.property]

/-- This fixes the operator's action on each actual database basis vector. -/
@[simp] theorem T_single (N t : ℕ) (I : Level N t) :
    T N t (EuclideanSpace.single I 1) = ConsistentState.vector I.val := by
  classical
  ext π
  change Matrix.mulVec (matrix N t) (Pi.single I 1) π = _
  rw [Matrix.mulVec_single_one]
  rfl

theorem amplitude_mul_star (N t : ℕ) :
    amplitude N t * star (amplitude N t) = (1 : ℂ) / ((N - t).factorial : ℂ) := by
  have h : (Real.sqrt ((N - t).factorial : ℝ))⁻¹ *
      (Real.sqrt ((N - t).factorial : ℝ))⁻¹ = ((N - t).factorial : ℝ)⁻¹ := by
    rw [← mul_inv, ← sq, Real.sq_sqrt (Nat.cast_nonneg _)]
  simpa [amplitude] using congrArg Complex.ofReal h

def gramMatrix (N t : ℕ) : Matrix (Perm N) (Perm N) ℂ :=
  matrix N t * (matrix N t).conjTranspose

/-- The actual matrix of `T T†` has the manuscript's binomial kernel. -/
theorem gramMatrix_entry {N : ℕ} (t : ℕ) (π σ : Perm N) :
    gramMatrix N t π σ =
      ((Nat.choose (CommonDatabases.agreeingInputs π σ).card t : ℕ) : ℂ) /
        ((N - t).factorial : ℂ) := by
  classical
  unfold gramMatrix
  rw [matrix_eq_incidence, FiniteIncidence.kernel_entry, amplitude_mul_star]
  rw [CommonDatabases.card_level_common]
  ring

/-- Appendix A, `eq:central-kernel`, with the relative-permutation orientation explicit. -/
theorem gramMatrix_entry_fixedPoints {N : ℕ} (t : ℕ) (π σ : Perm N) :
    gramMatrix N t π σ =
      ((Nat.choose (Fintype.card {x : Fin N // (σ.trans π.symm) x = x}) t : ℕ) : ℂ) /
        ((N - t).factorial : ℂ) := by
  rw [gramMatrix_entry, CommonDatabases.card_agreeingInputs_eq_fixedPoints]

/-- The counted matrix really is the product of T with its mathematical adjoint. -/
theorem gramMatrix_operator (N t : ℕ) :
    (gramMatrix N t).toEuclideanLin = (T N t).comp (T N t).adjoint :=
  FiniteIncidence.gram_operator _

/-- Appendix A's entry formula expressed directly through the operator and its adjoint. -/
theorem T_adjoint_basis_entry {N : ℕ} (t : ℕ) (π σ : Perm N) :
    ((T N t).comp (T N t).adjoint) (EuclideanSpace.single σ 1) π =
      ((Nat.choose (Fintype.card {x : Fin N // (σ.trans π.symm) x = x}) t : ℕ) : ℂ) /
        ((N - t).factorial : ℂ) := by
  classical
  rw [← gramMatrix_operator]
  change Matrix.mulVec (gramMatrix N t) (Pi.single σ 1) π = _
  rw [Matrix.mulVec_single_one]
  exact gramMatrix_entry_fixedPoints t π σ

/-- The actual kernel is invariant under simultaneous input and output relabeling. -/
theorem gramMatrix_relabel {N : ℕ} (t : ℕ) (π σ α β : Perm N) :
    gramMatrix N t ((α.trans π).trans β) ((α.trans σ).trans β) =
      gramMatrix N t π σ := by
  rw [gramMatrix_entry, gramMatrix_entry, CommonDatabases.card_agreeingInputs_relabel]

end QuantumOracle.ExtensionOperator
