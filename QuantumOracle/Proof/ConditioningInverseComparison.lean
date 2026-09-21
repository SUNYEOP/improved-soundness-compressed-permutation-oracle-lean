import QuantumOracle.Proof.ConditioningComparison
import QuantumOracle.Proof.ConditioningInverse
import QuantumOracle.Proof.PolarInversion

/-!
# Actual inverse-query comparison from two forward conditioning errors

The constructed polar map intertwines the actual register inversions. The
database flip is an isometry and the actual inverse compressed query is its
conjugate of the forward query. These facts transfer the concrete forward
two-error reduction to inverse ordinary and marked queries, without any
numerical conditioning-error premise.
-/

noncomputable section

namespace QuantumOracle.ConditioningInverseComparison

open BasisLookup PermutationExtensions HiddenIsometry

variable {N w : ℕ}

attribute [local irreducible] PolarEmbedding.candidate

/-- The proved actual polar inversion relation lifts over any finite workspace. -/
theorem onOracle_candidate_inversion {A : Type*} [Fintype A]
    (ψ : EuclideanSpace ℂ (A × Perm N)) :
    onOracle A (PolarEmbedding.candidate N)
        (onOracle A (InversionSymmetry.oracle N).toLinearIsometry ψ) =
      CompressedQuery.flip A (onOracle A (PolarEmbedding.candidate N) ψ) := by
  ext ⟨a, I⟩
  change PolarEmbedding.candidate N (InversionSymmetry.oracle N (WorkspaceKnowledge.slice ψ a)) I =
    PolarEmbedding.candidate N (WorkspaceKnowledge.slice ψ a) I.inverse
  rw [PolarInversion.candidate_intertwines]
  rfl

private theorem norm_involutive_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E ≃ₗᵢ[ℂ] E) (hF : Function.Involutive F) (a b : E) :
    ‖F a - b‖ = ‖a - F b‖ := by
  have hn := F.norm_map (a - F b)
  rw [map_sub, hF] at hn
  exact hn

theorem inverse_ordinary_apply (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ (Bits w × Database N)) :
    CompressedQuery.inverseOrdinary encode x ψ =
      CompressedQuery.flip (Bits w) (CompressedQuery.ordinary encode x (CompressedQuery.flip (Bits w) ψ)) := rfl

theorem inverse_marked_apply (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Database N)) :
    CompressedQuery.inverseMarked encode x ψ =
      CompressedQuery.flip (Bool × Bits w)
        (CompressedQuery.marked encode x (CompressedQuery.flip (Bool × Bits w) ψ)) := rfl

/-- The inverse comparison has the forward error norm on the inverted exact input. -/
theorem inverse_ordinary_error_eq (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ (Bits w × Perm N)) :
    ‖CompressedQuery.inverseOrdinary encode x
        (onOracle (Bits w) (PolarEmbedding.candidate N) ψ) -
      onOracle (Bits w) (PolarEmbedding.candidate N) (Query.exactOrdinary encode true x ψ)‖ =
    ‖CompressedQuery.ordinary encode x
        (onOracle (Bits w) (PolarEmbedding.candidate N)
          (onOracle (Bits w) (InversionSymmetry.oracle N).toLinearIsometry ψ)) -
      onOracle (Bits w) (PolarEmbedding.candidate N)
        (Query.exactOrdinary encode false x
          (onOracle (Bits w) (InversionSymmetry.oracle N).toLinearIsometry ψ))‖ := by
  rw [inverse_ordinary_apply,
    norm_involutive_sub (CompressedQuery.flip (Bits w)) CompressedQuery.flip_involutive]
  rw [← onOracle_candidate_inversion ψ,
    ← onOracle_candidate_inversion (Query.exactOrdinary encode true x ψ),
    ConditioningInverse.oracle_exactOrdinary_inverse encode x ψ]

/-- The same exact norm transfer includes arbitrary marker values. -/
theorem inverse_marked_error_eq (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Perm N)) :
    ‖CompressedQuery.inverseMarked encode x
        (onOracle (Bool × Bits w) (PolarEmbedding.candidate N) ψ) -
      onOracle (Bool × Bits w) (PolarEmbedding.candidate N) (Query.exactMarked encode true x ψ)‖ =
    ‖CompressedQuery.marked encode x
        (onOracle (Bool × Bits w) (PolarEmbedding.candidate N)
          (onOracle (Bool × Bits w) (InversionSymmetry.oracle N).toLinearIsometry ψ)) -
      onOracle (Bool × Bits w) (PolarEmbedding.candidate N)
        (Query.exactMarked encode false x
          (onOracle (Bool × Bits w) (InversionSymmetry.oracle N).toLinearIsometry ψ))‖ := by
  rw [inverse_marked_apply,
    norm_involutive_sub (CompressedQuery.flip (Bool × Bits w)) CompressedQuery.flip_involutive]
  rw [← onOracle_candidate_inversion ψ,
    ← onOracle_candidate_inversion (Query.exactMarked encode true x ψ),
    ConditioningInverse.oracle_exactMarked_inverse encode x ψ]

/-- Two actual conditioning discrepancies bound the actual inverse ordinary query error. -/
theorem inverse_ordinary_error_le (encode : Encoding (N + 1) w) (x : Fin (N + 1))
    (ψ : EuclideanSpace ℂ (Bits w × Perm (N + 1))) :
    ‖CompressedQuery.inverseOrdinary encode x
        (onOracle (Bits w) (PolarEmbedding.candidate (N + 1)) ψ) -
      onOracle (Bits w) (PolarEmbedding.candidate (N + 1))
        (Query.exactOrdinary encode true x ψ)‖ ≤
      ConditioningComparison.error (Bits w) x
        (onOracle (Bits w) (InversionSymmetry.oracle (N + 1)).toLinearIsometry ψ) +
      ConditioningComparison.error (Bits w) x
        (onOracle (Bits w) (InversionSymmetry.oracle (N + 1)).toLinearIsometry
          (Query.exactOrdinary encode true x ψ)) := by
  rw [inverse_ordinary_error_eq encode x ψ,
    ConditioningInverse.oracle_exactOrdinary_inverse encode x ψ]
  exact ConditioningComparison.ordinary_error_le encode x _

/-- The actual inverse marked query obeys the same two-error reduction. -/
theorem inverse_marked_error_le (encode : Encoding (N + 1) w) (x : Fin (N + 1))
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Perm (N + 1))) :
    ‖CompressedQuery.inverseMarked encode x
        (onOracle (Bool × Bits w) (PolarEmbedding.candidate (N + 1)) ψ) -
      onOracle (Bool × Bits w) (PolarEmbedding.candidate (N + 1))
        (Query.exactMarked encode true x ψ)‖ ≤
      ConditioningComparison.error (Bool × Bits w) x
        (onOracle (Bool × Bits w) (InversionSymmetry.oracle (N + 1)).toLinearIsometry ψ) +
      ConditioningComparison.error (Bool × Bits w) x
        (onOracle (Bool × Bits w) (InversionSymmetry.oracle (N + 1)).toLinearIsometry
          (Query.exactMarked encode true x ψ)) := by
  rw [inverse_marked_error_eq encode x ψ,
    ConditioningInverse.oracle_exactMarked_inverse encode x ψ]
  exact ConditioningComparison.marked_error_le encode x _

end QuantumOracle.ConditioningInverseComparison
