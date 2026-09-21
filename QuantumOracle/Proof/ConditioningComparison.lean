import QuantumOracle.Proof.ConditioningQuery
import QuantumOracle.Model.CompressedQuery

/-!
# Concrete two-error reduction for one query

The true compressed query error is bounded by two actual J-versus-pC errors,
before and after the true exact query. All intertwining and isometry facts are
proved for the concrete operators. This does not bound either conditioning
error numerically.
-/

noncomputable section

namespace QuantumOracle.ConditioningComparison

open BasisLookup PermutationExtensions HiddenIsometry

private theorem two_error_bound {O D : Type*}
    [NormedAddCommGroup O] [NormedSpace ℂ O]
    [NormedAddCommGroup D] [NormedSpace ℂ D]
    (C P : D ≃ₗᵢ[ℂ] D) (hCC : Function.Involutive C)
    (W J : O →ₗᵢ[ℂ] D) (Q : O ≃ₗᵢ[ℂ] O)
    (hJ : ∀ ψ, J (Q ψ) = P (J ψ)) (ψ : O) :
    ‖C (P (C (W ψ))) - W (Q ψ)‖ ≤
      ‖J ψ - C (W ψ)‖ + ‖J (Q ψ) - C (W (Q ψ))‖ := by
  simp only [← dist_eq_norm]
  calc
    dist (C (P (C (W ψ)))) (W (Q ψ)) = dist (P (C (W ψ))) (C (W (Q ψ))) := by
      simpa only [hCC (W (Q ψ))] using (C.dist_map (P (C (W ψ))) (C (W (Q ψ))))
    _ ≤ dist (P (C (W ψ))) (P (J ψ)) + dist (P (J ψ)) (C (W (Q ψ))) :=
      dist_triangle _ _ _
    _ = dist (J ψ) (C (W ψ)) + dist (J (Q ψ)) (C (W (Q ψ))) := by
      rw [P.dist_map, ← hJ, dist_comm (C (W ψ)) (J ψ)]

variable {N w : ℕ}

/-- The genuine conditioning discrepancy, retaining any finite workspace. -/
def error (A : Type*) [Fintype A] (x : Fin (N + 1))
    (ψ : EuclideanSpace ℂ (A × Perm (N + 1))) : ℝ :=
  ‖onOracle A (Conditioning.J x) ψ -
    CompressedQuery.compression A x (onOracle A (PolarEmbedding.candidate (N + 1)) ψ)‖

theorem error_nonneg (A : Type*) [Fintype A] (x : Fin (N + 1))
    (ψ : EuclideanSpace ℂ (A × Perm (N + 1))) : 0 ≤ error A x ψ := norm_nonneg _

/-- Both errors use actual exact states, not a compressed reachable state. -/
theorem ordinary_error_le (encode : Encoding (N + 1) w) (x : Fin (N + 1))
    (ψ : EuclideanSpace ℂ (Bits w × Perm (N + 1))) :
    ‖CompressedQuery.ordinary encode x
        (onOracle (Bits w) (PolarEmbedding.candidate (N + 1)) ψ) -
      onOracle (Bits w) (PolarEmbedding.candidate (N + 1))
        (Query.exactOrdinary encode false x ψ)‖ ≤
      error (Bits w) x ψ + error (Bits w) x (Query.exactOrdinary encode false x ψ) := by
  rw [CompressedQuery.ordinary_apply]
  exact two_error_bound (CompressedQuery.compression (Bits w) x)
    (Query.ordinaryLookup encode x) (CompressedQuery.compression_involutive x)
    (onOracle (Bits w) (PolarEmbedding.candidate (N + 1)))
    (onOracle (Bits w) (Conditioning.J x)) (Query.exactOrdinary encode false x)
    (ConditioningQuery.ordinary_intertwines encode x) ψ

theorem marked_error_le (encode : Encoding (N + 1) w) (x : Fin (N + 1))
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Perm (N + 1))) :
    ‖CompressedQuery.marked encode x
        (onOracle (Bool × Bits w) (PolarEmbedding.candidate (N + 1)) ψ) -
      onOracle (Bool × Bits w) (PolarEmbedding.candidate (N + 1))
        (Query.exactMarked encode false x ψ)‖ ≤
      error (Bool × Bits w) x ψ +
        error (Bool × Bits w) x (Query.exactMarked encode false x ψ) := by
  rw [CompressedQuery.marked_apply]
  exact two_error_bound (CompressedQuery.compression (Bool × Bits w) x)
    (Query.markedLookup encode x) (CompressedQuery.compression_involutive x)
    (onOracle (Bool × Bits w) (PolarEmbedding.candidate (N + 1)))
    (onOracle (Bool × Bits w) (Conditioning.J x)) (Query.exactMarked encode false x)
    (ConditioningQuery.marked_intertwines encode x) ψ

end QuantumOracle.ConditioningComparison
