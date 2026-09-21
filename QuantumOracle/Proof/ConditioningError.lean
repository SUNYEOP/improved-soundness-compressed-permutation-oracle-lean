import QuantumOracle.Proof.ConditioningComparison

/-!
# Finite-workspace stability of the actual conditioning error

The discrepancy between the constructed J and actual pC W acts independently
on every workspace slice. Its squared norm is their squared-norm sum. Thus a
single-register numerical bound on any subspace lifts to arbitrary finite
entangled workspace states supported in that subspace, with the same constant.
No numerical bound is assumed by the operator definitions or proved here.
-/

noncomputable section

namespace QuantumOracle.ConditioningError

open PermutationExtensions WorkspaceKnowledge HiddenIsometry
open scoped BigOperators

variable {N s : ℕ} {A : Type*} [Fintype A]

/-- Actual compression applies pC independently at each workspace coordinate. -/
theorem slice_compression (x : Fin (N + 1))
    (ψ : EuclideanSpace ℂ (A × Database (N + 1))) (a : A) :
    slice (CompressedQuery.compression A x ψ) a = Compression.pC x (slice ψ a) := by
  ext I
  exact CompressedQuery.compression_apply x ψ a I

/-- The actual joint discrepancy has exactly the single-register discrepancies
as its workspace slices. -/
theorem slice_discrepancy (x : Fin (N + 1))
    (ψ : EuclideanSpace ℂ (A × Perm (N + 1))) (a : A) :
    slice (onOracle A (Conditioning.J x) ψ -
      CompressedQuery.compression A x
        (onOracle A (PolarEmbedding.candidate (N + 1)) ψ)) a =
      Conditioning.J x (slice ψ a) -
        Compression.pC x (PolarEmbedding.candidate (N + 1) (slice ψ a)) := by
  change (sliceLinear (O := Database (N + 1)) a)
    (onOracle A (Conditioning.J x) ψ -
      CompressedQuery.compression A x
        (onOracle A (PolarEmbedding.candidate (N + 1)) ψ)) = _
  rw [map_sub]
  change slice (onOracle A (Conditioning.J x) ψ) a -
    slice (CompressedQuery.compression A x
      (onOracle A (PolarEmbedding.candidate (N + 1)) ψ)) a = _
  rw [slice_onOracle, slice_compression, slice_onOracle]

/-- The actual conditioning error squared is the sum of the actual slice
errors squared, with no dimensional factor. -/
theorem error_sq_eq_sum_slices (x : Fin (N + 1))
    (ψ : EuclideanSpace ℂ (A × Perm (N + 1))) :
    ConditioningComparison.error A x ψ ^ 2 =
      ∑ a : A, ‖Conditioning.J x (slice ψ a) -
        Compression.pC x (PolarEmbedding.candidate (N + 1) (slice ψ a))‖ ^ 2 := by
  rw [ConditioningComparison.error, norm_sq_eq_sum_slices]
  apply Finset.sum_congr rfl
  intro a _
  rw [slice_discrepancy]

/-- Homogeneous bounds on every actual oracle slice give the same bound on
the whole entangled vector, for any finite workspace including the empty one. -/
theorem error_le_of_slice_bounds (x : Fin (N + 1)) (ε : ℝ) (hε : 0 ≤ ε)
    (ψ : EuclideanSpace ℂ (A × Perm (N + 1)))
    (hbound : ∀ a : A, ‖Conditioning.J x (slice ψ a) -
      Compression.pC x (PolarEmbedding.candidate (N + 1) (slice ψ a))‖ ≤
        ε * ‖slice ψ a‖) :
    ConditioningComparison.error A x ψ ≤ ε * ‖ψ‖ := by
  apply (sq_le_sq₀ (ConditioningComparison.error_nonneg A x ψ)
    (mul_nonneg hε (norm_nonneg ψ))).mp
  rw [error_sq_eq_sum_slices, mul_pow, norm_sq_eq_sum_slices, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε (norm_nonneg (slice ψ a)))).mpr (hbound a)

/-- A numerical bound for the actual maps on a subspace extends to all finite
workspace states whose oracle slices belong to that subspace. -/
theorem error_le_of_supported (x : Fin (N + 1))
    (K : Submodule ℂ (EuclideanSpace ℂ (Perm (N + 1))))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : ∀ h ∈ K, ‖Conditioning.J x h -
      Compression.pC x (PolarEmbedding.candidate (N + 1) h)‖ ≤ ε * ‖h‖)
    {ψ : EuclideanSpace ℂ (A × Perm (N + 1))} (hψ : Supported K ψ) :
    ConditioningComparison.error A x ψ ≤ ε * ‖ψ‖ :=
  error_le_of_slice_bounds x ε hε ψ (fun a => hbound (slice ψ a) (hψ a))

/-- Specialization to the actual consistency filtration used by exact prefixes. -/
theorem error_le_of_supported_K (x : Fin (N + 1)) (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : ∀ h ∈ KnowledgeSpace.K (N + 1) s, ‖Conditioning.J x h -
      Compression.pC x (PolarEmbedding.candidate (N + 1) h)‖ ≤ ε * ‖h‖)
    {ψ : EuclideanSpace ℂ (A × Perm (N + 1))}
    (hψ : Supported (KnowledgeSpace.K (N + 1) s) ψ) :
    ConditioningComparison.error A x ψ ≤ ε * ‖ψ‖ :=
  error_le_of_supported x (KnowledgeSpace.K (N + 1) s) ε hε hbound hψ

end QuantumOracle.ConditioningError
