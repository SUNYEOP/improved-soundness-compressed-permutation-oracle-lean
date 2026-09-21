import QuantumOracle.Proof.ConditioningSpechtBounds
import QuantumOracle.Proof.ConditioningSoundness

/-!
# Assembly of the actual joint-component conditioning bounds

The actual spectral decomposition and all numerical branch estimates are
internal. Two structural obligations are explicit: corner support of the actual
joint spaces, and orthogonality of the actual error images on distinct allowed
joint spaces. Input Parseval alone is not used to claim output orthogonality.
-/

noncomputable section

namespace QuantumOracle.ConditioningJointBound

open PermutationExtensions SpechtFoundation HookRowFactorization
open JointSpectralDecomposition
open scoped BigOperators InnerProductSpace

attribute [local irreducible] PolarEmbedding.candidate

variable {N : ℕ}

/-- The actual conditioning discrepancy, as a complex linear map. -/
def error (x : Fin (N + 1)) :
    EuclideanSpace ℂ (Perm (N + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Database (N + 1)) :=
  (Conditioning.J x).toLinearMap -
    (Compression.pC x).toLinearEquiv.toLinearMap.comp (PolarEmbedding.candidate (N + 1)).toLinearMap

@[simp] theorem error_apply (x : Fin (N + 1)) (h : EuclideanSpace ℂ (Perm (N + 1))) :
    error x h = Conditioning.J x h - Compression.pC x (PolarEmbedding.candidate (N + 1) h) := rfl

/-- A reachable input has no joint component whose full tail degree exceeds its level. -/
theorem project_eq_zero_of_tail_gt (x : Fin (N + 1)) (label : Labels N) {q : ℕ}
    (hq : q ≤ N + 1) {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ KnowledgeSpace.K (N + 1) q)
    (ht : q < (tail (diagram label.1)).card) : project x label h = 0 := by
  have hrow := SpechtMinimalMultiplicity.rowLen_add_tail_card (N + 1) label.1
  have he := SpechtMultiplicitySupport.eigenvalue_eq_zero_of_rowLen_lt (N + 1) q hq label.1
    (by omega)
  have hp := (SpechtIsotypicLayers.mem_K_iff_projection_eq_zero (N + 1) q h).mp hh label.1 he
  change ResidualSpectralDecomposition.project x label.2
    ((SpechtIsotypic.space (N + 1) label.1).starProjection h) = 0
  rw [hp, map_zero]

private theorem norm_sum_sq {I E : Type*} [Fintype I] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v : I → E)
    (hv : Pairwise (fun i j => ⟪v i, v j⟫_ℂ = 0)) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  classical
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner]
  simp only [inner_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact (norm_sq_eq_re_inner (𝕜 := ℂ) (v i)).symm
  · intro j _ hji
    rw [hv (Ne.symm hji)]
    rfl
  · simp

/-- The precise two structural inputs still needed to assemble the branch bounds. -/
theorem bound_of_support_and_error_orthogonality (q : ℕ) (hq : 4 * q ≤ N + 1)
    (hsupport : ∀ (x : Fin (N + 1)) (label : Labels N)
      (h : EuclideanSpace ℂ (Perm (N + 1))), h ∈ space x label → h ≠ 0 →
        label.2 ∈ removeCorners label.1)
    (horth : ∀ (x : Fin (N + 1)) (a b : Labels N), a ≠ b →
      a.2 ∈ removeCorners a.1 → b.2 ∈ removeCorners b.1 →
      ∀ (h k : EuclideanSpace ℂ (Perm (N + 1))), h ∈ space x a → k ∈ space x b →
        ⟪error x h, error x k⟫_ℂ = 0) :
    ConditioningLocalBound.Bound N q (2 / Real.sqrt (N + 1 : ℕ)) := by
  intro x h hh
  have hqN : q ≤ N + 1 := by omega
  have heach : ∀ label : Labels N, ‖error x (project x label h)‖ ≤
      (2 / Real.sqrt (N + 1 : ℕ)) * ‖project x label h‖ := by
    intro label
    by_cases hz : project x label h = 0
    · simp only [hz, map_zero, norm_zero, mul_zero, le_refl]
    · have htail : (tail (diagram label.1)).card ≤ q := by
        by_contra hn
        exact hz (project_eq_zero_of_tail_gt x label hqN hh (Nat.lt_of_not_ge hn))
      exact ConditioningSpechtBounds.error_project_le x label.1 label.2
        (hsupport x label _ (project_mem x label h) hz) (by omega) h
  have hpair : Pairwise (fun a b : Labels N =>
      ⟪error x (project x a h), error x (project x b h)⟫_ℂ = 0) := by
    intro a b hne
    by_cases ha : project x a h = 0
    · rw [ha, map_zero, inner_zero_left]
    by_cases hb : project x b h = 0
    · rw [hb, map_zero, inner_zero_right]
    exact horth x a b hne
      (hsupport x a _ (project_mem x a h) ha) (hsupport x b _ (project_mem x b h) hb)
      _ _ (project_mem x a h) (project_mem x b h)
  have herr : ‖error x h‖ ^ 2 = ∑ label : Labels N, ‖error x (project x label h)‖ ^ 2 := by
    have he := norm_sum_sq (fun label : Labels N => error x (project x label h)) hpair
    rw [← map_sum, sum_project] at he
    exact he
  change ‖error x h‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [herr, mul_pow, norm_sq_eq_sum_project x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro label _
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (heach label)

end QuantumOracle.ConditioningJointBound
