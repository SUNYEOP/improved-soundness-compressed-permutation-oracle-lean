import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic.Module

/-!
# Swapping orthogonal equal-norm vectors

The reflection in the orthogonal complement of `e - u` is an actual complex
linear isometry equivalence. For an orthogonal equal-norm pair it exchanges the
pair and fixes every vector orthogonal to both. This provides the elementary
block operator used by permutation compression `pC`.
-/

noncomputable section

namespace QuantumOracle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Reflection in the hyperplane perpendicular to `e - u`.
No unproved isometry hypothesis is part of this definition. -/
def orthonormalSwap (e u : E) : E ≃ₗᵢ[ℂ] E :=
  (ℂ ∙ (e - u))ᗮ.reflection

@[simp]
theorem orthonormalSwap_involutive (e u : E) (v : E) :
    orthonormalSwap e u (orthonormalSwap e u v) = v :=
  Submodule.reflection_reflection _ _

theorem orthonormalSwap_neg_sub (e u : E) :
    orthonormalSwap e u (e - u) = -(e - u) :=
  Submodule.reflection_orthogonalComplement_singleton_eq_neg _

/-- The operation fixes the common orthogonal complement pointwise. -/
theorem orthonormalSwap_fixed (e u v : E)
    (hev : inner ℂ e v = 0) (huv : inner ℂ u v = 0) :
    orthonormalSwap e u v = v := by
  apply Submodule.reflection_mem_subspace_eq_self
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  rw [inner_eq_zero_symm]
  simp [inner_sub_left, hev, huv]

theorem orthonormalSwap_add (e u : E) (hnorm : ‖e‖ = ‖u‖)
    (horth : inner ℂ e u = 0) :
    orthonormalSwap e u (e + u) = e + u := by
  apply Submodule.reflection_mem_subspace_eq_self
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  have hue : inner ℂ u e = 0 := by
    rw [inner_eq_zero_symm]
    exact horth
  simp [inner_sub_right, inner_add_left, horth, hue, inner_self_eq_norm_sq_to_K,
    hnorm]

/-- The first member of the orthogonal equal-norm pair maps to the second. -/
theorem orthonormalSwap_left (e u : E) (hnorm : ‖e‖ = ‖u‖)
    (horth : inner ℂ e u = 0) : orthonormalSwap e u e = u := by
  have hsum := orthonormalSwap_add e u hnorm horth
  have hdiff := orthonormalSwap_neg_sub e u
  have heq : orthonormalSwap e u e + orthonormalSwap e u e = u + u := by
    have h := congr_arg₂ (· + ·) hsum hdiff
    simp only [map_add, map_sub] at h
    calc
      orthonormalSwap e u e + orthonormalSwap e u e =
          (orthonormalSwap e u e + orthonormalSwap e u u) +
            (orthonormalSwap e u e - orthonormalSwap e u u) := by abel
      _ = (e + u) + -(e - u) := h
      _ = u + u := by abel
  exact (smul_right_injective E (by norm_num : (2 : ℂ) ≠ 0)) (by
    simpa only [two_smul] using heq)

/-- The second member maps back to the first. -/
theorem orthonormalSwap_right (e u : E) (hnorm : ‖e‖ = ‖u‖)
    (horth : inner ℂ e u = 0) : orthonormalSwap e u u = e := by
  calc
    orthonormalSwap e u u =
        orthonormalSwap e u (orthonormalSwap e u e) :=
      congrArg (orthonormalSwap e u) (orthonormalSwap_left e u hnorm horth).symm
    _ = e := orthonormalSwap_involutive e u e

/-- The explicit conditioning formula for an orthonormal pair. -/
theorem orthonormalSwap_apply (e u v : E) (he : ‖e‖ = 1) (hu : ‖u‖ = 1)
    (horth : inner ℂ e u = 0) :
    orthonormalSwap e u v = v + (inner ℂ e v - inner ℂ u v) • (u - e) := by
  have hue : inner ℂ u e = 0 := inner_eq_zero_symm.mpr horth
  have hn : (‖e - u‖ : ℂ) ^ 2 = 2 := by
    calc
      (‖e - u‖ : ℂ) ^ 2 = inner ℂ (e - u) (e - u) :=
        (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (e - u)).symm
      _ = 2 := by
        rw [inner_sub_left, inner_sub_right, inner_sub_right]
        norm_num [inner_self_eq_norm_sq_to_K, he, hu, horth, hue]
  change (ℂ ∙ (e - u))ᗮ.reflection v = _
  rw [Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply (𝕜 := ℂ)]
  change -(2 • (inner ℂ (e - u) v / (‖e - u‖ : ℂ) ^ 2) • (e - u) - v) = _
  rw [hn, inner_sub_left]
  module

end QuantumOracle


