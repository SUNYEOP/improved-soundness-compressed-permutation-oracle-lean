import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import QuantumOracle.Proof.Hybrid

/-!
# Comparing two complex linear isometries from a scalar overlap

This file proves the norm identity used in manuscript §3.4 from linear-isometry
data and a pointwise inner-product overlap. The identity is derived rather than
assumed. The overlap hypothesis itself remains explicit: this file does not
construct `D_x`, `pC_x`, or their representation-theoretic overlap coefficients.
-/

namespace QuantumOracle

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The real part of the overlap suffices for the squared-distance identity. -/
theorem isometry_norm_sub_sq_of_re_overlap
    (D P : E →ₗᵢ[ℂ] F) (h : E) (c : ℝ)
    (hoverlap : (inner ℂ (D h) (P h)).re = c * ‖h‖ ^ 2) :
    ‖D h - P h‖ ^ 2 = 2 * (1 - c) * ‖h‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), D.norm_map, P.norm_map]
  change ‖h‖ ^ 2 - 2 * (inner ℂ (D h) (P h)).re + ‖h‖ ^ 2 = _
  rw [hoverlap]
  ring

/-- A real scalar overlap as a complex equality implies the same identity. -/
theorem isometry_norm_sub_sq_of_scalar_overlap
    (D P : E →ₗᵢ[ℂ] F) (h : E) (c : ℝ)
    (hoverlap : inner ℂ (D h) (P h) = (c : ℂ) * ((‖h‖ ^ 2 : ℝ) : ℂ)) :
    ‖D h - P h‖ ^ 2 = 2 * (1 - c) * ‖h‖ ^ 2 := by
  apply isometry_norm_sub_sq_of_re_overlap D P h c
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] using congrArg Complex.re hoverlap

/-- The pointwise conditioning constant from two actual linear-isometry values.
Only the scalar overlap and its defect bound are conditional here; the squared
norm identity is proved from the isometry structure, not a further assumption. -/
theorem conditional_isometry_error_le_of_overlap
    (D P : E →ₗᵢ[ℂ] F) (h : E) (hunit : ‖h‖ = 1)
    (c : ℝ) (N : ℕ) (hN : 0 < N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hoverlap : (inner ℂ (D h) (P h)).re = c * ‖h‖ ^ 2)
    (hdefect : 1 - c ^ 2 ≤ 2 / (N : ℝ)) :
    ‖D h - P h‖ ≤ 2 / Real.sqrt (N : ℝ) := by
  apply conditional_error_le_of_overlap ‖D h - P h‖ c N hN hc0 hc1
    _ hdefect
  simpa only [hunit, one_pow, mul_one] using
    isometry_norm_sub_sq_of_re_overlap D P h c hoverlap

end QuantumOracle
