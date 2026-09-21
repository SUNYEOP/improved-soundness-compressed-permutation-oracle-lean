import QuantumOracle.Model.KnowledgeSpace
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Exact extension-state resolution and elementary cancellation

For a fresh input, summing the actual consistent states over every fresh output
is sqrt(N-|I|) times the original state. This is the first identity in the proof
of manuscript `lem:harmonic-cancellation`.

The vanishing statements below assume explicit orthogonality to the actual
lower-level span in permutation space. They neither construct the harmonic
embedding W nor identify these inner products with W's database coefficients.
-/

noncomputable section

namespace QuantumOracle.ExtensionResolution

open PermutationExtensions ConsistentState
open scoped BigOperators InnerProductSpace

variable {N : ℕ}

/-- Only unused outputs contribute when resolving a consistent state at a fresh input. -/
theorem sum_fresh_answerProjection (I : Database N) (x : Fin N)
    (hx : x ∉ I.domain) :
    (∑ y : UnusedImage I, answerProjection x y.val (vector I)) = vector I := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun y : Fin N => y ∉ I.image))
    (by simp) (fun y => answerProjection x y (vector I))]
  calc
    (∑ y ∈ Finset.univ.filter (fun y : Fin N => y ∉ I.image),
        answerProjection x y (vector I)) = ∑ y, answerProjection x y (vector I) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro y _ hy
      have hyImage : y ∈ I.image := by simpa using hy
      exact answerProjection_vector_of_occupied I x y hx hyImage
    _ = vector I := sum_answerProjection x (vector I)

/-- The same resolution expressed using the normalized fresh extension states. -/
theorem inv_sqrt_smul_sum_extensions (I : Database N) (x : Fin N)
    (hx : x ∉ I.domain) :
    ((Real.sqrt (N - I.size : ℕ))⁻¹ : ℂ) •
      (∑ y : UnusedImage I, vector (I.set x y.val)) = vector I := by
  rw [Finset.smul_sum]
  calc
    (∑ y : UnusedImage I,
        ((Real.sqrt (N - I.size : ℕ))⁻¹ : ℂ) • vector (I.set x y.val)) =
        ∑ y : UnusedImage I, answerProjection x y.val (vector I) := by
      apply Finset.sum_congr rfl
      intro y _
      exact (answerProjection_vector_of_fresh I x y.val hx y.property).symm
    _ = vector I := sum_fresh_answerProjection I x hx

/-- Exact extension sum from the proof of `lem:harmonic-cancellation`.
The freshness hypothesis itself implies `I.size < N`. -/
theorem sum_extensions (I : Database N) (x : Fin N) (hx : x ∉ I.domain) :
    (∑ y : UnusedImage I, vector (I.set x y.val)) =
      (Real.sqrt (N - I.size : ℕ) : ℂ) • vector I := by
  have hlt : I.size < N := CompressionIndex.base_size_lt ⟨I, hx⟩
  have hpos : (0 : ℝ) < (N - I.size : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hlt
  have hsqrt : Real.sqrt (N - I.size : ℕ) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hsqrtC : (Real.sqrt (N - I.size : ℕ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsqrt
  have h := congrArg (fun v => (Real.sqrt (N - I.size : ℕ) : ℂ) • v)
    (inv_sqrt_smul_sum_extensions I x hx)
  simpa only [smul_smul, mul_inv_cancel₀ hsqrtC, one_smul] using h

/-- Cancellation in permutation space against a vector orthogonal to the lower span. -/
theorem sum_inner_extensions_eq_zero (I : Database N) (x : Fin N)
    (hx : x ∉ I.domain) (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ (KnowledgeSpace.K N I.size)ᗮ) :
    (∑ y : UnusedImage I, ⟪vector (I.set x y.val), h⟫_ℂ) = 0 := by
  rw [← sum_inner, sum_extensions I x hx, inner_smul_left]
  have hz : ⟪vector I, h⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (KnowledgeSpace.vector_mem I rfl) hh
  rw [hz, mul_zero]

/-- The conjugate inner-product convention gives the same zero sum. -/
theorem sum_inner_extensions_eq_zero' (I : Database N) (x : Fin N)
    (hx : x ∉ I.domain) (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ (KnowledgeSpace.K N I.size)ᗮ) :
    (∑ y : UnusedImage I, ⟪h, vector (I.set x y.val)⟫_ℂ) = 0 := by
  rw [← inner_sum, sum_extensions I x hx, inner_smul_right]
  have hz : ⟪h, vector I⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (KnowledgeSpace.vector_mem I rfl) hh
  rw [hz, mul_zero]

end QuantumOracle.ExtensionResolution
