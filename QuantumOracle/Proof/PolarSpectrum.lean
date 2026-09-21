import QuantumOracle.Proof.PolarDegree
import QuantumOracle.Proof.PolarEigenvector

/-!
# Scalar normalization on actual Gram eigenvectors

On a genuine eigenvector in harmonic degree t, the constructed polar map is
exactly the scalar inverse-square-root normalization of the actual T_t adjoint.
The eigenvector equation is explicit: no Specht eigenvalue formula or branching
theorem is supplied by this result.
-/

noncomputable section

namespace QuantumOracle.PolarSpectrum

open PermutationExtensions HarmonicLayers
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable

/-- A real eigenvalue on a nonzero actual degree vector is strictly positive. -/
theorem eigenvalue_pos {N t : ℕ} {h : EuclideanSpace ℂ (Perm N)}
    (hh : h ∈ H N t) (hne : h ≠ 0) (g : ℝ)
    (heigen : GramFiltration.gram N t h = (g : ℂ) • h) : 0 < g := by
  have hpos := GramFiltration.re_inner_gram_pos (H_le_K N t hh) hne
  have hvalue : (⟪h, GramFiltration.gram N t h⟫_ℂ).re = g * ‖h‖ ^ 2 := by
    rw [heigen, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [hvalue] at hpos
  by_contra! hg
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hg (sq_nonneg ‖h‖))) hpos

/-- Positive polar normalization has the manuscript's scalar form wherever
the actual own-degree Gram eigenvector equation has been established. -/
theorem candidate_of_gram_eigen_pos {N t : ℕ} {h : EuclideanSpace ℂ (Perm N)}
    (hh : h ∈ H N t) (g : ℝ) (hg : 0 < g)
    (heigen : GramFiltration.gram N t h = (g : ℂ) • h) :
    PolarEmbedding.candidate N h =
      (((Real.sqrt g)⁻¹ : ℝ) : ℂ) • RawHarmonic.raw N t h := by
  have hm : ((PolarEmbedding.matrix N).conjTranspose * PolarEmbedding.matrix N).toEuclideanLin h =
      (g : ℂ) • h := by
    rw [FiniteIncidence.toEuclideanLin_mul,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, PolarEmbedding.matrix_operator]
    exact (RawDegree.total_adjoint_total_of_mem_H hh).trans heigen
  calc
    PolarEmbedding.candidate N h = (((Real.sqrt g)⁻¹ : ℝ) : ℂ) •
        (PolarEmbedding.matrix N).toEuclideanLin h :=
      PolarEigenvector.isometry_apply_of_gram_eigenvector (PolarEmbedding.matrix N)
        (PolarEmbedding.matrix_mulVec_injective N) h g hg hm
    _ = _ := by rw [PolarEmbedding.matrix_operator, RawDegree.total_of_mem_H hh]

/-- Positivity is derived internally for nonzero eigenvectors; the zero vector
also satisfies the scalar normalization identity. -/
theorem candidate_of_gram_eigen {N t : ℕ} {h : EuclideanSpace ℂ (Perm N)}
    (hh : h ∈ H N t) (g : ℝ)
    (heigen : GramFiltration.gram N t h = (g : ℂ) • h) :
    PolarEmbedding.candidate N h =
      (((Real.sqrt g)⁻¹ : ℝ) : ℂ) • RawHarmonic.raw N t h := by
  by_cases hz : h = 0
  · rw [hz, map_zero, map_zero, smul_zero]
  · exact candidate_of_gram_eigen_pos hh g (eigenvalue_pos hh hz g heigen) heigen

end QuantumOracle.PolarSpectrum
