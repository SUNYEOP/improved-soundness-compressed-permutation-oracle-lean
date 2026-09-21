import QuantumOracle.Proof.ConditioningFirstRow

/-!
# Consequences of the actual equal-degree residual overlap

The explicit actual Gram eigenvector equations are retained. Once the overlap
is proved, the real squared discrepancy and the orientation of the two positive
eigenvalues follow from norm preservation and positivity.
-/

noncomputable section

namespace QuantumOracle.ConditioningFirstRowBounds

open PermutationExtensions HarmonicLayers
open scoped InnerProductSpace

attribute [local irreducible] PolarEmbedding.candidate

variable {N t : ℕ}

theorem norm_pC_candidate_sub_J_sq (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) t)
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N t)
    (gh gr : ℝ) (hgh : 0 < gh) (hgr : 0 < gr)
    (hfull : GramFiltration.gram (N + 1) t h = (gh : ℂ) • h)
    (hresidual : ∀ y, GramFiltration.gram N t (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h) :
    ‖Compression.pC x (PolarEmbedding.candidate (N + 1) h) - Conditioning.J x h‖ ^ 2 =
      2 * (1 - Real.sqrt gh / Real.sqrt gr) * ‖h‖ ^ 2 := by
  rw [norm_sub_rev, norm_sub_sq (𝕜 := ℂ), Conditioning.J_norm,
    (Compression.pC x).norm_map, (PolarEmbedding.candidate (N + 1)).norm_map,
    ConditioningFirstRow.inner_J_pC_candidate x hh hres gh gr hgh hgr hfull hresidual]
  change ‖h‖ ^ 2 - 2 *
    ((((Real.sqrt gh / Real.sqrt gr : ℝ) : ℂ) * ((‖h‖ ^ 2 : ℝ) : ℂ)).re) + ‖h‖ ^ 2 = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

theorem sqrt_ratio_pos_le_one (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) t)
    (hne : h ≠ 0) (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N t)
    (gh gr : ℝ) (hgh : 0 < gh) (hgr : 0 < gr)
    (hfull : GramFiltration.gram (N + 1) t h = (gh : ℂ) • h)
    (hresidual : ∀ y, GramFiltration.gram N t (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h) :
    0 < Real.sqrt gh / Real.sqrt gr ∧ Real.sqrt gh / Real.sqrt gr ≤ 1 := by
  refine ⟨div_pos (Real.sqrt_pos.mpr hgh) (Real.sqrt_pos.mpr hgr), ?_⟩
  have hn := sq_nonneg
    ‖Compression.pC x (PolarEmbedding.candidate (N + 1) h) - Conditioning.J x h‖
  rw [norm_pC_candidate_sub_J_sq x hh hres gh gr hgh hgr hfull hresidual] at hn
  have hnorm : 0 < ‖h‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hr := nonneg_of_mul_nonneg_left hn hnorm
  linarith

theorem full_eigenvalue_le (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) t)
    (hne : h ≠ 0) (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N t)
    (gh gr : ℝ) (hgh : 0 < gh) (hgr : 0 < gr)
    (hfull : GramFiltration.gram (N + 1) t h = (gh : ℂ) • h)
    (hresidual : ∀ y, GramFiltration.gram N t (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h) : gh ≤ gr := by
  have hr := (sqrt_ratio_pos_le_one x hh hne hres gh gr hgh hgr hfull hresidual).2
  have hs : Real.sqrt gh ≤ Real.sqrt gr := (div_le_one (Real.sqrt_pos.mpr hgr)).mp hr
  nlinarith [Real.sq_sqrt hgh.le, Real.sq_sqrt hgr.le, Real.sqrt_nonneg gh,
    Real.sqrt_nonneg gr]

end QuantumOracle.ConditioningFirstRowBounds
