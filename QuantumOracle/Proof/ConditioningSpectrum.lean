import QuantumOracle.Proof.PolarSpectrum
import QuantumOracle.Proof.ResidualAdjoint
import QuantumOracle.Proof.ResidualRemoval
import QuantumOracle.Proof.Conditioning
import QuantumOracle.Proof.CompressionDegree

/-!
# Actual conditioning coefficients under Gram eigenvector equations

The polar coefficient on an inserted database and the actual conditioning
coefficient have the same unnormalized residual inner product. Their ratio is
therefore the square-root ratio of the two actual Gram eigenvalues. The
eigenvector hypotheses are explicit; no branching rule or numerical estimate
for these eigenvalues is asserted here.
-/

noncomputable section

namespace QuantumOracle.ConditioningSpectrum

open PermutationExtensions HarmonicLayers
open scoped InnerProductSpace

attribute [local irreducible] PolarEmbedding.candidate

variable {N t u : ℕ}

/-- Full polar coefficients at an inserted edge are normalized residual
consistent-state inner products, under the actual full Gram equation. -/
theorem candidate_apply_insert_of_gram_eigen (x y : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) t)
    (g : ℝ) (heigen : GramFiltration.gram (N + 1) t h = (g : ℂ) • h)
    (I : Database N) (hI : I.size + 1 = t) :
    PolarEmbedding.candidate (N + 1) h (ResidualDatabase.insert x y I) =
      (((Real.sqrt g)⁻¹ : ℝ) : ℂ) *
        ⟪ConsistentState.vector I, ResidualAdjoint.restrict x y h⟫_ℂ := by
  rw [PolarSpectrum.candidate_of_gram_eigen hh g heigen, PiLp.smul_apply,
    smul_eq_mul, RawHarmonic.raw_apply_of_size (N + 1) t h _
      ((ResidualDatabase.insert_size x y I).trans hI),
    ResidualAdjoint.inner_vector_insert]

/-- The actual conditioning coefficient uses the residual Gram normalization. -/
theorem J_apply_insert_of_gram_eigen (x y : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))}
    (hh : ResidualAdjoint.restrict x y h ∈ H N u) (g : ℝ)
    (heigen : GramFiltration.gram N u (ResidualAdjoint.restrict x y h) =
      (g : ℂ) • ResidualAdjoint.restrict x y h)
    (I : Database N) (hI : I.size = u) :
    Conditioning.J x h (ResidualDatabase.insert x y I) =
      (((Real.sqrt g)⁻¹ : ℝ) : ℂ) *
        ⟪ConsistentState.vector I, ResidualAdjoint.restrict x y h⟫_ℂ := by
  rw [Conditioning.J_apply_insert, ← ResidualAdjoint.restrict_eq_slice,
    PolarSpectrum.candidate_of_gram_eigen hh g heigen, PiLp.smul_apply,
    smul_eq_mul, RawHarmonic.raw_apply_of_size N u _ I hI]

/-- On adjacent full and residual degrees, the actual two coefficients differ
by the square-root ratio of their genuine Gram eigenvalues. -/
theorem candidate_apply_insert_eq_ratio_J (x y : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) (u + 1))
    (hres : ResidualAdjoint.restrict x y h ∈ H N u)
    (gh gr : ℝ) (hgh : 0 < gh) (hgr : 0 < gr)
    (hfull : GramFiltration.gram (N + 1) (u + 1) h = (gh : ℂ) • h)
    (hresidual : GramFiltration.gram N u (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h)
    (I : Database N) (hI : I.size = u) :
    PolarEmbedding.candidate (N + 1) h (ResidualDatabase.insert x y I) =
      ((Real.sqrt gr / Real.sqrt gh : ℝ) : ℂ) *
        Conditioning.J x h (ResidualDatabase.insert x y I) := by
  rw [candidate_apply_insert_of_gram_eigen x y hh gh hfull I (by omega),
    J_apply_insert_of_gram_eigen x y hres gr hresidual I hI]
  have hh0 : (Real.sqrt gh : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hgh).ne'
  have hr0 : (Real.sqrt gr : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hgr).ne'
  push_cast
  field_simp

/-- The same coefficient identity holds off the selected residual degree,
because both actual polar coefficients then vanish. -/
theorem candidate_apply_insert_eq_ratio_J_all (x y : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) (u + 1))
    (hres : ResidualAdjoint.restrict x y h ∈ H N u)
    (gh gr : ℝ) (hgh : 0 < gh) (hgr : 0 < gr)
    (hfull : GramFiltration.gram (N + 1) (u + 1) h = (gh : ℂ) • h)
    (hresidual : GramFiltration.gram N u (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h)
    (I : Database N) :
    PolarEmbedding.candidate (N + 1) h (ResidualDatabase.insert x y I) =
      ((Real.sqrt gr / Real.sqrt gh : ℝ) : ℂ) *
        Conditioning.J x h (ResidualDatabase.insert x y I) := by
  by_cases hI : I.size = u
  · exact candidate_apply_insert_eq_ratio_J x y hh hres gh gr hgh hgr
      hfull hresidual I hI
  · rw [PolarDegree.candidate_apply_eq_zero_of_size_ne hh _
        (by rw [ResidualDatabase.insert_size]; omega),
      Conditioning.J_apply_insert, ← ResidualAdjoint.restrict_eq_slice,
      PolarDegree.candidate_apply_eq_zero_of_size_ne hres I hI, mul_zero]

/-- If every actual answer restriction has one residual degree and eigenvalue,
the full already-defined component is exactly a scalar multiple of actual J. -/
theorem definedPart_candidate_eq_ratio_J (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) (u + 1))
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N u)
    (gh gr : ℝ) (hgh : 0 < gh) (hgr : 0 < gr)
    (hfull : GramFiltration.gram (N + 1) (u + 1) h = (gh : ℂ) • h)
    (hresidual : ∀ y, GramFiltration.gram N u (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h) :
    CompressionCancellation.definedPart x (PolarEmbedding.candidate (N + 1) h) =
      ((Real.sqrt gr / Real.sqrt gh : ℝ) : ℂ) • Conditioning.J x h := by
  classical
  ext I
  rw [CompressionCancellation.definedPart_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ I.domain
  · rw [if_pos hx]
    obtain ⟨y, hxy⟩ := (Database.mem_domain I x).mp hx
    rw [← ResidualRemoval.insert_remove x y I hxy]
    exact candidate_apply_insert_eq_ratio_J_all x y hh (hres y) gh gr hgh hgr
      hfull (hresidual y) _
  · rw [if_neg hx, Conditioning.J_apply_of_undefined x h I hx, mul_zero]

/-- A single residual degree in every actual answer sector puts J at the
corresponding inserted database degree. -/
theorem J_mem_exactLevel (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))}
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N u) :
    Conditioning.J x h ∈ DatabaseDegree.exactLevel (N + 1) (u + 1) := by
  classical
  intro I hI
  by_cases hmem : I ∈ Set.range (ResidualDatabase.jointInsert x)
  · obtain ⟨⟨y, R⟩, rfl⟩ := hmem
    change Conditioning.J x h (ResidualDatabase.insert x y R) = 0
    rw [Conditioning.J_apply_insert, ← ResidualAdjoint.restrict_eq_slice]
    apply PolarDegree.candidate_apply_eq_zero_of_size_ne (hres y)
    intro hR
    exact hI ((ResidualDatabase.insert_size x y R).trans (by rw [hR]))
  · exact Conditioning.J_apply_of_notMem x h I hmem

/-- The conditional scalar identity gives an exact actual inner product,
without any abstract comparison form or supplied overlap assumption. -/
theorem inner_J_definedPart_candidate (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) (u + 1))
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N u)
    (gh gr : ℝ) (hgh : 0 < gh) (hgr : 0 < gr)
    (hfull : GramFiltration.gram (N + 1) (u + 1) h = (gh : ℂ) • h)
    (hresidual : ∀ y, GramFiltration.gram N u (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h) :
    ⟪Conditioning.J x h,
        CompressionCancellation.definedPart x (PolarEmbedding.candidate (N + 1) h)⟫_ℂ =
      ((Real.sqrt gr / Real.sqrt gh : ℝ) : ℂ) * (‖h‖ ^ 2 : ℝ) := by
  rw [definedPart_candidate_eq_ratio_J x hh hres gh gr hgh hgr hfull hresidual,
    inner_smul_right, Conditioning.J_inner, inner_self_eq_norm_sq_to_K]
  simp only [Complex.ofReal_pow]
  rfl

/-- The actual compression overlap has the same exact scalar value. Its
higher database-degree component is orthogonal to this actual J image. -/
theorem inner_J_pC_candidate (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) (u + 1))
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N u)
    (gh gr : ℝ) (hgh : 0 < gh) (hgr : 0 < gr)
    (hfull : GramFiltration.gram (N + 1) (u + 1) h = (gh : ℂ) • h)
    (hresidual : ∀ y, GramFiltration.gram N u (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h) :
    ⟪Conditioning.J x h, Compression.pC x (PolarEmbedding.candidate (N + 1) h)⟫_ℂ =
      ((Real.sqrt gr / Real.sqrt gh : ℝ) : ℂ) * (‖h‖ ^ 2 : ℝ) := by
  calc
    _ = ⟪DatabaseDegree.project (N + 1) (u + 1) (Conditioning.J x h),
        Compression.pC x (PolarEmbedding.candidate (N + 1) h)⟫_ℂ := by
      rw [(DatabaseDegree.project_eq_self_iff (N + 1) (u + 1) _).mpr
        (J_mem_exactLevel x hres)]
    _ = ⟪Conditioning.J x h, DatabaseDegree.project (N + 1) (u + 1)
        (Compression.pC x (PolarEmbedding.candidate (N + 1) h))⟫_ℂ :=
      DatabaseDegree.project_isSymmetric (N + 1) (u + 1) _ _
    _ = _ := by
      rw [CompressionDegree.project_pC_candidate x hh]
      exact inner_J_definedPart_candidate x hh hres gh gr hgh hgr hfull hresidual

/-- Consequently the actual conditioning discrepancy has an exact squared
norm, still conditional only on the displayed actual degree and eigen equations. -/
theorem norm_pC_candidate_sub_J_sq (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) (u + 1))
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N u)
    (gh gr : ℝ) (hgh : 0 < gh) (hgr : 0 < gr)
    (hfull : GramFiltration.gram (N + 1) (u + 1) h = (gh : ℂ) • h)
    (hresidual : ∀ y, GramFiltration.gram N u (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h) :
    ‖Compression.pC x (PolarEmbedding.candidate (N + 1) h) - Conditioning.J x h‖ ^ 2 =
      2 * (1 - Real.sqrt gr / Real.sqrt gh) * ‖h‖ ^ 2 := by
  rw [norm_sub_rev, norm_sub_sq (𝕜 := ℂ), Conditioning.J_norm,
    (Compression.pC x).norm_map, (PolarEmbedding.candidate (N + 1)).norm_map,
    inner_J_pC_candidate x hh hres gh gr hgh hgr hfull hresidual]
  change ‖h‖ ^ 2 - 2 *
    ((((Real.sqrt gr / Real.sqrt gh : ℝ) : ℂ) * ((‖h‖ ^ 2 : ℝ) : ℂ)).re) + ‖h‖ ^ 2 = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- For a nonzero actual vector in this common residual eigenbranch, the
square-root ratio lies in the unit interval as a consequence of norm positivity. -/
theorem sqrt_ratio_pos_le_one (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) (u + 1))
    (hne : h ≠ 0) (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N u)
    (gh gr : ℝ) (hgh : 0 < gh) (hgr : 0 < gr)
    (hfull : GramFiltration.gram (N + 1) (u + 1) h = (gh : ℂ) • h)
    (hresidual : ∀ y, GramFiltration.gram N u (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h) :
    0 < Real.sqrt gr / Real.sqrt gh ∧ Real.sqrt gr / Real.sqrt gh ≤ 1 := by
  refine ⟨div_pos (Real.sqrt_pos.mpr hgr) (Real.sqrt_pos.mpr hgh), ?_⟩
  have hn := sq_nonneg
    ‖Compression.pC x (PolarEmbedding.candidate (N + 1) h) - Conditioning.J x h‖
  rw [norm_pC_candidate_sub_J_sq x hh hres gh gr hgh hgr hfull hresidual] at hn
  have hnorm : 0 < ‖h‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hr := nonneg_of_mul_nonneg_left hn hnorm
  linarith

/-- The residual eigenvalue cannot exceed the full eigenvalue on this actual
nonzero common residual eigenbranch. -/
theorem residual_eigenvalue_le (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) (u + 1))
    (hne : h ≠ 0) (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N u)
    (gh gr : ℝ) (hgh : 0 < gh) (hgr : 0 < gr)
    (hfull : GramFiltration.gram (N + 1) (u + 1) h = (gh : ℂ) • h)
    (hresidual : ∀ y, GramFiltration.gram N u (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h) : gr ≤ gh := by
  have hr := (sqrt_ratio_pos_le_one x hh hne hres gh gr hgh hgr hfull hresidual).2
  have hs : Real.sqrt gr ≤ Real.sqrt gh := (div_le_one (Real.sqrt_pos.mpr hgh)).mp hr
  nlinarith [Real.sq_sqrt hgh.le, Real.sq_sqrt hgr.le, Real.sqrt_nonneg gh,
    Real.sqrt_nonneg gr]

end QuantumOracle.ConditioningSpectrum
