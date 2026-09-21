import QuantumOracle.Proof.ConditioningSpectrum

/-!
# Actual same-degree residual conditioning overlap

When every answer restriction has the same harmonic degree as the input,
actual extension-state resolution determines the lower-size component of pC J.
Explicit full and residual Gram eigenvector equations then give its positive
square-root ratio and the actual compression overlap. No Specht identification
or numerical eigenvalue estimate is assumed in these coefficient calculations.
-/

noncomputable section

namespace QuantumOracle.ConditioningFirstRow

open PermutationExtensions HarmonicLayers Compression CompressionIndex
open scoped BigOperators InnerProductSpace

attribute [local irreducible] PolarEmbedding.candidate

variable {N t : ℕ}

/-- Same-degree residual orthogonality kills every degree-t coefficient at a
database that already records the input, before polar normalization. -/
theorem raw_apply_eq_zero_of_defined (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))}
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N t)
    (I : Database (N + 1)) (hx : x ∈ I.domain) :
    RawHarmonic.raw (N + 1) t h I = 0 := by
  by_cases hI : I.size = t
  · obtain ⟨y, hxy⟩ := (Database.mem_domain I x).mp hx
    let R := ResidualRemoval.remove x y I
    have hR : R.size + 1 = t :=
      (ResidualRemoval.size_remove_add_one x y I hxy).trans hI
    rw [RawHarmonic.raw_apply_of_size (N + 1) t h I hI,
      ← ResidualRemoval.insert_remove x y I hxy, ResidualAdjoint.inner_vector_insert]
    apply Submodule.inner_right_of_mem_orthogonal (KnowledgeSpace.vector_mem R rfl)
    apply H_succ_le_orthogonal N R.size
    simpa only [hR] using hres y
  · exact RawHarmonic.raw_apply_of_ne (N + 1) t h I hI

theorem definedPart_raw_eq_zero (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))}
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N t) :
    CompressionCancellation.definedPart x (RawHarmonic.raw (N + 1) t h) = 0 := by
  classical
  ext I
  by_cases hx : x ∈ I.domain
  · simp [CompressionCancellation.definedPart_apply, hx, raw_apply_eq_zero_of_defined x hres I hx]
  · simp [CompressionCancellation.definedPart_apply, hx]

/-- The actual full Gram equation transfers this zero defined component to W. -/
theorem definedPart_candidate_eq_zero (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) t)
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N t)
    (gh : ℝ) (hfull : GramFiltration.gram (N + 1) t h = (gh : ℂ) • h) :
    CompressionCancellation.definedPart x (PolarEmbedding.candidate (N + 1) h) = 0 := by
  rw [PolarSpectrum.candidate_of_gram_eigen hh gh hfull, map_smul,
    definedPart_raw_eq_zero x hres, smul_zero]

/-- At an actual fresh extension, the J coefficient is the residual scalar
normalization of the full extended consistent-state inner product. -/
theorem J_apply_extension_of_gram_eigen (x y : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))}
    (hres : ResidualAdjoint.restrict x y h ∈ H N t) (gr : ℝ)
    (heigen : GramFiltration.gram N t (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h)
    (I : Database (N + 1)) (hx : x ∉ I.domain) (hy : y ∉ I.image) (hI : I.size = t) :
    Conditioning.J x h (I.set x y) = (((Real.sqrt gr)⁻¹ : ℝ) : ℂ) *
      ⟪ConsistentState.vector (I.set x y), h⟫_ℂ := by
  let R := ResidualRemoval.remove x y (I.set x y)
  have hinsert : ResidualDatabase.insert x y R = I.set x y :=
    ResidualRemoval.insert_remove x y (I.set x y) (Database.set_contains I x y)
  have hR : R.size = t := by
    have hs := ResidualRemoval.size_remove_add_one x y (I.set x y) (Database.set_contains I x y)
    rw [Database.set_size_of_fresh I x y hx hy, hI] at hs
    change R.size + 1 = t + 1 at hs
    omega
  calc
    _ = Conditioning.J x h (ResidualDatabase.insert x y R) := congrArg _ hinsert.symm
    _ = (((Real.sqrt gr)⁻¹ : ℝ) : ℂ) *
        ⟪ConsistentState.vector R, ResidualAdjoint.restrict x y h⟫_ℂ :=
      ConditioningSpectrum.J_apply_insert_of_gram_eigen x y hres gr heigen R hR
    _ = _ := by rw [← ResidualAdjoint.inner_vector_insert, hinsert]

/-- The lower-size base coefficient of pC J is fixed by the actual fresh
extension resolution, including the cancellation of its cardinal normalization. -/
theorem pC_J_apply_base_of_gram_eigen (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))}
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N t) (gr : ℝ)
    (heigen : ∀ y, GramFiltration.gram N t (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h)
    (B : Base x) (hB : B.val.size = t) :
    pC x (Conditioning.J x h) B.val = (((Real.sqrt gr)⁻¹ : ℝ) : ℂ) *
      ⟪ConsistentState.vector B.val, h⟫_ℂ := by
  letI := fresh_nonempty B
  change coordinates x (pC x (Conditioning.J x h)) B none = _
  rw [coordinates_pC, CompressionBlock.compression_apply_none,
    CompressionCancellation.inner_extensionUniform_coordinates]
  have hsum : (∑ y : Fresh B.val, Conditioning.J x h (B.val.set x y.val)) =
      (((Real.sqrt gr)⁻¹ : ℝ) : ℂ) *
        ((Real.sqrt (N + 1 - B.val.size : ℕ) : ℂ) *
          ⟪ConsistentState.vector B.val, h⟫_ℂ) := by
    calc
      _ = ∑ y : Fresh B.val, (((Real.sqrt gr)⁻¹ : ℝ) : ℂ) *
          ⟪ConsistentState.vector (B.val.set x y.val), h⟫_ℂ := by
        apply Finset.sum_congr rfl
        intro y _
        exact J_apply_extension_of_gram_eigen x y.val (hres y.val) gr (heigen y.val)
          B.val B.property y.property hB
      _ = _ := by
        rw [← Finset.mul_sum, ← sum_inner, ExtensionResolution.sum_extensions B.val x B.property,
          inner_smul_left]
        simp
  rw [hsum]
  have hsqrt : (Real.sqrt (N + 1 - B.val.size : ℕ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply (Real.sqrt_pos.mpr _).ne'
    exact_mod_cast Nat.sub_pos_of_lt (base_size_lt B)
  simp only [UniformState.amplitude, card_fresh, Complex.ofReal_inv]
  field_simp

/-- At the original database size, every undefined pC J coefficient is the
positive full-to-residual square-root ratio times the actual polar coefficient. -/
theorem pC_J_apply_base_eq_ratio_candidate (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) t)
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N t)
    (gh gr : ℝ) (hgh : 0 < gh) (hgr : 0 < gr)
    (hfull : GramFiltration.gram (N + 1) t h = (gh : ℂ) • h)
    (hresidual : ∀ y, GramFiltration.gram N t (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h)
    (B : Base x) (hB : B.val.size = t) :
    pC x (Conditioning.J x h) B.val =
      ((Real.sqrt gh / Real.sqrt gr : ℝ) : ℂ) *
        PolarEmbedding.candidate (N + 1) h B.val := by
  rw [pC_J_apply_base_of_gram_eigen x hres gr hresidual B hB,
    PolarSpectrum.candidate_of_gram_eigen hh gh hfull, PiLp.smul_apply, smul_eq_mul,
    RawHarmonic.raw_apply_of_size (N + 1) t h B.val hB]
  have hh0 : (Real.sqrt gh : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hgh).ne'
  have hr0 : (Real.sqrt gr : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hgr).ne'
  push_cast
  field_simp

/-- The actual first-row-type compression overlap follows from the actual
Gram equations and same-degree answer restrictions. The ratio is derived;
no overlap identity is supplied as a premise. -/
theorem inner_J_pC_candidate (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) t)
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N t)
    (gh gr : ℝ) (hgh : 0 < gh) (hgr : 0 < gr)
    (hfull : GramFiltration.gram (N + 1) t h = (gh : ℂ) • h)
    (hresidual : ∀ y, GramFiltration.gram N t (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h) :
    ⟪Conditioning.J x h, pC x (PolarEmbedding.candidate (N + 1) h)⟫_ℂ =
      ((Real.sqrt gh / Real.sqrt gr : ℝ) : ℂ) * (‖h‖ ^ 2 : ℝ) := by
  classical
  let c : ℂ := ((Real.sqrt gh / Real.sqrt gr : ℝ) : ℂ)
  have hinner : ⟪pC x (Conditioning.J x h), PolarEmbedding.candidate (N + 1) h⟫_ℂ =
      ⟪c • PolarEmbedding.candidate (N + 1) h, PolarEmbedding.candidate (N + 1) h⟫_ℂ := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro I _
    by_cases hI : I.size = t
    · by_cases hx : x ∈ I.domain
      · have hz : PolarEmbedding.candidate (N + 1) h I = 0 := by
          have hc := congrArg (fun ψ : State (N + 1) => ψ I)
            (definedPart_candidate_eq_zero x hh hres gh hfull)
          simpa [CompressionCancellation.definedPart_apply, hx] using hc
        rw [hz]
        simp
      · have hc := pC_J_apply_base_eq_ratio_candidate x hh hres gh gr hgh hgr
          hfull hresidual ⟨I, hx⟩ hI
        change inner ℂ (pC x (Conditioning.J x h) I)
            (PolarEmbedding.candidate (N + 1) h I) =
          inner ℂ (c * PolarEmbedding.candidate (N + 1) h I)
            (PolarEmbedding.candidate (N + 1) h I)
        rw [hc]
    · rw [PolarDegree.candidate_apply_eq_zero_of_size_ne hh I hI]
      simp
  calc
    _ = ⟪pC x (Conditioning.J x h), PolarEmbedding.candidate (N + 1) h⟫_ℂ := by
      simpa only [pC_involutive] using
        ((pC x).inner_map_map (Conditioning.J x h)
          (pC x (PolarEmbedding.candidate (N + 1) h))).symm
    _ = ⟪c • PolarEmbedding.candidate (N + 1) h, PolarEmbedding.candidate (N + 1) h⟫_ℂ :=
      hinner
    _ = _ := by
      rw [inner_smul_left, inner_self_eq_norm_sq_to_K,
        (PolarEmbedding.candidate (N + 1)).norm_map]
      simp [c, ← Complex.ofReal_pow]

end QuantumOracle.ConditioningFirstRow
