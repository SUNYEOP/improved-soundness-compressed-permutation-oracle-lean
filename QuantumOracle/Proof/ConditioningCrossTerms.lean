import QuantumOracle.Proof.ConditioningSpechtBounds

/-!
# Bilinear conditioning overlaps and actual error cross terms

The coefficient identities are applied to two different input vectors. The
proofs use the physical database degrees and the actual compression blocks;
no distinctness of Gram eigenvalues or error-image orthogonality is assumed.
-/

noncomputable section

namespace QuantumOracle.ConditioningCrossTerms

open PermutationExtensions HarmonicLayers Compression CompressionIndex
open CompressionCancellation DatabaseDegree
open scoped BigOperators InnerProductSpace

attribute [local irreducible] PolarEmbedding.candidate

variable {N t u : ℕ}

theorem inner_pC_swap (x : Fin N) (v w : State N) :
    ⟪v, pC x w⟫_ℂ = ⟪pC x v, w⟫_ℂ := by
  simpa only [pC_involutive] using ((pC x).inner_map_map v (pC x w)).symm

theorem inner_raw_raw (N t : ℕ) (h k : EuclideanSpace ℂ (Perm N)) :
    ⟪RawHarmonic.raw N t h, RawHarmonic.raw N t k⟫_ℂ =
      ⟪h, GramFiltration.gram N t k⟫_ℂ := by
  change ⟪LevelEmbedding.embed N t ((ExtensionOperator.T N t).adjoint h),
    LevelEmbedding.embed N t ((ExtensionOperator.T N t).adjoint k)⟫_ℂ = _
  rw [(LevelEmbedding.embed N t).inner_map_map]
  exact (ExtensionOperator.T N t).adjoint_inner_left _ _

/-- Compression of an inserted pure residual degree has no defined amplitude
at other degrees. The base coordinates of J are identically zero. -/
theorem pC_J_apply_defined_of_size_ne (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))}
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N u)
    (I : Database (N + 1)) (hx : x ∈ I.domain) (hI : I.size ≠ u + 1) :
    pC x (Conditioning.J x h) I = 0 := by
  obtain ⟨⟨B, o⟩, rfl⟩ := decode_surjective x I
  cases o with
  | none => exact (B.property hx).elim
  | some y =>
    have hB : B.val.size + 1 ≠ u + 1 := by
      simpa only [decode_some_size] using hI
    have hc : coordinates x (Conditioning.J x h) B = 0 := by
      ext z
      cases z with
      | none => exact Conditioning.J_apply_of_undefined x h B.val B.property
      | some z =>
        change Conditioning.J x h (B.val.set x z.val) = 0
        apply ConditioningSpectrum.J_mem_exactLevel x hres
        simpa only [Database.set_size_of_fresh B.val x z.val B.property z.property] using hB
    change coordinates x (pC x (Conditioning.J x h)) B (some y) = 0
    rw [coordinates_pC, hc, map_zero]
    rfl

/-- The complete lower-degree part of pC J is the normalized raw adjoint.
The input itself need not have that full harmonic degree. -/
theorem project_pC_J_eq_raw (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))}
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N t) (gr : ℝ)
    (hresidual : ∀ y, GramFiltration.gram N t (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h) :
    project (N + 1) t (pC x (Conditioning.J x h)) =
      (((Real.sqrt gr)⁻¹ : ℝ) : ℂ) • RawHarmonic.raw (N + 1) t h := by
  classical
  ext I
  rw [project_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases hI : I.size = t
  · rw [if_pos hI]
    by_cases hx : x ∈ I.domain
    · rw [pC_J_apply_defined_of_size_ne x hres I hx (by omega),
        ConditioningFirstRow.raw_apply_eq_zero_of_defined x hres I hx, mul_zero]
    · rw [ConditioningFirstRow.pC_J_apply_base_of_gram_eigen x hres gr hresidual
        ⟨I, hx⟩ hI, RawHarmonic.raw_apply_of_size (N + 1) t h I hI]
  · rw [if_neg hI, RawHarmonic.raw_apply_of_ne (N + 1) t h I hI, mul_zero]

/-- The lower-degree bilinear overlap, with an arbitrary first input. -/
theorem inner_J_pC_candidate_lower (x : Fin (N + 1))
    {h k : EuclideanSpace ℂ (Perm (N + 1))}
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N t)
    (hk : k ∈ H (N + 1) t) (gk gr : ℝ) (hgk : 0 < gk) (hgr : 0 < gr)
    (hfull : GramFiltration.gram (N + 1) t k = (gk : ℂ) • k)
    (hresidual : ∀ y, GramFiltration.gram N t (ResidualAdjoint.restrict x y h) =
      (gr : ℂ) • ResidualAdjoint.restrict x y h) :
    ⟪Conditioning.J x h, pC x (PolarEmbedding.candidate (N + 1) k)⟫_ℂ =
      ((Real.sqrt gk / Real.sqrt gr : ℝ) : ℂ) * ⟪h, k⟫_ℂ := by
  rw [inner_pC_swap]
  have hp := (project_eq_self_iff (N + 1) t _).mpr
    (PolarDegree.candidate_mem_exactLevel hk)
  calc
    _ = ⟪project (N + 1) t (pC x (Conditioning.J x h)),
        PolarEmbedding.candidate (N + 1) k⟫_ℂ := by
      rw [project_isSymmetric, hp]
    _ = _ := by
      rw [project_pC_J_eq_raw x hres gr hresidual,
        PolarSpectrum.candidate_of_gram_eigen hk gk hfull,
        inner_smul_left, inner_smul_right, inner_raw_raw, hfull, inner_smul_right]
      simp only [map_inv₀, Complex.conj_ofReal, Complex.ofReal_inv]
      have ha : (Real.sqrt gk : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hgk).ne'
      have hb : (Real.sqrt gr : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hgr).ne'
      have hs : (Real.sqrt gk : ℂ) ^ 2 = (gk : ℂ) := by
        exact_mod_cast Real.sq_sqrt hgk.le
      push_cast
      field_simp
      rw [← hs]

/-- The adjacent-degree bilinear overlap comes from the actual defined part. -/
theorem inner_J_pC_candidate_tail (x : Fin (N + 1))
    {h k : EuclideanSpace ℂ (Perm (N + 1))}
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N u)
    (hk : k ∈ H (N + 1) (u + 1))
    (kres : ∀ y, ResidualAdjoint.restrict x y k ∈ H N u)
    (gk gr : ℝ) (hgk : 0 < gk) (hgr : 0 < gr)
    (hfull : GramFiltration.gram (N + 1) (u + 1) k = (gk : ℂ) • k)
    (hresidual : ∀ y, GramFiltration.gram N u (ResidualAdjoint.restrict x y k) =
      (gr : ℂ) • ResidualAdjoint.restrict x y k) :
    ⟪Conditioning.J x h, pC x (PolarEmbedding.candidate (N + 1) k)⟫_ℂ =
      ((Real.sqrt gr / Real.sqrt gk : ℝ) : ℂ) * ⟪h, k⟫_ℂ := by
  have hp := (project_eq_self_iff (N + 1) (u + 1) _).mpr
    (ConditioningSpectrum.J_mem_exactLevel x hres)
  calc
    _ = ⟪project (N + 1) (u + 1) (Conditioning.J x h),
        pC x (PolarEmbedding.candidate (N + 1) k)⟫_ℂ := by rw [hp]
    _ = _ := by
      rw [project_isSymmetric, CompressionDegree.project_pC_candidate x hk,
        ConditioningSpectrum.definedPart_candidate_eq_ratio_J x hk kres gk gr hgk hgr
          hfull hresidual, inner_smul_right, Conditioning.J_inner]

/-- All directed cross terms vanish between orthogonal inputs with the actual
full/residual degree pattern. Both same-degree and adjacent-degree cases are
covered by the proved bilinear formulas; all other degrees have disjoint support. -/
theorem inner_J_pC_candidate_eq_zero {v : ℕ} (x : Fin (N + 1))
    {h k : EuclideanSpace ℂ (Perm (N + 1))}
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N u)
    (hk : k ∈ H (N + 1) t)
    (kres : ∀ y, ResidualAdjoint.restrict x y k ∈ H N v)
    (gk ghres gkres : ℝ) (hgk : 0 < gk) (hghres : 0 < ghres) (hgkres : 0 < gkres)
    (hfull : GramFiltration.gram (N + 1) t k = (gk : ℂ) • k)
    (hresidual : ∀ y, GramFiltration.gram N u (ResidualAdjoint.restrict x y h) =
      (ghres : ℂ) • ResidualAdjoint.restrict x y h)
    (kresidual : ∀ y, GramFiltration.gram N v (ResidualAdjoint.restrict x y k) =
      (gkres : ℂ) • ResidualAdjoint.restrict x y k)
    (hbranch : v = t ∨ v + 1 = t) (horth : ⟪h, k⟫_ℂ = 0) :
    ⟪Conditioning.J x h, pC x (PolarEmbedding.candidate (N + 1) k)⟫_ℂ = 0 := by
  by_cases hu : u = t
  · subst u
    rw [inner_J_pC_candidate_lower x hres hk gk ghres hgk hghres hfull hresidual,
      horth, mul_zero]
  · by_cases hut : u + 1 = t
    · rcases hbranch with hvt | hvt
      · subst v
        have hp := (project_eq_self_iff (N + 1) t _).mpr
          (show Conditioning.J x h ∈ exactLevel (N + 1) t from
            hut ▸ ConditioningSpectrum.J_mem_exactLevel x hres)
        calc
          _ = ⟪project (N + 1) t (Conditioning.J x h),
              pC x (PolarEmbedding.candidate (N + 1) k)⟫_ℂ := by rw [hp]
          _ = 0 := by
            rw [project_isSymmetric, CompressionDegree.project_pC_candidate x hk,
              ConditioningFirstRow.definedPart_candidate_eq_zero x hk kres gk hfull,
              inner_zero_right]
      · have hvu : v = u := by omega
        subst v
        subst t
        rw [inner_J_pC_candidate_tail x hres hk kres gk gkres hgk hgkres hfull kresidual,
          horth, mul_zero]
    · rw [PiLp.inner_apply]
      apply Finset.sum_eq_zero
      intro I _
      by_cases hI : I.size = u + 1
      · rw [PolarDegree.pC_candidate_supported_two_levels x hk I (by omega) (by omega),
          inner_zero_right]
      · rw [ConditioningSpectrum.J_mem_exactLevel x hres I hI, inner_zero_left]

open SpechtFoundation HookRowFactorization

/-- Actual corner deletion supplies exactly the two harmonic degree patterns. -/
theorem branch_degrees {N : ℕ} (la : Nat.Partition (N + 1)) (mu : Nat.Partition N)
    (hbranch : mu ∈ removeCorners la) :
    (tail (diagram mu)).card = (tail (diagram la)).card ∨
      (tail (diagram mu)).card + 1 = (tail (diagram la)).card := by
  rcases YoungBranchCases.branching_cases la mu hbranch with ⟨_, ht⟩ | ⟨_, c, ht⟩
  · exact Or.inl (congrArg YoungDiagram.card ht)
  · right
    rw [ht]
    exact AtlasKnownTheorems.HookLengthFormula.eraseCorner_card_add_one _ c.1 c.2

/-- Cross overlap between distinct actual joint blocks is zero; the genuine
hook scalar and harmonic degree are obtained internally from their types. -/
theorem inner_J_pC_candidate_joint_eq_zero (x : Fin (N + 1))
    (a b : JointSpectralDecomposition.Labels N) (hne : a ≠ b)
    (hbranch : b.2 ∈ removeCorners b.1)
    {h k : EuclideanSpace ℂ (Perm (N + 1))}
    (hh : h ∈ JointSpectralDecomposition.space x a)
    (hk : k ∈ JointSpectralDecomposition.space x b) :
    ⟪Conditioning.J x h, pC x (PolarEmbedding.candidate (N + 1) k)⟫_ℂ = 0 := by
  have hr := (ResidualSpectralDecomposition.mem_space x a.2 h).mp hh.2
  have kr := (ResidualSpectralDecomposition.mem_space x b.2 k).mp hk.2
  exact inner_J_pC_candidate_eq_zero x
    (fun y => SpechtSpectralFormula.space_le_H_minimal N a.2 (hr y))
    (SpechtSpectralFormula.space_le_H_minimal (N + 1) b.1 hk.1)
    (fun y => SpechtSpectralFormula.space_le_H_minimal N b.2 (kr y))
    (HookRatioProducts.normalizedRowProduct ((diagram b.1).rowLen 0) (tail (diagram b.1)))
    (HookRatioProducts.normalizedRowProduct ((diagram a.2).rowLen 0) (tail (diagram a.2)))
    (HookRatioProducts.normalizedRowProduct ((diagram b.2).rowLen 0) (tail (diagram b.2)))
    (HookRatioProducts.normalizedRowProduct_pos _ _ (tail_rowLen_le _))
    (HookRatioProducts.normalizedRowProduct_pos _ _ (tail_rowLen_le _))
    (HookRatioProducts.normalizedRowProduct_pos _ _ (tail_rowLen_le _))
    (SpechtSpectralFormula.gram_minimal (N + 1) b.1 hk.1)
    (fun y => SpechtSpectralFormula.gram_minimal N a.2 (hr y))
    (fun y => SpechtSpectralFormula.gram_minimal N b.2 (kr y))
    (branch_degrees b.1 b.2 hbranch)
    (JointSpectralDecomposition.inner_eq_zero hne hh hk)

/-- The actual error images of distinct allowed joint branches are orthogonal.
This is derived from the actual coefficient formulas and two isometries. -/
theorem error_inner_eq_zero (x : Fin (N + 1))
    (a b : JointSpectralDecomposition.Labels N) (hne : a ≠ b)
    (ha : a.2 ∈ removeCorners a.1) (hb : b.2 ∈ removeCorners b.1)
    {h k : EuclideanSpace ℂ (Perm (N + 1))}
    (hh : h ∈ JointSpectralDecomposition.space x a)
    (hk : k ∈ JointSpectralDecomposition.space x b) :
    ⟪Conditioning.J x h - pC x (PolarEmbedding.candidate (N + 1) h),
      Conditioning.J x k - pC x (PolarEmbedding.candidate (N + 1) k)⟫_ℂ = 0 := by
  have horth := JointSpectralDecomposition.inner_eq_zero hne hh hk
  have hcross := inner_J_pC_candidate_joint_eq_zero x a b hne hb hh hk
  have kcross := (inner_eq_zero_symm (𝕜 := ℂ)).mp
    (inner_J_pC_candidate_joint_eq_zero x b a (Ne.symm hne) ha hk hh)
  rw [inner_sub_left, inner_sub_right, inner_sub_right, Conditioning.J_inner,
    (pC x).inner_map_map, (PolarEmbedding.candidate (N + 1)).inner_map_map,
    horth, hcross, kcross]
  ring

end QuantumOracle.ConditioningCrossTerms
