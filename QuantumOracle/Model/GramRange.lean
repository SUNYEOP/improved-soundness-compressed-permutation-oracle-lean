import QuantumOracle.Model.KnowledgeSpace

/-! The range equality used after Appendix A's spectrum lemma is finite-dimensional
linear algebra and is independent of the symmetric-group spectral calculation. -/

noncomputable section

namespace QuantumOracle.GramRange

open scoped InnerProductSpace

variable {R C : Type*} [Fintype R] [Fintype C]

theorem range_orthogonal (A : EuclideanSpace ℂ C →ₗ[ℂ] EuclideanSpace ℂ R) :
    (LinearMap.range A)ᗮ = LinearMap.ker A.adjoint := by
  ext v
  simp only [Submodule.mem_orthogonal, LinearMap.mem_ker]
  constructor
  · intro h
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [A.adjoint_inner_right]
    exact h _ ⟨A.adjoint v, rfl⟩
  · intro h x hx
    obtain ⟨w, rfl⟩ := hx
    rw [← A.adjoint_inner_right, h, inner_zero_right]

theorem ker_comp_adjoint (A : EuclideanSpace ℂ C →ₗ[ℂ] EuclideanSpace ℂ R) :
    LinearMap.ker (A.comp A.adjoint) = LinearMap.ker A.adjoint := by
  ext v
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · intro h
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [A.adjoint_inner_right, h, inner_zero_left]
  · intro h
    rw [h, map_zero]

theorem range_comp_adjoint (A : EuclideanSpace ℂ C →ₗ[ℂ] EuclideanSpace ℂ R) :
    LinearMap.range (A.comp A.adjoint) = LinearMap.range A := by
  have h : (LinearMap.range (A.comp A.adjoint))ᗮ = (LinearMap.range A)ᗮ := by
    rw [range_orthogonal, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
      ker_comp_adjoint, range_orthogonal]
  have hh := congrArg Submodule.orthogonal h
  simpa only [Submodule.orthogonal_orthogonal] using hh

/-- The range of the actual `T T†` is exactly the span of size-t consistent states. -/
theorem range_T_comp_adjoint (N t : ℕ) :
    LinearMap.range ((ExtensionOperator.T N t).comp (ExtensionOperator.T N t).adjoint) =
      KnowledgeSpace.K N t := by
  rw [range_comp_adjoint, KnowledgeSpace.range_T]

end QuantumOracle.GramRange
