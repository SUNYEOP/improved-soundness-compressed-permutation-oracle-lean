import QuantumOracle.Model.ExtensionResolution
import QuantumOracle.Model.GramRange

/-!
# Actual adjoint coefficients and fresh-extension cancellation

The coefficients here belong to the adjoint of the concrete extension operator.
They are not yet coefficients of the harmonic isometry: normalizing the adjoint
on the relevant spectral summands remains a separate step.
-/

noncomputable section

namespace QuantumOracle.AdjointCoefficients

open PermutationExtensions ExtensionOperator
open scoped BigOperators InnerProductSpace

variable {N t : ℕ}

/-- Each database coefficient of the actual adjoint is its extension-state overlap. -/
theorem adjoint_apply (N t : ℕ) (h : EuclideanSpace ℂ (Perm N))
    (I : Level N t) :
    (T N t).adjoint h I = ⟪ConsistentState.vector I.val, h⟫_ℂ := by
  classical
  rw [← T_single N t I, ← LinearMap.adjoint_inner_right]
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul]

/-- A fresh extension, packaged as an actual database in the next level. -/
def freshExtension (I : Database N) (x : Fin N) (hx : x ∉ I.domain)
    (y : UnusedImage I) : Level N (I.size + 1) :=
  ⟨I.set x y.val, Database.set_size_of_fresh I x y.val hx y.property⟩

/-- The unnormalized adjoint already has the fresh-output cancellation identity
on vectors orthogonal to the actual lower knowledge space. -/
theorem sum_adjoint_extensions_eq_zero (I : Database N) (x : Fin N)
    (hx : x ∉ I.domain) (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ (KnowledgeSpace.K N I.size)ᗮ) :
    (∑ y : UnusedImage I,
      (T N (I.size + 1)).adjoint h (freshExtension I x hx y)) = 0 := by
  simp_rw [adjoint_apply]
  exact ExtensionResolution.sum_inner_extensions_eq_zero I x hx h hh

/-- On its actual range, the extension operator's adjoint has no kernel. -/
theorem adjoint_eq_zero_iff_of_mem (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ KnowledgeSpace.K N t) :
    (T N t).adjoint h = 0 ↔ h = 0 := by
  constructor
  · intro hz
    have ho : h ∈ (KnowledgeSpace.K N t)ᗮ := by
      rw [← KnowledgeSpace.range_T, GramRange.range_orthogonal]
      exact hz
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp
      (Submodule.inner_right_of_mem_orthogonal hh ho)
  · intro hz
    rw [hz, map_zero]

/-- Distinct vectors in the actual knowledge space have distinct adjoint images. -/
theorem adjoint_injective_on_knowledge :
    Set.InjOn (T N t).adjoint (KnowledgeSpace.K N t : Set _) := by
  intro h hh k hk heq
  apply sub_eq_zero.mp
  apply (adjoint_eq_zero_iff_of_mem (h - k)
    ((KnowledgeSpace.K N t).sub_mem hh hk)).mp
  rw [map_sub, heq, sub_self]

/-- A nonzero actual knowledge vector has a strictly positive adjoint norm. -/
theorem norm_adjoint_pos_of_mem (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ KnowledgeSpace.K N t) (hne : h ≠ 0) :
    0 < ‖(T N t).adjoint h‖ := by
  apply norm_pos_iff.mpr
  intro hz
  exact hne ((adjoint_eq_zero_iff_of_mem h hh).mp hz)

end QuantumOracle.AdjointCoefficients
