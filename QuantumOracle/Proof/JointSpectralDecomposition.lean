import QuantumOracle.Proof.ResidualSpectralSymmetry

/-!
# Actual joint full and residual spectral components

First project onto a full Specht block and then perform the answerwise residual
projection. Residual splitting preserves the full type. The resulting actual
vectors form a complete orthogonal decomposition, with no assumption about
which pairs of partition labels are allowed by branching.
-/

noncomputable section

namespace QuantumOracle.JointSpectralDecomposition

open PermutationExtensions
open scoped BigOperators InnerProductSpace

variable {N : ℕ}

abbrev Labels (N : ℕ) := Nat.Partition (N + 1) × Nat.Partition N

def space (x : Fin (N + 1)) (label : Labels N) :
    Submodule ℂ (EuclideanSpace ℂ (Perm (N + 1))) :=
  SpechtIsotypic.space (N + 1) label.1 ⊓ ResidualSpectralDecomposition.space x label.2

/-- The two actual spectral projections, with the full projection applied first. -/
def project (x : Fin (N + 1)) (label : Labels N) :
    EuclideanSpace ℂ (Perm (N + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Perm (N + 1)) :=
  (ResidualSpectralDecomposition.project x label.2).comp
    (SpechtIsotypic.space (N + 1) label.1).starProjection.toLinearMap

theorem project_mem (x : Fin (N + 1)) (label : Labels N)
    (h : EuclideanSpace ℂ (Perm (N + 1))) : project x label h ∈ space x label :=
  ⟨ResidualSpectralSymmetry.project_mem_full_space x label.2 label.1
      ((SpechtIsotypic.space (N + 1) label.1).starProjection_apply_mem h),
    ResidualSpectralDecomposition.project_mem x label.2 _⟩

theorem inner_eq_zero {x : Fin (N + 1)} {a b : Labels N} (hne : a ≠ b)
    {h k : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ space x a) (hk : k ∈ space x b) :
    ⟪h, k⟫_ℂ = 0 := by
  by_cases hf : a.1 = b.1
  · have hr : a.2 ≠ b.2 := fun he => hne (Prod.ext hf he)
    exact ResidualSpectralDecomposition.inner_eq_zero hr hh.2 hk.2
  · exact SpechtOrthogonal.inner_eq_zero hf hh.1 hk.1

/-- Both actual finite spectral splittings reconstruct every input. -/
theorem sum_project (x : Fin (N + 1)) (h : EuclideanSpace ℂ (Perm (N + 1))) :
    (∑ label : Labels N, project x label h) = h := by
  rw [Fintype.sum_prod_type]
  change (∑ la : Nat.Partition (N + 1), ∑ mu : Nat.Partition N,
    ResidualSpectralDecomposition.project x mu ((SpechtIsotypic.space (N + 1) la).starProjection h)) = h
  simp only [ResidualSpectralDecomposition.sum_project]
  exact SpechtOrthogonal.sum_projection (N + 1) h

theorem full_gram_project (x : Fin (N + 1)) (label : Labels N) (t : ℕ)
    (h : EuclideanSpace ℂ (Perm (N + 1))) :
    GramFiltration.gram (N + 1) t (project x label h) =
      SpechtCharacter.eigenvalue (N + 1) t label.1 • project x label h :=
  SpechtIsotypic.gram_eq_eigenvalue (N + 1) t label.1 (project_mem x label h).1

theorem residual_gram_project (x y : Fin (N + 1)) (label : Labels N) (t : ℕ)
    (h : EuclideanSpace ℂ (Perm (N + 1))) :
    GramFiltration.gram N t (ResidualAdjoint.restrict x y (project x label h)) =
      SpechtCharacter.eigenvalue N t label.2 • ResidualAdjoint.restrict x y (project x label h) :=
  SpechtIsotypic.gram_eq_eigenvalue N t label.2
    ((ResidualSpectralDecomposition.mem_space x label.2 _).mp (project_mem x label h).2 y)

attribute [local irreducible] space

local instance blockInnerProductSpace (x : Fin (N + 1)) :
    (label : Labels N) → InnerProductSpace ℂ ↥(space x label) := fun _ => inferInstance

theorem orthogonalFamily (x : Fin (N + 1)) :
    OrthogonalFamily ℂ (fun label : Labels N => ↥(space x label))
      (fun label => (space x label).subtypeₗᵢ) := by
  intro a b hne h k
  exact inner_eq_zero hne h.property k.property

/-- Exact Parseval identity for the actual joint components. -/
theorem norm_sq_eq_sum_project (x : Fin (N + 1))
    (h : EuclideanSpace ℂ (Perm (N + 1))) :
    ‖h‖ ^ 2 = ∑ label : Labels N, ‖project x label h‖ ^ 2 := by
  have he := (orthogonalFamily x).norm_sum
    (fun label => ⟨project x label h, project_mem x label h⟩) Finset.univ
  change ‖∑ label : Labels N, project x label h‖ ^ 2 =
    ∑ label : Labels N, ‖project x label h‖ ^ 2 at he
  rwa [sum_project] at he

end QuantumOracle.JointSpectralDecomposition
