import QuantumOracle.Model.FiniteDensity
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Actual output projections and finite purification distance

An output Hilbert orthogonal projection acts independently at each ancilla
coordinate. Its norm is contractive, and its projected norm is determined by
the actual output reduction. Thus differences of projected norms are bounded
by the infimum over all actual common finite purifications.
-/

noncomputable section

namespace QuantumOracle.ProjectorPurification

open WorkspaceKnowledge
open scoped BigOperators InnerProductSpace

variable {d n m : ℕ}

/-- The actual output vector at one fixed ancilla coordinate. -/
def column (ψ : PureState d n) (a : Fin n) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 (fun i => ψ (i, a))

/-- Lift the output's Hilbert orthogonal projection to the actual joint vector. -/
def project (P : Submodule ℂ (EuclideanSpace ℂ (Fin d))) :
    PureState d n →ₗ[ℂ] PureState d n :=
  onWorkspace (Fin n) P.starProjection.toLinearMap

@[simp] theorem project_apply (P : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    (ψ : PureState d n) (i : Fin d) (a : Fin n) :
    project P ψ (i, a) = P.starProjection (column ψ a) i := rfl

@[simp] theorem column_project (P : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    (ψ : PureState d n) (a : Fin n) :
    column (project P ψ) a = P.starProjection (column ψ a) := by
  ext i
  rfl

theorem norm_sq_eq_sum_columns (ψ : PureState d n) :
    ‖ψ‖ ^ 2 = ∑ a : Fin n, ‖column ψ a‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, column]
  exact Finset.sum_comm

theorem norm_project_le (P : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    (ψ : PureState d n) : ‖project P ψ‖ ≤ ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_sum_columns, norm_sq_eq_sum_columns]
  apply Finset.sum_le_sum
  intro a _
  rw [column_project]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (P.norm_starProjection_apply_le (column ψ a))

theorem norm_project_sub_le (P : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    (ψ φ : PureState d n) : ‖project P ψ - project P φ‖ ≤ ‖ψ - φ‖ := by
  rw [← map_sub]
  exact norm_project_le P (ψ - φ)

theorem abs_project_norm_sub_le_norm (P : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    (ψ φ : PureState d n) : |‖project P ψ‖ - ‖project P φ‖| ≤ ‖ψ - φ‖ :=
  (abs_norm_sub_norm_le (project P ψ) (project P φ)).trans (norm_project_sub_le P ψ φ)

/-- Any fixed output linear operation has the same resulting norm on two
vectors with the same actual reduced state, even with different ancillas. -/
theorem norm_onWorkspace_eq_of_reduced_eq
    (U : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d))
    {ψ : PureState d n} {φ : PureState d m} (h : reducedState ψ = reducedState φ) :
    ‖onWorkspace (Fin n) U ψ‖ = ‖onWorkspace (Fin m) U φ‖ := by
  have hg : HiddenIsometry.reduced ψ = HiddenIsometry.reduced φ := h
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [HiddenIsometry.norm_sq_eq_sum_slices, HiddenIsometry.norm_sq_eq_sum_slices]
  apply Finset.sum_congr rfl
  intro a _
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
  congr 1
  simp only [slice_onWorkspace, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  simp_rw [← HiddenIsometry.reduced_eq_inner, hg]

/-- The actual projected norm depends only on the actual output reduction. -/
theorem norm_project_eq_of_reduced_eq (P : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    {ψ : PureState d n} {φ : PureState d m} (h : reducedState ψ = reducedState φ) :
    ‖project P ψ‖ = ‖project P φ‖ :=
  norm_onWorkspace_eq_of_reduced_eq P.starProjection.toLinearMap h

/-- The projected-norm discrepancy is bounded by every actual witness distance. -/
theorem abs_project_norm_sub_le_witness (P : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    {ρ σ : ReducedState d} (p q : CommonPurification ρ σ) :
    |‖project P p.exactVector‖ - ‖project P p.compressedVector‖| ≤ q.distance := by
  rw [norm_project_eq_of_reduced_eq P (p.exact_reduction.trans q.exact_reduction.symm),
    norm_project_eq_of_reduced_eq P (p.compressed_reduction.trans q.compressed_reduction.symm)]
  exact abs_project_norm_sub_le_norm P q.exactVector q.compressedVector

/-- Taking the infimum over all finite common purifications preserves the
projector estimate; no minimizing witness or attainment assumption is needed. -/
theorem abs_project_norm_sub_le_purificationDistance
    (P : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    {ρ σ : ReducedState d} (p : CommonPurification ρ σ) :
    |‖project P p.exactVector‖ - ‖project P p.compressedVector‖| ≤ purificationDistance ρ σ := by
  apply le_csInf ⟨p.distance, Set.mem_range_self p⟩
  rintro _ ⟨q, rfl⟩
  exact abs_project_norm_sub_le_witness P p q

/-- Reference vectors with the prescribed reductions obey the same bound,
regardless of whether they share an ancilla or realize the infimum. -/
theorem abs_project_norm_sub_le_purificationDistance_of_reduced_eq
    (P : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    {ρ σ : ReducedState d} (p : CommonPurification ρ σ)
    {ψ : PureState d n} {φ : PureState d m}
    (hψ : reducedState ψ = ρ) (hφ : reducedState φ = σ) :
    |‖project P ψ‖ - ‖project P φ‖| ≤ purificationDistance ρ σ := by
  rw [norm_project_eq_of_reduced_eq P (hψ.trans p.exact_reduction.symm),
    norm_project_eq_of_reduced_eq P (hφ.trans p.compressed_reduction.symm)]
  exact abs_project_norm_sub_le_purificationDistance P p

end QuantumOracle.ProjectorPurification
