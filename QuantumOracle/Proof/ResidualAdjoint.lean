import QuantumOracle.Proof.ResidualConsistency
import QuantumOracle.Model.KnowledgeSpace
import QuantumOracle.Model.WorkspaceKnowledge

/-!
# Actual answer restriction and its adjoint

Restriction selects one answer sector after the concrete residual reindexing.
Its mathematical adjoint adjoins that answer. On actual consistent states it
agrees exactly with insertion of the prescribed database edge, which gives the
knowledge-space and orthogonality transfer without spectral assumptions.
-/

noncomputable section

namespace QuantumOracle.ResidualAdjoint

open PermutationExtensions WorkspaceKnowledge
open scoped BigOperators InnerProductSpace

variable {N s : ℕ}

/-- Actual restriction to the answer y at x in residual permutation coordinates. -/
def restrict (x y : Fin (N + 1)) :
    EuclideanSpace ℂ (Perm (N + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Perm N) :=
  (sliceLinear y).comp (ResidualPermutation.reindex x).toLinearEquiv.toLinearMap

@[simp] theorem restrict_apply (x y : Fin (N + 1))
    (h : EuclideanSpace ℂ (Perm (N + 1))) (σ : Perm N) :
    restrict x y h σ = h (ResidualPermutation.insert x y σ) := rfl

theorem restrict_eq_slice (x y : Fin (N + 1)) (h : EuclideanSpace ℂ (Perm (N + 1))) :
    restrict x y h = slice (ResidualPermutation.reindex x h) y := rfl

/-- Adjoining an answer is the actual Euclidean adjoint of restriction. -/
def adjoin (x y : Fin (N + 1)) :
    EuclideanSpace ℂ (Perm N) →ₗ[ℂ] EuclideanSpace ℂ (Perm (N + 1)) :=
  (restrict x y).adjoint

theorem inner_vector_insert (x y : Fin (N + 1)) (I : Database N)
    (h : EuclideanSpace ℂ (Perm (N + 1))) :
    ⟪ConsistentState.vector (ResidualDatabase.insert x y I), h⟫_ℂ =
      ⟪ConsistentState.vector I, restrict x y h⟫_ℂ := by
  classical
  calc
    _ = ⟪ResidualPermutation.reindex x (ConsistentState.vector (ResidualDatabase.insert x y I)),
        ResidualPermutation.reindex x h⟫_ℂ :=
      ((ResidualPermutation.reindex x).inner_map_map _ _).symm
    _ = _ := by
      simp only [PiLp.inner_apply, Fintype.sum_prod_type,
        ResidualConsistency.reindex_vector_insert]
      rw [Finset.sum_eq_single y]
      · simp only
        rfl
      · intro z _ hzy
        simp only [if_neg hzy, inner_zero_left, Finset.sum_const_zero]
      · simp

/-- The adjoint truly inserts the prescribed edge into every consistent state. -/
@[simp] theorem adjoin_vector (x y : Fin (N + 1)) (I : Database N) :
    adjoin x y (ConsistentState.vector I) =
      ConsistentState.vector (ResidualDatabase.insert x y I) := by
  apply ext_inner_right ℂ
  intro h
  rw [adjoin, LinearMap.adjoint_inner_left, inner_vector_insert]

/-- Actual adjoint answer insertion increases the consistency level by one. -/
theorem adjoin_mem_K (x y : Fin (N + 1)) (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ KnowledgeSpace.K N s) :
    adjoin x y h ∈ KnowledgeSpace.K (N + 1) (s + 1) := by
  apply Submodule.span_induction
    (p := fun h _ => adjoin x y h ∈ KnowledgeSpace.K (N + 1) (s + 1)) ?_ ?_ ?_ ?_ hh
  · rintro _ ⟨I, rfl⟩
    rw [adjoin_vector]
    apply KnowledgeSpace.vector_mem
    rw [ResidualDatabase.insert_size, I.property]
  · simp
  · intro h k _ _ hh hk
    simpa using (KnowledgeSpace.K (N + 1) (s + 1)).add_mem hh hk
  · intro c h _ hh
    simpa using (KnowledgeSpace.K (N + 1) (s + 1)).smul_mem c hh

/-- Orthogonality lowers to the residual consistency space under actual restriction. -/
theorem restrict_mem_orthogonal (x y : Fin (N + 1))
    (h : EuclideanSpace ℂ (Perm (N + 1)))
    (hh : h ∈ (KnowledgeSpace.K (N + 1) (s + 1))ᗮ) :
    restrict x y h ∈ (KnowledgeSpace.K N s)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro k hk
  rw [← LinearMap.adjoint_inner_left]
  exact Submodule.inner_right_of_mem_orthogonal (adjoin_mem_K x y k hk) hh

/-- Selecting the same actual answer before restriction leaves all residual coefficients unchanged. -/
theorem restrict_answerProjection (x y : Fin (N + 1))
    (h : EuclideanSpace ℂ (Perm (N + 1))) :
    restrict x y (ConsistentState.answerProjection x y h) = restrict x y h := by
  ext σ
  simp [restrict_apply, ConsistentState.answerProjection_apply, ResidualPermutation.insert_at]

end QuantumOracle.ResidualAdjoint
