import QuantumOracle.Model.RawHarmonic

/-!
# Assembling the unnormalized degree maps

Orthogonal projections onto the actual knowledge layers followed by their
actual extension adjoints give a concrete injective map into the database
register. This is an algebraic precursor to W, with no isometry claim.
-/

noncomputable section

namespace QuantumOracle.RawEmbedding

open PermutationExtensions HarmonicLayers RawHarmonic
open scoped BigOperators InnerProductSpace

attribute [local irreducible] HarmonicLayers.H KnowledgeSpace.K

private theorem sum_apply {ι α : Type*} [Fintype ι] [Fintype α]
    (v : ι → EuclideanSpace ℂ α) (a : α) : (∑ i, v i) a = ∑ i, v i a :=
  map_sum (PiLp.projₗ 2 (𝕜 := ℂ) (fun _ : α => ℂ) a) v Finset.univ

/-- Assemble all actual degree components into their physical database levels. -/
def total (N : ℕ) : EuclideanSpace ℂ (Perm N) →ₗ[ℂ] Compression.State N :=
  ∑ i : Fin (N + 1), (raw N i.val).comp (H N i.val).starProjection.toLinearMap

theorem total_apply (N : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    total N h = ∑ i : Fin (N + 1), raw N i.val ((H N i.val).starProjection h) := by
  simp only [total, LinearMap.sum_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe]

theorem total_inner_component (N : ℕ) (h : EuclideanSpace ℂ (Perm N))
    (i : Fin (N + 1)) :
    ⟪total N h, raw N i.val ((H N i.val).starProjection h)⟫_ℂ =
      ⟪raw N i.val ((H N i.val).starProjection h),
        raw N i.val ((H N i.val).starProjection h)⟫_ℂ := by
  rw [total_apply, sum_inner]
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact inner_raw_of_ne (fun heq => hji (Fin.ext heq)) _ _
  · simp

/-- No exact hidden-register vector is lost by the unnormalized layer assembly. -/
theorem total_eq_zero_iff (N : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    total N h = 0 ↔ h = 0 := by
  constructor
  · intro hz
    have hproj (i : Fin (N + 1)) : (H N i.val).starProjection h = 0 := by
      apply (raw_eq_zero_iff_of_mem _
        (H_le_K N i.val ((H N i.val).starProjection_apply_mem h))).mp
      apply (inner_self_eq_zero (𝕜 := ℂ)).mp
      rw [← total_inner_component, hz, inner_zero_left]
    rw [← sum_projection N h]
    exact Finset.sum_eq_zero (fun i _ => hproj i)
  · rintro rfl
    exact map_zero _

theorem total_injective (N : ℕ) : Function.Injective (total N) := by
  intro h k heq
  apply sub_eq_zero.mp
  apply (total_eq_zero_iff N (h - k)).mp
  rw [map_sub, heq, sub_self]

/-- Every assembled vector satisfies the actual fresh-extension cancellation. -/
theorem total_cancels {N : ℕ} (x : Fin N) (h : EuclideanSpace ℂ (Perm N)) :
    CompressionCancellation.Cancels x (total N h) := by
  classical
  intro J
  rw [total_apply]
  simp only [sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  exact raw_cancels x _ ((H N i.val).starProjection_apply_mem h) J

/-- The degree-zero initialization is unchanged by assembling all degrees. -/
theorem total_uniform (N : ℕ) :
    total N (ConsistentState.vector Database.empty) =
      EuclideanSpace.single (Database.empty : Database N) 1 := by
  classical
  have hzero : ConsistentState.vector (Database.empty : Database N) ∈ H N 0 := by
    rw [H_zero]
    exact KnowledgeSpace.vector_empty_mem N
  rw [total_apply]
  calc
    (∑ i : Fin (N + 1), raw N i.val
        ((H N i.val).starProjection (ConsistentState.vector Database.empty))) =
        raw N 0 ((H N 0).starProjection (ConsistentState.vector Database.empty)) := by
      apply Finset.sum_eq_single 0
      · intro i _ hi
        have hpos : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
        have horth : ConsistentState.vector (Database.empty : Database N) ∈ (H N i.val)ᗮ :=
          (Submodule.IsOrtho.symm (orthogonal_of_lt hpos (Nat.le_of_lt_succ i.isLt))) hzero
        rw [(H N i.val).starProjection_apply_eq_zero_iff.mpr horth, map_zero]
      · simp
    _ = EuclideanSpace.single (Database.empty : Database N) 1 := by
      rw [(H N 0).starProjection_eq_self_iff.mpr hzero, raw_zero_uniform]

/-- The empty database coefficient is the original uniform-state overlap. -/
theorem total_apply_empty (N : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    total N h Database.empty = ⟪ConsistentState.vector Database.empty, h⟫_ℂ := by
  classical
  rw [total_apply, sum_apply]
  have hsum :
      (∑ i : Fin (N + 1), raw N i.val ((H N i.val).starProjection h) Database.empty) =
        raw N 0 ((H N 0).starProjection h) Database.empty := by
    apply Finset.sum_eq_single 0
    · intro i _ hi
      apply raw_apply_of_ne
      intro hz
      apply hi
      exact Fin.ext (by simpa only [Database.empty_size, Fin.val_zero] using hz.symm)
    · simp
  rw [hsum, raw_apply_of_size N 0 _ _ Database.empty_size,
    ← (H N 0).inner_starProjection_left_eq_right]
  have hz : ConsistentState.vector (Database.empty : Database N) ∈ H N 0 := by
    rw [H_zero]
    exact KnowledgeSpace.vector_empty_mem N
  rw [(H N 0).starProjection_eq_self_iff.mpr hz]

theorem total_adjoint_empty (N : ℕ) :
    (total N).adjoint (EuclideanSpace.single (Database.empty : Database N) 1) =
      ConsistentState.vector Database.empty := by
  classical
  apply ext_inner_right ℂ
  intro h
  rw [LinearMap.adjoint_inner_left, EuclideanSpace.inner_single_left, total_apply_empty]
  simp

/-- Uniform initialization lies in the unit-eigenvalue sector of the actual
domain Gram operator, so positive polar normalization can preserve it. -/
theorem total_gram_uniform (N : ℕ) :
    (total N).adjoint (total N (ConsistentState.vector Database.empty)) =
      ConsistentState.vector Database.empty := by
  rw [total_uniform, total_adjoint_empty]

/-- The actual image subspace consists entirely of cancelling database vectors. -/
theorem cancels_of_mem_range {N : ℕ} (x : Fin N) (ψ : Compression.State N)
    (hψ : ψ ∈ LinearMap.range (total N)) : CompressionCancellation.Cancels x ψ := by
  obtain ⟨h, rfl⟩ := hψ
  exact total_cancels x h

end QuantumOracle.RawEmbedding
