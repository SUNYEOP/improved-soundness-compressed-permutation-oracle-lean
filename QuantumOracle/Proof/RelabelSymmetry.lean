import QuantumOracle.Proof.DatabaseRelabel
import QuantumOracle.Model.RawEmbedding

/-!
# Actual relabeling equivariance of knowledge layers and the raw embedding

The permutation register uses the existing map `π ↦ β π α⁻¹`, while the
database register relabels each edge by `(x,y) ↦ (α x, β y)`. Both are actual
basis permutations. They need not be involutions.
-/

noncomputable section

namespace QuantumOracle.RelabelSymmetry

open PermutationExtensions KernelEquivariance
open scoped BigOperators InnerProductSpace

variable {N t : ℕ}

@[simp] theorem oracle_symm_apply (α β : Perm N) (h : EuclideanSpace ℂ (Perm N)) :
    (relabelOperator α β).symm h = relabelOperator α.symm β.symm h := by
  have he : (relabelPerm α β).symm = relabelPerm α.symm β.symm := by
    ext π x
    rfl
  unfold relabelOperator Query.linearLift
  rw [LinearIsometryEquiv.piLpCongrLeft_symm, he]

/-- Actual relabeling sends a consistent state to the relabeled database state. -/
@[simp] theorem oracle_vector (α β : Perm N) (I : Database N) :
    relabelOperator α β (ConsistentState.vector I) =
      ConsistentState.vector (DatabaseRelabel.relabel α β I) := by
  ext π
  obtain ⟨σ, rfl⟩ := (relabelPerm α β).surjective π
  change Query.linearLift (relabelPerm α β) (ConsistentState.vector I)
    (relabelPerm α β σ) = _
  rw [Query.linearLift_apply]
  exact (DatabaseRelabel.vector_relabel_apply α β I σ).symm

theorem oracle_mem_K (α β : Perm N) (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ KnowledgeSpace.K N t) : relabelOperator α β h ∈ KnowledgeSpace.K N t := by
  apply Submodule.span_induction
    (p := fun h _ => relabelOperator α β h ∈ KnowledgeSpace.K N t) ?_ ?_ ?_ ?_ hh
  · rintro _ ⟨I, rfl⟩
    rw [oracle_vector]
    exact KnowledgeSpace.vector_mem _ ((DatabaseRelabel.relabel_size α β I.val).trans I.property)
  · simp
  · intro h k _ _ hh hk
    simpa using (KnowledgeSpace.K N t).add_mem hh hk
  · intro c h _ hh
    simpa using (KnowledgeSpace.K N t).smul_mem c hh

@[simp] theorem oracle_mem_K_iff (α β : Perm N) (h : EuclideanSpace ℂ (Perm N)) :
    relabelOperator α β h ∈ KnowledgeSpace.K N t ↔ h ∈ KnowledgeSpace.K N t := by
  constructor
  · intro hh
    have hi := oracle_mem_K α.symm β.symm (relabelOperator α β h) hh
    rw [← oracle_symm_apply, LinearIsometryEquiv.symm_apply_apply] at hi
    exact hi
  · exact oracle_mem_K α β h

theorem oracle_mem_K_orthogonal (α β : Perm N) (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ (KnowledgeSpace.K N t)ᗮ) :
    relabelOperator α β h ∈ (KnowledgeSpace.K N t)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro k hk
  have hin := (relabelOperator α β).inner_map_map ((relabelOperator α β).symm k) h
  rw [LinearIsometryEquiv.apply_symm_apply] at hin
  rw [hin]
  apply Submodule.inner_right_of_mem_orthogonal _ hh
  rw [oracle_symm_apply]
  exact oracle_mem_K α.symm β.symm k hk

theorem oracle_mem_H (α β : Perm N) (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ HarmonicLayers.H N t) : relabelOperator α β h ∈ HarmonicLayers.H N t := by
  cases t with
  | zero => exact oracle_mem_K α β h hh
  | succ t =>
    exact ⟨oracle_mem_K α β h hh.1, oracle_mem_K_orthogonal α β h hh.2⟩

@[simp] theorem oracle_mem_H_iff (α β : Perm N) (h : EuclideanSpace ℂ (Perm N)) :
    relabelOperator α β h ∈ HarmonicLayers.H N t ↔ h ∈ HarmonicLayers.H N t := by
  constructor
  · intro hh
    have hi := oracle_mem_H α.symm β.symm (relabelOperator α β h) hh
    rw [← oracle_symm_apply, LinearIsometryEquiv.symm_apply_apply] at hi
    exact hi
  · exact oracle_mem_H α β h

theorem map_H (α β : Perm N) (t : ℕ) :
    (HarmonicLayers.H N t).map (relabelOperator α β).toLinearEquiv.toLinearMap =
      HarmonicLayers.H N t := by
  apply le_antisymm
  · rintro _ ⟨h, hh, rfl⟩
    exact oracle_mem_H α β h hh
  · intro h hh
    refine ⟨(relabelOperator α β).symm h, ?_, LinearIsometryEquiv.apply_symm_apply _ _⟩
    rw [oracle_symm_apply]
    exact oracle_mem_H α.symm β.symm h hh

/-- Every actual harmonic-layer projection commutes with input/output relabeling. -/
theorem oracle_projection (α β : Perm N) (t : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    relabelOperator α β ((HarmonicLayers.H N t).starProjection h) =
      (HarmonicLayers.H N t).starProjection (relabelOperator α β h) := by
  have hp := (relabelOperator α β).toLinearIsometry.map_starProjection (HarmonicLayers.H N t) h
  change relabelOperator α β ((HarmonicLayers.H N t).starProjection h) =
    ((HarmonicLayers.H N t).map (relabelOperator α β).toLinearEquiv.toLinearMap).starProjection
      (relabelOperator α β h) at hp
  simpa only [map_H] using hp

/-- Each actual level adjoint intertwines both actual relabelings. -/
theorem raw_intertwines (α β : Perm N) (t : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    RawHarmonic.raw N t (relabelOperator α β h) =
      DatabaseRelabel.operator α β (RawHarmonic.raw N t h) := by
  ext I
  obtain ⟨J, rfl⟩ := (DatabaseRelabel.equiv α β).surjective I
  change RawHarmonic.raw N t (relabelOperator α β h) (DatabaseRelabel.relabel α β J) =
    DatabaseRelabel.operator α β (RawHarmonic.raw N t h) (DatabaseRelabel.relabel α β J)
  rw [DatabaseRelabel.operator_apply_relabel]
  by_cases hJ : J.size = t
  · rw [RawHarmonic.raw_apply_of_size N t _ _ ((DatabaseRelabel.relabel_size α β J).trans hJ),
      RawHarmonic.raw_apply_of_size N t _ J hJ, ← oracle_vector,
      (relabelOperator α β).inner_map_map]
  · rw [RawHarmonic.raw_apply_of_ne N t _ _ (by simpa only [DatabaseRelabel.relabel_size] using hJ),
      RawHarmonic.raw_apply_of_ne N t _ J hJ]

/-- The full actual raw assembly intertwines simultaneous input/output relabeling. -/
theorem total_intertwines (α β : Perm N) (h : EuclideanSpace ℂ (Perm N)) :
    RawEmbedding.total N (relabelOperator α β h) =
      DatabaseRelabel.operator α β (RawEmbedding.total N h) := by
  rw [RawEmbedding.total_apply, RawEmbedding.total_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← oracle_projection, raw_intertwines]

end QuantumOracle.RelabelSymmetry
