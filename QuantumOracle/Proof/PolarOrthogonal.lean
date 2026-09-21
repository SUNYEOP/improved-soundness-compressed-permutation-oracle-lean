import QuantumOracle.Proof.PolarDegree

/-!
# Lower support bounds from actual knowledge orthogonality

An output coefficient of the constructed polar map depends only on the input
projection of the same degree. Orthogonality to a valid knowledge level thus
forces all coefficients at or below that level to vanish.
-/

noncomputable section

namespace QuantumOracle.PolarOrthogonal

open PermutationExtensions HarmonicLayers

attribute [local irreducible] HarmonicLayers.H KnowledgeSpace.K

theorem candidate_apply_projection (N : ℕ) (h : EuclideanSpace ℂ (Perm N))
    (I : Database N) :
    PolarEmbedding.candidate N ((H N I.size).starProjection h) I =
      PolarEmbedding.candidate N h I := by
  have heq := LinearMap.congr_fun (PolarDegree.candidate_intertwines_projection I.size_le) h
  have hc := congrArg (fun v : EuclideanSpace ℂ (Database N) => v I) heq
  change PolarEmbedding.candidate N ((H N I.size).starProjection h) I =
    DatabaseDegree.project N I.size (PolarEmbedding.candidate N h) I at hc
  simpa only [DatabaseDegree.project_apply, if_pos rfl, ite_true] using hc

/-- A coefficient at size s vanishes on the actual orthogonal complement of K_s. -/
theorem candidate_apply_eq_zero_of_orthogonal_size {N : ℕ}
    (h : EuclideanSpace ℂ (Perm N)) (I : Database N)
    (hh : h ∈ (KnowledgeSpace.K N I.size)ᗮ) : PolarEmbedding.candidate N h I = 0 := by
  have hp : (H N I.size).starProjection h = 0 :=
    (H N I.size).starProjection_apply_eq_zero_iff.mpr
      (Submodule.orthogonal_le (H_le_K N I.size) hh)
  rw [← candidate_apply_projection N h I, hp, map_zero]
  rfl

/-- Cumulative orthogonality supplies the corresponding lower database-size bound. -/
theorem candidate_apply_eq_zero_of_orthogonal_K {N s : ℕ} (hs : s ≤ N)
    (h : EuclideanSpace ℂ (Perm N)) (hh : h ∈ (KnowledgeSpace.K N s)ᗮ)
    (I : Database N) (hI : I.size ≤ s) : PolarEmbedding.candidate N h I = 0 := by
  apply candidate_apply_eq_zero_of_orthogonal_size
  exact Submodule.orthogonal_le (KnowledgeSpace.mono hI hs) hh

/-- Exact physical support detects the same input degree on the actual polar image. -/
theorem candidate_mem_exactLevel_iff {N t : ℕ} (h : EuclideanSpace ℂ (Perm N)) :
    PolarEmbedding.candidate N h ∈ DatabaseDegree.exactLevel N t ↔ h ∈ H N t := by
  constructor
  · intro hh
    by_cases ht : t ≤ N
    · apply (H N t).starProjection_eq_self_iff.mp
      apply (PolarEmbedding.candidate N).injective
      have heq := LinearMap.congr_fun (PolarDegree.candidate_intertwines_projection ht) h
      change PolarEmbedding.candidate N ((H N t).starProjection h) =
        DatabaseDegree.project N t (PolarEmbedding.candidate N h) at heq
      rw [(DatabaseDegree.project_eq_self_iff N t _).mpr hh] at heq
      exact heq
    · have hw : PolarEmbedding.candidate N h = 0 := by
        ext I
        exact hh I (by have hI := I.size_le; omega)
      have hz : h = 0 := (PolarEmbedding.candidate N).injective (by simpa using hw)
      rw [hz]
      exact (H N t).zero_mem
  · exact PolarDegree.candidate_mem_exactLevel

end QuantumOracle.PolarOrthogonal
