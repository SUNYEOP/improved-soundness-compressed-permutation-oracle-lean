import QuantumOracle.Proof.DatabaseDegree
import QuantumOracle.Proof.RawDegree
import QuantumOracle.Model.PolarEmbedding
import QuantumOracle.Proof.PolarIntertwining

/-!
# Exact database degree of the constructed polar comparison map

The actual raw map intertwines the orthogonal input-degree projection and
physical database-size projection. Positive polar normalization preserves that
intertwining, so the normalized map preserves each degree exactly.
-/

noncomputable section

namespace QuantumOracle.PolarDegree

open PermutationExtensions HarmonicLayers RawEmbedding RawHarmonic
open scoped BigOperators InnerProductSpace

attribute [local irreducible] HarmonicLayers.H KnowledgeSpace.K
attribute [local instance] Classical.propDecidable

theorem project_total {N t : ℕ} (ht : t ≤ N) (h : EuclideanSpace ℂ (Perm N)) :
    DatabaseDegree.project N t (total N h) = raw N t ((H N t).starProjection h) := by
  rw [total_apply, map_sum]
  let i : Fin (N + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
  calc
    (∑ j : Fin (N + 1), DatabaseDegree.project N t
        (raw N j.val ((H N j.val).starProjection h))) =
        DatabaseDegree.project N t (raw N i.val ((H N i.val).starProjection h)) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact DatabaseDegree.project_raw_of_ne N t j.val
          (fun hval => hji (Fin.ext hval.symm)) _
      · simp
    _ = raw N t ((H N t).starProjection h) := DatabaseDegree.project_raw_self N t _

/-- This equality is between the actual two physical projections and raw map. -/
theorem total_intertwines_projection {N t : ℕ} (ht : t ≤ N) :
    (total N).comp (H N t).starProjection.toLinearMap =
      (DatabaseDegree.project N t).comp (total N) := by
  apply LinearMap.ext
  intro h
  change total N ((H N t).starProjection h) = DatabaseDegree.project N t (total N h)
  rw [project_total ht]
  exact RawDegree.total_of_mem_H ((H N t).starProjection_apply_mem h)

def domainProjection (N t : ℕ) : Matrix (Perm N) (Perm N) ℂ :=
  Matrix.toEuclideanLin.symm (H N t).starProjection.toLinearMap

def databaseProjection (N t : ℕ) : Matrix (Database N) (Database N) ℂ :=
  Matrix.toEuclideanLin.symm (DatabaseDegree.project N t)

@[simp] theorem domainProjection_operator (N t : ℕ) :
    (domainProjection N t).toEuclideanLin = (H N t).starProjection.toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

@[simp] theorem databaseProjection_operator (N t : ℕ) :
    (databaseProjection N t).toEuclideanLin = DatabaseDegree.project N t :=
  Matrix.toEuclideanLin.apply_symm_apply _

theorem domainProjection_isHermitian (N t : ℕ) : (domainProjection N t).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymmetric.mpr
  rw [domainProjection_operator]
  exact (H N t).starProjection_isSymmetric

theorem databaseProjection_isHermitian (N t : ℕ) :
    (databaseProjection N t).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymmetric.mpr
  rw [databaseProjection_operator]
  exact DatabaseDegree.project_isSymmetric N t

theorem matrix_intertwines_projection {N t : ℕ} (ht : t ≤ N) :
    PolarEmbedding.matrix N * domainProjection N t =
      databaseProjection N t * PolarEmbedding.matrix N := by
  apply Matrix.toEuclideanLin.injective
  simp only [FiniteIncidence.toEuclideanLin_mul, PolarEmbedding.matrix_operator,
    domainProjection_operator, databaseProjection_operator]
  exact total_intertwines_projection ht

/-- The actual positive polar map intertwines the input and output degree projections. -/
theorem candidate_intertwines_projection {N t : ℕ} (ht : t ≤ N) :
    (PolarEmbedding.candidate N).toLinearMap.comp (H N t).starProjection.toLinearMap =
      (DatabaseDegree.project N t).comp (PolarEmbedding.candidate N).toLinearMap := by
  have h := PolarIntertwining.normalize_intertwines (PolarEmbedding.matrix N)
    (PolarEmbedding.matrix_mulVec_injective N) (domainProjection N t) (databaseProjection N t)
    (domainProjection_isHermitian N t) (databaseProjection_isHermitian N t)
    (matrix_intertwines_projection ht)
  have hlin := congrArg Matrix.toEuclideanLin h
  simpa only [FiniteIncidence.toEuclideanLin_mul, domainProjection_operator,
    databaseProjection_operator, ← PolarEmbedding.candidate_toLinearMap] using hlin

/-- Every normalized degree-t input has amplitudes only at databases of size t. -/
theorem candidate_mem_exactLevel {N t : ℕ} {h : EuclideanSpace ℂ (Perm N)}
    (hh : h ∈ H N t) : PolarEmbedding.candidate N h ∈ DatabaseDegree.exactLevel N t := by
  by_cases ht : t ≤ N
  · apply (DatabaseDegree.project_eq_self_iff N t _).mp
    have h := LinearMap.congr_fun (candidate_intertwines_projection ht) h
    change PolarEmbedding.candidate N ((H N t).starProjection _) =
      DatabaseDegree.project N t (PolarEmbedding.candidate N _) at h
    rw [(H N t).starProjection_eq_self_iff.mpr hh] at h
    exact h.symm
  · have hz : h = 0 := by
      simpa only [H_eq_bot_of_gt (Nat.lt_of_not_ge ht), Submodule.mem_bot] using hh
    rw [hz, map_zero]
    exact (DatabaseDegree.exactLevel N t).zero_mem

theorem candidate_apply_eq_zero_of_size_ne {N t : ℕ}
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ H N t) (I : Database N) (hI : I.size ≠ t) :
    PolarEmbedding.candidate N h I = 0 := candidate_mem_exactLevel hh I hI

private theorem sum_apply {ι α : Type*} [Fintype ι] [Fintype α]
    (v : ι → EuclideanSpace ℂ α) (a : α) : (∑ i, v i) a = ∑ i, v i a :=
  map_sum (PiLp.projₗ 2 (𝕜 := ℂ) (fun _ : α => ℂ) a) v Finset.univ

/-- A cumulative knowledge bound becomes the same actual database-size bound. -/
theorem candidate_apply_eq_zero_of_mem_K {N t : ℕ} {h : EuclideanSpace ℂ (Perm N)}
    (hh : h ∈ KnowledgeSpace.K N t) (I : Database N) (hI : t < I.size) :
    PolarEmbedding.candidate N h I = 0 := by
  have ht : t ≤ N := (Nat.le_of_lt hI).trans I.size_le
  rw [← sum_projection_of_mem ht h hh, map_sum, sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply candidate_apply_eq_zero_of_size_ne ((H N i.val).starProjection_apply_mem h)
  have hi := i.isLt
  omega

/-- On a normalized pure degree, compression has no lower-size component. -/
theorem pC_candidate_supported_two_levels {N t : ℕ} (x : Fin N)
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ H N t) (I : Database N)
    (ht : I.size ≠ t) (ht' : I.size ≠ t + 1) :
    Compression.pC x (PolarEmbedding.candidate N h) I = 0 := by
  obtain ⟨⟨J, o⟩, rfl⟩ := CompressionIndex.decode_surjective x I
  cases o with
  | none => exact PolarEmbedding.pC_candidate_apply_base x h J
  | some y =>
    change (J.val.set x y.val).size ≠ t at ht
    change (J.val.set x y.val).size ≠ t + 1 at ht'
    rw [CompressionIndex.decode_some,
      CompressionCancellation.pC_apply_extension x _ (PolarEmbedding.candidate_cancels x h) J y,
      candidate_apply_eq_zero_of_size_ne hh _ ht]
    have hbase : J.val.size ≠ t := by
      intro heq
      apply ht'
      simp only [Database.set_size_of_fresh J.val x y.val J.property y.property, heq]
    rw [candidate_apply_eq_zero_of_size_ne hh _ hbase, zero_mul, zero_add]

end QuantumOracle.PolarDegree
