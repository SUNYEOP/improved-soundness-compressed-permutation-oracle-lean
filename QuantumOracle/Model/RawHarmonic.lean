import QuantumOracle.Model.HarmonicLayers
import QuantumOracle.Model.AdjointCoefficients
import QuantumOracle.Model.LevelEmbedding
import QuantumOracle.Model.CompressionCancellation

/-!
# Unnormalized harmonic-layer images in the actual database space

The concrete extension adjoint is embedded by zero padding into its physical
database level. Its coefficients and cancellation are proved directly. This
map is injective on the corresponding knowledge space, but is not asserted to
be an isometry or to equal the manuscript's spectrally normalized W.
-/

noncomputable section

namespace QuantumOracle.RawHarmonic

open PermutationExtensions ExtensionOperator CompressionIndex
open scoped BigOperators InnerProductSpace

variable {N t : ℕ}

/-- The actual extension adjoint, placed at its exact physical database size. -/
def raw (N t : ℕ) :
    EuclideanSpace ℂ (Perm N) →ₗ[ℂ] Compression.State N :=
  (LevelEmbedding.embed N t).toLinearMap.comp (T N t).adjoint

theorem raw_apply_of_size (N t : ℕ) (h : EuclideanSpace ℂ (Perm N))
    (I : Database N) (hI : I.size = t) :
    raw N t h I = ⟪ConsistentState.vector I, h⟫_ℂ := by
  change LevelEmbedding.embed N t ((T N t).adjoint h) I = _
  rw [LevelEmbedding.embed_apply_of_size N t _ I hI,
    AdjointCoefficients.adjoint_apply]

theorem raw_apply_of_ne (N t : ℕ) (h : EuclideanSpace ℂ (Perm N))
    (I : Database N) (hI : I.size ≠ t) : raw N t h I = 0 :=
  LevelEmbedding.embed_apply_of_ne N t _ I hI

theorem raw_norm (N t : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    ‖raw N t h‖ = ‖(T N t).adjoint h‖ := (LevelEmbedding.embed N t).norm_map _

theorem raw_eq_zero_iff_of_mem (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ KnowledgeSpace.K N t) : raw N t h = 0 ↔ h = 0 := by
  change (LevelEmbedding.embed N t).toLinearMap ((T N t).adjoint h) = 0 ↔ _
  rw [(LevelEmbedding.embed N t).map_eq_zero_iff,
    AdjointCoefficients.adjoint_eq_zero_iff_of_mem h hh]
  exact (LevelEmbedding.embed N t).injective

/-- Physical images of distinct database levels are mutually orthogonal. -/
theorem inner_raw_of_ne {s t : ℕ} (hst : s ≠ t)
    (h k : EuclideanSpace ℂ (Perm N)) : ⟪raw N s h, raw N t k⟫_ℂ = 0 :=
  LevelEmbedding.inner_embed_of_ne hst _ _

/-- Every actual orthogonal knowledge layer gives cancelling physical
database coefficients, including the degree-zero boundary. -/
theorem raw_cancels (x : Fin N) (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ HarmonicLayers.H N t) :
    CompressionCancellation.Cancels x (raw N t h) := by
  classical
  intro J
  by_cases ht : J.val.size + 1 = t
  · have horth : h ∈ (KnowledgeSpace.K N J.val.size)ᗮ := by
      apply HarmonicLayers.H_succ_le_orthogonal N J.val.size
      rwa [ht]
    calc
      (∑ y : Fresh J.val, raw N t h (J.val.set x y.val)) =
          ∑ y : Fresh J.val, ⟪ConsistentState.vector (J.val.set x y.val), h⟫_ℂ := by
        apply Finset.sum_congr rfl
        intro y _
        exact raw_apply_of_size N t h _
          ((Database.set_size_of_fresh J.val x y.val J.property y.property).trans ht)
      _ = 0 := ExtensionResolution.sum_inner_extensions_eq_zero J.val x J.property h horth
  · apply Finset.sum_eq_zero
    intro y _
    apply raw_apply_of_ne
    rwa [Database.set_size_of_fresh J.val x y.val J.property y.property]

/-- Actual compression fixes the already-defined part of each raw harmonic layer. -/
theorem pC_definedPart_raw (x : Fin N) (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ HarmonicLayers.H N t) :
    Compression.pC x (CompressionCancellation.definedPart x (raw N t h)) =
      CompressionCancellation.definedPart x (raw N t h) :=
  CompressionCancellation.pC_definedPart x _ (raw_cancels x h hh)

theorem pC_raw_apply_base (x : Fin N) (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ HarmonicLayers.H N t) (J : Base x) :
    Compression.pC x (raw N t h) J.val = 0 :=
  CompressionCancellation.pC_apply_base x _ (raw_cancels x h hh) J

/-- The exact physical fresh-extension formula, with its actual cardinal normalization. -/
theorem pC_raw_apply_extension (x : Fin N) (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ HarmonicLayers.H N t) (J : Base x) (y : Fresh J.val) :
    Compression.pC x (raw N t h) (J.val.set x y.val) =
      raw N t h (J.val.set x y.val) + raw N t h J.val *
        ((Real.sqrt ((N - J.val.size : ℕ) : ℝ))⁻¹ : ℂ) := by
  simpa only [UniformState.amplitude, card_fresh, Complex.ofReal_inv] using
    CompressionCancellation.pC_apply_extension x _ (raw_cancels x h hh) J y

/-- Cancellation removes the potentially lower database-size component. -/
theorem pC_raw_supported_two_levels (x : Fin N) (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ HarmonicLayers.H N t) (I : Database N)
    (ht : I.size ≠ t) (ht' : I.size ≠ t + 1) :
    Compression.pC x (raw N t h) I = 0 := by
  obtain ⟨⟨J, o⟩, rfl⟩ := decode_surjective x I
  cases o with
  | none => exact pC_raw_apply_base x h hh J
  | some y =>
    change (J.val.set x y.val).size ≠ t at ht
    change (J.val.set x y.val).size ≠ t + 1 at ht'
    rw [decode_some, pC_raw_apply_extension x h hh J y,
      raw_apply_of_ne N t h _ ht]
    have hbase : J.val.size ≠ t := by
      intro heq
      apply ht'
      simp only [Database.set_size_of_fresh J.val x y.val J.property y.property,
        heq]
    rw [raw_apply_of_ne N t h _ hbase, zero_mul, zero_add]

/-- The unnormalized degree-zero map already has the exact initialization identity. -/
theorem raw_zero_uniform (N : ℕ) :
    raw N 0 (ConsistentState.vector Database.empty) =
      EuclideanSpace.single (Database.empty : Database N) 1 := by
  classical
  ext I
  by_cases hI : I.size = 0
  · have heq := KnowledgeSpace.database_eq_empty_of_size_zero I hI
    subst I
    rw [raw_apply_of_size N 0 _ _ Database.empty_size, inner_self_eq_norm_sq_to_K,
      ConsistentState.vector_norm]
    simp
  · have heq : I ≠ Database.empty := by
      intro heq
      subst I
      exact hI Database.empty_size
    rw [raw_apply_of_ne N 0 _ I hI]
    simp [heq]

end QuantumOracle.RawHarmonic
