import QuantumOracle.Model.UniformState
import QuantumOracle.Model.OrthonormalSwap

/-!
# The finite local partial-database compression block

For a nonempty finite extension index set, this concrete unitary exchanges the
empty database basis state and the normalized uniform extension state, fixing
their common orthogonal complement. The construction is a proved reflection,
not an assumed unitary. Identifying these blocks with actual database fibres
and assembling the whole database operator is a separate step.
-/

noncomputable section

namespace QuantumOracle.CompressionBlock

open UniformState
open scoped InnerProductSpace

/-- The local compression map, as an actual complex linear isometry equivalence. -/
def compression (α : Type*) [Fintype α] :
    EuclideanSpace ℂ (Option α) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Option α) :=
  orthonormalSwap (emptyKet α) (extensionUniform α)

@[simp] theorem compression_involutive (α : Type*) [Fintype α]
    (v : EuclideanSpace ℂ (Option α)) :
    compression α (compression α v) = v :=
  orthonormalSwap_involutive _ _ _

@[simp] theorem compression_empty (α : Type*) [Fintype α] [Nonempty α] :
    compression α (emptyKet α) = extensionUniform α := by
  apply orthonormalSwap_left
  · simp
  · simp

@[simp] theorem compression_uniform (α : Type*) [Fintype α] [Nonempty α] :
    compression α (extensionUniform α) = emptyKet α := by
  apply orthonormalSwap_right
  · simp
  · simp

theorem compression_fixed (α : Type*) [Fintype α]
    (v : EuclideanSpace ℂ (Option α))
    (he : ⟪emptyKet α, v⟫_ℂ = 0) (hu : ⟪extensionUniform α, v⟫_ℂ = 0) :
    compression α v = v :=
  orthonormalSwap_fixed _ _ _ he hu

theorem compression_apply (α : Type*) [Fintype α] [Nonempty α]
    (v : EuclideanSpace ℂ (Option α)) :
    compression α v =
      v + (⟪emptyKet α, v⟫_ℂ - ⟪extensionUniform α, v⟫_ℂ) •
        (extensionUniform α - emptyKet α) :=
  orthonormalSwap_apply _ _ _ (emptyKet_norm α) (extensionUniform_norm α)
    (emptyKet_inner_extensionUniform α)

@[simp] theorem compression_norm (α : Type*) [Fintype α]
    (v : EuclideanSpace ℂ (Option α)) : ‖compression α v‖ = ‖v‖ :=
  (compression α).norm_map v

theorem compression_isometry (α : Type*) [Fintype α] : Isometry (compression α) :=
  (compression α).isometry

/-- The amplitude at the empty state is the previous uniform extension overlap. -/
theorem compression_apply_none (α : Type*) [Fintype α] [Nonempty α]
    (v : EuclideanSpace ℂ (Option α)) :
    compression α v none = ⟪extensionUniform α, v⟫_ℂ := by
  classical
  rw [compression_apply]
  simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, emptyKet,
    EuclideanSpace.inner_single_left]

/-- Each extension receives the same rank-one correction. -/
theorem compression_apply_some (α : Type*) [Fintype α] [Nonempty α]
    (v : EuclideanSpace ℂ (Option α)) (a : α) :
    compression α v (some a) = v (some a) +
      (v none - ⟪extensionUniform α, v⟫_ℂ) * (amplitude α : ℂ) := by
  classical
  rw [compression_apply]
  simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, emptyKet,
    EuclideanSpace.inner_single_left]

end QuantumOracle.CompressionBlock
