import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators

/-!
# Normalized uniform vectors

This file constructs actual finite complex vectors used in a local compression
block. `Option α` indexes an empty database together with its possible one-edge
extensions. The unit-norm assertions require a nonempty extension set; the
definitions themselves are also available when it is empty.
-/

noncomputable section

namespace QuantumOracle.UniformState

open scoped InnerProductSpace

/-- The common real amplitude of a uniform state on a finite set. -/
def amplitude (α : Type*) [Fintype α] : ℝ :=
  (Real.sqrt (Fintype.card α : ℝ))⁻¹

theorem amplitude_nonneg (α : Type*) [Fintype α] : 0 ≤ amplitude α :=
  inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem card_mul_amplitude_sq (α : Type*) [Fintype α] [Nonempty α] :
    (Fintype.card α : ℝ) * amplitude α ^ 2 = 1 := by
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [amplitude, inv_pow, Real.sq_sqrt (le_of_lt hcard)]
  exact mul_inv_cancel₀ (ne_of_gt hcard)

/-- The normalized uniform vector, with one coordinate per element. -/
def uniform (α : Type*) [Fintype α] : EuclideanSpace ℂ α :=
  WithLp.toLp 2 (fun _ => (amplitude α : ℂ))

@[simp] theorem uniform_apply (α : Type*) [Fintype α] (a : α) :
    uniform α a = (amplitude α : ℂ) := rfl

@[simp] theorem uniform_norm (α : Type*) [Fintype α] [Nonempty α] :
    ‖uniform α‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [uniform_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (amplitude_nonneg α), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, card_mul_amplitude_sq, Real.sqrt_one]

/-- The empty database basis vector in a local extension block. -/
def emptyKet (α : Type*) [Fintype α] : EuclideanSpace ℂ (Option α) := by
  classical
  exact EuclideanSpace.single none 1

@[simp] theorem emptyKet_none (α : Type*) [Fintype α] : emptyKet α none = 1 := by
  classical
  simp [emptyKet]

@[simp] theorem emptyKet_some (α : Type*) [Fintype α] (a : α) :
    emptyKet α (some a) = 0 := by
  classical
  simp [emptyKet]

@[simp] theorem emptyKet_norm (α : Type*) [Fintype α] : ‖emptyKet α‖ = 1 := by
  classical
  simp [emptyKet]

/-- Uniform vector on the extensions, with zero empty-database amplitude. -/
def extensionUniform (α : Type*) [Fintype α] : EuclideanSpace ℂ (Option α) :=
  WithLp.toLp 2 (fun a => a.elim 0 (fun _ => (amplitude α : ℂ)))

@[simp] theorem extensionUniform_none (α : Type*) [Fintype α] :
    extensionUniform α none = 0 := rfl

@[simp] theorem extensionUniform_some (α : Type*) [Fintype α] (a : α) :
    extensionUniform α (some a) = (amplitude α : ℂ) := rfl

@[simp] theorem extensionUniform_norm (α : Type*) [Fintype α] [Nonempty α] :
    ‖extensionUniform α‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fintype.sum_option]
  simp only [extensionUniform_none, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_add, extensionUniform_some,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (amplitude_nonneg α),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_mul_amplitude_sq,
    Real.sqrt_one]

@[simp] theorem emptyKet_inner_extensionUniform (α : Type*) [Fintype α] :
    ⟪emptyKet α, extensionUniform α⟫_ℂ = 0 := by
  classical
  simp [emptyKet, EuclideanSpace.inner_single_left]

@[simp] theorem extensionUniform_inner_emptyKet (α : Type*) [Fintype α] :
    ⟪extensionUniform α, emptyKet α⟫_ℂ = 0 := by
  classical
  simp [emptyKet, EuclideanSpace.inner_single_right]

end QuantumOracle.UniformState
