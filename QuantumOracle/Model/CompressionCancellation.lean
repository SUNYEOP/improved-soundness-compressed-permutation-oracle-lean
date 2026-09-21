import QuantumOracle.Model.CompressionAction

/-!
# The actual compression action on cancelling database amplitudes

If every fresh-extension sum vanishes, compression fixes the part that already
defines the queried input. The undefined part is sent to the normalized uniform
extension in each actual database block. This is an operator theorem about pC;
it assumes only the displayed coefficient cancellation, not a harmonic isometry.
-/

noncomputable section

namespace QuantumOracle.CompressionCancellation

open Compression CompressionIndex UniformState
open scoped BigOperators InnerProductSpace

variable {N : ℕ}

/-- Keep exactly the databases in which the queried input is already defined. -/
def definedPart (x : Fin N) : State N →ₗ[ℂ] State N where
  toFun ψ := WithLp.toLp 2 (fun I => if x ∈ I.domain then ψ I else 0)
  map_add' ψ φ := by
    classical
    ext I
    by_cases hx : x ∈ I.domain <;> simp [hx]
  map_smul' a ψ := by
    classical
    ext I
    by_cases hx : x ∈ I.domain <;> simp [hx]

/-- The complementary part, where the queried input is undefined. -/
def undefinedPart (x : Fin N) : State N →ₗ[ℂ] State N :=
  LinearMap.id - definedPart x

@[simp] theorem definedPart_apply (x : Fin N) (ψ : State N) (I : Database N) :
    definedPart x ψ I = if x ∈ I.domain then ψ I else 0 := rfl

@[simp] theorem undefinedPart_apply (x : Fin N) (ψ : State N) (I : Database N) :
    undefinedPart x ψ I = if x ∈ I.domain then 0 else ψ I := by
  classical
  simp only [undefinedPart, LinearMap.sub_apply, LinearMap.id_apply,
    PiLp.sub_apply, definedPart_apply]
  split_ifs <;> simp

theorem definedPart_add_undefinedPart (x : Fin N) (ψ : State N) :
    definedPart x ψ + undefinedPart x ψ = ψ := by
  simp [undefinedPart]

private theorem set_mem_domain (I : Database N) (x y : Fin N) :
    x ∈ (I.set x y).domain :=
  (Database.mem_domain _ _).mpr ⟨y, Database.set_contains I x y⟩

@[simp] theorem coordinates_definedPart_none (x : Fin N) (ψ : State N) (J : Base x) :
    coordinates x (definedPart x ψ) J none = 0 := by
  simp [J.property]

@[simp] theorem coordinates_definedPart_some (x : Fin N) (ψ : State N)
    (J : Base x) (y : Fresh J.val) :
    coordinates x (definedPart x ψ) J (some y) = ψ (J.val.set x y.val) := by
  simp [set_mem_domain]

/-- Cancellation of the actual fresh-extension database coordinates. -/
def Cancels (x : Fin N) (ψ : State N) : Prop :=
  ∀ J : Base x, ∑ y : Fresh J.val, ψ (J.val.set x y.val) = 0

theorem inner_extensionUniform_coordinates (x : Fin N) (ψ : State N) (J : Base x) :
    ⟪extensionUniform (Fresh J.val), coordinates x ψ J⟫_ℂ =
      (amplitude (Fresh J.val) : ℂ) * ∑ y : Fresh J.val, ψ (J.val.set x y.val) := by
  simp [PiLp.inner_apply, Fintype.sum_option, RCLike.inner_apply,
    ← Finset.sum_mul, mul_comm]

theorem inner_extensionUniform_coordinates_definedPart (x : Fin N) (ψ : State N)
    (J : Base x) :
    ⟪extensionUniform (Fresh J.val), coordinates x (definedPart x ψ) J⟫_ℂ =
      (amplitude (Fresh J.val) : ℂ) * ∑ y : Fresh J.val, ψ (J.val.set x y.val) := by
  simp [PiLp.inner_apply, Fintype.sum_option, RCLike.inner_apply,
    set_mem_domain, ← Finset.sum_mul, mul_comm]

/-- The already-defined part is fixed by actual pC whenever the extension sums cancel. -/
theorem pC_definedPart (x : Fin N) (ψ : State N) (h : Cancels x ψ) :
    pC x (definedPart x ψ) = definedPart x ψ := by
  apply state_ext_coordinates x
  intro J
  rw [coordinates_pC]
  apply CompressionBlock.compression_fixed
  · simp [emptyKet, EuclideanSpace.inner_single_left, J.property]
  · rw [inner_extensionUniform_coordinates_definedPart, h J, mul_zero]

theorem coordinates_undefinedPart (x : Fin N) (ψ : State N) (J : Base x) :
    coordinates x (undefinedPart x ψ) J = ψ J.val • emptyKet (Fresh J.val) := by
  ext o
  cases o with
  | none => simp [J.property]
  | some y => simp [set_mem_domain]

/-- Every undefined block is uniformly extended with its original base amplitude. -/
theorem coordinates_pC_undefinedPart (x : Fin N) (ψ : State N) (J : Base x) :
    coordinates x (pC x (undefinedPart x ψ)) J =
      ψ J.val • extensionUniform (Fresh J.val) := by
  letI := fresh_nonempty J
  rw [coordinates_pC, coordinates_undefinedPart, map_smul,
    CompressionBlock.compression_empty]

/-- Full compression action once the cancelling defined component is separated. -/
theorem pC_eq_defined_add (x : Fin N) (ψ : State N) (h : Cancels x ψ) :
    pC x ψ = definedPart x ψ + pC x (undefinedPart x ψ) := by
  conv_lhs => rw [← definedPart_add_undefinedPart x ψ]
  rw [map_add, pC_definedPart x ψ h]

/-- Cancellation removes every undefined-base output amplitude. -/
theorem pC_apply_base (x : Fin N) (ψ : State N) (h : Cancels x ψ) (J : Base x) :
    pC x ψ J.val = 0 := by
  letI := fresh_nonempty J
  change coordinates x (pC x ψ) J none = 0
  rw [coordinates_pC, CompressionBlock.compression_apply_none,
    inner_extensionUniform_coordinates, h J, mul_zero]

/-- Each defined database retains its amplitude and receives only the uniform
extension of its base amplitude. -/
theorem pC_apply_extension (x : Fin N) (ψ : State N) (h : Cancels x ψ)
    (J : Base x) (y : Fresh J.val) :
    pC x ψ (J.val.set x y.val) = ψ (J.val.set x y.val) +
      ψ J.val * (amplitude (Fresh J.val) : ℂ) := by
  letI := fresh_nonempty J
  change coordinates x (pC x ψ) J (some y) = _
  rw [coordinates_pC, CompressionBlock.compression_apply_some,
    inner_extensionUniform_coordinates, h J, mul_zero, sub_zero]
  rfl

end QuantumOracle.CompressionCancellation
