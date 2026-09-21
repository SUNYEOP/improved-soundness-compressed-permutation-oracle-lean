import QuantumOracle.Model.ExtensionCount
import QuantumOracle.Model.UniformState
import QuantumOracle.Model.CompressionIndex
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Actual consistent-permutation vectors

This is the vector `v_I` in manuscript Section 3.1: its coefficient at an
actual permutation is the reciprocal square root of `(N - |I|)!` when the
permutation extends `I`, and zero otherwise. No normalization assertion about
the harmonic embedding `W_N` is used here.
-/

noncomputable section

namespace QuantumOracle.ConsistentState

open PermutationExtensions
open scoped BigOperators InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {N : ℕ}

private theorem sum_apply {ι α : Type*} [Fintype ι] [Fintype α]
    (v : ι → EuclideanSpace ℂ α) (a : α) : (∑ i, v i) a = ∑ i, v i a :=
  map_sum (PiLp.projₗ 2 (𝕜 := ℂ) (fun _ : α => ℂ) a) v Finset.univ

/-- The manuscript's exact factorial amplitude. -/
def amplitude (I : Database N) : ℝ :=
  (Real.sqrt ((N - I.size).factorial : ℝ))⁻¹

theorem amplitude_pos (I : Database N) : 0 < amplitude I := by
  apply inv_pos.mpr
  apply Real.sqrt_pos.mpr
  exact_mod_cast Nat.factorial_pos (N - I.size)

theorem amplitude_nonneg (I : Database N) : 0 ≤ amplitude I :=
  (amplitude_pos I).le

theorem factorial_mul_amplitude_sq (I : Database N) :
    ((N - I.size).factorial : ℝ) * amplitude I ^ 2 = 1 := by
  have hpos : (0 : ℝ) < (N - I.size).factorial := by
    exact_mod_cast Nat.factorial_pos (N - I.size)
  rw [amplitude, inv_pow, Real.sq_sqrt hpos.le]
  exact mul_inv_cancel₀ hpos.ne'

/-- Uniform superposition over the genuine permutations extending `I`. -/
def vector (I : Database N) : EuclideanSpace ℂ (Perm N) := by
  classical
  exact WithLp.toLp 2 (fun π => if Extends I π then (amplitude I : ℂ) else 0)

theorem vector_apply (I : Database N) (π : Perm N) :
    vector I π = if Extends I π then (amplitude I : ℂ) else 0 := by
  classical
  rfl

@[simp] theorem vector_apply_of_extends (I : Database N) (π : Perm N)
    (h : Extends I π) : vector I π = (amplitude I : ℂ) := by
  simp [vector_apply, h]

@[simp] theorem vector_apply_of_not_extends (I : Database N) (π : Perm N)
    (h : ¬ Extends I π) : vector I π = 0 := by
  simp [vector_apply, h]

@[simp] theorem star_vector_apply (I : Database N) (π : Perm N) :
    star (vector I π) = vector I π := by
  classical
  by_cases h : Extends I π <;> simp [h]

theorem vector_norm_sq_eq_card (I : Database N) :
    ‖vector I‖ ^ 2 = (Fintype.card (Extensions I) : ℝ) * amplitude I ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq, Fintype.card_subtype]
  simp only [vector_apply, apply_ite norm, norm_zero, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (amplitude_nonneg I), ite_pow]
  simp [Finset.sum_ite]

/-- Unit normalization follows from the proved count of actual extensions. -/
@[simp] theorem vector_norm (I : Database N) : ‖vector I‖ = 1 := by
  have hsq : ‖vector I‖ ^ 2 = 1 := by
    rw [vector_norm_sq_eq_card, card_extensions, factorial_mul_amplitude_sq]
  nlinarith [norm_nonneg (vector I)]

@[simp] theorem vector_empty_apply (π : Perm N) :
    vector (Database.empty : Database N) π =
      (amplitude (Database.empty : Database N) : ℂ) := by
  simp

theorem vector_empty_eq_uniform :
    vector (Database.empty : Database N) = UniformState.uniform (Perm N) := by
  ext π
  simp [UniformState.uniform_apply, amplitude, UniformState.amplitude,
    Fintype.card_perm]

/-- Inverting the database and permutation preserves every coefficient. -/
theorem vector_inverse_apply (I : Database N) (π : Perm N) :
    vector I.inverse π.symm = vector I π := by
  classical
  simp only [vector_apply, extends_inverse_iff]
  congr 1
  simp [amplitude]

/-- The exact Gram entry counts genuine permutations satisfying both constraints. -/
theorem inner_vector_eq_card_common (I J : Database N) :
    ⟪vector I, vector J⟫_ℂ =
      (Fintype.card {π : Perm N // Extends I π ∧ Extends J π} : ℂ) *
        (amplitude I : ℂ) * (amplitude J : ℂ) := by
  classical
  change (∑ π, vector J π * star (vector I π)) = _
  simp only [star_vector_apply]
  calc
    (∑ π, vector J π * vector I π) =
        ∑ π, if Extends I π ∧ Extends J π then
          (amplitude I : ℂ) * (amplitude J : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro π _
      by_cases hi : Extends I π <;> by_cases hj : Extends J π <;>
        simp [hi, hj, mul_comm]
    _ = _ := by
      rw [Fintype.card_subtype]
      simp [Finset.sum_ite, mul_assoc]

theorem inner_vector_eq_zero_of_no_common (I J : Database N)
    (h : ∀ π : Perm N, ¬ (Extends I π ∧ Extends J π)) :
    ⟪vector I, vector J⟫_ℂ = 0 := by
  rw [inner_vector_eq_card_common]
  haveI : IsEmpty {π : Perm N // Extends I π ∧ Extends J π} :=
    ⟨fun π => h π.val π.property⟩
  simp

/-- Adding one fresh edge changes the exact factorial normalization by this factor. -/
theorem amplitude_set_of_fresh (I : Database N) (x y : Fin N)
    (hx : x ∉ I.domain) (hy : y ∉ I.image) :
    amplitude I = (Real.sqrt (N - I.size : ℕ))⁻¹ * amplitude (I.set x y) := by
  have hlt : I.size < N := CompressionIndex.base_size_lt ⟨I, hx⟩
  have hsub : N - I.size = (N - (I.size + 1)) + 1 := by omega
  have hfact : (N - I.size).factorial =
      (N - I.size) * (N - (I.size + 1)).factorial := by
    conv_lhs => rw [hsub, Nat.factorial_succ, ← hsub]
  simp only [amplitude, Database.set_size_of_fresh I x y hx hy]
  rw [hfact, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
  exact mul_inv _ _

/-- The actual answer-sector indicator on the permutation register. -/
def answerProjection (x y : Fin N) :
    EuclideanSpace ℂ (Perm N) →ₗ[ℂ] EuclideanSpace ℂ (Perm N) where
  toFun v := WithLp.toLp 2 (fun π => if π x = y then v π else 0)
  map_add' u v := by
    ext π
    change (if π x = y then u π + v π else 0) =
      (if π x = y then u π else 0) + (if π x = y then v π else 0)
    split_ifs <;> simp
  map_smul' c v := by
    ext π
    change (if π x = y then c * v π else 0) =
      c * (if π x = y then v π else 0)
    split_ifs <;> simp

@[simp] theorem answerProjection_apply (x y : Fin N)
    (v : EuclideanSpace ℂ (Perm N)) (π : Perm N) :
    answerProjection x y v π = if π x = y then v π else 0 := rfl

@[simp] theorem answerProjection_idempotent (x y : Fin N)
    (v : EuclideanSpace ℂ (Perm N)) :
    answerProjection x y (answerProjection x y v) = answerProjection x y v := by
  ext π
  by_cases h : π x = y <;> simp [h]

theorem sum_answerProjection (x : Fin N) (v : EuclideanSpace ℂ (Perm N)) :
    ∑ y, answerProjection x y v = v := by
  ext π
  simp [sum_apply]

/-- Exact indicator action on a consistent state when both endpoints are fresh. -/
theorem answerProjection_vector_of_fresh (I : Database N) (x y : Fin N)
    (hx : x ∉ I.domain) (hy : y ∉ I.image) :
    answerProjection x y (vector I) =
      ((Real.sqrt (N - I.size : ℕ))⁻¹ : ℂ) • vector (I.set x y) := by
  ext π
  simp only [answerProjection_apply, vector_apply, PiLp.smul_apply, smul_eq_mul,
    extends_set_iff_of_fresh I x y hx hy]
  by_cases hext : Extends I π <;> by_cases hxy : π x = y <;> simp [hext, hxy]
  exact_mod_cast amplitude_set_of_fresh I x y hx hy

theorem answerProjection_vector_fresh_norm (I : Database N) (x y : Fin N)
    (hx : x ∉ I.domain) (hy : y ∉ I.image) :
    ‖answerProjection x y (vector I)‖ = (Real.sqrt (N - I.size : ℕ))⁻¹ := by
  rw [answerProjection_vector_of_fresh I x y hx hy, norm_smul, vector_norm, mul_one]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The squared norm of one fresh answer sector is exactly `1 / (N - |I|)`. -/
theorem answerProjection_vector_fresh_norm_sq (I : Database N) (x y : Fin N)
    (hx : x ∉ I.domain) (hy : y ∉ I.image) :
    ‖answerProjection x y (vector I)‖ ^ 2 = ((N - I.size : ℕ) : ℝ)⁻¹ := by
  rw [answerProjection_vector_fresh_norm I x y hx hy, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]

/-- An already recorded answer is fixed by the corresponding exact indicator. -/
theorem answerProjection_vector_of_mem (I : Database N) (x y : Fin N)
    (hxy : (x, y) ∈ I.edges) : answerProjection x y (vector I) = vector I := by
  ext π
  by_cases hext : Extends I π
  · simp [hext, hext x y hxy]
  · simp [hext]

/-- A fresh input cannot map to an output already occupied in the database. -/
theorem answerProjection_vector_of_occupied (I : Database N) (x y : Fin N)
    (hx : x ∉ I.domain) (hy : y ∈ I.image) :
    answerProjection x y (vector I) = 0 := by
  obtain ⟨a, ha⟩ := (Database.mem_image I y).mp hy
  ext π
  by_cases hext : Extends I π
  · have hneq : π x ≠ y := by
      intro hxy
      have hxa : x = a := π.injective (hxy.trans (hext a y ha).symm)
      exact hx (hxa ▸ (Database.mem_domain I a).mpr ⟨y, ha⟩)
    simp [hneq]
  · simp [hext]

end QuantumOracle.ConsistentState
