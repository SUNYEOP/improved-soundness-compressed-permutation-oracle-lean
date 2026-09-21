import QuantumOracle.Proof.ConditioningInverseComparison
import QuantumOracle.Model.CompressedCoherentQuery
import QuantumOracle.Model.ExactQueryGrowth

/-!
# Actual query-error assembly across coherent controls

The enable, direction, point and marker registers are sliced in the actual
query coordinate space. Squared norms add across these orthogonal slices.
Consequently a uniform bound for the actual enabled query blocks gives the
same bound for their coherent combination; disabled slices have zero error.
Numerical block bounds remain explicit hypotheses in these assembly results.
-/

noncomputable section

namespace QuantumOracle.CoherentComparison

open BasisLookup PermutationExtensions ExactCoherentQuery HiddenIsometry
open scoped BigOperators

attribute [local irreducible] PolarEmbedding.candidate

variable {N w : ℕ}

def controlSlice {O : Type*} (ψ : EuclideanSpace ℂ (Args N w × O))
    (enable inverse : Bool) (x : Fin N) : EuclideanSpace ℂ ((Bool × Bits w) × O) :=
  WithLp.toLp 2 (fun p => ψ ((enable, ((inverse, x), p.1)), p.2))

def ordinarySlice {O : Type*} (ψ : EuclideanSpace ℂ (Args N w × O))
    (enable inverse : Bool) (x : Fin N) (marker : Bool) : EuclideanSpace ℂ (Bits w × O) :=
  WithLp.toLp 2 (fun p => ψ ((enable, ((inverse, x), (marker, p.1))), p.2))

theorem norm_sq_eq_controlSlices {O : Type*} [Fintype O]
    (ψ : EuclideanSpace ℂ (Args N w × O)) :
    ‖ψ‖ ^ 2 = ∑ enable : Bool, ∑ inverse : Bool, ∑ x : Fin N,
      ‖controlSlice ψ enable inverse x‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, controlSlice]

theorem norm_sq_eq_ordinarySlices {O : Type*} [Fintype O]
    (ψ : EuclideanSpace ℂ (Args N w × O)) :
    ‖ψ‖ ^ 2 = ∑ enable : Bool, ∑ inverse : Bool, ∑ x : Fin N, ∑ marker : Bool,
      ‖ordinarySlice ψ enable inverse x marker‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, ordinarySlice]

theorem controlSlice_onOracle {O D : Type*} [Fintype O] [Fintype D]
    (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ D)
    (ψ : EuclideanSpace ℂ (Args N w × O)) (enable inverse : Bool) (x : Fin N) :
    controlSlice (onOracle (Args N w) W ψ) enable inverse x =
      onOracle (Bool × Bits w) W (controlSlice ψ enable inverse x) := by
  ext ⟨z, I⟩
  rfl

theorem ordinarySlice_onOracle {O D : Type*} [Fintype O] [Fintype D]
    (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ D)
    (ψ : EuclideanSpace ℂ (Args N w × O)) (enable inverse : Bool) (x : Fin N)
    (marker : Bool) :
    ordinarySlice (onOracle (Args N w) W ψ) enable inverse x marker =
      onOracle (Bits w) W (ordinarySlice ψ enable inverse x marker) := by
  ext ⟨z, I⟩
  rfl

/-- Difference of the two actual coherent queries after the constructed embedding. -/
def difference (encode : Encoding N w) (marked : Bool)
    (ψ : EuclideanSpace ℂ (Args N w × Perm N)) :
    EuclideanSpace ℂ (Args N w × Database N) :=
  CompressedCoherentQuery.query encode marked
      (onOracle (Args N w) (PolarEmbedding.candidate N) ψ) -
    onOracle (Args N w) (PolarEmbedding.candidate N)
      (ExactCoherentQuery.query encode marked ψ)

theorem controlSlice_difference_disabled (encode : Encoding N w) (marked inverse : Bool)
    (x : Fin N) (ψ : EuclideanSpace ℂ (Args N w × Perm N)) :
    controlSlice (difference encode marked ψ) false inverse x = 0 := by
  have hc := CompressedCoherentQuery.markedSlice_query_disabled encode marked inverse x
    (onOracle (Args N w) (PolarEmbedding.candidate N) ψ)
  have he := ExactCoherentQuery.markedSlice_query_disabled encode marked ψ inverse x
  change controlSlice (CompressedCoherentQuery.query encode marked
      (onOracle (Args N w) (PolarEmbedding.candidate N) ψ)) false inverse x =
    controlSlice (onOracle (Args N w) (PolarEmbedding.candidate N) ψ) false inverse x at hc
  change controlSlice (ExactCoherentQuery.query encode marked ψ) false inverse x =
    controlSlice ψ false inverse x at he
  have hs : controlSlice (difference encode marked ψ) false inverse x =
      controlSlice (CompressedCoherentQuery.query encode marked
        (onOracle (Args N w) (PolarEmbedding.candidate N) ψ)) false inverse x -
      controlSlice (onOracle (Args N w) (PolarEmbedding.candidate N)
        (ExactCoherentQuery.query encode marked ψ)) false inverse x := rfl
  rw [hs, hc, controlSlice_onOracle, controlSlice_onOracle, he, sub_self]

theorem controlSlice_difference_marked (encode : Encoding N w) (inverse : Bool)
    (x : Fin N) (ψ : EuclideanSpace ℂ (Args N w × Perm N)) :
    controlSlice (difference encode true ψ) true inverse x =
      (if inverse then CompressedQuery.inverseMarked encode x else CompressedQuery.marked encode x)
        (onOracle (Bool × Bits w) (PolarEmbedding.candidate N) (controlSlice ψ true inverse x)) -
      onOracle (Bool × Bits w) (PolarEmbedding.candidate N)
        (Query.exactMarked encode inverse x (controlSlice ψ true inverse x)) := by
  have hc := CompressedCoherentQuery.markedSlice_query_enabled encode true inverse x
    (onOracle (Args N w) (PolarEmbedding.candidate N) ψ)
  unfold CompressedCoherentQuery.branch at hc
  have he := ExactCoherentQuery.markedSlice_query_enabled encode ψ inverse x
  change controlSlice (CompressedCoherentQuery.query encode true
      (onOracle (Args N w) (PolarEmbedding.candidate N) ψ)) true inverse x =
    (if inverse then CompressedQuery.inverseMarked encode x else CompressedQuery.marked encode x)
      (controlSlice (onOracle (Args N w) (PolarEmbedding.candidate N) ψ) true inverse x) at hc
  change controlSlice (ExactCoherentQuery.query encode true ψ) true inverse x =
    Query.exactMarked encode inverse x (controlSlice ψ true inverse x) at he
  change controlSlice (CompressedCoherentQuery.query encode true
      (onOracle (Args N w) (PolarEmbedding.candidate N) ψ)) true inverse x -
    controlSlice (onOracle (Args N w) (PolarEmbedding.candidate N)
      (ExactCoherentQuery.query encode true ψ)) true inverse x = _
  rw [hc, controlSlice_onOracle, controlSlice_onOracle, he]

theorem ordinarySlice_difference (encode : Encoding N w) (inverse : Bool)
    (x : Fin N) (marker : Bool) (ψ : EuclideanSpace ℂ (Args N w × Perm N)) :
    ordinarySlice (difference encode false ψ) true inverse x marker =
      (if inverse then CompressedQuery.inverseOrdinary encode x else CompressedQuery.ordinary encode x)
        (onOracle (Bits w) (PolarEmbedding.candidate N) (ordinarySlice ψ true inverse x marker)) -
      onOracle (Bits w) (PolarEmbedding.candidate N)
        (Query.exactOrdinary encode inverse x (ordinarySlice ψ true inverse x marker)) := by
  have hc := CompressedCoherentQuery.ordinarySlice_query_enabled encode inverse x marker
    (onOracle (Args N w) (PolarEmbedding.candidate N) ψ)
  have he := ExactCoherentQuery.ordinarySlice_query_enabled encode ψ inverse x marker
  change ordinarySlice (CompressedCoherentQuery.query encode false
      (onOracle (Args N w) (PolarEmbedding.candidate N) ψ)) true inverse x marker =
    (if inverse then CompressedQuery.inverseOrdinary encode x else CompressedQuery.ordinary encode x)
      (ordinarySlice (onOracle (Args N w) (PolarEmbedding.candidate N) ψ) true inverse x marker) at hc
  change ordinarySlice (ExactCoherentQuery.query encode false ψ) true inverse x marker =
    Query.exactOrdinary encode inverse x (ordinarySlice ψ true inverse x marker) at he
  change ordinarySlice (CompressedCoherentQuery.query encode false
      (onOracle (Args N w) (PolarEmbedding.candidate N) ψ)) true inverse x marker -
    ordinarySlice (onOracle (Args N w) (PolarEmbedding.candidate N)
      (ExactCoherentQuery.query encode false ψ)) true inverse x marker = _
  rw [hc, ordinarySlice_onOracle, ordinarySlice_onOracle, he]

theorem marked_error_le (encode : Encoding N w) (ε : ℝ) (hε : 0 ≤ ε)
    (ψ : EuclideanSpace ℂ (Args N w × Perm N))
    (hblock : ∀ (inverse : Bool) (x : Fin N),
      ‖(if inverse then CompressedQuery.inverseMarked encode x else CompressedQuery.marked encode x)
          (onOracle (Bool × Bits w) (PolarEmbedding.candidate N) (controlSlice ψ true inverse x)) -
        onOracle (Bool × Bits w) (PolarEmbedding.candidate N)
          (Query.exactMarked encode inverse x (controlSlice ψ true inverse x))‖ ≤
        ε * ‖controlSlice ψ true inverse x‖) :
    ‖difference encode true ψ‖ ≤ ε * ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε (norm_nonneg ψ))).mp
  rw [mul_pow, norm_sq_eq_controlSlices, norm_sq_eq_controlSlices]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro enable _
  apply Finset.sum_le_sum
  intro inverse _
  apply Finset.sum_le_sum
  intro x _
  cases enable
  · rw [controlSlice_difference_disabled, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity
  · rw [controlSlice_difference_marked]
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε (norm_nonneg _))).mpr (hblock inverse x)

theorem ordinary_error_le (encode : Encoding N w) (ε : ℝ) (hε : 0 ≤ ε)
    (ψ : EuclideanSpace ℂ (Args N w × Perm N))
    (hblock : ∀ (inverse : Bool) (x : Fin N) (marker : Bool),
      ‖(if inverse then CompressedQuery.inverseOrdinary encode x else CompressedQuery.ordinary encode x)
          (onOracle (Bits w) (PolarEmbedding.candidate N) (ordinarySlice ψ true inverse x marker)) -
        onOracle (Bits w) (PolarEmbedding.candidate N)
          (Query.exactOrdinary encode inverse x (ordinarySlice ψ true inverse x marker))‖ ≤
        ε * ‖ordinarySlice ψ true inverse x marker‖) :
    ‖difference encode false ψ‖ ≤ ε * ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε (norm_nonneg ψ))).mp
  rw [mul_pow, norm_sq_eq_ordinarySlices, norm_sq_eq_ordinarySlices]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro enable _
  apply Finset.sum_le_sum
  intro inverse _
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro marker _
  cases enable
  · have hs : ordinarySlice (difference encode false ψ) false inverse x marker = 0 := by
      have hc := controlSlice_difference_disabled encode false inverse x ψ
      ext ⟨z, I⟩
      exact congrArg (fun v => v ((marker, z), I)) hc
    rw [hs, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity
  · rw [ordinarySlice_difference]
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε (norm_nonneg _))).mpr (hblock inverse x marker)

/-- Fix only private memory, retaining all coherent query controls. -/
def auxiliarySlice {Aux O : Type*}
    (ψ : EuclideanSpace ℂ ((Aux × Args N w) × O)) (a : Aux) :
    EuclideanSpace ℂ (Args N w × O) :=
  WithLp.toLp 2 (fun p => ψ ((a, p.1), p.2))

theorem norm_sq_eq_auxiliarySlices {Aux O : Type*} [Fintype Aux] [Fintype O]
    (ψ : EuclideanSpace ℂ ((Aux × Args N w) × O)) :
    ‖ψ‖ ^ 2 = ∑ a : Aux, ‖auxiliarySlice ψ a‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, auxiliarySlice]

theorem auxiliarySlice_onOracle {Aux O D : Type*} [Fintype Aux] [Fintype O] [Fintype D]
    (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ D)
    (ψ : EuclideanSpace ℂ ((Aux × Args N w) × O)) (a : Aux) :
    auxiliarySlice (onOracle (Aux × Args N w) W ψ) a =
      onOracle (Args N w) W (auxiliarySlice ψ a) := by
  ext ⟨args, I⟩
  rfl

def liftedDifference {Aux : Type*} [Fintype Aux]
    (encode : Encoding N w) (marked : Bool)
    (ψ : EuclideanSpace ℂ ((Aux × Args N w) × Perm N)) :
    EuclideanSpace ℂ ((Aux × Args N w) × Database N) :=
  CompressedCoherentQuery.liftedQuery Aux encode marked
      (onOracle (Aux × Args N w) (PolarEmbedding.candidate N) ψ) -
    onOracle (Aux × Args N w) (PolarEmbedding.candidate N)
      (ExactQueryGrowth.liftedQuery Aux encode marked ψ)

theorem auxiliarySlice_liftedDifference {Aux : Type*} [Fintype Aux]
    (encode : Encoding N w) (marked : Bool)
    (ψ : EuclideanSpace ℂ ((Aux × Args N w) × Perm N)) (a : Aux) :
    auxiliarySlice (liftedDifference encode marked ψ) a =
      difference encode marked (auxiliarySlice ψ a) := by
  have hc : auxiliarySlice (CompressedCoherentQuery.liftedQuery Aux encode marked
      (onOracle (Aux × Args N w) (PolarEmbedding.candidate N) ψ)) a =
    CompressedCoherentQuery.query encode marked
      (auxiliarySlice (onOracle (Aux × Args N w) (PolarEmbedding.candidate N) ψ) a) :=
    CompressedCoherentQuery.slice_liftedQuery encode marked _ a
  have he : auxiliarySlice (ExactQueryGrowth.liftedQuery Aux encode marked ψ) a =
      ExactCoherentQuery.query encode marked (auxiliarySlice ψ a) := by
    ext ⟨args, π⟩
    rfl
  change auxiliarySlice (CompressedCoherentQuery.liftedQuery Aux encode marked
      (onOracle (Aux × Args N w) (PolarEmbedding.candidate N) ψ)) a -
    auxiliarySlice (onOracle (Aux × Args N w) (PolarEmbedding.candidate N)
      (ExactQueryGrowth.liftedQuery Aux encode marked ψ)) a = _
  rw [hc, auxiliarySlice_onOracle, auxiliarySlice_onOracle, he]
  rfl

/-- Entangled finite private memory introduces no dimension or control-count factor. -/
theorem lifted_error_le {Aux : Type*} [Fintype Aux]
    (encode : Encoding N w) (marked : Bool) (ε : ℝ) (hε : 0 ≤ ε)
    (ψ : EuclideanSpace ℂ ((Aux × Args N w) × Perm N))
    (hlocal : ∀ a : Aux, ‖difference encode marked (auxiliarySlice ψ a)‖ ≤
      ε * ‖auxiliarySlice ψ a‖) :
    ‖liftedDifference encode marked ψ‖ ≤ ε * ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε (norm_nonneg ψ))).mp
  rw [mul_pow, norm_sq_eq_auxiliarySlices, norm_sq_eq_auxiliarySlices, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [auxiliarySlice_liftedDifference]
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε (norm_nonneg _))).mpr (hlocal a)

end QuantumOracle.CoherentComparison
