import QuantumOracle.Proof.ConditioningLocalBound
import QuantumOracle.Proof.CoherentComparison
import QuantumOracle.Proof.PolarComparison

/-!
# From a conditioning estimate to the actual output distance

The sole quantitative premise is a bound for the constructed conditioning
discrepancy on the actual knowledge space `K N q`. Coherent query controls,
arbitrary finite private memory, exact-prefix support, normalization, and the
hybrid argument are all discharged for the actual paired executions.

The numerical conditioning premise is not proved here. In particular the last
theorem is a conditional reduction, not the completed spectral soundness proof.
-/

noncomputable section

namespace QuantumOracle.ConditioningSoundness

open BasisLookup PermutationExtensions WorkspaceKnowledge HiddenIsometry
open KnowledgeSpace ExactCoherentQuery CoherentComparison ConditioningLocalBound

attribute [local irreducible] PolarEmbedding.candidate

variable {N t w : ℕ}

theorem controlSlice_supported
    {ψ : EuclideanSpace ℂ (Args N w × Perm N)} (hψ : Supported (K N t) ψ)
    (enable inverse : Bool) (x : Fin N) :
    Supported (K N t) (controlSlice ψ enable inverse x) := by
  intro z
  exact hψ (enable, ((inverse, x), z))

theorem ordinarySlice_supported
    {ψ : EuclideanSpace ℂ (Args N w × Perm N)} (hψ : Supported (K N t) ψ)
    (enable inverse : Bool) (x : Fin N) (marker : Bool) :
    Supported (K N t) (CoherentComparison.ordinarySlice ψ enable inverse x marker) := by
  intro z
  exact hψ (enable, ((inverse, x), (marker, z)))

theorem auxiliarySlice_supported {Aux : Type*} [Fintype Aux]
    {ψ : EuclideanSpace ℂ ((Aux × Args N w) × Perm N)}
    (hψ : Supported (K N t) ψ) (a : Aux) :
    Supported (K N t) (auxiliarySlice ψ a) := by
  intro z
  exact hψ (a, z)

/-- All coherent controls retain the same two-error bound. -/
theorem query_error_le (encode : Encoding (N + 1) w) (marked : Bool)
    (ε : ℝ) (hε : 0 ≤ ε) (hbound : Bound N (t + 1) ε) (ht : t < N + 1)
    {ψ : EuclideanSpace ℂ (Args (N + 1) w × Perm (N + 1))}
    (hψ : Supported (K (N + 1) t) ψ) :
    ‖difference encode marked ψ‖ ≤ (2 * ε) * ‖ψ‖ := by
  cases marked
  · apply CoherentComparison.ordinary_error_le encode (2 * ε) (by positivity)
    intro inverse x marker
    exact ConditioningLocalBound.ordinary_error_le encode inverse x ε hε hbound ht
      (ordinarySlice_supported hψ true inverse x marker)
  · apply CoherentComparison.marked_error_le encode (2 * ε) (by positivity)
    intro inverse x
    exact ConditioningLocalBound.marked_error_le encode inverse x ε hε hbound ht
      (controlSlice_supported hψ true inverse x)

/-- Finite private memory can remain arbitrarily entangled with all query arguments. -/
theorem lifted_query_error_le {Aux : Type*} [Fintype Aux]
    (encode : Encoding (N + 1) w) (marked : Bool)
    (ε : ℝ) (hε : 0 ≤ ε) (hbound : Bound N (t + 1) ε) (ht : t < N + 1)
    {ψ : EuclideanSpace ℂ ((Aux × Args (N + 1) w) × Perm (N + 1))}
    (hψ : Supported (K (N + 1) t) ψ) :
    ‖liftedDifference encode marked ψ‖ ≤ (2 * ε) * ‖ψ‖ := by
  apply CoherentComparison.lifted_error_le encode marked (2 * ε) (by positivity)
  intro a
  exact query_error_le encode marked ε hε hbound ht (auxiliarySlice_supported hψ a)

/-- A bound at the maximal permitted degree applies to every earlier degree. -/
theorem bound_mono {s q : ℕ} {ε : ℝ} (hsq : s ≤ q) (hq : q ≤ N + 1)
    (hbound : Bound N q ε) : Bound N s ε := by
  intro x h hh
  exact hbound x h (KnowledgeSpace.mono hsq hq hh)

/-- Only the actual exact prefix is used in each hybrid step. -/
theorem localError_le (encode : Encoding (N + 1) w)
    (a : ConcreteExperiment.Algorithm (N + 1) w) (j : ℕ)
    (ε : ℝ) (hε : 0 ≤ ε) (hbound : Bound N (j + 1) ε) (hj : j < N + 1) :
    PolarComparison.localError encode a j ≤ 2 * ε := by
  have hs := ExactExecution.run_supported_of_le encode a.marked a.gates a.initial j
    (Nat.le_of_lt hj)
  have he := lifted_query_error_le encode (a.marked j) ε hε hbound hj hs
  rw [ExactExecution.run_norm, a.normalized, mul_one] at he
  unfold PolarComparison.localError ConcreteHybrid.localError
  rw [norm_sub_rev]
  exact he

/-- A single uniform conditioning estimate implies the actual operational bound. -/
theorem dist_le_of_conditioning_bound (encode : Encoding (N + 1) w)
    (q : ℕ) (hq : q ≤ N + 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : Bound N q ε) :
    OutputExperiment.Dist encode q ≤ (q : ℝ) * (2 * ε) := by
  apply PolarComparison.dist_le_of_local_error encode (Nat.succ_pos N) q (2 * ε)
    (by positivity)
  intro a haq j hj
  have hjq : j + 1 ≤ q := (Nat.succ_le_of_lt hj).trans haq
  exact localError_le encode a j ε hε (bound_mono hjq hq hbound)
    (Nat.lt_of_lt_of_le (Nat.lt_of_succ_le hjq) hq)

/-- The manuscript's numerical conclusion follows once its actual conditioning
estimate has been proved, with the post-query degree bounded by `q`. -/
theorem dist_le_four_mul_div_sqrt_of_conditioning_bound
    (encode : Encoding (N + 1) w) (q : ℕ) (hq : 4 * q ≤ N + 1)
    (hbound : Bound N q (2 / Real.sqrt (N + 1 : ℕ))) :
    OutputExperiment.Dist encode q ≤ 4 * (q : ℝ) / Real.sqrt (N + 1 : ℕ) := by
  have hqN : q ≤ N + 1 := by omega
  have he := dist_le_of_conditioning_bound encode q hqN
    (2 / Real.sqrt (N + 1 : ℕ)) (by positivity) hbound
  convert he using 1
  ring

end QuantumOracle.ConditioningSoundness
