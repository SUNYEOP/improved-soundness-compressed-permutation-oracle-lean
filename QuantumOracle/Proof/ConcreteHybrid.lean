import QuantumOracle.Model.ConcreteExperiment
import Mathlib.Tactic.Ring

/-!
# Exact-prefix hybrids for the actual paired executions

The oracle runs, compressed isometries, and their common purifications are
constructed internally. The hidden isometry, its initial-state identity, and
the local error estimate remain explicit mathematical hypotheses. In
particular, this module does not construct the harmonic isometry or prove
the manuscript's sharp one-query bound.
-/

noncomputable section

namespace QuantumOracle.ConcreteHybrid

open PermutationExtensions HiddenIsometry WorkspaceKnowledge ConcreteExperiment

variable {N w : ℕ}

/-- A proposed actual hidden isometry must take the exact uniform permutation
state to the actual empty database ket. This lemma propagates that identity
through an arbitrary initial workspace vector. -/
theorem initial_transport {A : Type*} [Fintype A]
    (W : EuclideanSpace ℂ (Perm N) →ₗᵢ[ℂ] EuclideanSpace ℂ (Database N))
    (hinit : W (ConsistentState.vector Database.empty) = EuclideanSpace.single Database.empty 1)
    (φ : EuclideanSpace ℂ A) :
    onOracle A W (ExactExecution.initial N φ) = CompressedExecution.initial N φ := by
  change onOracle A W (productState φ (ConsistentState.vector Database.empty)) = _
  rw [onOracle_productState, hinit, CompressedExecution.initial_eq_productState]

/-- Error of the two actual next-query operations, evaluated only on a genuine
exact prefix. All coherent controls and private memory are retained. -/
def localError (encode : BasisLookup.Encoding N w)
    (W : EuclideanSpace ℂ (Perm N) →ₗᵢ[ℂ] EuclideanSpace ℂ (Database N))
    (a : Algorithm N w) (j : ℕ) : ℝ :=
  ‖onOracle a.Workspace W
      (ExactQueryGrowth.liftedQuery (Fin a.auxDim) encode (a.marked j)
        (ExactExecution.run encode a.marked a.gates a.initial j)) -
    CompressedCoherentQuery.liftedQuery (Fin a.auxDim) encode (a.marked j)
      (onOracle a.Workspace W (ExactExecution.run encode a.marked a.gates a.initial j))‖

private theorem norm_onWorkspace_sub {A O : Type*} [Fintype A] [Fintype O]
    (U : EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (ψ χ : EuclideanSpace ℂ (A × O)) :
    ‖onWorkspace O U.toLinearEquiv.toLinearMap ψ -
      onWorkspace O U.toLinearEquiv.toLinearMap χ‖ = ‖ψ - χ‖ := by
  rw [← map_sub, norm_onWorkspace]

/-- A telescoping bound for the genuine executions. The only comparison
hypotheses are the hidden initial identity and the next-query error on each
exact prefix. In particular, no run, purification, or compressed-step
isometry is supplied as a hypothesis. -/
theorem run_error_le (encode : BasisLookup.Encoding N w)
    (W : EuclideanSpace ℂ (Perm N) →ₗᵢ[ℂ] EuclideanSpace ℂ (Database N))
    (hinit : W (ConsistentState.vector Database.empty) = EuclideanSpace.single Database.empty 1)
    (a : Algorithm N w) (q : ℕ) (ε : ℝ)
    (hlocal : ∀ j < q, localError encode W a j ≤ ε) :
    ‖onOracle a.Workspace W (ExactExecution.run encode a.marked a.gates a.initial q) -
      CompressedExecution.run encode a.marked a.gates a.initial q‖ ≤ (q : ℝ) * ε := by
  suffices ∀ n ≤ q,
      ‖onOracle a.Workspace W (ExactExecution.run encode a.marked a.gates a.initial n) -
        CompressedExecution.run encode a.marked a.gates a.initial n‖ ≤ (n : ℝ) * ε by
    exact this q le_rfl
  intro n
  induction n with
  | zero =>
    intro _
    rw [ExactExecution.run, CompressedExecution.run, onOracle_onWorkspace,
      initial_transport W hinit, sub_self, norm_zero, Nat.cast_zero, zero_mul]
  | succ n ih =>
    intro hn
    have hnq : n < q := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
    let e := ExactExecution.run encode a.marked a.gates a.initial n
    let c := CompressedExecution.run encode a.marked a.gates a.initial n
    let Q := CompressedCoherentQuery.liftedQuery (Fin a.auxDim) encode (a.marked n)
    let x := onOracle a.Workspace W
      (ExactQueryGrowth.liftedQuery (Fin a.auxDim) encode (a.marked n) e)
    have hQ : ‖Q (onOracle a.Workspace W e) - Q c‖ =
        ‖onOracle a.Workspace W e - c‖ := by
      simpa only [dist_eq_norm] using Q.isometry.dist_eq (onOracle a.Workspace W e) c
    calc
      ‖onOracle a.Workspace W
          (ExactExecution.run encode a.marked a.gates a.initial (n + 1)) -
          CompressedExecution.run encode a.marked a.gates a.initial (n + 1)‖ =
          ‖x - Q c‖ := by
        rw [ExactExecution.run, CompressedExecution.run, onOracle_onWorkspace,
          norm_onWorkspace_sub]
      _ ≤ ‖x - Q (onOracle a.Workspace W e)‖ +
          ‖Q (onOracle a.Workspace W e) - Q c‖ := by
        simpa only [dist_eq_norm] using
          dist_triangle x (Q (onOracle a.Workspace W e)) (Q c)
      _ = localError encode W a n + ‖onOracle a.Workspace W e - c‖ := by
        rw [hQ]
        rfl
      _ ≤ ε + (n : ℝ) * ε := add_le_add (hlocal n hnq) (ih (Nat.le_of_lt hnq))
      _ = ((n + 1 : ℕ) : ℝ) * ε := by rw [Nat.cast_add, Nat.cast_one]; ring

theorem vector_error_le (encode : BasisLookup.Encoding N w)
    (W : EuclideanSpace ℂ (Perm N) →ₗᵢ[ℂ] EuclideanSpace ℂ (Database N))
    (hinit : W (ConsistentState.vector Database.empty) = EuclideanSpace.single Database.empty 1)
    (a : Algorithm N w) (ε : ℝ)
    (hlocal : ∀ j < a.queries, localError encode W a j ≤ ε) :
    ‖onOracle a.Workspace W (exactVector encode a) - compressedVector encode a‖ ≤
      (a.queries : ℝ) * ε :=
  run_error_le encode W hinit a a.queries ε hlocal

/-- The genuine supremum/infimum operational distance inherits a uniform local
query comparison. The construction of `W`, its initial identity, and this
local estimate are deliberately still explicit obligations. -/
theorem dist_le_of_local_error (encode : BasisLookup.Encoding N w) (hN : 0 < N)
    (W : EuclideanSpace ℂ (Perm N) →ₗᵢ[ℂ] EuclideanSpace ℂ (Database N))
    (hinit : W (ConsistentState.vector Database.empty) = EuclideanSpace.single Database.empty 1)
    (q : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hlocal : ∀ a : Algorithm N w, a.queries ≤ q →
      ∀ j < a.queries, localError encode W a j ≤ ε) :
    Dist encode q ≤ (q : ℝ) * ε := by
  apply dist_le_of_hidden_comparison encode hN q ((q : ℝ) * ε) W
  intro a ha
  exact (vector_error_le encode W hinit a ε (hlocal a ha)).trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ha) hε)

end QuantumOracle.ConcreteHybrid
