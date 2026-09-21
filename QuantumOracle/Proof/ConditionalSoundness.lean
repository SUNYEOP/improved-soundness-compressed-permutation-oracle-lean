import QuantumOracle.Proof.Hybrid
import QuantumOracle.Model.PurificationDistance

/-!
This module connects the generic hybrid estimate to the supremum/infimum
distance construction for supplied executions and one-query bounds.
`FiniteSoundness` proves the bound for the concrete oracle experiments.
-/

noncomputable section

namespace QuantumOracle

/-- Two executions whose final vectors really purify the specified reduced
matrices. Their step functions are parameters of this general interface. -/
structure PurifiedRunPair {d : ℕ} (ρ σ : ReducedState d) (m : ℕ) where
  purification : CommonPurification ρ σ
  exactStep : ℕ → PureState d purification.ancillaDim → PureState d purification.ancillaDim
  compressedStep : ℕ → PureState d purification.ancillaDim → PureState d purification.ancillaDim
  initial : PureState d purification.ancillaDim
  exact_final : evolution exactStep initial m = purification.exactVector
  compressed_final : evolution compressedStep initial m = purification.compressedVector

/-- Analytic assembly only: the one-query comparison is an explicit hypothesis
on every exact prefix, including every query variant used by the algorithm. -/
theorem PurifiedRunPair.conditional_distance_le {d m : ℕ} {ρ σ : ReducedState d}
    (run : PurifiedRunPair ρ σ m) (N : ℕ)
    (hc : ∀ j < m, Isometry (run.compressedStep j))
    (he : ∀ j < m,
      dist (run.exactStep j (evolution run.exactStep run.initial j))
        (run.compressedStep j (evolution run.exactStep run.initial j)) ≤
      4 / Real.sqrt (N : ℝ)) :
    run.purification.distance ≤ 4 * (m : ℝ) / Real.sqrt (N : ℝ) := by
  have h := conditional_evolution_four_mul_div_sqrt
    run.exactStep run.compressedStep run.initial m N hc he
  rw [run.exact_final, run.compressed_final, dist_eq_norm] at h
  exact h

/-- Generic hybrid form of the final inequality in `thm:soundness`.

The hypotheses supply executions, their correct purifications, compressed-step
isometries, and the one-query estimate. The concrete oracle bound is proved
in `FiniteSoundness`; this lemma accepts the corresponding data abstractly.
The generic summation itself works for every `q`.
-/
theorem ExperimentFamily.conditional_soundness {Algorithm : Type*}
    (F : ExperimentFamily Algorithm) (q N : ℕ)
    (hne : ∃ a, F.queries a ≤ q)
    (runs : ∀ a, PurifiedRunPair (F.exactFinal a) (F.compressedFinal a) (F.queries a))
    (hc : ∀ a, F.queries a ≤ q → ∀ j < F.queries a,
      Isometry ((runs a).compressedStep j))
    (he : ∀ a, F.queries a ≤ q → ∀ j < F.queries a,
      dist ((runs a).exactStep j (evolution (runs a).exactStep (runs a).initial j))
        ((runs a).compressedStep j (evolution (runs a).exactStep (runs a).initial j)) ≤
      4 / Real.sqrt (N : ℝ)) :
    F.Dist q ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) := by
  apply F.dist_le_of_witnesses q _ hne
  intro a ha
  refine ⟨(runs a).purification, ?_⟩
  calc
    (runs a).purification.distance ≤
        4 * (F.queries a : ℝ) / Real.sqrt (N : ℝ) :=
      (runs a).conditional_distance_le N (hc a ha) (he a ha)
    _ ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ha) (by norm_num))
        (Real.sqrt_nonneg _)

/-- The manuscript's natural-number query range is used to discharge the
`j+1 ≤ N/4` side condition of each supplied local estimate. The estimate
and the run/purification semantics are explicit hypotheses of this lemma. -/
theorem ExperimentFamily.conditional_soundness_in_range {Algorithm : Type*}
    (F : ExperimentFamily Algorithm) (q N : ℕ) (hq : 4 * q ≤ N)
    (hne : ∃ a, F.queries a ≤ q)
    (runs : ∀ a, PurifiedRunPair (F.exactFinal a) (F.compressedFinal a) (F.queries a))
    (hc : ∀ a, F.queries a ≤ q → ∀ j < F.queries a,
      Isometry ((runs a).compressedStep j))
    (he : ∀ a, F.queries a ≤ q → ∀ j < F.queries a, 4 * (j + 1) ≤ N →
      dist ((runs a).exactStep j (evolution (runs a).exactStep (runs a).initial j))
        ((runs a).compressedStep j (evolution (runs a).exactStep (runs a).initial j)) ≤
      4 / Real.sqrt (N : ℝ)) :
    F.Dist q ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) := by
  apply F.conditional_soundness q N hne runs hc
  intro a ha j hj
  apply he a ha j hj
  exact (Nat.mul_le_mul_left 4 ((Nat.succ_le_of_lt hj).trans ha)).trans hq

end QuantumOracle
