import QuantumOracle.Proof.ConditioningJointBound
import QuantumOracle.Proof.ConditioningCrossTerms
import QuantumOracle.Proof.ResidualBranchSupport

/-!
# Soundness for the actual finite oracle experiments

The conditioning estimate is assembled from the actual Specht decomposition,
corner support, and orthogonality of the actual error images. The resulting
operational theorem quantifies over all algorithms and output decompositions in
`OutputExperiment.Dist`; no spectral or local-error hypothesis remains.
-/

noncomputable section

namespace QuantumOracle.FiniteSoundness

variable {N w : ℕ}

/-- The actual conditioning discrepancy has the manuscript's uniform bound. -/
theorem conditioning_bound (N q : ℕ) (hq : 4 * q ≤ N + 1) :
    ConditioningLocalBound.Bound N q (2 / Real.sqrt (N + 1 : ℕ)) :=
  ConditioningJointBound.bound_of_support_and_error_orthogonality q hq
    (fun x label _ hh hn =>
      ResidualBranchSupport.mem_removeCorners_of_joint_ne_zero x label hh hn)
    (fun x a b hn ha hb _ _ hh hk =>
      ConditioningCrossTerms.error_inner_eq_zero x a b hn ha hb hh hk)

/-- The numerical bound for a successor-sized oracle domain. -/
theorem dist_le_four_mul_div_sqrt_succ
    (encode : BasisLookup.Encoding (N + 1) w) (q : ℕ) (hq : 4 * q ≤ N + 1) :
    OutputExperiment.Dist encode q ≤ 4 * (q : ℝ) / Real.sqrt (N + 1 : ℕ) :=
  ConditioningSoundness.dist_le_four_mul_div_sqrt_of_conditioning_bound
    encode q hq (conditioning_bound N q hq)

/-- The actual worst-case output distance for every positive finite domain. -/
theorem dist_le_four_mul_div_sqrt
    (encode : BasisLookup.Encoding N w) (hN : 0 < N) (q : ℕ) (hq : 4 * q ≤ N) :
    OutputExperiment.Dist encode q ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) := by
  cases N with
  | zero => omega
  | succ n => exact dist_le_four_mul_div_sqrt_succ encode q hq

/-- The same bound when the entire algorithm workspace is retained. -/
theorem retained_dist_le_four_mul_div_sqrt
    (encode : BasisLookup.Encoding N w) (hN : 0 < N) (q : ℕ) (hq : 4 * q ≤ N) :
    ConcreteExperiment.Dist encode q ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) := by
  rw [← OutputExperiment.dist_eq_retained encode hN q]
  exact dist_le_four_mul_div_sqrt encode hN q hq

/-- Every permitted algorithm and final output choice obeys the same bound. -/
theorem algorithm_distance_le_four_mul_div_sqrt
    (encode : BasisLookup.Encoding N w) (hN : 0 < N) (q : ℕ) (hq : 4 * q ≤ N)
    (a : OutputExperiment.Algorithm N w) (ha : a.base.queries ≤ q) :
    purificationDistance (OutputExperiment.exactFinal encode a)
      (OutputExperiment.compressedFinal encode a) ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) :=
  (OutputExperiment.algorithm_distance_le_dist encode q a ha).trans
    (dist_le_four_mul_div_sqrt encode hN q hq)

end QuantumOracle.FiniteSoundness
