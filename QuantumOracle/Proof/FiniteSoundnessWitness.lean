import QuantumOracle.Proof.FiniteSoundness
import QuantumOracle.Model.SoundnessPurification

/-! # Explicit finite purifications witnessing soundness

The exact final vector is transported by the actual polar embedding into the
same database register as the compressed final vector. These concrete vectors
give common purifications whose distance satisfies the numerical upper bound,
including after an arbitrary finite output factor is retained.
-/

noncomputable section

namespace QuantumOracle.FiniteSoundnessWitness

open PermutationExtensions HiddenIsometry FinitePurification OutputDiscard

attribute [local irreducible] PolarEmbedding.candidate

variable {N w : ℕ}

/-- The actual next-query discrepancy at every admissible exact prefix. -/
theorem local_error_le_four_div_sqrt (encode : BasisLookup.Encoding N w)
    (hN : 0 < N) (q : ℕ) (hq : 4 * q ≤ N)
    (a : ConcreteExperiment.Algorithm N w) (ha : a.queries ≤ q)
    (j : ℕ) (hj : j < a.queries) :
    PolarComparison.localError encode a j ≤ 4 / Real.sqrt (N : ℝ) := by
  cases N with
  | zero => omega
  | succ n =>
    have hqN : q ≤ n + 1 := by omega
    have hjq : j + 1 ≤ q := by omega
    have hb := ConditioningSoundness.bound_mono hjq hqN
      (FiniteSoundness.conditioning_bound n q hq)
    have he := ConditioningSoundness.localError_le encode a j
      (2 / Real.sqrt (n + 1 : ℕ)) (by positivity) hb (by omega)
    convert he using 1
    ring

/-- The actual polar-transported and compressed final vectors satisfy the
manuscript bound before taking an infimum over purifications. -/
theorem vector_error_le_four_mul_div_sqrt (encode : BasisLookup.Encoding N w)
    (hN : 0 < N) (q : ℕ) (hq : 4 * q ≤ N)
    (a : ConcreteExperiment.Algorithm N w) (ha : a.queries ≤ q) :
    ‖onOracle a.Workspace (PolarEmbedding.candidate N)
        (ConcreteExperiment.exactVector encode a) - ConcreteExperiment.compressedVector encode a‖ ≤
      4 * (q : ℝ) / Real.sqrt (N : ℝ) := by
  have he := PolarComparison.vector_error_le encode a (4 / Real.sqrt (N : ℝ))
    (fun j hj => local_error_le_four_div_sqrt encode hN q hq a ha j hj)
  calc
    _ ≤ (a.queries : ℝ) * (4 / Real.sqrt (N : ℝ)) := he
    _ ≤ (q : ℝ) * (4 / Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ha) (by positivity)
    _ = _ := by ring

theorem retainedPurification_distance_le (encode : BasisLookup.Encoding N w)
    (hN : 0 < N) (q : ℕ) (hq : 4 * q ≤ N)
    (a : ConcreteExperiment.Algorithm N w) (ha : a.queries ≤ q) :
    (retainedPurification encode a).distance ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) := by
  rw [retainedPurification_distance]
  exact vector_error_le_four_mul_div_sqrt encode hN q hq a ha

theorem outputPurification_distance_le (encode : BasisLookup.Encoding N w)
    (hN : 0 < N) (q : ℕ) (hq : 4 * q ≤ N)
    (a : OutputExperiment.Algorithm N w) (ha : a.base.queries ≤ q) :
    (outputPurification encode a).distance ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) := by
  rw [outputPurification_distance]
  exact retainedPurification_distance_le encode hN q hq a.base ha

theorem exists_retained_purification (encode : BasisLookup.Encoding N w)
    (hN : 0 < N) (q : ℕ) (hq : 4 * q ≤ N)
    (a : ConcreteExperiment.Algorithm N w) (ha : a.queries ≤ q) :
    ∃ p : CommonPurification (ConcreteExperiment.exactFinal encode a)
        (ConcreteExperiment.compressedFinal encode a),
      p.distance ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) :=
  ⟨retainedPurification encode a, retainedPurification_distance_le encode hN q hq a ha⟩

theorem exists_output_purification (encode : BasisLookup.Encoding N w)
    (hN : 0 < N) (q : ℕ) (hq : 4 * q ≤ N)
    (a : OutputExperiment.Algorithm N w) (ha : a.base.queries ≤ q) :
    ∃ p : CommonPurification (OutputExperiment.exactFinal encode a)
        (OutputExperiment.compressedFinal encode a),
      p.distance ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) :=
  ⟨outputPurification encode a, outputPurification_distance_le encode hN q hq a ha⟩

end QuantumOracle.FiniteSoundnessWitness
