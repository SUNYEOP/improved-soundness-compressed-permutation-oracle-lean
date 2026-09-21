import QuantumOracle.Proof.FiniteSoundnessWitness
import QuantumOracle.Model.ProjectorPurification

/-!
# The three conclusions of the manuscript's improved soundness theorem

This module packages `thm:soundness` in `paper/sections/03_harmonic_comparison.tex`:
the bound `Dist(q) ≤ 4q/√N`, the specified close common purification pair, and the
final-projector inequality through `Dist(q)`.

The interface is the purified finite query model adopted in the manuscript's
preliminaries. `OutputExperiment.Dist` takes the supremum over that algorithm
class and the infimum over all finite common purifications of its actual output
states. No spectrum, branching rule, overlap, or local-error bound is a caller
hypothesis. The external representation and hook-length sources are compiled
dependencies; the oracle comparison is proved by this project.

See `docs/THEOREM_STATEMENT.md` for the parameter-by-parameter correspondence,
the selected model scope, and the role of dependencies outside mathlib.
-/

noncomputable section

namespace QuantumOracle.ImprovedSoundness

open ProjectorPurification FiniteSoundnessWitness

variable {N w : ℕ}

/-- The final-projector inequality through the actual supremum/infimum distance.
`P` is the output subspace; `project P` lifts its orthogonal projection by the
identity on the common ancilla. The projected norms depend only on the reduced
states, so this uses every purification pair, not just the constructed pair.
No numerical query-range hypothesis is needed for this first inequality. -/
theorem projected_norm_difference_le_dist
    (encode : BasisLookup.Encoding N w) (q : ℕ)
    (a : OutputExperiment.Algorithm N w) (ha : a.base.queries ≤ q)
    (P : Submodule ℂ (EuclideanSpace ℂ (Fin (Fintype.card a.Output)))) :
    |‖project P (outputPurification encode a).exactVector‖ -
      ‖project P (outputPurification encode a).compressedVector‖| ≤
        OutputExperiment.Dist encode q :=
  (abs_project_norm_sub_le_purificationDistance P (outputPurification encode a)).trans
    (OutputExperiment.algorithm_distance_le_dist encode q a ha)

/-- The manuscript's complete final-projector chain, represented as a conjunction:
the projected-norm difference is at most `Dist`, which is at most `4q/√N`.
The first theorem supplies the left inequality and `FiniteSoundness` the right. -/
theorem projected_norm_difference_le_dist_le_four_mul_div_sqrt
    (encode : BasisLookup.Encoding N w) (hN : 0 < N) (q : ℕ) (hq : 4 * q ≤ N)
    (a : OutputExperiment.Algorithm N w) (ha : a.base.queries ≤ q)
    (P : Submodule ℂ (EuclideanSpace ℂ (Fin (Fintype.card a.Output)))) :
    (|‖project P (outputPurification encode a).exactVector‖ -
      ‖project P (outputPurification encode a).compressedVector‖| ≤
        OutputExperiment.Dist encode q) ∧
      OutputExperiment.Dist encode q ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) :=
  ⟨projected_norm_difference_le_dist encode q a ha P,
    FiniteSoundness.dist_le_four_mul_div_sqrt encode hN q hq⟩

/-- The three conclusions of the manuscript's `thm:soundness`.

`N` counts permutation points, while `w` counts bits in each encoded answer.
`encode` supplies the distinct encodings; `hN` requires a positive domain and
`hq` expresses the paper's range `q ≤ N/4` without natural-number division.
`a` supplies the finite algorithm and its final output/discard split; `ha`
allows it to use any number of queries at most `q`. Normalization and unitary
gates are already part of the algorithm's type.

The `let p` constructs the actual pair: the exact final vector transported by
the harmonic isometry and the compressed final vector, with discarded output
coordinates included in their common ancilla. Its type already proves unit
norms and the two required reduced-state equalities. The conjunction then gives
(1) this pair's distance bound, (2) the worst-case `Dist` bound, and (3) every
final orthogonal projector's bound through `Dist`. The first two conjuncts are
ordered oppositely to the manuscript's presentation, with the same conclusions.
-/
theorem soundness
    (encode : BasisLookup.Encoding N w) (hN : 0 < N) (q : ℕ) (hq : 4 * q ≤ N)
    (a : OutputExperiment.Algorithm N w) (ha : a.base.queries ≤ q) :
    let p := outputPurification encode a
    p.distance ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) ∧
      OutputExperiment.Dist encode q ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) ∧
      ∀ P : Submodule ℂ (EuclideanSpace ℂ (Fin (Fintype.card a.Output))),
        |‖project P p.exactVector‖ - ‖project P p.compressedVector‖| ≤
          OutputExperiment.Dist encode q :=
  ⟨outputPurification_distance_le encode hN q hq a ha,
    FiniteSoundness.dist_le_four_mul_div_sqrt encode hN q hq,
    fun P => projected_norm_difference_le_dist encode q a ha P⟩

end QuantumOracle.ImprovedSoundness
