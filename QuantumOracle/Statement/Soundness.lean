import QuantumOracle.Model.SoundnessPurification
import QuantumOracle.Model.ProjectorPurification

/-!
# The complete improved soundness specification

This is the canonical proposition corresponding to the manuscript's
`thm:soundness` in `paper/sections/03_harmonic_comparison.tex`. It imports the
implemented model and its foundational facts; the numerical soundness proof
does not belong to this module's import closure.

The model is the manuscript's finite purified query model. The exact and
compressed oracles execute the same algorithm record. Its finite auxiliary
register, normalized oracle-independent initial state, unitary workspace gates,
query schedule, and final output/discard split are actual data in that record.

Human review starts with this proposition and then follows the definitions of
the algorithm, oracle executions, `outputPurification`, `Dist`, and `project`.
Lean checks their typing and the proof supplied separately in
`QuantumOracle.Soundness`; correspondence with the manuscript remains the
semantic review task. See `docs/THEOREM_STATEMENT.md` and `review/README.md`.

-/

namespace QuantumOracle

open FiniteSoundnessWitness ProjectorPurification

/-- The full improved soundness claim, with no spectral or error estimate supplied
as an assumption.

Parameters and assumptions:
* `N` is the number of permutation points; `w` is the encoded answer's bit length.
* `encode` supplies the distinct encodings of the `N` points into `w` bits.
* `_hN` requires `N > 0`.
* `q` is the query budget, and `_hq : 4 * q ≤ N` expresses `q ≤ N/4` without
  natural-number division or rounding.
* `a` is any algorithm in the finite purified query model, including its final
  output/discard split. Normalization and unitary gates are part of its type.
* `_ha` permits any actual query count at most the budget `q`.

The specified `p` is built from the actual exact final vector transported by
the harmonic isometry `W` and the actual compressed final vector. The discarded
output factor is included in their common ancilla. The type `CommonPurification`
already requires both unit norms and both prescribed reduced-state equalities.

The three conclusions are, in order:
1. This specified common purification pair has vector distance at most `4q/√N`.
2. `Dist` has the same bound. Its definition takes the supremum over all
   admissible algorithms and the infimum over all finite normalized common
   purifications of their actual output states.
3. For every output subspace `P`, the absolute difference of projected norms is
   at most `Dist`. `project P` is the orthogonal projection on the output tensored
   with the identity on the common ancilla. These norms are square roots of
   acceptance probabilities. Together with conclusion 2 this gives the full
   projector inequality chain in the manuscript.

The manuscript lists conclusions 1 and 2 in the opposite order. This is the same
complete proposition as the existing `ImprovedSoundness.soundness` theorem.
-/
def SoundnessStatement : Prop :=
  ∀ (N w : ℕ) (encode : BasisLookup.Encoding N w) (_hN : 0 < N)
    (q : ℕ) (_hq : 4 * q ≤ N)
    (a : OutputExperiment.Algorithm N w) (_ha : a.base.queries ≤ q),
    let p := outputPurification encode a
    p.distance ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) ∧
      OutputExperiment.Dist encode q ≤ 4 * (q : ℝ) / Real.sqrt (N : ℝ) ∧
      ∀ P : Submodule ℂ (EuclideanSpace ℂ (Fin (Fintype.card a.Output))),
        |‖project P p.exactVector‖ - ‖project P p.compressedVector‖| ≤
          OutputExperiment.Dist encode q

end QuantumOracle
