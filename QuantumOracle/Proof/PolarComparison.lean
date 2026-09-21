import QuantumOracle.Model.PolarEmbedding
import QuantumOracle.Proof.OutputComparison

/-!
# Actual paired-execution comparison using the constructed polar isometry

The hidden isometry and its uniform-to-empty initialization identity are now
constructed internally. Only the actual local query error remains a comparison
hypothesis. No sharp numerical estimate or identification with the manuscript's
scalar spectral formula is assumed in the definition of this error.
-/

noncomputable section

namespace QuantumOracle.PolarComparison

open ConcreteExperiment

variable {N w : ℕ}

/-- Difference of the two actual next-query operations on an actual exact prefix,
using the concrete positive polar embedding. -/
def localError (encode : BasisLookup.Encoding N w) (a : Algorithm N w) (j : ℕ) : ℝ :=
  ConcreteHybrid.localError encode (PolarEmbedding.candidate N) a j

/-- The concrete initial identity and all step isometries are discharged internally. -/
theorem run_error_le (encode : BasisLookup.Encoding N w) (a : Algorithm N w)
    (q : ℕ) (ε : ℝ) (hlocal : ∀ j < q, localError encode a j ≤ ε) :
    ‖HiddenIsometry.onOracle a.Workspace (PolarEmbedding.candidate N)
        (ExactExecution.run encode a.marked a.gates a.initial q) -
      CompressedExecution.run encode a.marked a.gates a.initial q‖ ≤ (q : ℝ) * ε :=
  ConcreteHybrid.run_error_le encode (PolarEmbedding.candidate N)
    (PolarEmbedding.candidate_uniform N) a q ε hlocal

theorem vector_error_le (encode : BasisLookup.Encoding N w) (a : Algorithm N w)
    (ε : ℝ) (hlocal : ∀ j < a.queries, localError encode a j ≤ ε) :
    ‖HiddenIsometry.onOracle a.Workspace (PolarEmbedding.candidate N)
        (exactVector encode a) - compressedVector encode a‖ ≤ (a.queries : ℝ) * ε :=
  run_error_le encode a a.queries ε hlocal

/-- For all finite output choices, the only remaining quantitative premise is
the local error bound for this fixed, actually constructed comparison map. -/
theorem dist_le_of_local_error (encode : BasisLookup.Encoding N w) (hN : 0 < N)
    (q : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hlocal : ∀ a : Algorithm N w, a.queries ≤ q →
      ∀ j < a.queries, localError encode a j ≤ ε) :
    OutputExperiment.Dist encode q ≤ (q : ℝ) * ε :=
  OutputExperiment.dist_le_of_local_error encode hN (PolarEmbedding.candidate N)
    (PolarEmbedding.candidate_uniform N) q ε hε hlocal

end QuantumOracle.PolarComparison
