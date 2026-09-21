import QuantumOracle.Model.OutputExperiment
import QuantumOracle.Proof.ConcreteHybrid

/-! # Local comparison bounds for chosen final outputs

The model of output experiments is independent of this hybrid argument. Here a
local query comparison is converted into an operational-distance bound. The
main proof later supplies the polar comparison and its numerical estimate.
-/

noncomputable section

namespace QuantumOracle.OutputExperiment

open PermutationExtensions

variable {N w : ℕ}

/-- The same local comparison controls every chosen final output. This modular
lemma accepts the comparison map and its error bound; `ImprovedSoundness.soundness`
discharges these inputs for the actual polar map and proves the numerical bound. -/
theorem dist_le_of_local_error (encode : BasisLookup.Encoding N w) (hN : 0 < N)
    (W : EuclideanSpace ℂ (Perm N) →ₗᵢ[ℂ] EuclideanSpace ℂ (Database N))
    (hinit : W (ConsistentState.vector Database.empty) = EuclideanSpace.single Database.empty 1)
    (q : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hlocal : ∀ a : ConcreteExperiment.Algorithm N w, a.queries ≤ q →
      ∀ j < a.queries, ConcreteHybrid.localError encode W a j ≤ ε) :
    Dist encode q ≤ (q : ℝ) * ε := by
  rw [dist_eq_retained encode hN]
  exact ConcreteHybrid.dist_le_of_local_error encode hN W hinit q ε hε hlocal

end QuantumOracle.OutputExperiment
