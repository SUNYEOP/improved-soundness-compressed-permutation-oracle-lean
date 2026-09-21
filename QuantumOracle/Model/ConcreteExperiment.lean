import QuantumOracle.Model.ConcreteAlgorithm
import QuantumOracle.Model.CompressedExecution
import QuantumOracle.Model.FinitePurification
import QuantumOracle.Model.ProductReduction

/-!
# Actual paired experiments and their operational distance

The same finite algorithm is run against the exact and compressed oracles.
Both final reductions and common purifications are constructed internally.
The distance is the supremum over these algorithms of the original infimum
over all finite common normalized purifications. No proposed error bound
appears in the definitions, and no harmonic comparison is assumed.
-/

noncomputable section

namespace QuantumOracle.ConcreteExperiment

open PermutationExtensions FinitePurification

variable {N w : ℕ}

def exactVector (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    EuclideanSpace ℂ (a.Workspace × Perm N) :=
  ExactExecution.run encode a.marked a.gates a.initial a.queries

def compressedVector (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    EuclideanSpace ℂ (a.Workspace × Database N) :=
  CompressedExecution.run encode a.marked a.gates a.initial a.queries

theorem exactVector_normalized (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    ‖exactVector encode a‖ = 1 :=
  ExactExecution.run_normalized encode a.marked a.gates a.initial a.normalized a.queries

theorem compressedVector_normalized (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    ‖compressedVector encode a‖ = 1 :=
  CompressedExecution.run_normalized encode a.marked a.gates a.initial a.normalized a.queries

def exactFinal (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    ReducedState (Fintype.card a.Workspace) := reducedFin (exactVector encode a)

def compressedFinal (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    ReducedState (Fintype.card a.Workspace) := reducedFin (compressedVector encode a)

/-- An explicit common-space purification, used for existence and elementary bounds.
The comparison pair used for soundness is defined in `SoundnessPurification`. -/
def purification (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    CommonPurification (exactFinal encode a) (compressedFinal encode a) :=
  anyHidden (exactVector encode a) (compressedVector encode a)
    (exactVector_normalized encode a) (compressedVector_normalized encode a)

/-- The experiment-family interface instantiated by actual oracle runs. -/
def family (encode : BasisLookup.Encoding N w) : ExperimentFamily (Algorithm N w) where
  queries a := a.queries
  workspaceDim a := Fintype.card a.Workspace
  exactFinal := exactFinal encode
  compressedFinal := compressedFinal encode
  hasPurifications a := ⟨purification encode a⟩

/-- Operational distance for the implemented finite pure/unitary algorithm class. -/
def Dist (encode : BasisLookup.Encoding N w) (q : ℕ) : ℝ := (family encode).Dist q

theorem dist_def (encode : BasisLookup.Encoding N w) (q : ℕ) :
    Dist encode q = sSup {r : ℝ | ∃ a : Algorithm N w, a.queries ≤ q ∧
      r = purificationDistance (exactFinal encode a) (compressedFinal encode a)} := rfl

theorem algorithm_distance_nonneg (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    0 ≤ purificationDistance (exactFinal encode a) (compressedFinal encode a) :=
  purificationDistance_nonneg ⟨purification encode a⟩

theorem algorithm_distance_le_two (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    purificationDistance (exactFinal encode a) (compressedFinal encode a) ≤ 2 :=
  (purificationDistance_le_witness (purification encode a)).trans
    (purification encode a).distance_le_two

theorem distances_bddAbove (encode : BasisLookup.Encoding N w) (q : ℕ) :
    BddAbove {r : ℝ | ∃ a : Algorithm N w, a.queries ≤ q ∧
      r = purificationDistance (exactFinal encode a) (compressedFinal encode a)} := by
  refine ⟨2, ?_⟩
  rintro r ⟨a, _, rfl⟩
  exact algorithm_distance_le_two encode a

theorem distances_nonempty (encode : BasisLookup.Encoding N w) (hN : 0 < N) (q : ℕ) :
    {r : ℝ | ∃ a : Algorithm N w, a.queries ≤ q ∧
      r = purificationDistance (exactFinal encode a) (compressedFinal encode a)}.Nonempty := by
  obtain ⟨a, ha⟩ := exists_algorithm_le (w := w) hN q
  exact ⟨_, a, ha, rfl⟩

theorem algorithm_distance_le_dist (encode : BasisLookup.Encoding N w) (q : ℕ)
    (a : Algorithm N w) (ha : a.queries ≤ q) :
    purificationDistance (exactFinal encode a) (compressedFinal encode a) ≤ Dist encode q :=
  le_csSup (distances_bddAbove encode q) ⟨a, ha, rfl⟩

theorem dist_nonneg (encode : BasisLookup.Encoding N w) (hN : 0 < N) (q : ℕ) :
    0 ≤ Dist encode q := by
  obtain ⟨a, ha⟩ := exists_algorithm_le (w := w) hN q
  exact (algorithm_distance_nonneg encode a).trans (algorithm_distance_le_dist encode q a ha)

theorem dist_le_two (encode : BasisLookup.Encoding N w) (hN : 0 < N) (q : ℕ) :
    Dist encode q ≤ 2 := by
  rw [dist_def]
  apply csSup_le (distances_nonempty encode hN q)
  rintro r ⟨a, _, rfl⟩
  exact algorithm_distance_le_two encode a

theorem dist_mono (encode : BasisLookup.Encoding N w) (hN : 0 < N)
    {q r : ℕ} (hqr : q ≤ r) : Dist encode q ≤ Dist encode r := by
  rw [dist_def]
  apply csSup_le (distances_nonempty encode hN q)
  rintro s ⟨a, ha, rfl⟩
  exact algorithm_distance_le_dist encode r a (ha.trans hqr)

/-- No-query executions have identical observable states despite different hidden registers. -/
theorem reduced_eq_of_zero_queries (encode : BasisLookup.Encoding N w)
    (a : Algorithm N w) (ha : a.queries = 0) :
    HiddenIsometry.reduced (exactVector encode a) =
      HiddenIsometry.reduced (compressedVector encode a) := by
  classical
  simp only [exactVector, compressedVector, ha, ExactExecution.run, CompressedExecution.run,
    CompressedExecution.initial_eq_productState]
  change HiddenIsometry.reduced
      (WorkspaceKnowledge.onWorkspace (Perm N) (a.gates 0).toLinearMap
        (WorkspaceKnowledge.productState a.initial (ConsistentState.vector Database.empty))) = _
  rw [ProductReduction.onWorkspace_productState, ProductReduction.onWorkspace_productState]
  apply ProductReduction.reduced_productState_eq
  · exact ConsistentState.vector_norm _
  · simp

theorem final_eq_of_zero_queries (encode : BasisLookup.Encoding N w)
    (a : Algorithm N w) (ha : a.queries = 0) : exactFinal encode a = compressedFinal encode a := by
  unfold exactFinal compressedFinal reducedFin
  rw [reduced_eq_of_zero_queries encode a ha]

theorem algorithm_distance_zero (encode : BasisLookup.Encoding N w)
    (a : Algorithm N w) (ha : a.queries = 0) :
    purificationDistance (exactFinal encode a) (compressedFinal encode a) = 0 := by
  rw [← final_eq_of_zero_queries encode a ha]
  exact purificationDistance_self (exactVector encode a) (exactVector_normalized encode a)

/-- The operational distance is exactly zero with no oracle calls. -/
theorem dist_zero (encode : BasisLookup.Encoding N w) (hN : 0 < N) : Dist encode 0 = 0 := by
  apply le_antisymm ?_ (dist_nonneg encode hN 0)
  rw [dist_def]
  apply csSup_le (distances_nonempty encode hN 0)
  rintro r ⟨a, ha, rfl⟩
  exact (algorithm_distance_zero encode a (Nat.eq_zero_of_le_zero ha)).le

/-- A hidden isometry and a uniform bound on the paired final vectors imply
an operational distance bound. `FiniteSoundnessWitness` proves the required
vector estimate for the polar embedding. -/
theorem dist_le_of_hidden_comparison (encode : BasisLookup.Encoding N w)
    (hN : 0 < N) (q : ℕ) (R : ℝ)
    (W : EuclideanSpace ℂ (Perm N) →ₗᵢ[ℂ] EuclideanSpace ℂ (Database N))
    (h : ∀ a : Algorithm N w, a.queries ≤ q →
      ‖HiddenIsometry.onOracle a.Workspace W (exactVector encode a) -
        compressedVector encode a‖ ≤ R) : Dist encode q ≤ R := by
  rw [dist_def]
  apply csSup_le (distances_nonempty encode hN q)
  rintro r ⟨a, ha, rfl⟩
  exact (purificationDistance_le_hiddenIsometry W (exactVector encode a)
    (compressedVector encode a) (exactVector_normalized encode a)
    (compressedVector_normalized encode a)).trans (h a ha)

end QuantumOracle.ConcreteExperiment
