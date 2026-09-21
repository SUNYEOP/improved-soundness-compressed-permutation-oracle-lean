import QuantumOracle.Model.ConcreteExperiment
import QuantumOracle.Model.OutputDiscard
import QuantumOracle.Model.DiscardDistance
import QuantumOracle.Model.FiniteDensity

/-!
# Actual experiments with a chosen observable output

An algorithm may discard any factor of its final workspace. The discarded
factor joins the hidden oracle register in an actual normalized purification.
The resulting operational distance still takes the infimum over all finite
common purifications and the supremum over all admissible algorithms.
-/

noncomputable section

namespace QuantumOracle.OutputExperiment

open PermutationExtensions FinitePurification OutputDiscard
open scoped ComplexOrder

variable {N w : ℕ}

/-- An implemented finite unitary algorithm together with its chosen final
output factor. Both finite basis types are data, allowing the entire original
workspace as a special case without changing its coordinate convention. -/
structure Algorithm (N w : ℕ) where
  base : ConcreteExperiment.Algorithm N w
  Output : Type
  Discard : Type
  outputFintype : Fintype Output
  discardFintype : Fintype Discard
  split : base.Workspace ≃ Output × Discard

attribute [instance] Algorithm.outputFintype Algorithm.discardFintype

/-- Every original algorithm is included by discarding a trivial register. -/
def keepAll (a : ConcreteExperiment.Algorithm N w) : Algorithm N w where
  base := a
  Output := a.Workspace
  Discard := Unit
  outputFintype := inferInstance
  discardFintype := inferInstance
  split := keepAllEquiv a.Workspace

def exactVector (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    EuclideanSpace ℂ (a.Output × (a.Discard × Perm N)) :=
  discardVector a.split (ConcreteExperiment.exactVector encode a.base)

def compressedVector (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    EuclideanSpace ℂ (a.Output × (a.Discard × Database N)) :=
  discardVector a.split (ConcreteExperiment.compressedVector encode a.base)

theorem exactVector_normalized (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    ‖exactVector encode a‖ = 1 :=
  (norm_discardVector _ _).trans (ConcreteExperiment.exactVector_normalized encode a.base)

theorem compressedVector_normalized (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    ‖compressedVector encode a‖ = 1 :=
  (norm_discardVector _ _).trans (ConcreteExperiment.compressedVector_normalized encode a.base)

def exactFinal (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    ReducedState (Fintype.card a.Output) := reducedFin (exactVector encode a)

def compressedFinal (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    ReducedState (Fintype.card a.Output) := reducedFin (compressedVector encode a)

theorem exactFinal_posSemidef (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    (exactFinal encode a).PosSemidef := FiniteDensity.reducedFin_posSemidef _

theorem compressedFinal_posSemidef (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    (compressedFinal encode a).PosSemidef := FiniteDensity.reducedFin_posSemidef _

theorem exactFinal_isHermitian (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    (exactFinal encode a).IsHermitian := (exactFinal_posSemidef encode a).isHermitian

theorem compressedFinal_isHermitian (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    (compressedFinal encode a).IsHermitian := (compressedFinal_posSemidef encode a).isHermitian

theorem exactFinal_trace_one (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    Matrix.trace (exactFinal encode a) = 1 :=
  FiniteDensity.trace_reducedFin_of_normalized _ (exactVector_normalized encode a)

theorem compressedFinal_trace_one (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    Matrix.trace (compressedFinal encode a) = 1 :=
  FiniteDensity.trace_reducedFin_of_normalized _ (compressedVector_normalized encode a)

theorem exactFinal_eq_discardMatrix (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    exactFinal encode a = discardMatrix a.split (ConcreteExperiment.exactFinal encode a.base) :=
  reducedFin_discardVector _ _

theorem compressedFinal_eq_discardMatrix (encode : BasisLookup.Encoding N w)
    (a : Algorithm N w) :
    compressedFinal encode a =
      discardMatrix a.split (ConcreteExperiment.compressedFinal encode a.base) :=
  reducedFin_discardVector _ _

@[simp] theorem exactFinal_keepAll (encode : BasisLookup.Encoding N w)
    (a : ConcreteExperiment.Algorithm N w) :
    exactFinal encode (keepAll a) = ConcreteExperiment.exactFinal encode a :=
  reducedFin_keepAll _

@[simp] theorem compressedFinal_keepAll (encode : BasisLookup.Encoding N w)
    (a : ConcreteExperiment.Algorithm N w) :
    compressedFinal encode (keepAll a) = ConcreteExperiment.compressedFinal encode a :=
  reducedFin_keepAll _

/-- Honest common purifications of the actual chosen outputs. -/
def purification (encode : BasisLookup.Encoding N w) (a : Algorithm N w) :
    CommonPurification (exactFinal encode a) (compressedFinal encode a) :=
  anyHidden (exactVector encode a) (compressedVector encode a)
    (exactVector_normalized encode a) (compressedVector_normalized encode a)

def family (encode : BasisLookup.Encoding N w) : ExperimentFamily (Algorithm N w) where
  queries a := a.base.queries
  workspaceDim a := Fintype.card a.Output
  exactFinal := exactFinal encode
  compressedFinal := compressedFinal encode
  hasPurifications a := ⟨purification encode a⟩

/-- The supremum now also ranges over all finite final output decompositions. -/
def Dist (encode : BasisLookup.Encoding N w) (q : ℕ) : ℝ := (family encode).Dist q

theorem dist_def (encode : BasisLookup.Encoding N w) (q : ℕ) :
    Dist encode q = sSup {r : ℝ | ∃ a : Algorithm N w, a.base.queries ≤ q ∧
      r = purificationDistance (exactFinal encode a) (compressedFinal encode a)} := rfl

theorem distances_bddAbove (encode : BasisLookup.Encoding N w) (q : ℕ) :
    BddAbove {r : ℝ | ∃ a : Algorithm N w, a.base.queries ≤ q ∧
      r = purificationDistance (exactFinal encode a) (compressedFinal encode a)} := by
  refine ⟨2, ?_⟩
  rintro r ⟨a, _, rfl⟩
  exact (purificationDistance_le_witness (purification encode a)).trans
    (purification encode a).distance_le_two

theorem distances_nonempty (encode : BasisLookup.Encoding N w) (hN : 0 < N) (q : ℕ) :
    {r : ℝ | ∃ a : Algorithm N w, a.base.queries ≤ q ∧
      r = purificationDistance (exactFinal encode a) (compressedFinal encode a)}.Nonempty := by
  obtain ⟨a, ha⟩ := ConcreteExperiment.exists_algorithm_le (w := w) hN q
  exact ⟨_, keepAll a, ha, rfl⟩

theorem algorithm_distance_le_dist (encode : BasisLookup.Encoding N w) (q : ℕ)
    (a : Algorithm N w) (ha : a.base.queries ≤ q) :
    purificationDistance (exactFinal encode a) (compressedFinal encode a) ≤ Dist encode q :=
  le_csSup (distances_bddAbove encode q) ⟨a, ha, rfl⟩

/-- Discarding private output registers cannot improve distinguishing distance. -/
theorem algorithm_distance_le_retained (encode : BasisLookup.Encoding N w)
    (a : Algorithm N w) :
    purificationDistance (exactFinal encode a) (compressedFinal encode a) ≤
      purificationDistance (ConcreteExperiment.exactFinal encode a.base)
        (ConcreteExperiment.compressedFinal encode a.base) := by
  rw [exactFinal_eq_discardMatrix, compressedFinal_eq_discardMatrix]
  exact DiscardDistance.purificationDistance_discard_le a.split
    ⟨ConcreteExperiment.purification encode a.base⟩

/-- The worst-case distance is unchanged by permitting arbitrary finite output
factors: partial trace decreases each distance, and keeping everything is allowed. -/
theorem dist_eq_retained (encode : BasisLookup.Encoding N w) (hN : 0 < N) (q : ℕ) :
    Dist encode q = ConcreteExperiment.Dist encode q := by
  apply le_antisymm
  · rw [dist_def]
    apply csSup_le (distances_nonempty encode hN q)
    rintro r ⟨a, ha, rfl⟩
    exact (algorithm_distance_le_retained encode a).trans
      (ConcreteExperiment.algorithm_distance_le_dist encode q a.base ha)
  · rw [ConcreteExperiment.dist_def]
    apply csSup_le (ConcreteExperiment.distances_nonempty encode hN q)
    rintro r ⟨a, ha, rfl⟩
    have h := algorithm_distance_le_dist encode q (keepAll a) ha
    rw [exactFinal_keepAll, compressedFinal_keepAll] at h
    exact h

theorem dist_nonneg (encode : BasisLookup.Encoding N w) (hN : 0 < N) (q : ℕ) :
    0 ≤ Dist encode q := by
  rw [dist_eq_retained encode hN]
  exact ConcreteExperiment.dist_nonneg encode hN q

theorem dist_le_two (encode : BasisLookup.Encoding N w) (hN : 0 < N) (q : ℕ) :
    Dist encode q ≤ 2 := by
  rw [dist_eq_retained encode hN]
  exact ConcreteExperiment.dist_le_two encode hN q

theorem dist_mono (encode : BasisLookup.Encoding N w) (hN : 0 < N)
    {q r : ℕ} (hqr : q ≤ r) : Dist encode q ≤ Dist encode r := by
  rw [dist_eq_retained encode hN, dist_eq_retained encode hN]
  exact ConcreteExperiment.dist_mono encode hN hqr

theorem dist_zero (encode : BasisLookup.Encoding N w) (hN : 0 < N) : Dist encode 0 = 0 := by
  rw [dist_eq_retained encode hN, ConcreteExperiment.dist_zero encode hN]

end QuantumOracle.OutputExperiment
