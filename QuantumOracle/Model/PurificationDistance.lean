import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum

/-!
Finite-dimensional semantics for Section 2.4, eq:dist-definition.

The arguments are final reduced matrices supplied by an experiment family.
The infimum ranges over every finite common ancilla dimension and all normalized
vectors with the prescribed reductions. No equivalence with the range of
arbitrary Hilbert-space purifications is asserted.
-/

noncomputable section

namespace QuantumOracle

abbrev PureState (d n : ℕ) := EuclideanSpace ℂ (Fin d × Fin n)
abbrev ReducedState (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- Partial trace of the rank-one matrix `|ψ⟩⟨ψ|` over the common ancilla. -/
def reducedState {d n : ℕ} (ψ : PureState d n) : ReducedState d :=
  fun i j => ∑ a : Fin n, ψ (i, a) * star (ψ (j, a))

/-- An actual pair of normalized purifications of the given reduced states.
The common ambient space is part of the witness. -/
structure CommonPurification {d : ℕ} (ρ σ : ReducedState d) where
  ancillaDim : ℕ
  exactVector : PureState d ancillaDim
  compressedVector : PureState d ancillaDim
  exact_normalized : ‖exactVector‖ = 1
  compressed_normalized : ‖compressedVector‖ = 1
  exact_reduction : reducedState exactVector = ρ
  compressed_reduction : reducedState compressedVector = σ

def CommonPurification.distance {d : ℕ} {ρ σ : ReducedState d}
    (p : CommonPurification ρ σ) : ℝ :=
  ‖p.exactVector - p.compressedVector‖

theorem CommonPurification.distance_nonneg {d : ℕ} {ρ σ : ReducedState d}
    (p : CommonPurification ρ σ) : 0 ≤ p.distance := norm_nonneg _

theorem CommonPurification.distance_le_two {d : ℕ} {ρ σ : ReducedState d}
    (p : CommonPurification ρ σ) : p.distance ≤ 2 := by
  calc
    p.distance ≤ ‖p.exactVector‖ + ‖p.compressedVector‖ := norm_sub_le _ _
    _ = 2 := by rw [p.exact_normalized, p.compressed_normalized]; norm_num

/-- The infimum is over purifications, and is independent of any proposed bound. -/
def purificationDistance {d : ℕ} (ρ σ : ReducedState d) : ℝ :=
  sInf (Set.range (CommonPurification.distance (ρ := ρ) (σ := σ)))

theorem purificationDistances_bddBelow {d : ℕ} (ρ σ : ReducedState d) :
    BddBelow (Set.range (CommonPurification.distance (ρ := ρ) (σ := σ))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact p.distance_nonneg

theorem purificationDistance_le_witness {d : ℕ} {ρ σ : ReducedState d}
    (p : CommonPurification ρ σ) : purificationDistance ρ σ ≤ p.distance :=
  csInf_le (purificationDistances_bddBelow ρ σ) (Set.mem_range_self p)

theorem purificationDistance_nonneg {d : ℕ} {ρ σ : ReducedState d}
    (hex : Nonempty (CommonPurification ρ σ)) : 0 ≤ purificationDistance ρ σ := by
  obtain ⟨p⟩ := hex
  apply le_csInf ⟨p.distance, Set.mem_range_self p⟩
  rintro _ ⟨p', rfl⟩
  exact p'.distance_nonneg

/-- An interface for a family of final reduced states and query counts.
`ConcreteExperiment.family` instantiates it with algorithms and oracle runs. -/
structure ExperimentFamily (Algorithm : Type*) where
  queries : Algorithm → ℕ
  workspaceDim : Algorithm → ℕ
  exactFinal : (a : Algorithm) → ReducedState (workspaceDim a)
  compressedFinal : (a : Algorithm) → ReducedState (workspaceDim a)
  hasPurifications : ∀ a, Nonempty (CommonPurification (exactFinal a) (compressedFinal a))

/-- Section 2.4's supremum/infimum construction for a supplied experiment family.
No soundness upper bound appears in this definition. -/
def ExperimentFamily.Dist {Algorithm : Type*} (F : ExperimentFamily Algorithm) (q : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ a, F.queries a ≤ q ∧
    r = purificationDistance (F.exactFinal a) (F.compressedFinal a)}

/-- The final supremum/infimum step, conditional on honest witnesses for every
admissible algorithm. Nonemptiness is explicit to avoid empty real suprema. -/
theorem ExperimentFamily.dist_le_of_witnesses {Algorithm : Type*}
    (F : ExperimentFamily Algorithm) (q : ℕ) (R : ℝ)
    (hne : ∃ a, F.queries a ≤ q)
    (hw : ∀ a, F.queries a ≤ q →
      ∃ p : CommonPurification (F.exactFinal a) (F.compressedFinal a), p.distance ≤ R) :
    F.Dist q ≤ R := by
  apply csSup_le
  · obtain ⟨a, ha⟩ := hne
    exact ⟨_, a, ha, rfl⟩
  · rintro r ⟨a, ha, rfl⟩
    obtain ⟨p, hp⟩ := hw a ha
    exact (purificationDistance_le_witness p).trans hp

end QuantumOracle
