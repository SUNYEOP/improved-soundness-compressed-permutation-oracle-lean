import QuantumOracle.Proof.SpechtBranchingPaths
import QuantumOracle.Proof.SpechtTrivialMultiplicity
import QuantumOracle.Proof.SpechtLayers

/-!
# First-row support of the actual tuple multiplicities

One-corner branching can only shorten rows. Together with the actual
degree-zero invariant calculation, this forces the actual multiplicity to
vanish when the first row is shorter than the unrevealed permutation degree.
-/

noncomputable section

namespace QuantumOracle.SpechtMultiplicitySupport

open PermutationExtensions SpechtFoundation SpechtMultiplicity SpechtBranchingPaths
open scoped BigOperators Classical

/-- On a valid database level the actual Gram scalar vanishes exactly when
the actual tuple-intertwiner space has dimension zero. -/
theorem eigenvalue_eq_zero_iff_tupleMultiplicity_eq_zero (N t : ℕ) (ht : t ≤ N)
    (la : Nat.Partition N) :
    SpechtCharacter.eigenvalue N t la = 0 ↔ tupleMultiplicity N t la = 0 := by
  have hc : (N.choose t : ℂ) ≠ 0 := by exact_mod_cast Nat.choose_pos ht |>.ne'
  have hd : (Module.finrank ℂ (specht N la) : ℂ) ≠ 0 := by
    exact_mod_cast SpechtCharacter.dimension_ne_zero N la
  rw [eigenvalue_eq_choose_mul_multiplicity N t ht la]
  simp only [div_eq_zero_iff, hd, or_false, mul_eq_zero, hc, false_or, Nat.cast_eq_zero]

/-- Nonvanishing of the actual multiplicity propagates up the valid filtration. -/
theorem tupleMultiplicity_ne_zero_mono {N s t : ℕ} (la : Nat.Partition N)
    (hst : s ≤ t) (ht : t ≤ N) (hs : tupleMultiplicity N s la ≠ 0) :
    tupleMultiplicity N t la ≠ 0 := by
  have hes : SpechtCharacter.eigenvalue N s la ≠ 0 := by
    intro hz
    exact hs ((eigenvalue_eq_zero_iff_tupleMultiplicity_eq_zero N s (hst.trans ht) la).mp hz)
  have het := SpechtLayers.eigenvalue_ne_zero_mono la hst ht hes
  intro hz
  exact het ((eigenvalue_eq_zero_iff_tupleMultiplicity_eq_zero N t ht la).mpr hz)

theorem rowLen_le_of_mem_removeCorners {N : ℕ} (la : Nat.Partition N)
    (mu : Nat.Partition (N + 1)) (hla : la ∈ removeCorners mu) (i : ℕ) :
    (diagram la).rowLen i ≤ (diagram mu).rowLen i :=
  (RepresentationTheory.Auxiliary.PartitionPermutationRelations.YoungDiagram.le_iff_row_len_le.mp
    ((mem_removeCorners la mu).mp hla)) i

/-- The actual tuple multiplicity vanishes below the first-row threshold. -/
theorem tupleMultiplicity_eq_zero_of_rowLen_lt (N t : ℕ) (ht : t ≤ N)
    (la : Nat.Partition N) (hrow : (diagram la).rowLen 0 < N - t) :
    tupleMultiplicity N t la = 0 := by
  induction t generalizing N with
  | zero =>
    apply SpechtTrivialMultiplicity.tupleMultiplicity_zero_of_rowLen_lt N la
    simpa only [Nat.sub_zero] using hrow
  | succ t ih =>
    cases N with
    | zero => omega
    | succ N =>
      rw [tupleMultiplicity_succ N t (by omega)]
      apply Finset.sum_eq_zero
      intro mu hmu
      apply ih N (by omega) mu
      have hr := rowLen_le_of_mem_removeCorners mu la hmu 0
      omega

/-- Consequently the actual finite-character Gram eigenvalue is zero. -/
theorem eigenvalue_eq_zero_of_rowLen_lt (N t : ℕ) (ht : t ≤ N)
    (la : Nat.Partition N) (hrow : (diagram la).rowLen 0 < N - t) :
    SpechtCharacter.eigenvalue N t la = 0 := by
  rw [eigenvalue_eq_choose_mul_multiplicity N t ht la,
    tupleMultiplicity_eq_zero_of_rowLen_lt N t ht la hrow]
  simp

/-- The original Gram operator annihilates every vector of this actual Specht ideal. -/
theorem gram_eq_zero_of_rowLen_lt (N t : ℕ) (ht : t ≤ N)
    (la : Nat.Partition N) (hrow : (diagram la).rowLen 0 < N - t)
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ SpechtGram.space N la) :
    GramFiltration.gram N t h = 0 := by
  rw [SpechtCharacter.gram_eq_eigenvalue N t la hh,
    eigenvalue_eq_zero_of_rowLen_lt N t ht la hrow, zero_smul]

/-- At the minimal degree, all corner terms that shorten the first row vanish. -/
theorem tupleMultiplicity_succ_eq_sum_preserving_rowLen (N t : ℕ) (ht : t ≤ N)
    (mu : Nat.Partition (N + 1)) (hrow : (diagram mu).rowLen 0 = N - t) :
    tupleMultiplicity (N + 1) (t + 1) mu =
      ∑ la ∈ (removeCorners mu).filter
          (fun la => (diagram la).rowLen 0 = (diagram mu).rowLen 0),
        tupleMultiplicity N t la := by
  rw [tupleMultiplicity_succ N t ht, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro la hla
  by_cases heq : (diagram la).rowLen 0 = (diagram mu).rowLen 0
  · rw [if_pos heq]
  · rw [if_neg heq]
    apply tupleMultiplicity_eq_zero_of_rowLen_lt N t ht la
    have hr := rowLen_le_of_mem_removeCorners la mu hla 0
    omega

end QuantumOracle.SpechtMultiplicitySupport
