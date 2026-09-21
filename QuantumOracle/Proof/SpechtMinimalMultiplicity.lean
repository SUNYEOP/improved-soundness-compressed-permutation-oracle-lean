import QuantumOracle.Proof.SpechtMultiplicitySupport
import QuantumOracle.Proof.HookRowFactorization
import QuantumOracle.Proof.TailBranching

/-!
# The actual multiplicity at the first harmonic degree

The first-row complement is the size of the actual tail diagram. At this
degree the actual tuple multiplicity is computed by corner branching, with
the degree-zero case supplied by character orthogonality.
-/

noncomputable section

namespace QuantumOracle.SpechtMinimalMultiplicity

open SpechtFoundation SpechtMultiplicity HookRowFactorization
open AtlasKnownTheorems.HookLengthFormula
open scoped BigOperators Classical

theorem rowLen_add_tail_card (N : ℕ) (la : Nat.Partition N) :
    (diagram la).rowLen 0 + (tail (diagram la)).card = N := by
  rw [← card_eq_firstRow_add_tail, SpechtHookBridge.diagram_card]

theorem tail_card_le (N : ℕ) (la : Nat.Partition N) :
    (tail (diagram la)).card ≤ N := by
  have h := rowLen_add_tail_card N la
  omega

theorem tail_eq_bot_of_card_zero (μ : YoungDiagram) (h : (tail μ).card = 0) :
    tail μ = ⊥ := by
  apply YoungDiagram.ext
  exact Finset.card_eq_zero.mp h

/-- The empty-tail case of the actual minimal-degree multiplicity. -/
theorem tupleMultiplicity_minimal_of_tail_empty (N : ℕ) (la : Nat.Partition N)
    (ht : (tail (diagram la)).card = 0) :
    tupleMultiplicity N (tail (diagram la)).card la =
      standardTableauCount (tail (diagram la)) := by
  have hr : (diagram la).rowLen 0 = N := by
    have h := rowLen_add_tail_card N la
    omega
  rw [ht, SpechtTrivialMultiplicity.tupleMultiplicity_zero_eq_indicator, if_pos hr,
    tail_eq_bot_of_card_zero (diagram la) ht, standardTableauCount_bot]

/-- At its first possible degree, the actual tuple-intertwiner dimension is
the number of standard tableaux of the actual tail diagram. -/
theorem tupleMultiplicity_minimal (N : ℕ) (la : Nat.Partition N) :
    tupleMultiplicity N (tail (diagram la)).card la =
      standardTableauCount (tail (diagram la)) := by
  induction N with
  | zero =>
    apply tupleMultiplicity_minimal_of_tail_empty
    exact Nat.eq_zero_of_le_zero (tail_card_le 0 la)
  | succ N ih =>
    by_cases hz : (tail (diagram la)).card = 0
    · exact tupleMultiplicity_minimal_of_tail_empty (N + 1) la hz
    · obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hz
      have hr := rowLen_add_tail_card (N + 1) la
      have htle : t ≤ N := by omega
      have hrow : (diagram la).rowLen 0 = N - t := by omega
      rw [ht, SpechtMultiplicitySupport.tupleMultiplicity_succ_eq_sum_preserving_rowLen
        N t htle la hrow]
      calc
        _ = ∑ mu ∈ (removeCorners la).filter
            (fun mu => (diagram mu).rowLen 0 = (diagram la).rowLen 0),
            standardTableauCount (tail (diagram mu)) := by
          apply Finset.sum_congr rfl
          intro mu hmu
          have hrowmu := (Finset.mem_filter.mp hmu).2
          have hcardmu := rowLen_add_tail_card N mu
          have htm : (tail (diagram mu)).card = t := by omega
          simpa only [htm] using ih mu
        _ = ∑ c : CornerCells (tail (diagram la)),
            standardTableauCount (eraseCorner (tail (diagram la)) c.1 c.2) :=
          TailBranching.sum_preserving_firstRow la standardTableauCount
        _ = standardTableauCount (tail (diagram la)) :=
          (standardTableauCount_eq_sum_erased _ (Finset.card_pos.mp (Nat.pos_of_ne_zero hz))).symm

/-- The actual Gram scalar at the first harmonic degree is the actual
normalized first-row hook product. -/
theorem eigenvalue_minimal (N : ℕ) (la : Nat.Partition N) :
    SpechtCharacter.eigenvalue N (tail (diagram la)).card la =
      (HookRatioProducts.normalizedRowProduct ((diagram la).rowLen 0)
        (tail (diagram la)) : ℂ) := by
  rw [eigenvalue_eq_choose_mul_multiplicity N _ (tail_card_le N la) la,
    tupleMultiplicity_minimal, SpechtHookBridge.dimension_eq_proofAtlas_tableauCount]
  have h := choose_mul_tableauCount_ratio (diagram la)
  rw [SpechtHookBridge.diagram_card] at h
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast] using
    congrArg Complex.ofReal h

theorem eigenvalue_minimal_re_pos (N : ℕ) (la : Nat.Partition N) :
    0 < (SpechtCharacter.eigenvalue N (tail (diagram la)).card la).re := by
  rw [eigenvalue_minimal, Complex.ofReal_re]
  exact HookRatioProducts.normalizedRowProduct_pos _ _ (tail_rowLen_le _)

theorem eigenvalue_minimal_ne_zero (N : ℕ) (la : Nat.Partition N) :
    SpechtCharacter.eigenvalue N (tail (diagram la)).card la ≠ 0 :=
  (SpechtLayers.eigenvalue_re_pos_iff N _ la).mp (eigenvalue_minimal_re_pos N la)

/-- The first-row threshold is now exact for the actual intertwiner dimension. -/
theorem tupleMultiplicity_ne_zero_iff_tail_card_le (N t : ℕ) (ht : t ≤ N)
    (la : Nat.Partition N) :
    tupleMultiplicity N t la ≠ 0 ↔ (tail (diagram la)).card ≤ t := by
  constructor
  · intro hm
    by_contra htail
    have hr := rowLen_add_tail_card N la
    exact hm (SpechtMultiplicitySupport.tupleMultiplicity_eq_zero_of_rowLen_lt N t ht la
      (by omega))
  · intro htail
    apply SpechtMultiplicitySupport.tupleMultiplicity_ne_zero_mono la htail ht
    rw [tupleMultiplicity_minimal]
    exact YoungHookRatio.standardTableauCount_ne_zero _

theorem eigenvalue_ne_zero_iff_rowLen (N t : ℕ) (ht : t ≤ N)
    (la : Nat.Partition N) :
    SpechtCharacter.eigenvalue N t la ≠ 0 ↔ N - t ≤ (diagram la).rowLen 0 := by
  have hr := rowLen_add_tail_card N la
  rw [ne_eq, SpechtMultiplicitySupport.eigenvalue_eq_zero_iff_tupleMultiplicity_eq_zero N t ht la,
    ← ne_eq, tupleMultiplicity_ne_zero_iff_tail_card_le N t ht la]
  omega

/-- The constructed actual Specht space appears at precisely the manuscript's
first-row threshold in the actual knowledge filtration. -/
theorem space_le_K_iff_rowLen (N t : ℕ) (ht : t ≤ N) (la : Nat.Partition N) :
    SpechtGram.space N la ≤ KnowledgeSpace.K N t ↔ N - t ≤ (diagram la).rowLen 0 := by
  rw [SpechtLayers.space_le_K_iff, eigenvalue_ne_zero_iff_rowLen N t ht la]

/-- The entire constructed actual Specht space lies in the harmonic layer
indexed by the size of its actual tail. -/
theorem space_le_H_minimal (N : ℕ) (la : Nat.Partition N) :
    SpechtGram.space N la ≤ HarmonicLayers.H N (tail (diagram la)).card := by
  have he := eigenvalue_minimal_ne_zero N la
  cases ht : (tail (diagram la)).card with
  | zero =>
    apply (SpechtLayers.space_le_H_zero_iff N la).mpr
    simpa only [ht] using he
  | succ t =>
    apply (SpechtLayers.space_le_H_succ_iff N t la).mpr
    refine ⟨by simpa only [ht] using he, ?_⟩
    have hr := rowLen_add_tail_card N la
    apply SpechtMultiplicitySupport.eigenvalue_eq_zero_of_rowLen_lt N t (by omega) la
    omega

end QuantumOracle.SpechtMinimalMultiplicity
