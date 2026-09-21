import QuantumOracle.Proof.YoungHookRatio
import QuantumOracle.Proof.OverlapBounds

/-!
# Bounds for the actual column-height hook-ratio products

The factors are formed from the column lengths of an actual Young diagram.
Their mass, positivity and index bounds are proved from the diagram, rather
than supplied as hypotheses. The final inequalities reuse `OverlapBounds`.
No identification with oracle overlaps or Gram eigenvalues is asserted here.
-/

noncomputable section

namespace QuantumOracle.HookRatioBounds

open AtlasKnownTheorems.HookLengthFormula
open scoped BigOperators

theorem rowLen_zero_le_card (θ : YoungDiagram) : θ.rowLen 0 ≤ θ.card := by
  rw [YoungDiagram.rowLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem sum_colLen (θ : YoungDiagram) :
    ∑ j ∈ Finset.range (θ.rowLen 0), θ.colLen j = θ.card := by
  have hcard : θ.transpose.card = θ.card := by
    simp [YoungDiagram.card, YoungDiagram.transpose]
  simpa only [YoungDiagram.colLen_transpose, YoungDiagram.rowLen_transpose, hcard] using
    (card_eq_sum_rowLen θ.transpose).symm

theorem colLen_pos_of_lt_rowLen (θ : YoungDiagram) {j : ℕ}
    (hj : j < θ.rowLen 0) : 0 < θ.colLen j :=
  YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hj)

theorem column_index_lt_card (θ : YoungDiagram) {j : ℕ}
    (hj : j < θ.rowLen 0) : j < θ.card :=
  hj.trans_le (rowLen_zero_le_card θ)

/-- The manuscript's first-row factor, with zero-based column index `j`. -/
def firstRowDefect (a : ℕ) (θ : YoungDiagram) (j : ℕ) : ℝ :=
  (θ.colLen j : ℝ) /
    (((a : ℝ) - j) * ((a : ℝ) - j - 1 + θ.colLen j))

/-- The product built from the actual tail diagram's column heights. -/
def firstRowRatioSq (a : ℕ) (θ : YoungDiagram) : ℝ :=
  ∏ j ∈ Finset.range (θ.rowLen 0), (1 - firstRowDefect a θ j)

private theorem column_bounds (a : ℕ) (θ : YoungDiagram) (ha : θ.card < a)
    {j : ℕ} (hj : j < θ.rowLen 0) :
    1 ≤ (θ.colLen j : ℝ) ∧
      1 ≤ (a : ℝ) - θ.card + 1 ∧
      (a : ℝ) - θ.card + 1 ≤ (a : ℝ) - j ∧
      (a : ℝ) - j ≤ (a : ℝ) - j - 1 + θ.colLen j := by
  have hheight : 1 ≤ θ.colLen j := colLen_pos_of_lt_rowLen θ hj
  have hjcard : j + 1 ≤ θ.card := column_index_lt_card θ hj
  have ha' : (θ.card : ℝ) < a := by exact_mod_cast ha
  have hh' : (1 : ℝ) ≤ θ.colLen j := by exact_mod_cast hheight
  have hj' : (j : ℝ) + 1 ≤ θ.card := by exact_mod_cast hjcard
  exact ⟨hh', by linarith, by linarith, by linarith⟩

theorem firstRowDefect_mem_Icc (a : ℕ) (θ : YoungDiagram) (ha : θ.card < a)
    {j : ℕ} (hj : j < θ.rowLen 0) : firstRowDefect a θ j ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hh, hd, hjb, hhb⟩ := column_bounds a θ ha hj
  have hA : 1 ≤ (a : ℝ) - j := hd.trans hjb
  have hB : 0 < (a : ℝ) - j - 1 + θ.colLen j := by linarith
  have hden : 0 < ((a : ℝ) - j) * ((a : ℝ) - j - 1 + θ.colLen j) :=
    mul_pos (by linarith) hB
  refine ⟨div_nonneg (by positivity) hden.le, ?_⟩
  unfold firstRowDefect
  apply (div_le_one hden).mpr
  have hm := mul_nonneg (sub_nonneg.mpr hA)
    (show 0 ≤ (a : ℝ) - j - 1 + θ.colLen j by linarith)
  nlinarith

theorem firstRowDefect_le (a : ℕ) (θ : YoungDiagram) (ha : θ.card < a)
    {j : ℕ} (hj : j < θ.rowLen 0) :
    firstRowDefect a θ j ≤ (θ.colLen j : ℝ) / ((a : ℝ) - θ.card + 1) ^ 2 := by
  obtain ⟨hh, hd, hjb, hhb⟩ := column_bounds a θ ha hj
  have hprod : ((a : ℝ) - θ.card + 1) ^ 2 ≤
      ((a : ℝ) - j) * ((a : ℝ) - j - 1 + θ.colLen j) := by
    calc
      _ = ((a : ℝ) - θ.card + 1) * ((a : ℝ) - θ.card + 1) := sq _
      _ ≤ _ := mul_le_mul hjb (hjb.trans hhb) (by linarith) (by linarith)
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos (by linarith)) hprod

/-- The actual column mass supplies the numerator in the first-row product bound. -/
theorem firstRow_deficit_bound (a : ℕ) (θ : YoungDiagram) (ha : θ.card < a) :
    1 - firstRowRatioSq a θ ≤ (θ.card : ℝ) / ((a : ℝ) - θ.card + 1) ^ 2 := by
  calc
    _ ≤ ∑ j ∈ Finset.range (θ.rowLen 0), firstRowDefect a θ j :=
      one_sub_prod_one_sub_le_sum _ _ (fun j hj =>
        firstRowDefect_mem_Icc a θ ha (Finset.mem_range.mp hj))
    _ ≤ ∑ j ∈ Finset.range (θ.rowLen 0),
        (θ.colLen j : ℝ) / ((a : ℝ) - θ.card + 1) ^ 2 :=
      Finset.sum_le_sum (fun j hj => firstRowDefect_le a θ ha (Finset.mem_range.mp hj))
    _ = _ := by rw [← Finset.sum_div, ← Nat.cast_sum, sum_colLen]

/-- The tail-corner ratio uses the actual column and height of a removable cell. -/
def tailCornerRatioSq (a : ℕ) (θ : YoungDiagram) (c : CornerCells θ) : ℝ :=
  ((a : ℝ) - c.1.val.2 - 1 + θ.colLen c.1.val.2) /
    ((a : ℝ) - c.1.val.2 + θ.colLen c.1.val.2)

theorem corner_column_lt_rowLen (θ : YoungDiagram) (c : CornerCells θ) :
    c.1.val.2 < θ.rowLen 0 := by
  have hcell : c.1.val ∈ θ := c.1.property
  exact (YoungDiagram.mem_iff_lt_rowLen.mp hcell).trans_le
    (θ.rowLen_anti 0 c.1.val.1 (Nat.zero_le _))

/-- The actual corner's column lies within the tail and has positive height. -/
theorem tailCorner_deficit_bound (a : ℕ) (θ : YoungDiagram) (ha : θ.card < a)
    (c : CornerCells θ) :
    1 - tailCornerRatioSq a θ c ≤ 1 / ((a : ℝ) - θ.card + 2) := by
  obtain ⟨hh, hd, hjb, hhb⟩ := column_bounds a θ ha (corner_column_lt_rowLen θ c)
  have hbase : 0 < (a : ℝ) - θ.card + 2 := by linarith
  have hden : 0 < (a : ℝ) - c.1.val.2 + θ.colLen c.1.val.2 := by linarith
  have he : 1 - tailCornerRatioSq a θ c =
      1 / ((a : ℝ) - c.1.val.2 + θ.colLen c.1.val.2) := by
    unfold tailCornerRatioSq
    field_simp
    ring
  rw [he]
  exact one_div_le_one_div_of_le hbase (by linarith)

/-- Substituting the actual total size `N = a + |θ|` and the quarter-size range. -/
theorem firstRow_deficit_le_two_div {N : ℕ} (θ : YoungDiagram) (hN : 0 < N)
    (hrange : 4 * θ.card ≤ N) :
    1 - firstRowRatioSq (N - θ.card) θ ≤ 2 / (N : ℝ) := by
  have hcard : θ.card ≤ N := by omega
  have ha : θ.card < N - θ.card := by omega
  have h := firstRow_deficit_bound (N - θ.card) θ ha
  rw [Nat.cast_sub hcard] at h
  have he : (N : ℝ) - θ.card - θ.card + 1 = (N : ℝ) - 2 * θ.card + 1 := by ring
  rw [he] at h
  exact h.trans (first_row_scalar_bound (by exact_mod_cast hN) (by positivity)
    (by exact_mod_cast hrange))

theorem tailCorner_deficit_le_two_div {N : ℕ} (θ : YoungDiagram) (hN : 0 < N)
    (hrange : 4 * θ.card ≤ N) (c : CornerCells θ) :
    1 - tailCornerRatioSq (N - θ.card) θ c ≤ 2 / (N : ℝ) := by
  have hcard : θ.card ≤ N := by omega
  have ha : θ.card < N - θ.card := by omega
  have h := tailCorner_deficit_bound (N - θ.card) θ ha c
  rw [Nat.cast_sub hcard] at h
  have he : (N : ℝ) - θ.card - θ.card + 2 = (N : ℝ) - 2 * θ.card + 2 := by ring
  rw [he] at h
  exact h.trans (tail_corner_scalar_bound (by exact_mod_cast hN) (by exact_mod_cast hrange))

end QuantumOracle.HookRatioBounds
