import QuantumOracle.Proof.HookRatioBounds

/-!
# Cancellation of row factors under actual corner deletion

The row product is built from actual tail column lengths. Its quotient under
decreasing the first-row length gives the first-row product bounded in
`HookRatioBounds`. Actual corner deletion changes only its own column and
gives the tail-corner ratio. This module does not identify the row product
with a Gram eigenvalue or an oracle overlap.
-/

noncomputable section

namespace QuantumOracle.HookRatioProducts

open AtlasKnownTheorems.HookLengthFormula HookRatioBounds
open scoped BigOperators

attribute [local instance] Classical.propDecidable

def rowFactor (a : ℕ) (θ : YoungDiagram) (j : ℕ) : ℝ :=
  ((a : ℝ) - j + θ.colLen j) / ((a : ℝ) - j)

/-- The normalized first-row factors determined by the actual tail diagram. -/
def normalizedRowProduct (a : ℕ) (θ : YoungDiagram) : ℝ :=
  ∏ j ∈ Finset.range (θ.rowLen 0), rowFactor a θ j

theorem rowFactor_pos (a : ℕ) (θ : YoungDiagram) {j : ℕ} (hj : j < a) :
    0 < rowFactor a θ j := by
  have hj' : (j : ℝ) < a := by exact_mod_cast hj
  unfold rowFactor
  exact div_pos (by positivity) (sub_pos.mpr hj')

theorem normalizedRowProduct_pos (a : ℕ) (θ : YoungDiagram) (ha : θ.rowLen 0 ≤ a) :
    0 < normalizedRowProduct a θ :=
  Finset.prod_pos (fun _ hj => rowFactor_pos a θ ((Finset.mem_range.mp hj).trans_le ha))

theorem normalizedRowProduct_firstRow_ratio (a : ℕ) (θ : YoungDiagram)
    (ha : θ.card < a) :
    normalizedRowProduct a θ / normalizedRowProduct (a - 1) θ = firstRowRatioSq a θ := by
  unfold normalizedRowProduct firstRowRatioSq
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hjc : j < θ.card := column_index_lt_card θ (Finset.mem_range.mp hj)
  have ha1 : 1 ≤ a := by omega
  have hj' : (j : ℝ) + 1 < a := by exact_mod_cast (show j + 1 < a by omega)
  have hh : 0 < (θ.colLen j : ℝ) := by
    exact_mod_cast colLen_pos_of_lt_rowLen θ (Finset.mem_range.mp hj)
  unfold rowFactor firstRowDefect
  rw [Nat.cast_sub ha1, Nat.cast_one]
  have hA : (a : ℝ) - j ≠ 0 := by linarith
  have hB : (a : ℝ) - 1 - j ≠ 0 := by linarith
  have hC : (a : ℝ) - 1 - j + θ.colLen j ≠ 0 := by linarith
  have hD : (a : ℝ) - j - 1 + θ.colLen j ≠ 0 := by linarith
  field_simp
  ring

theorem colLen_eq_zero_of_ge (θ : YoungDiagram) {j : ℕ} (hj : θ.rowLen 0 ≤ j) :
    θ.colLen j = 0 := by
  by_contra h
  have hmem : (0, j) ∈ θ := YoungDiagram.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero h)
  have := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  omega

theorem normalizedRowProduct_eq_prod (a : ℕ) (θ : YoungDiagram) {m : ℕ}
    (hm : θ.rowLen 0 ≤ m) (hma : m ≤ a) :
    normalizedRowProduct a θ = ∏ j ∈ Finset.range m, rowFactor a θ j := by
  apply Finset.prod_subset (Finset.range_mono hm)
  intro j hj hjnot
  have hj' : (j : ℝ) < a := by
    exact_mod_cast (Finset.mem_range.mp hj).trans_le hma
  have hz := colLen_eq_zero_of_ge θ (by simpa only [Finset.mem_range, not_lt] using hjnot)
  simp only [rowFactor, hz, Nat.cast_zero, add_zero, div_self (sub_ne_zero.mpr (ne_of_gt hj'))]

theorem colLen_eraseCorner_of_ne (θ : YoungDiagram) (c : CornerCells θ) {j : ℕ}
    (hj : j ≠ c.1.val.2) : (eraseCorner θ c.1 c.2).colLen j = θ.colLen j := by
  rw [YoungDiagram.colLen_eq_card, YoungDiagram.colLen_eq_card]
  congr 1
  ext d
  simp only [YoungDiagram.col, eraseCorner_cells, Finset.mem_filter, Finset.mem_erase]
  aesop

theorem colLen_eraseCorner_add_one (θ : YoungDiagram) (c : CornerCells θ) :
    (eraseCorner θ c.1 c.2).colLen c.1.val.2 + 1 = θ.colLen c.1.val.2 := by
  rw [YoungDiagram.colLen_eq_card, YoungDiagram.colLen_eq_card]
  change ((θ.cells.erase c.1.val).filter (fun d => d.2 = c.1.val.2)).card + 1 = _
  rw [Finset.filter_erase]
  apply Finset.card_erase_add_one
  exact Finset.mem_filter.mpr ⟨c.1.property, rfl⟩

theorem rowLen_eraseCorner_le (θ : YoungDiagram) (c : CornerCells θ) :
    (eraseCorner θ c.1 c.2).rowLen 0 ≤ θ.rowLen 0 := by
  by_contra! h
  have hmem : (0, θ.rowLen 0) ∈ eraseCorner θ c.1 c.2 :=
    YoungDiagram.mem_iff_lt_rowLen.mpr h
  have hmem' : (0, θ.rowLen 0) ∈ θ :=
    ((mem_eraseCorner_cells_iff θ c.1 c.2 _).mp hmem).1
  exact (lt_irrefl _) (YoungDiagram.mem_iff_lt_rowLen.mp hmem')

/-- Actual corner deletion changes exactly one row factor. -/
theorem normalizedRowProduct_tailCorner_ratio (a : ℕ) (θ : YoungDiagram)
    (ha : θ.card < a) (c : CornerCells θ) :
    normalizedRowProduct a (eraseCorner θ c.1 c.2) / normalizedRowProduct a θ =
      tailCornerRatioSq a θ c := by
  have hwidth : θ.rowLen 0 ≤ a := (rowLen_zero_le_card θ).trans ha.le
  rw [normalizedRowProduct_eq_prod a (eraseCorner θ c.1 c.2)
    (rowLen_eraseCorner_le θ c) hwidth]
  unfold normalizedRowProduct
  rw [← Finset.prod_div_distrib]
  rw [Finset.prod_eq_single c.1.val.2]
  · have hheight := colLen_eraseCorner_add_one θ c
    have hheight' : ((eraseCorner θ c.1 c.2).colLen c.1.val.2 : ℝ) + 1 =
        θ.colLen c.1.val.2 := by exact_mod_cast hheight
    have hj : (c.1.val.2 : ℝ) < a := by
      exact_mod_cast (corner_column_lt_rowLen θ c).trans_le hwidth
    have hA : (a : ℝ) - c.1.val.2 ≠ 0 := by linarith
    have hB : (a : ℝ) - c.1.val.2 + θ.colLen c.1.val.2 ≠ 0 := by
      have : (0 : ℝ) ≤ θ.colLen c.1.val.2 := by positivity
      linarith
    unfold rowFactor tailCornerRatioSq
    field_simp
    nlinarith
  · intro j hj hjc
    have hp : rowFactor a θ j ≠ 0 := ne_of_gt
      (rowFactor_pos a θ ((Finset.mem_range.mp hj).trans_le hwidth))
    simp only [rowFactor, colLen_eraseCorner_of_ne θ c hjc] at hp ⊢
    exact div_self hp
  · intro hc
    exact False.elim (hc (Finset.mem_range.mpr (corner_column_lt_rowLen θ c)))

/-- The first-row quotient inherits the proved diagram-dependent product estimate. -/
theorem firstRow_quotient_deficit_bound (a : ℕ) (θ : YoungDiagram) (ha : θ.card < a) :
    1 - normalizedRowProduct a θ / normalizedRowProduct (a - 1) θ ≤
      (θ.card : ℝ) / ((a : ℝ) - θ.card + 1) ^ 2 := by
  rw [normalizedRowProduct_firstRow_ratio a θ ha]
  exact firstRow_deficit_bound a θ ha

/-- The quotient under an actual corner deletion has the tail-corner estimate. -/
theorem tailCorner_quotient_deficit_bound (a : ℕ) (θ : YoungDiagram) (ha : θ.card < a)
    (c : CornerCells θ) :
    1 - normalizedRowProduct a (eraseCorner θ c.1 c.2) / normalizedRowProduct a θ ≤
      1 / ((a : ℝ) - θ.card + 2) := by
  rw [normalizedRowProduct_tailCorner_ratio a θ ha c]
  exact tailCorner_deficit_bound a θ ha c

theorem firstRow_quotient_deficit_le_two_div {N : ℕ} (θ : YoungDiagram) (hN : 0 < N)
    (hrange : 4 * θ.card ≤ N) :
    1 - normalizedRowProduct (N - θ.card) θ /
      normalizedRowProduct (N - θ.card - 1) θ ≤ 2 / (N : ℝ) := by
  rw [normalizedRowProduct_firstRow_ratio (N - θ.card) θ (by omega)]
  exact firstRow_deficit_le_two_div θ hN hrange

theorem tailCorner_quotient_deficit_le_two_div {N : ℕ} (θ : YoungDiagram) (hN : 0 < N)
    (hrange : 4 * θ.card ≤ N) (c : CornerCells θ) :
    1 - normalizedRowProduct (N - θ.card) (eraseCorner θ c.1 c.2) /
      normalizedRowProduct (N - θ.card) θ ≤ 2 / (N : ℝ) := by
  rw [normalizedRowProduct_tailCorner_ratio (N - θ.card) θ (by omega) c]
  exact tailCorner_deficit_le_two_div θ hN hrange c

end QuantumOracle.HookRatioProducts
