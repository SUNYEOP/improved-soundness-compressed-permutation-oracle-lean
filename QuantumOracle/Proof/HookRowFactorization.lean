import QuantumOracle.Proof.HookRatioProducts
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Actual first-row and tail hook factorization

The tail is obtained by deleting the first row of an actual Young diagram and
shifting the remaining rows up. Hooks below the first row are unchanged. Thus
the full hook product factors into the first-row hooks and the tail hooks.
The actual first-row product divided by its row-length factorial is the
`normalizedRowProduct` previously bounded using actual column heights.
-/

noncomputable section

namespace QuantumOracle.HookRowFactorization

open AtlasKnownTheorems.HookLengthFormula HookRatioProducts
open scoped BigOperators

attribute [local instance] Classical.propDecidable

def shiftRow : (ℕ × ℕ) ↪ (ℕ × ℕ) where
  toFun p := (p.1 + 1, p.2)
  inj' := by
    intro p q hpq
    apply Prod.ext
    · exact Nat.add_right_cancel (congrArg Prod.fst hpq)
    · simpa only using congrArg (fun z : ℕ × ℕ => z.2) hpq

/-- Delete the actual first row and reindex every later row by one less. -/
def tail (μ : YoungDiagram) : YoungDiagram where
  cells := μ.cells.preimage shiftRow shiftRow.injective.injOn
  isLowerSet := by
    intro p q hpq hp
    simp only [Finset.mem_coe, Finset.mem_preimage] at hp ⊢
    apply μ.isLowerSet ?_ hp
    exact ⟨Nat.add_le_add_right hpq.1 1, hpq.2⟩

@[simp] theorem mem_tail (μ : YoungDiagram) (p : ℕ × ℕ) :
    p ∈ tail μ ↔ shiftRow p ∈ μ := by
  change p ∈ μ.cells.preimage shiftRow shiftRow.injective.injOn ↔ _
  exact Finset.mem_preimage

@[simp] theorem tail_rowLen (μ : YoungDiagram) (i : ℕ) :
    (tail μ).rowLen i = μ.rowLen (i + 1) := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_tail]
  exact YoungDiagram.mem_iff_lt_rowLen

@[simp] theorem tail_colLen (μ : YoungDiagram) (j : ℕ) :
    (tail μ).colLen j = μ.colLen j - 1 := by
  apply eq_of_forall_lt_iff
  intro i
  rw [← YoungDiagram.mem_iff_lt_colLen, mem_tail]
  change (i + 1, j) ∈ μ ↔ i < μ.colLen j - 1
  rw [YoungDiagram.mem_iff_lt_colLen]
  omega

theorem tail_rowLen_le (μ : YoungDiagram) : (tail μ).rowLen 0 ≤ μ.rowLen 0 := by
  rw [tail_rowLen]
  exact μ.rowLen_anti 0 1 (by omega)

theorem tail_map_cells (μ : YoungDiagram) :
    (tail μ).cells.map shiftRow = μ.cells.filter (fun p => p.1 ≠ 0) := by
  ext ⟨i, j⟩
  constructor
  · intro h
    obtain ⟨p, hp, hpq⟩ := Finset.mem_map.mp h
    have hm := (mem_tail μ p).mp hp
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · change (i, j) ∈ μ
      simpa only [hpq] using hm
    · have hi : p.1 + 1 = i := congrArg Prod.fst hpq
      omega
  · intro h
    obtain ⟨hm, hi⟩ := Finset.mem_filter.mp h
    cases i with
    | zero => exact False.elim (hi rfl)
    | succ i =>
      refine Finset.mem_map.mpr ⟨(i, j), ?_, rfl⟩
      exact (mem_tail μ (i, j)).mpr hm

/-- The usual hook statistic on coordinates; equality with actual hook cardinality
is asserted only for cells of the diagram. -/
def hookAt (μ : YoungDiagram) (p : ℕ × ℕ) : ℕ :=
  (μ.rowLen p.1 - p.2) + (μ.colLen p.2 - p.1) - 1

theorem hookLength_eq_hookAt (μ : YoungDiagram) (c : Cell μ) :
    hookLength μ c = hookAt μ c.val :=
  hookLength_eq_rowLen_sub_add_colLen_sub_sub_one μ c

theorem hookProduct_eq_prod_hookAt (μ : YoungDiagram) :
    hookProduct μ = ∏ p ∈ μ.cells, hookAt μ p := by
  unfold hookProduct
  simp only [hookLength_eq_hookAt]
  exact Finset.prod_attach μ.cells (hookAt μ)

theorem hookAt_shiftRow (μ : YoungDiagram) {p : ℕ × ℕ} (hp : p ∈ tail μ) :
    hookAt μ (shiftRow p) = hookAt (tail μ) p := by
  have hm := (mem_tail μ p).mp hp
  have hc : p.1 + 1 < μ.colLen p.2 := YoungDiagram.mem_iff_lt_colLen.mp hm
  simp only [hookAt, tail_rowLen, tail_colLen, shiftRow, Function.Embedding.coeFn_mk]
  omega

/-- Product of the actual hook statistics over the actual first row. -/
def firstRowHookProduct (μ : YoungDiagram) : ℕ :=
  ∏ p ∈ μ.row 0, hookAt μ p

/-- All hooks below the first row are exactly the tail's hooks. -/
theorem hookProduct_factorization (μ : YoungDiagram) :
    hookProduct μ = firstRowHookProduct μ * hookProduct (tail μ) := by
  rw [hookProduct_eq_prod_hookAt, hookProduct_eq_prod_hookAt]
  rw [← Finset.prod_filter_mul_prod_filter_not μ.cells (fun p => p.1 = 0)]
  change firstRowHookProduct μ * _ = firstRowHookProduct μ * _
  congr 1
  rw [← tail_map_cells, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro p hp
  exact hookAt_shiftRow μ hp

theorem hookAt_firstRow (μ : YoungDiagram) {j : ℕ} (hj : j < μ.rowLen 0) :
    hookAt μ (0, j) = μ.rowLen 0 - j + (tail μ).colLen j := by
  have hm : (0, j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hj
  have hc : 0 < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hm
  simp only [hookAt, tail_colLen, Nat.sub_zero]
  omega

theorem firstRowHookProduct_eq_prod (μ : YoungDiagram) :
    firstRowHookProduct μ =
      ∏ j ∈ Finset.range (μ.rowLen 0), (μ.rowLen 0 - j + (tail μ).colLen j) := by
  unfold firstRowHookProduct
  rw [YoungDiagram.row_eq_prod, Finset.prod_product]
  simp only [Finset.prod_singleton]
  apply Finset.prod_congr rfl
  intro j hj
  exact hookAt_firstRow μ (Finset.mem_range.mp hj)

theorem prod_range_sub_eq_factorial (a : ℕ) :
    ∏ j ∈ Finset.range a, (a - j) = a.factorial := by
  calc
    _ = ∏ j ∈ Finset.range a, (a - 1 - j + 1) := by
      apply Finset.prod_congr rfl
      intro j hj
      have := Finset.mem_range.mp hj
      omega
    _ = ∏ j ∈ Finset.range a, (j + 1) := Finset.prod_range_reflect (fun j => j + 1) a
    _ = _ := Finset.prod_range_add_one_eq_factorial a

/-- The normalized row product is the actual first-row hook product divided by
the actual first-row factorial, including the empty diagram. -/
theorem firstRowHookProduct_div_factorial (μ : YoungDiagram) :
    (firstRowHookProduct μ : ℝ) / (μ.rowLen 0).factorial =
      normalizedRowProduct (μ.rowLen 0) (tail μ) := by
  rw [firstRowHookProduct_eq_prod,
    ← prod_range_sub_eq_factorial (μ.rowLen 0), Nat.cast_prod, Nat.cast_prod,
    ← Finset.prod_div_distrib,
    normalizedRowProduct_eq_prod (μ.rowLen 0) (tail μ) (tail_rowLen_le μ) le_rfl]
  apply Finset.prod_congr rfl
  intro j hj
  have hj' : j ≤ μ.rowLen 0 := (Finset.mem_range.mp hj).le
  simp only [Nat.cast_add, Nat.cast_sub hj', rowFactor]

/-- The actual full hook ratio also gives the normalized row product. -/
theorem hookProduct_div_tail_factorial (μ : YoungDiagram) :
    (hookProduct μ : ℝ) / ((μ.rowLen 0).factorial * hookProduct (tail μ)) =
      normalizedRowProduct (μ.rowLen 0) (tail μ) := by
  have ht : (hookProduct (tail μ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (hookProduct_pos (tail μ))
  rw [hookProduct_factorization, Nat.cast_mul,
    ← firstRowHookProduct_div_factorial]
  exact mul_div_mul_right _ _ ht

/-- The actual diagram splits into its first row and tail, also at the level of cardinality. -/
theorem card_eq_firstRow_add_tail (μ : YoungDiagram) :
    μ.card = μ.rowLen 0 + (tail μ).card := by
  have h := Finset.card_filter_add_card_filter_not (s := μ.cells) (fun p : ℕ × ℕ => p.1 = 0)
  rw [← tail_map_cells, Finset.card_map] at h
  rw [YoungDiagram.rowLen_eq_card]
  exact h.symm

/-- Applying the actual hook formulas identifies the minimal-degree tableau
count ratio with the previously bounded row product. No representation or
Gram-eigenvalue identity is assumed here. -/
theorem choose_mul_tableauCount_ratio (μ : YoungDiagram) :
    ((μ.card.choose (tail μ).card : ℕ) : ℝ) * standardTableauCount (tail μ) /
        standardTableauCount μ = normalizedRowProduct (μ.rowLen 0) (tail μ) := by
  have hcard := card_eq_firstRow_add_tail μ
  have hchoose : μ.card.choose (tail μ).card * (tail μ).card.factorial *
      (μ.rowLen 0).factorial = μ.card.factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial
      (show (tail μ).card ≤ μ.card by omega)
    have hsub : μ.card - (tail μ).card = μ.rowLen 0 := by omega
    simpa only [hsub] using h
  have hcross : μ.card.choose (tail μ).card * standardTableauCount (tail μ) *
      (μ.rowLen 0).factorial = firstRowHookProduct μ * standardTableauCount μ := by
    apply mul_left_cancel₀ (Nat.ne_of_gt (hookProduct_pos (tail μ)))
    calc
      hookProduct (tail μ) *
          (μ.card.choose (tail μ).card * standardTableauCount (tail μ) *
            (μ.rowLen 0).factorial) =
          μ.card.choose (tail μ).card *
            (hookProduct (tail μ) * standardTableauCount (tail μ)) *
              (μ.rowLen 0).factorial := by ring
      _ = μ.card.factorial := by rw [hookLengthFormula, hchoose]
      _ = hookProduct μ * standardTableauCount μ := (hookLengthFormula μ).symm
      _ = hookProduct (tail μ) *
          (firstRowHookProduct μ * standardTableauCount μ) := by
        rw [hookProduct_factorization]
        ring
  rw [← firstRowHookProduct_div_factorial]
  apply (div_eq_div_iff (by exact_mod_cast YoungHookRatio.standardTableauCount_ne_zero μ)
    (by exact_mod_cast Nat.factorial_ne_zero (μ.rowLen 0))).mpr
  exact_mod_cast hcross

end QuantumOracle.HookRowFactorization
