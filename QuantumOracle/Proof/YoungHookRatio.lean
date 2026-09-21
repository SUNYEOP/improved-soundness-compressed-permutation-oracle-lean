import QuantumOracle.Proof.HookLengthFormula

/-!
# Actual tableau counts and normalized corner ratios

The hook-length formula is applied to the genuine finite count of standard
tableaux and to actual corner deletion in a Young diagram. The resulting
positive corner weights sum to one. No identification with Specht dimensions,
Gram eigenvalues or conditioning overlaps is made in this module.
-/

noncomputable section

namespace QuantumOracle.YoungHookRatio

open AtlasKnownTheorems.HookLengthFormula
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The actual tableau count is positive, including the empty shape. -/
theorem standardTableauCount_pos (μ : YoungDiagram) : 0 < standardTableauCount μ := by
  have h := Nat.factorial_pos μ.card
  rw [← hookLengthFormula μ] at h
  exact Nat.pos_of_mul_pos_left h

theorem standardTableauCount_ne_zero (μ : YoungDiagram) : standardTableauCount μ ≠ 0 :=
  Nat.ne_of_gt (standardTableauCount_pos μ)

/-- The proved hook-length formula, with rational division and no formula premise. -/
theorem standardTableauCount_eq_factorial_div_hookProduct (μ : YoungDiagram) :
    (standardTableauCount μ : ℚ) = (Nat.factorial μ.card : ℚ) / hookProduct μ :=
  standardTableauCount_eq_factorial_div_hookProduct_of_formula μ (hookLengthFormula μ)

/-- Corner deletion turns the two actual hook formulas into a denominator-free
identity relating the two tableau counts. -/
theorem corner_count_mul_hookProduct (μ : YoungDiagram) (c : CornerCells μ) :
    μ.card * standardTableauCount (eraseCorner μ c.1 c.2) *
      hookProduct (eraseCorner μ c.1 c.2) = standardTableauCount μ * hookProduct μ := by
  calc
    _ = μ.card * (hookProduct (eraseCorner μ c.1 c.2) *
        standardTableauCount (eraseCorner μ c.1 c.2)) := by ring
    _ = μ.card * Nat.factorial (eraseCorner μ c.1 c.2).card := by
      rw [hookLengthFormula]
    _ = Nat.factorial μ.card := by
      rw [← eraseCorner_card_add_one μ c.1 c.2, Nat.factorial_succ]
    _ = standardTableauCount μ * hookProduct μ := by
      rw [← hookLengthFormula μ, Nat.mul_comm]

/-- The actual deleted-to-original tableau-count ratio is the original-to-deleted
hook-product ratio divided by the original number of cells. -/
theorem corner_count_ratio (μ : YoungDiagram) (c : CornerCells μ) :
    (standardTableauCount (eraseCorner μ c.1 c.2) : ℚ) / standardTableauCount μ =
      hookProductCornerRatio μ c / μ.card := by
  have hcount : (standardTableauCount μ : ℚ) ≠ 0 := by
    exact_mod_cast standardTableauCount_ne_zero μ
  have hhook : (hookProduct (eraseCorner μ c.1 c.2) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hookProduct_pos (eraseCorner μ c.1 c.2)))
  have hcard : (μ.card : ℚ) ≠ 0 := by
    have h := eraseCorner_card_add_one μ c.1 c.2
    exact_mod_cast (show μ.card ≠ 0 by omega)
  have hcross : (μ.card : ℚ) * standardTableauCount (eraseCorner μ c.1 c.2) *
      hookProduct (eraseCorner μ c.1 c.2) =
        (standardTableauCount μ : ℚ) * hookProduct μ := by
    exact_mod_cast corner_count_mul_hookProduct μ c
  unfold hookProductCornerRatio
  field_simp [hcount, hhook, hcard]
  nlinarith [hcross]

/-- Real-valued version of the same actual count ratio for subsequent inequalities. -/
theorem corner_count_ratio_real (μ : YoungDiagram) (c : CornerCells μ) :
    (standardTableauCount (eraseCorner μ c.1 c.2) : ℝ) / standardTableauCount μ =
      (hookProduct μ : ℝ) / hookProduct (eraseCorner μ c.1 c.2) / μ.card := by
  have h := corner_count_ratio μ c
  unfold hookProductCornerRatio at h
  simpa only [Rat.cast_div, Rat.cast_natCast] using
    congrArg (fun q : ℚ => (q : ℝ)) h

/-- A normalized weight defined by actual tableau counts, not by a desired bound. -/
def cornerWeight (μ : YoungDiagram) (c : CornerCells μ) : ℝ :=
  (standardTableauCount (eraseCorner μ c.1 c.2) : ℝ) / standardTableauCount μ

theorem cornerWeight_pos (μ : YoungDiagram) (c : CornerCells μ) :
    0 < cornerWeight μ c := by
  apply div_pos
  · exact_mod_cast standardTableauCount_pos (eraseCorner μ c.1 c.2)
  · exact_mod_cast standardTableauCount_pos μ

theorem cornerWeight_eq_hook_ratio (μ : YoungDiagram) (c : CornerCells μ) :
    cornerWeight μ c =
      (hookProduct μ : ℝ) / hookProduct (eraseCorner μ c.1 c.2) / μ.card :=
  corner_count_ratio_real μ c

/-- Actual tableau branching normalizes the corner weights to one for every
nonempty diagram. The empty shape deliberately has no such normalization. -/
theorem sum_cornerWeight (μ : YoungDiagram) (hμ : μ.cells.Nonempty) :
    ∑ c : CornerCells μ, cornerWeight μ c = 1 := by
  classical
  unfold cornerWeight
  rw [← Finset.sum_div]
  have hsum : (∑ c : CornerCells μ,
      (standardTableauCount (eraseCorner μ c.1 c.2) : ℝ)) = standardTableauCount μ := by
    exact_mod_cast (standardTableauCount_eq_sum_erased μ hμ).symm
  rw [hsum, div_self]
  exact_mod_cast standardTableauCount_ne_zero μ

theorem cornerWeight_le_one (μ : YoungDiagram) (c : CornerCells μ) :
    cornerWeight μ c ≤ 1 := by
  classical
  rw [← sum_cornerWeight μ ⟨c.1.val, c.1.property⟩]
  exact Finset.single_le_sum (fun d _ => le_of_lt (cornerWeight_pos μ d)) (Finset.mem_univ c)

/-- The hook-product expression inherits both positivity and the unit upper
bound from the actual normalized corner counts. -/
theorem hook_ratio_mem_Ioc (μ : YoungDiagram) (c : CornerCells μ) :
    (hookProduct μ : ℝ) / hookProduct (eraseCorner μ c.1 c.2) / μ.card ∈
      Set.Ioc (0 : ℝ) 1 := by
  rw [← cornerWeight_eq_hook_ratio]
  exact ⟨cornerWeight_pos μ c, cornerWeight_le_one μ c⟩

end QuantumOracle.YoungHookRatio
