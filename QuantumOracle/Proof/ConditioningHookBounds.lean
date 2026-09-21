import QuantumOracle.Proof.ConditioningFirstRowBounds
import QuantumOracle.Proof.HookRatioProducts

/-!
# Numerical conditioning bounds from actual column-product eigenvalues

Both actual conditioning overlap formulas now imply the manuscript constant
when their full and residual Gram eigenvalues are the column products of an
actual Young diagram and its actual corner removal. Harmonic membership and
these Gram equations remain explicit premises. This does not supply their
representation-theoretic identification or a decomposition of arbitrary inputs.
-/

noncomputable section

namespace QuantumOracle.ConditioningHookBounds

open PermutationExtensions HarmonicLayers
open AtlasKnownTheorems.HookLengthFormula HookRatioBounds HookRatioProducts

attribute [local irreducible] PolarEmbedding.candidate

private theorem error_le_of_sq_deficit {e m a b D : ℝ}
    (he : 0 ≤ e) (hm : 0 ≤ m) (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (hr : Real.sqrt a / Real.sqrt b ≤ 1)
    (hsq : e ^ 2 = 2 * (1 - Real.sqrt a / Real.sqrt b) * m ^ 2)
    (hdef : 1 - a / b ≤ 2 / D) : e ≤ (2 / Real.sqrt D) * m := by
  have hr0 : 0 ≤ Real.sqrt a / Real.sqrt b := by positivity
  have hrsq : (Real.sqrt a / Real.sqrt b) ^ 2 = a / b := by
    rw [div_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
  have hrr : (Real.sqrt a / Real.sqrt b) ^ 2 ≤ Real.sqrt a / Real.sqrt b := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr)]
  have hf : 2 * (1 - Real.sqrt a / Real.sqrt b) ≤ 4 / D := by
    rw [hrsq] at hrr
    calc
      _ ≤ 2 * (2 / D) := mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
      _ = _ := by ring
  apply (sq_le_sq₀ he (by positivity : 0 ≤ (2 / Real.sqrt D) * m)).mp
  calc
    e ^ 2 ≤ (4 / D) * m ^ 2 := by
      rw [hsq]
      exact mul_le_mul_of_nonneg_right hf (sq_nonneg m)
    _ = ((2 / Real.sqrt D) * m) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hD.le]
      norm_num

variable {N : ℕ}

/-- The equal-degree branch has the sharp uniform conditioning constant once
the actual two Gram equations are evaluated by the diagram's row products. -/
theorem firstRow_error_le (x : Fin (N + 1)) (θ : YoungDiagram)
    (hrange : 4 * θ.card ≤ N + 1)
    {h : EuclideanSpace ℂ (Perm (N + 1))}
    (hh : h ∈ H (N + 1) θ.card)
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N θ.card)
    (hfull : GramFiltration.gram (N + 1) θ.card h =
      (normalizedRowProduct (N + 1 - θ.card) θ : ℂ) • h)
    (hresidual : ∀ y, GramFiltration.gram N θ.card (ResidualAdjoint.restrict x y h) =
      (normalizedRowProduct (N + 1 - θ.card - 1) θ : ℂ) •
        ResidualAdjoint.restrict x y h) :
    ‖Conditioning.J x h - Compression.pC x (PolarEmbedding.candidate (N + 1) h)‖ ≤
      (2 / Real.sqrt (N + 1 : ℕ)) * ‖h‖ := by
  by_cases hz : h = 0
  · simp only [hz, map_zero, sub_self, norm_zero, mul_zero, le_refl]
  have hwidth := rowLen_zero_le_card θ
  have hp : 0 < normalizedRowProduct (N + 1 - θ.card) θ :=
    normalizedRowProduct_pos _ θ (by omega)
  have hpr : 0 < normalizedRowProduct (N + 1 - θ.card - 1) θ :=
    normalizedRowProduct_pos _ θ (by omega)
  have hratio := (ConditioningFirstRowBounds.sqrt_ratio_pos_le_one x hh hz hres
    _ _ hp hpr hfull hresidual).2
  have hsq := ConditioningFirstRowBounds.norm_pC_candidate_sub_J_sq x hh hres
    _ _ hp hpr hfull hresidual
  rw [norm_sub_rev] at hsq
  exact error_le_of_sq_deficit (norm_nonneg _) (norm_nonneg h) hp hpr
    (by positivity) hratio hsq (firstRow_quotient_deficit_le_two_div θ (Nat.succ_pos N) hrange)

/-- Actual tail-corner deletion supplies the other branch's numerical bound;
the lower residual degree is the actual size of the deleted diagram. -/
theorem tailCorner_error_le (x : Fin (N + 1)) (θ : YoungDiagram)
    (c : CornerCells θ) (hrange : 4 * θ.card ≤ N + 1)
    {h : EuclideanSpace ℂ (Perm (N + 1))}
    (hh : h ∈ H (N + 1) θ.card)
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ H N (eraseCorner θ c.1 c.2).card)
    (hfull : GramFiltration.gram (N + 1) θ.card h =
      (normalizedRowProduct (N + 1 - θ.card) θ : ℂ) • h)
    (hresidual : ∀ y, GramFiltration.gram N (eraseCorner θ c.1 c.2).card
        (ResidualAdjoint.restrict x y h) =
      (normalizedRowProduct (N + 1 - θ.card) (eraseCorner θ c.1 c.2) : ℂ) •
        ResidualAdjoint.restrict x y h) :
    ‖Conditioning.J x h - Compression.pC x (PolarEmbedding.candidate (N + 1) h)‖ ≤
      (2 / Real.sqrt (N + 1 : ℕ)) * ‖h‖ := by
  by_cases hz : h = 0
  · simp only [hz, map_zero, sub_self, norm_zero, mul_zero, le_refl]
  have hwidth := rowLen_zero_le_card θ
  have hp : 0 < normalizedRowProduct (N + 1 - θ.card) θ :=
    normalizedRowProduct_pos _ θ (by omega)
  have hpr : 0 < normalizedRowProduct (N + 1 - θ.card) (eraseCorner θ c.1 c.2) :=
    normalizedRowProduct_pos _ _ ((rowLen_eraseCorner_le θ c).trans (by omega))
  have hcard := eraseCorner_card_add_one θ c.1 c.2
  have hh' : h ∈ H (N + 1) ((eraseCorner θ c.1 c.2).card + 1) := by
    simpa only [hcard] using hh
  have hf' : GramFiltration.gram (N + 1) ((eraseCorner θ c.1 c.2).card + 1) h =
      (normalizedRowProduct (N + 1 - θ.card) θ : ℂ) • h := by
    simpa only [hcard] using hfull
  have hratio := (ConditioningSpectrum.sqrt_ratio_pos_le_one x hh' hz hres
    _ _ hp hpr hf' hresidual).2
  have hsq := ConditioningSpectrum.norm_pC_candidate_sub_J_sq x hh' hres
    _ _ hp hpr hf' hresidual
  rw [norm_sub_rev] at hsq
  exact error_le_of_sq_deficit (norm_nonneg _) (norm_nonneg h) hpr hp
    (by positivity) hratio hsq
    (tailCorner_quotient_deficit_le_two_div θ (Nat.succ_pos N) hrange c)

end QuantumOracle.ConditioningHookBounds
