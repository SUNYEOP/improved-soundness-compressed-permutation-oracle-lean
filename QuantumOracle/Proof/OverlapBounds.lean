import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Elementary scalar estimates used after the overlap calculation

These are the real inequalities in manuscript §3.4, following
`eq:first-row-ratio-bound`. They do not construct representation components,
prove the hook-length formula, or identify the overlap of any actual oracle maps.
In particular, no overlap identity is introduced as an axiom here.
-/

namespace QuantumOracle

/-- The first-row numerical estimate in §3.4. Both parameters are real;
the manuscript's natural parameters may be cast to the reals. -/
theorem first_row_scalar_bound {N t : ℝ} (hN : 0 < N)
    (ht : 0 ≤ t) (hrange : 4 * t ≤ N) :
    t / (N - 2 * t + 1) ^ 2 ≤ 2 / N := by
  have hd : 0 < N - 2 * t + 1 := by linarith
  have htd : t ≤ N - 2 * t + 1 := by linarith
  have hNd : N ≤ 2 * (N - 2 * t + 1) := by linarith
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) hN).2
  calc
    t * N ≤ t * (2 * (N - 2 * t + 1)) :=
      mul_le_mul_of_nonneg_left hNd ht
    _ ≤ (N - 2 * t + 1) * (2 * (N - 2 * t + 1)) :=
      mul_le_mul_of_nonneg_right htd (by linarith)
    _ = 2 * (N - 2 * t + 1) ^ 2 := by ring

/-- The tail-corner numerical estimate in §3.4. This estimate does not need
the additional nonnegativity assumption on `t`. -/
theorem tail_corner_scalar_bound {N t : ℝ} (hN : 0 < N)
    (hrange : 4 * t ≤ N) :
    1 / (N - 2 * t + 2) ≤ 2 / N := by
  have hd : 0 < N - 2 * t + 2 := by linarith
  apply (div_le_div_iff₀ hd hN).2
  linarith

/-- The finite-product estimate used to bound the first-row ratio.
This is an inequality about arbitrary real numbers in `[0,1]`, independent
of whether the numbers arise from hook lengths. -/
theorem one_sub_prod_one_sub_le_sum {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) :
    1 - ∏ i ∈ s, (1 - u i) ≤ ∑ i ∈ s, u i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ha0 : 0 ≤ u a := (hu a (Finset.mem_insert_self a s)).1
    have hs : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1 :=
      fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hp : ∏ i ∈ s, (1 - u i) ≤ 1 :=
      Finset.prod_le_one
        (fun i hi => sub_nonneg.mpr (hs i hi).2)
        (fun i hi => sub_le_self _ (hs i hi).1)
    have hmul := mul_nonneg ha0 (sub_nonneg.mpr hp)
    have hsum := ih hs
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    nlinarith

end QuantumOracle
