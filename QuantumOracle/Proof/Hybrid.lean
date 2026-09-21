import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact-prefix / compressed-suffix hybrids

This file proves general metric and norm inequalities.  In the manuscript they
are the analytic steps of §3.4 (`eq:one-query-comparison`, `thm:soundness`).
It does **not** construct either oracle, the harmonic embedding, or conditioning.
Theorems whose names contain `conditional` explicitly require the as-yet
uninstantiated one-query or conditioning estimates.

Steps may include the algorithm's intervening workspace operations.  Only the
compressed steps must be isometries.  Local comparison hypotheses are evaluated
on exact prefixes, never on states produced by the compressed experiment.
-/

namespace QuantumOracle

section Metric

variable {E F : Type*}

/-- Apply steps `0, ..., n-1` in chronological order. -/
def evolution (step : ℕ → E → E) (initial : E) : ℕ → E
  | 0 => initial
  | n + 1 => step n (evolution step initial n)

@[simp] theorem evolution_zero (step : ℕ → E → E) (initial : E) :
    evolution step initial 0 = initial := rfl

@[simp] theorem evolution_succ (step : ℕ → E → E) (initial : E) (n : ℕ) :
    evolution step initial (n + 1) = step n (evolution step initial n) := rfl

/-- A suffix consisting of `length` steps beginning with `start`. -/
def suffix (step : ℕ → E → E) : ℕ → ℕ → E → E
  | _, 0, x => x
  | start, length + 1, x => suffix step (start + 1) length (step start x)

variable [PseudoMetricSpace E] [PseudoMetricSpace F]

/-- Any suffix of isometric compressed steps preserves distances. -/
theorem suffix_isometry (step : ℕ → E → E)
    (hstep : ∀ j, Isometry (step j)) (start length : ℕ) :
    Isometry (suffix step start length) := by
  induction length generalizing start with
  | zero => exact isometry_id
  | succ length ih => exact (ih (start + 1)).comp (hstep start)

/-- A later isometric suffix transports a single replacement error unchanged. -/
theorem isometric_suffix_dist_le (S : E → F) (hS : Isometry S)
    (x y : E) (ε : ℝ) (hxy : dist x y ≤ ε) :
    dist (S x) (S y) ≤ ε := by
  simpa only [hS.dist_eq] using hxy

/-- Adjacent exact-prefix/compressed-suffix hybrids differ only at an exact
reachable state. The suffix length is arbitrary. -/
theorem hybrid_neighbor_dist_le
    (exactStep compressed : ℕ → E → E) (initial : E)
    (hcompressed : ∀ j, Isometry (compressed j))
    (j length : ℕ) (ε : ℝ)
    (hlocal : dist (exactStep j (evolution exactStep initial j))
      (compressed j (evolution exactStep initial j)) ≤ ε) :
    dist
      (suffix compressed (j + 1) length (evolution exactStep initial (j + 1)))
      (suffix compressed (j + 1) length
        (compressed j (evolution exactStep initial j))) ≤ ε := by
  exact isometric_suffix_dist_le _
    (suffix_isometry compressed hcompressed (j + 1) length) _ _ ε hlocal

/-- The telescoping estimate, requiring a local error only at exact prefixes.

At the induction step the two terms insert `compressed n (exactPrefix n)`.
Earlier differences pass through the final compressed isometry, giving precisely
an exact-prefix/compressed-suffix hybrid argument.  No comparison estimate is
assumed on any compressed reachable state. -/
theorem evolution_dist_le
    (exactStep compressed : ℕ → E → E) (initial : E) (q : ℕ) (ε : ℝ)
    (hcompressed : ∀ j < q, Isometry (compressed j))
    (hlocal : ∀ j < q, dist (exactStep j (evolution exactStep initial j))
      (compressed j (evolution exactStep initial j)) ≤ ε) :
    dist (evolution exactStep initial q) (evolution compressed initial q) ≤
      (q : ℝ) * ε := by
  suffices ∀ n ≤ q, dist (evolution exactStep initial n)
      (evolution compressed initial n) ≤ (n : ℝ) * ε by
    exact this q le_rfl
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hnq : n < q := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
    calc
      dist (evolution exactStep initial (n + 1))
          (evolution compressed initial (n + 1)) ≤
          dist (exactStep n (evolution exactStep initial n))
            (compressed n (evolution exactStep initial n)) +
          dist (compressed n (evolution exactStep initial n))
            (compressed n (evolution compressed initial n)) :=
        dist_triangle _ _ _
      _ = dist (exactStep n (evolution exactStep initial n))
            (compressed n (evolution exactStep initial n)) +
          dist (evolution exactStep initial n) (evolution compressed initial n) := by
        rw [(hcompressed n hnq).dist_eq]
      _ ≤ ε + (n : ℝ) * ε :=
        add_le_add (hlocal n hnq) (ih (Nat.le_of_lt hnq))
      _ = ((n + 1 : ℕ) : ℝ) * ε := by rw [Nat.cast_add, Nat.cast_one]; ring

/-- Abstract one-query comparison underlying `eq:one-query-comparison`.

`P` models involutive permutation compression, `U` database lookup, `O` the
transported exact query, and `D` conditioning. Only the displayed pointwise
intertwining and two local estimates are needed for this analytic step. -/
theorem conditioning_one_query_dist_le
    (P U O D : E → E) (hP : Isometry P) (hPP : Function.Involutive P)
    (hU : Isometry U) (h : E) (δ : ℝ)
    (hintertwine : D (O h) = U (D h))
    (hinput : dist (D h) (P h) ≤ δ)
    (houtput : dist (D (O h)) (P (O h)) ≤ δ) :
    dist (P (U (P h))) (O h) ≤ 2 * δ := by
  calc
    dist (P (U (P h))) (O h) = dist (U (P h)) (P (O h)) := by
      simpa only [hPP (O h)] using hP.dist_eq (U (P h)) (P (O h))
    _ ≤ dist (U (P h)) (U (D h)) + dist (U (D h)) (P (O h)) :=
      dist_triangle _ _ _
    _ = dist (P h) (D h) + dist (D (O h)) (P (O h)) := by
      rw [hU.dist_eq, ← hintertwine]
    _ ≤ δ + δ := add_le_add (by simpa only [dist_comm] using hinput) houtput
    _ = 2 * δ := by ring

/-- Conditional numerical instantiation: both conditioning bounds remain
explicit hypotheses. No normalization or overlap formula is proved here. -/
theorem conditional_one_query_four_div_sqrt
    (P U O D : E → E) (hP : Isometry P) (hPP : Function.Involutive P)
    (hU : Isometry U) (h : E) (N : ℕ)
    (hintertwine : D (O h) = U (D h))
    (hinput : dist (D h) (P h) ≤ 2 / Real.sqrt (N : ℝ))
    (houtput : dist (D (O h)) (P (O h)) ≤ 2 / Real.sqrt (N : ℝ)) :
    dist (P (U (P h))) (O h) ≤ 4 / Real.sqrt (N : ℝ) := by
  have hbound := conditioning_one_query_dist_le P U O D hP hPP hU h
    (2 / Real.sqrt (N : ℝ)) hintertwine hinput houtput
  calc
    _ ≤ 2 * (2 / Real.sqrt (N : ℝ)) := hbound
    _ = 4 / Real.sqrt (N : ℝ) := by ring

/-- Conditional final-state estimate: the actual oracle one-query bound must
still be supplied, for every exact prefix in the requested query range. -/
theorem conditional_evolution_four_mul_div_sqrt
    (exactStep compressed : ℕ → E → E) (initial : E) (q N : ℕ)
    (hcompressed : ∀ j < q, Isometry (compressed j))
    (hlocal : ∀ j < q, dist (exactStep j (evolution exactStep initial j))
      (compressed j (evolution exactStep initial j)) ≤ 4 / Real.sqrt (N : ℝ)) :
    dist (evolution exactStep initial q) (evolution compressed initial q) ≤
      4 * (q : ℝ) / Real.sqrt (N : ℝ) := by
  have hbound := evolution_dist_le exactStep compressed initial q
    (4 / Real.sqrt (N : ℝ)) hcompressed hlocal
  calc
    _ ≤ (q : ℝ) * (4 / Real.sqrt (N : ℝ)) := hbound
    _ = 4 * (q : ℝ) / Real.sqrt (N : ℝ) := by ring

/-- The manuscript's query range selects the local hypotheses needed above.
The condition is on `j+1`, because the conditioning estimate is also used on
the output of the next exact query. This is still a conditional theorem. -/
theorem conditional_evolution_four_mul_div_sqrt_of_query_range
    (exactStep compressed : ℕ → E → E) (initial : E) (q N : ℕ)
    (hq : q ≤ N / 4)
    (hcompressed : ∀ j < q, Isometry (compressed j))
    (hlocal : ∀ j, j + 1 ≤ N / 4 →
      dist (exactStep j (evolution exactStep initial j))
        (compressed j (evolution exactStep initial j)) ≤ 4 / Real.sqrt (N : ℝ)) :
    dist (evolution exactStep initial q) (evolution compressed initial q) ≤
      4 * (q : ℝ) / Real.sqrt (N : ℝ) := by
  apply conditional_evolution_four_mul_div_sqrt exactStep compressed initial q N hcompressed
  intro j hj
  exact hlocal j ((Nat.succ_le_of_lt hj).trans hq)

end Metric

section Norm

variable {E : Type*} [NormedAddCommGroup E]

/-- Norm formulation of the exact-prefix hybrid bound. -/
theorem evolution_norm_sub_le
    (exactStep compressed : ℕ → E → E) (initial : E) (q : ℕ) (ε : ℝ)
    (hcompressed : ∀ j < q, Isometry (compressed j))
    (hlocal : ∀ j < q, ‖exactStep j (evolution exactStep initial j) -
      compressed j (evolution exactStep initial j)‖ ≤ ε) :
    ‖evolution exactStep initial q - evolution compressed initial q‖ ≤
      (q : ℝ) * ε := by
  have hmetric : ∀ j < q, dist (exactStep j (evolution exactStep initial j))
      (compressed j (evolution exactStep initial j)) ≤ ε := by
    simpa only [dist_eq_norm] using hlocal
  simpa only [dist_eq_norm] using
    evolution_dist_le exactStep compressed initial q ε hcompressed hmetric

end Norm

section OverlapArithmetic

/-- Turn a squared pointwise error estimate into the conditioning constant.
This does not establish the squared estimate from an oracle construction. -/
theorem le_two_div_sqrt_of_sq_le (error : ℝ) (N : ℕ) (hN : 0 < N)
    (hsq : error ^ 2 ≤ 4 / (N : ℝ)) :
    error ≤ 2 / Real.sqrt (N : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hsqrt_sq : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt hNr.le
  have hmul_sq : (error * Real.sqrt (N : ℝ)) ^ 2 ≤ 4 := by
    calc
      _ = error ^ 2 * (N : ℝ) := by rw [mul_pow, hsqrt_sq]
      _ ≤ (4 / (N : ℝ)) * (N : ℝ) := mul_le_mul_of_nonneg_right hsq hNr.le
      _ = 4 := div_mul_cancel₀ 4 (ne_of_gt hNr)
  apply (le_div_iff₀ hsqrt).mpr
  nlinarith

/-- Unit-vector overlap arithmetic in §3.4. The norm identity and scalar
overlap bound are assumptions, to be derived from the concrete maps. -/
theorem conditional_error_le_of_overlap
    (error c : ℝ) (N : ℕ) (hN : 0 < N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hnorm : error ^ 2 = 2 * (1 - c))
    (hdefect : 1 - c ^ 2 ≤ 2 / (N : ℝ)) :
    error ≤ 2 / Real.sqrt (N : ℝ) := by
  apply le_two_div_sqrt_of_sq_le error N hN
  have hcsq : c ^ 2 ≤ c := by nlinarith
  calc
    error ^ 2 = 2 * (1 - c) := hnorm
    _ ≤ 2 * (1 - c ^ 2) := by nlinarith
    _ ≤ 2 * (2 / (N : ℝ)) := mul_le_mul_of_nonneg_left hdefect (by norm_num)
    _ = 4 / (N : ℝ) := by ring

end OverlapArithmetic

end QuantumOracle
