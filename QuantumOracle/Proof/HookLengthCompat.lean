import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Lagrange coefficient identity on the project's pinned mathlib

The adapted hook-length proof uses the coefficient identity proved below.
It follows from Lagrange interpolation and the leading coefficients of the
basis polynomials in the pinned mathlib.
-/

namespace QuantumOracle.HookLengthCompat

open Polynomial
open scoped BigOperators

theorem coeff_eq_sum {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {v : ι → F} {P : F[X]}
    (hinj : Set.InjOn v s) (hdegree : P.degree < s.card) :
    P.coeff (s.card - 1) =
      ∑ i ∈ s, P.eval (v i) / ∏ j ∈ s.erase i, (v i - v j) := by
  have hinterp := congrArg (fun Q : F[X] => Q.coeff (s.card - 1))
    (Lagrange.eq_interpolate hinj hdegree)
  rw [Lagrange.interpolate_apply, finsetSum_coeff] at hinterp
  rw [hinterp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_C_mul, ← Lagrange.natDegree_basis hinj hi]
  change P.eval (v i) * (Lagrange.basis s v i).leadingCoeff = _
  rw [Lagrange.basis, leadingCoeff_prod]
  simp only [Lagrange.basisDivisor, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_X_sub_C, mul_one, ← Finset.prod_inv_distrib, div_eq_mul_inv]

end QuantumOracle.HookLengthCompat
