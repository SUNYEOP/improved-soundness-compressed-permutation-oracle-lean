import QuantumOracle.Model.AnswerSelection
import QuantumOracle.Model.WorkspaceKnowledge
import QuantumOracle.Model.ExactCoherentQuery

/-!
# Degree growth of actual coherent exact queries

Every output-workspace slice is an answer-dependent selection of input slices.
The selection theorem applies to the actual forward or inverse answer. This
covers coherent enable, direction and input registers, arbitrary output values,
ordinary/marked queries on a common workspace, and an arbitrary finite auxiliary
register entangled with the query and oracle registers.
-/

noncomputable section

namespace QuantumOracle.ExactQueryGrowth

open PermutationExtensions KnowledgeSpace WorkspaceKnowledge ExactCoherentQuery

variable {N w t : ℕ}

/-- The complete actual query has one-step growth on the exact consistency spaces. -/
theorem query_supported (encode : BasisLookup.Encoding N w) (marked : Bool)
    (ht : t < N) {ψ : EuclideanSpace ℂ (Args N w × Perm N)}
    (hψ : Supported (K N t) ψ) :
    Supported (K N (t + 1)) (query encode marked ψ) := by
  intro args
  have h := AnswerSelection.select_mem_succ ht args.2.1.1 args.2.1.2
    (fun y => slice ψ (answerArgs encode marked args y))
    (fun y => hψ (answerArgs encode marked args y))
  have heq : slice (query encode marked ψ) args =
      AnswerSelection.select args.2.1.1 args.2.1.2
        (fun y => slice ψ (answerArgs encode marked args y)) := by
    ext π
    exact query_apply encode marked ψ args π
  rw [heq]
  exact h

/-- The actual coherent query, tensored with the identity on an auxiliary register.
The reassociation keeps the full workspace on the left of the oracle register. -/
def liftedQuery (Aux : Type*) [Fintype Aux] (encode : BasisLookup.Encoding N w)
    (marked : Bool) :
    EuclideanSpace ℂ ((Aux × Args N w) × Perm N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Aux × Args N w) × Perm N) :=
  let R := Query.linearLift (Equiv.prodAssoc Aux (Args N w) (Perm N))
  R.trans ((BlockOperator.onRight Aux (query encode marked)).trans R.symm)

@[simp] theorem liftedQuery_apply {Aux : Type*} [Fintype Aux]
    (encode : BasisLookup.Encoding N w) (marked : Bool)
    (ψ : EuclideanSpace ℂ ((Aux × Args N w) × Perm N))
    (a : Aux) (args : Args N w) (π : Perm N) :
    liftedQuery Aux encode marked ψ ((a, args), π) =
      ψ ((a, answerArgs encode marked args
        (Query.permutationAnswer args.2.1.1 π args.2.1.2)), π) := by
  change query encode marked (WithLp.toLp 2
      (fun p : Args N w × Perm N => ψ ((a, p.1), p.2))) (args, π) = _
  rw [query_apply]

theorem liftedQuery_isometry (Aux : Type*) [Fintype Aux]
    (encode : BasisLookup.Encoding N w) (marked : Bool) :
    Isometry (liftedQuery Aux encode marked) :=
  (liftedQuery Aux encode marked).isometry

/-- The degree bound is stable under an arbitrary finite ancillary register. -/
theorem liftedQuery_supported {Aux : Type*} [Fintype Aux]
    (encode : BasisLookup.Encoding N w) (marked : Bool) (ht : t < N)
    {ψ : EuclideanSpace ℂ ((Aux × Args N w) × Perm N)}
    (hψ : Supported (K N t) ψ) :
    Supported (K N (t + 1)) (liftedQuery Aux encode marked ψ) := by
  rintro ⟨a, args⟩
  have h := AnswerSelection.select_mem_succ ht args.2.1.1 args.2.1.2
    (fun y => slice ψ (a, answerArgs encode marked args y))
    (fun y => hψ (a, answerArgs encode marked args y))
  have heq : slice (liftedQuery Aux encode marked ψ) (a, args) =
      AnswerSelection.select args.2.1.1 args.2.1.2
        (fun y => slice ψ (a, answerArgs encode marked args y)) := by
    ext π
    exact liftedQuery_apply encode marked ψ a args π
  rw [heq]
  exact h

/-- Saturation at the full space makes the growth statement valid for every query count. -/
theorem liftedQuery_supported_min {Aux : Type*} [Fintype Aux]
    (encode : BasisLookup.Encoding N w) (marked : Bool) (t : ℕ)
    {ψ : EuclideanSpace ℂ ((Aux × Args N w) × Perm N)}
    (hψ : Supported (K N (min t N)) ψ) :
    Supported (K N (min (t + 1) N)) (liftedQuery Aux encode marked ψ) := by
  by_cases ht : t < N
  · have hmin : min t N = t := Nat.min_eq_left (Nat.le_of_lt ht)
    have hmin' : min (t + 1) N = t + 1 := Nat.min_eq_left (Nat.succ_le_of_lt ht)
    rw [hmin] at hψ
    rw [hmin']
    exact liftedQuery_supported encode marked ht hψ
  · have hmin : min (t + 1) N = N := Nat.min_eq_right (by omega)
    rw [hmin, full_eq_top]
    intro a
    trivial

end QuantumOracle.ExactQueryGrowth
