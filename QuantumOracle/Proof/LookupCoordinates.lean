import QuantumOracle.Model.Query

/-! Actual lookup amplitudes at arbitrary answer-register values. -/

noncomputable section

namespace QuantumOracle.LookupCoordinates

open BasisLookup

variable {N w : ℕ}

@[simp] theorem ordinary_apply (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ (Bits w × Database N)) (z : Bits w) (I : Database N) :
    Query.ordinaryLookup encode x ψ (z, I) = ψ (xor z (ordinaryAnswer encode I x), I) := rfl

@[simp] theorem marked_apply (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Database N)) (z : Bool × Bits w)
    (I : Database N) :
    Query.markedLookup encode x ψ (z, I) =
      ψ ((Bool.xor z.1 (markedAnswer encode I x).1,
        xor z.2 (markedAnswer encode I x).2), I) := rfl

@[simp] theorem exactOrdinary_apply (encode : Encoding N w) (inverse : Bool) (x : Fin N)
    (ψ : EuclideanSpace ℂ (Bits w × Equiv.Perm (Fin N))) (z : Bits w)
    (π : Equiv.Perm (Fin N)) :
    Query.exactOrdinary encode inverse x ψ (z, π) =
      ψ (xor z (encode (Query.permutationAnswer inverse π x)), π) := rfl

@[simp] theorem exactMarked_apply (encode : Encoding N w) (inverse : Bool) (x : Fin N)
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Equiv.Perm (Fin N))) (z : Bool × Bits w)
    (π : Equiv.Perm (Fin N)) :
    Query.exactMarked encode inverse x ψ (z, π) =
      ψ ((Bool.xor z.1 true, xor z.2 (encode (Query.permutationAnswer inverse π x))), π) := rfl

end QuantumOracle.LookupCoordinates
