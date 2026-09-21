import QuantumOracle.Model.CompressedQuery

/-! Involutions of the actual compressed queries, proved through their operator
equations while keeping the finite coordinate transports opaque. -/

noncomputable section

namespace QuantumOracle.CompressedQuery

open BasisLookup

variable {N w : ℕ}

@[simp] theorem ordinary_involutive (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ (Bits w × Database N)) :
    ordinary encode x (ordinary encode x ψ) = ψ := by
  rw [ordinary_apply, ordinary_apply, compression_involutive,
    ordinaryLookup_involutive, compression_involutive]

@[simp] theorem marked_involutive (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Database N)) :
    marked encode x (marked encode x ψ) = ψ := by
  rw [marked_apply, marked_apply, compression_involutive,
    markedLookup_involutive, compression_involutive]

theorem inverseOrdinary_apply (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ (Bits w × Database N)) :
    inverseOrdinary encode x ψ = flip (Bits w) (ordinary encode x (flip (Bits w) ψ)) :=
  rfl

theorem inverseMarked_apply (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Database N)) :
    inverseMarked encode x ψ =
      flip (Bool × Bits w) (marked encode x (flip (Bool × Bits w) ψ)) :=
  rfl

@[simp] theorem inverseOrdinary_involutive (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ (Bits w × Database N)) :
    inverseOrdinary encode x (inverseOrdinary encode x ψ) = ψ := by
  rw [inverseOrdinary_apply, inverseOrdinary_apply, flip_involutive,
    ordinary_involutive, flip_involutive]

@[simp] theorem inverseMarked_involutive (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Database N)) :
    inverseMarked encode x (inverseMarked encode x ψ) = ψ := by
  rw [inverseMarked_apply, inverseMarked_apply, flip_involutive,
    marked_involutive, flip_involutive]

end QuantumOracle.CompressedQuery
