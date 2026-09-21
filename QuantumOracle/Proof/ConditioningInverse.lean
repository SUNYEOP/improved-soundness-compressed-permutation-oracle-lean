import QuantumOracle.Proof.ConditioningQuery
import QuantumOracle.Proof.InversionSymmetry

/-!
# Actual inverse-direction conditioning and lookup intertwining

Conjugating the concrete forward conditioning isometry by the actual oracle
and database inversions gives inverse conditioning. Coordinate identities for
the genuine inverse lookups then prove ordinary and marked intertwining on
arbitrary answer-register values and entangled vectors.
-/

noncomputable section

namespace QuantumOracle.ConditioningInverse

open BasisLookup PermutationExtensions HiddenIsometry WorkspaceKnowledge

variable {N w : ℕ}

/-- Actual inverse conditioning, with proved isometry inherited from its factors. -/
def JInverse (x : Fin (N + 1)) :
    EuclideanSpace ℂ (Perm (N + 1)) →ₗᵢ[ℂ] EuclideanSpace ℂ (Database (N + 1)) :=
  (InversionSymmetry.database (N + 1)).toLinearIsometry.comp
    ((Conditioning.J x).comp (InversionSymmetry.oracle (N + 1)).toLinearIsometry)

@[simp] theorem JInverse_norm (x : Fin (N + 1))
    (h : EuclideanSpace ℂ (Perm (N + 1))) : ‖JInverse x h‖ = ‖h‖ :=
  (JInverse x).norm_map h

theorem JInverse_apply (x : Fin (N + 1))
    (h : EuclideanSpace ℂ (Perm (N + 1))) (I : Database (N + 1)) :
    JInverse x h I = Conditioning.J x (InversionSymmetry.oracle (N + 1) h) I.inverse := rfl

/-- Inverse conditioning records the queried output in every nonzero database. -/
theorem JInverse_apply_of_unattained (x : Fin (N + 1))
    (h : EuclideanSpace ℂ (Perm (N + 1))) (I : Database (N + 1))
    (hx : x ∉ I.image) : JInverse x h I = 0 := by
  rw [JInverse_apply]
  apply Conditioning.J_apply_of_undefined
  simpa only [Database.inverse_domain] using hx

theorem onOracle_JInverse {A : Type*} [Fintype A] (x : Fin (N + 1))
    (ψ : EuclideanSpace ℂ (A × Perm (N + 1))) :
    onOracle A (JInverse x) ψ =
      onOracle A (InversionSymmetry.database (N + 1)).toLinearIsometry
        (onOracle A (Conditioning.J x)
          (onOracle A (InversionSymmetry.oracle (N + 1)).toLinearIsometry ψ)) := by
  ext ⟨a, I⟩
  simp only [onOracle_apply, slice_onOracle]
  rfl

@[simp] theorem onOracle_oracle_apply {A : Type*} [Fintype A]
    (ψ : EuclideanSpace ℂ (A × Perm N)) (a : A) (π : Perm N) :
    onOracle A (InversionSymmetry.oracle N).toLinearIsometry ψ (a, π) = ψ (a, π.symm) := rfl

@[simp] theorem onOracle_database_apply {A : Type*} [Fintype A]
    (ψ : EuclideanSpace ℂ (A × Database N)) (a : A) (I : Database N) :
    onOracle A (InversionSymmetry.database N).toLinearIsometry ψ (a, I) =
      ψ (a, I.inverse) := rfl

theorem inverseOrdinary_apply (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ (Bits w × Database N)) (z : Bits w) (I : Database N) :
    Query.inverseOrdinaryLookup encode x ψ (z, I) =
      ψ (xor z (ordinaryAnswer encode I.inverse x), I) := by
  change ψ (xor z (ordinaryAnswer encode I.inverse x), I.inverse.inverse) = _
  rw [Database.inverse_inverse]

theorem inverseMarked_apply (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Database N)) (z : Bool × Bits w)
    (I : Database N) :
    Query.inverseMarkedLookup encode x ψ (z, I) =
      ψ ((Bool.xor z.1 (markedAnswer encode I.inverse x).1,
        xor z.2 (markedAnswer encode I.inverse x).2), I) := by
  change ψ ((Bool.xor z.1 (markedAnswer encode I.inverse x).1,
    xor z.2 (markedAnswer encode I.inverse x).2), I.inverse.inverse) = _
  rw [Database.inverse_inverse]

theorem oracle_exactOrdinary_inverse (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ (Bits w × Perm N)) :
    onOracle (Bits w) (InversionSymmetry.oracle N).toLinearIsometry
        (Query.exactOrdinary encode true x ψ) =
      Query.exactOrdinary encode false x
        (onOracle (Bits w) (InversionSymmetry.oracle N).toLinearIsometry ψ) := by
  ext ⟨z, π⟩
  rw [onOracle_oracle_apply, LookupCoordinates.exactOrdinary_apply,
    LookupCoordinates.exactOrdinary_apply, onOracle_oracle_apply]
  rfl

theorem oracle_exactMarked_inverse (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Perm N)) :
    onOracle (Bool × Bits w) (InversionSymmetry.oracle N).toLinearIsometry
        (Query.exactMarked encode true x ψ) =
      Query.exactMarked encode false x
        (onOracle (Bool × Bits w) (InversionSymmetry.oracle N).toLinearIsometry ψ) := by
  ext ⟨z, π⟩
  rw [onOracle_oracle_apply, LookupCoordinates.exactMarked_apply,
    LookupCoordinates.exactMarked_apply, onOracle_oracle_apply]
  rfl

theorem database_ordinary_inverse (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ (Bits w × Database N)) :
    onOracle (Bits w) (InversionSymmetry.database N).toLinearIsometry
        (Query.ordinaryLookup encode x ψ) =
      Query.inverseOrdinaryLookup encode x
        (onOracle (Bits w) (InversionSymmetry.database N).toLinearIsometry ψ) := by
  ext ⟨z, I⟩
  rw [onOracle_database_apply, LookupCoordinates.ordinary_apply,
    inverseOrdinary_apply, onOracle_database_apply]

theorem database_marked_inverse (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Database N)) :
    onOracle (Bool × Bits w) (InversionSymmetry.database N).toLinearIsometry
        (Query.markedLookup encode x ψ) =
      Query.inverseMarkedLookup encode x
        (onOracle (Bool × Bits w) (InversionSymmetry.database N).toLinearIsometry ψ) := by
  ext ⟨z, I⟩
  rw [onOracle_database_apply, LookupCoordinates.marked_apply,
    inverseMarked_apply, onOracle_database_apply]

/-- Actual inverse ordinary queries intertwine through actual inverse conditioning. -/
theorem ordinary_intertwines (encode : Encoding (N + 1) w) (x : Fin (N + 1))
    (ψ : EuclideanSpace ℂ (Bits w × Perm (N + 1))) :
    onOracle (Bits w) (JInverse x) (Query.exactOrdinary encode true x ψ) =
      Query.inverseOrdinaryLookup encode x (onOracle (Bits w) (JInverse x) ψ) := by
  simp only [onOracle_JInverse]
  rw [oracle_exactOrdinary_inverse, ConditioningQuery.ordinary_intertwines,
    database_ordinary_inverse]

/-- The inverse marked version holds for arbitrary initial marker and answer values. -/
theorem marked_intertwines (encode : Encoding (N + 1) w) (x : Fin (N + 1))
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Perm (N + 1))) :
    onOracle (Bool × Bits w) (JInverse x) (Query.exactMarked encode true x ψ) =
      Query.inverseMarkedLookup encode x (onOracle (Bool × Bits w) (JInverse x) ψ) := by
  simp only [onOracle_JInverse]
  rw [oracle_exactMarked_inverse, ConditioningQuery.marked_intertwines,
    database_marked_inverse]

end QuantumOracle.ConditioningInverse
