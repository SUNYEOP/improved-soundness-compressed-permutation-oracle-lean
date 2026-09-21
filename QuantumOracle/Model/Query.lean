import QuantumOracle.Model.Database
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Perm

/-!
# Actual finite query operators

Basis permutations are lifted to complex Hilbert-space linear isometry
equivalences. This covers extended database lookup and exact permutation
queries, including arbitrary answer-register values, inverse direction,
marked answers, and coherent controls. It does not construct `pC`, `cpO`,
`W`, `J`, or `D`, or prove any comparison estimate between the experiments.
-/

noncomputable section

namespace QuantumOracle.Query

open BasisLookup

/-- A basis reindexing extended linearly to the finite complex Hilbert space.
The direction is `|i⟩ ↦ |e i⟩`, proved by `linearLift_single`. -/
def linearLift {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ β :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

theorem linearLift_isometry {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) : Isometry (linearLift e) :=
  (linearLift e).isometry

@[simp] theorem linearLift_single {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (i : α) (z : ℂ) :
    linearLift e (EuclideanSpace.single i z) = EuclideanSpace.single (e i) z :=
  EuclideanSpace.piLpCongrLeft_single e i z

@[simp] theorem linearLift_apply {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (ψ : EuclideanSpace ℂ α) (i : α) :
    linearLift e ψ (e i) = ψ i := by
  change ψ (e.symm (e i)) = ψ i
  rw [e.symm_apply_apply]

section DatabaseLookup

variable {N w : ℕ}

/-- Ordinary extended database lookup `P_x`, as a genuine Hilbert-space map. -/
def ordinaryLookup (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ (Bits w × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Bits w × Database N) :=
  linearLift (BasisLookup.ordinary encode x)

/-- Marked lookup shifts both marker and output bits, for arbitrary inputs. -/
def markedLookup (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ ((Bool × Bits w) × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Bool × Bits w) × Database N) :=
  linearLift (BasisLookup.marked encode x)

def inverseOrdinaryLookup (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ (Bits w × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Bits w × Database N) :=
  linearLift (BasisLookup.inverseOrdinary encode x)

def inverseMarkedLookup (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ ((Bool × Bits w) × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Bool × Bits w) × Database N) :=
  linearLift (BasisLookup.inverseMarked encode x)

theorem ordinaryLookup_isometry (encode : Encoding N w) (x : Fin N) :
    Isometry (ordinaryLookup encode x) := (ordinaryLookup encode x).isometry

theorem markedLookup_isometry (encode : Encoding N w) (x : Fin N) :
    Isometry (markedLookup encode x) := (markedLookup encode x).isometry

theorem ordinaryLookup_defined (encode : Encoding N w) (x y : Fin N)
    (I : Database N) (h : (x, y) ∈ I.edges) (z : Bits w) :
    ordinaryLookup encode x (EuclideanSpace.single (z, I) 1) =
      EuclideanSpace.single (xor z (encode y), I) 1 := by
  rw [ordinaryLookup, linearLift_single, BasisLookup.ordinary_defined encode x y I h z]

theorem markedLookup_defined (encode : Encoding N w) (x y : Fin N)
    (I : Database N) (h : (x, y) ∈ I.edges) (z : Bool × Bits w) :
    markedLookup encode x (EuclideanSpace.single (z, I) 1) =
      EuclideanSpace.single ((Bool.xor z.1 true, xor z.2 (encode y)), I) 1 := by
  rw [markedLookup, linearLift_single, BasisLookup.marked_defined encode x y I h z]

theorem ordinaryLookup_undefined (encode : Encoding N w) (x : Fin N)
    (I : Database N) (h : x ∉ I.domain) (z : Bits w) :
    ordinaryLookup encode x (EuclideanSpace.single (z, I) 1) =
      EuclideanSpace.single (z, I) 1 := by
  rw [ordinaryLookup, linearLift_single, BasisLookup.ordinary_undefined encode x I h z]

theorem markedLookup_undefined (encode : Encoding N w) (x : Fin N)
    (I : Database N) (h : x ∉ I.domain) (z : Bool × Bits w) :
    markedLookup encode x (EuclideanSpace.single (z, I) 1) =
      EuclideanSpace.single (z, I) 1 := by
  rw [markedLookup, linearLift_single, BasisLookup.marked_undefined encode x I h z]

end DatabaseLookup

/-- A read-only oracle register controls a reversible answer-register operation. -/
def registerBasis {R Y : Type*} (action : R → Equiv.Perm Y) :
    Equiv.Perm (Y × R) where
  toFun := fun yr => (action yr.2 yr.1, yr.2)
  invFun := fun yr => ((action yr.2).symm yr.1, yr.2)
  left_inv := by rintro ⟨y, r⟩; simp
  right_inv := by rintro ⟨y, r⟩; simp

section ExactQuery

variable {N w : ℕ}

/-- `false` is the forward direction; `true` is inverse. -/
def permutationAnswer (inverse : Bool) (π : Equiv.Perm (Fin N)) (x : Fin N) : Fin N :=
  if inverse then π.symm x else π x

/-- The exact permutation oracle's ordinary basis action. -/
def exactOrdinaryBasis (encode : Encoding N w) (inverse : Bool) (x : Fin N) :
    Equiv.Perm (Bits w × Equiv.Perm (Fin N)) :=
  registerBasis (fun π => xorPerm (encode (permutationAnswer inverse π x)))

/-- The exact permutation oracle always supplies a defined marked answer. -/
def exactMarkedBasis (encode : Encoding N w) (inverse : Bool) (x : Fin N) :
    Equiv.Perm ((Bool × Bits w) × Equiv.Perm (Fin N)) :=
  registerBasis (fun π => Equiv.prodCongr (bitXorPerm true)
    (xorPerm (encode (permutationAnswer inverse π x))))

def exactOrdinary (encode : Encoding N w) (inverse : Bool) (x : Fin N) :
    EuclideanSpace ℂ (Bits w × Equiv.Perm (Fin N)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Bits w × Equiv.Perm (Fin N)) :=
  linearLift (exactOrdinaryBasis encode inverse x)

def exactMarked (encode : Encoding N w) (inverse : Bool) (x : Fin N) :
    EuclideanSpace ℂ ((Bool × Bits w) × Equiv.Perm (Fin N)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Bool × Bits w) × Equiv.Perm (Fin N)) :=
  linearLift (exactMarkedBasis encode inverse x)

theorem exactOrdinary_isometry (encode : Encoding N w) (inverse : Bool) (x : Fin N) :
    Isometry (exactOrdinary encode inverse x) := (exactOrdinary encode inverse x).isometry

theorem exactMarked_isometry (encode : Encoding N w) (inverse : Bool) (x : Fin N) :
    Isometry (exactMarked encode inverse x) := (exactMarked encode inverse x).isometry

theorem exactOrdinary_basis_action (encode : Encoding N w) (inverse : Bool)
    (x : Fin N) (z : Bits w) (π : Equiv.Perm (Fin N)) :
    exactOrdinary encode inverse x (EuclideanSpace.single (z, π) 1) =
      EuclideanSpace.single (xor z (encode (permutationAnswer inverse π x)), π) 1 := by
  rw [exactOrdinary, linearLift_single]
  rfl

theorem exactMarked_basis_action (encode : Encoding N w) (inverse : Bool)
    (x : Fin N) (z : Bool × Bits w) (π : Equiv.Perm (Fin N)) :
    exactMarked encode inverse x (EuclideanSpace.single (z, π) 1) =
      EuclideanSpace.single
        ((Bool.xor z.1 true, xor z.2 (encode (permutationAnswer inverse π x))), π) 1 := by
  rw [exactMarked, linearLift_single]
  rfl

end ExactQuery

section CoherentControl

/-- A coherent control qubit: both branches are present in one linear map. -/
def controlled {Y : Type*} [Fintype Y] (e : Equiv.Perm Y) :
    EuclideanSpace ℂ (Bool × Y) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × Y) :=
  linearLift (BasisLookup.controlled e)

theorem controlled_isometry {Y : Type*} [Fintype Y] (e : Equiv.Perm Y) :
    Isometry (controlled e) := (controlled e).isometry

theorem controlled_false {Y : Type*} [Fintype Y] [DecidableEq Y]
    (e : Equiv.Perm Y) (y : Y) :
    controlled e (EuclideanSpace.single (false, y) 1) =
      EuclideanSpace.single (false, y) 1 := by
  rw [controlled, linearLift_single, BasisLookup.controlled_false]

theorem controlled_true {Y : Type*} [Fintype Y] [DecidableEq Y]
    (e : Equiv.Perm Y) (y : Y) :
    controlled e (EuclideanSpace.single (true, y) 1) =
      EuclideanSpace.single (true, e y) 1 := by
  rw [controlled, linearLift_single, BasisLookup.controlled_true]

/-- Coherent selection of point, direction, or both. The index remains intact. -/
def indexedBasis {C Y : Type*} (action : C → Equiv.Perm Y) :
    Equiv.Perm (C × Y) where
  toFun := fun cy => (cy.1, action cy.1 cy.2)
  invFun := fun cy => (cy.1, (action cy.1).symm cy.2)
  left_inv := by rintro ⟨c, y⟩; simp
  right_inv := by rintro ⟨c, y⟩; simp

def indexed {C Y : Type*} [Fintype C] [Fintype Y]
    (action : C → Equiv.Perm Y) :
    EuclideanSpace ℂ (C × Y) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (C × Y) :=
  linearLift (indexedBasis action)

theorem indexed_isometry {C Y : Type*} [Fintype C] [Fintype Y]
    (action : C → Equiv.Perm Y) : Isometry (indexed action) :=
  (indexed action).isometry

theorem indexed_basis_action {C Y : Type*} [Fintype C] [Fintype Y]
    [DecidableEq C] [DecidableEq Y] (action : C → Equiv.Perm Y) (c : C) (y : Y) :
    indexed action (EuclideanSpace.single (c, y) 1) =
      EuclideanSpace.single (c, action c y) 1 := by
  rw [indexed, linearLift_single]
  rfl

end CoherentControl

end QuantumOracle.Query
