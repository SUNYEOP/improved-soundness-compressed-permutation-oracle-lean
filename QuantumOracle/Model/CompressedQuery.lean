import QuantumOracle.Model.Compression
import QuantumOracle.Model.Query

/-! Actual `cpO = pC P pC`, including inverse and coherent controlled queries.
No harmonic comparison or soundness bound is assumed by these constructions. -/

noncomputable section

-- Nested finite-coordinate isometry transports require deeper elaboration.
set_option maxRecDepth 4096

namespace QuantumOracle.CompressedQuery

open BasisLookup

variable {N w : ℕ}

/-- Compression leaves an arbitrary answer register unchanged. -/
@[irreducible] def compression (Y : Type*) [Fintype Y] (x : Fin N) :
    EuclideanSpace ℂ (Y × Database N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Y × Database N) :=
  BlockOperator.onRight Y (Compression.pC x)

@[simp] theorem compression_apply {Y : Type*} [Fintype Y]
    (x : Fin N) (ψ : EuclideanSpace ℂ (Y × Database N)) (y : Y) (I : Database N) :
    compression Y x ψ (y, I) =
      Compression.pC x (WithLp.toLp 2 (fun J => ψ (y, J))) I := by
  unfold compression
  rfl

@[simp] theorem compression_involutive {Y : Type*} [Fintype Y]
    (x : Fin N) (ψ : EuclideanSpace ℂ (Y × Database N)) :
    compression Y x (compression Y x ψ) = ψ := by
  unfold compression BlockOperator.onRight
  exact BlockOperator.family_involutive (fun _ : Y => Compression.pC x)
    (fun _ => Compression.pC_involutive x) ψ

/-- The exact forward compressed ordinary query in Section 2.2. -/
@[irreducible] def ordinary (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ (Bits w × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Bits w × Database N) :=
  (compression (Bits w) x).trans
    ((Query.ordinaryLookup encode x).trans (compression (Bits w) x))

/-- The exact forward compressed marked query in Section 2.3. -/
@[irreducible] def marked (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ ((Bool × Bits w) × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Bool × Bits w) × Database N) :=
  (compression (Bool × Bits w) x).trans
    ((Query.markedLookup encode x).trans (compression (Bool × Bits w) x))

@[simp] theorem ordinary_apply (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ (Bits w × Database N)) :
    ordinary encode x ψ = compression (Bits w) x
      (Query.ordinaryLookup encode x (compression (Bits w) x ψ)) := by
  unfold ordinary
  rfl

@[simp] theorem marked_apply (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Database N)) :
    marked encode x ψ = compression (Bool × Bits w) x
      (Query.markedLookup encode x (compression (Bool × Bits w) x ψ)) := by
  unfold marked
  rfl

/-- Actual database inversion as a complex linear isometry equivalence. -/
def flip (Y : Type*) [Fintype Y] :
    EuclideanSpace ℂ (Y × Database N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Y × Database N) :=
  Query.linearLift BasisLookup.flip

def inverseOrdinary (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ (Bits w × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Bits w × Database N) :=
  (flip (Bits w)).trans ((ordinary encode x).trans (flip (Bits w)))

def inverseMarked (encode : Encoding N w) (x : Fin N) :
    EuclideanSpace ℂ ((Bool × Bits w) × Database N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Bool × Bits w) × Database N) :=
  (flip (Bool × Bits w)).trans ((marked encode x).trans (flip (Bool × Bits w)))

/-- An actual coherent query on the point and direction registers. -/
def ordinaryTwoSided (encode : Encoding N w) :
    EuclideanSpace ℂ ((Bool × Fin N) × (Bits w × Database N)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Bool × Fin N) × (Bits w × Database N)) :=
  BlockOperator.family (fun bx => if bx.1 then inverseOrdinary encode bx.2
    else ordinary encode bx.2)

def markedTwoSided (encode : Encoding N w) :
    EuclideanSpace ℂ ((Bool × Fin N) × ((Bool × Bits w) × Database N)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Bool × Fin N) × ((Bool × Bits w) × Database N)) :=
  BlockOperator.family (fun bx => if bx.1 then inverseMarked encode bx.2
    else marked encode bx.2)

/-- Coherent on/off control of any of the constructed compressed query maps. -/
def controlled {Y : Type*} [Fintype Y]
    (U : EuclideanSpace ℂ Y ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y) :
    EuclideanSpace ℂ (Bool × Y) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × Y) :=
  BlockOperator.family (fun b => if b then U else LinearIsometryEquiv.refl ℂ _)

theorem ordinary_isometry (encode : Encoding N w) (x : Fin N) :
    Isometry (ordinary encode x) := (ordinary encode x).isometry

theorem marked_isometry (encode : Encoding N w) (x : Fin N) :
    Isometry (marked encode x) := (marked encode x).isometry

theorem ordinaryTwoSided_isometry (encode : Encoding N w) :
    Isometry (ordinaryTwoSided encode) := (ordinaryTwoSided encode).isometry

theorem markedTwoSided_isometry (encode : Encoding N w) :
    Isometry (markedTwoSided encode) := (markedTwoSided encode).isometry

/-- An involutive basis permutation lifts to an involutive Hilbert operator. -/
theorem linearLift_involutive {Y : Type*} [Fintype Y] (e : Equiv.Perm Y)
    (he : Function.Involutive e) (ψ : EuclideanSpace ℂ Y) :
    Query.linearLift e (Query.linearLift e ψ) = ψ := by
  have hinv : e.symm = e := by
    apply Equiv.ext
    intro y
    apply e.injective
    rw [e.apply_symm_apply, he y]
  ext y
  change ψ (e.symm (e.symm y)) = ψ y
  rw [hinv, he y]

@[simp] theorem ordinaryLookup_involutive (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ (Bits w × Database N)) :
    Query.ordinaryLookup encode x (Query.ordinaryLookup encode x ψ) = ψ :=
  linearLift_involutive _ (BasisLookup.ordinary_involutive encode x) ψ

@[simp] theorem markedLookup_involutive (encode : Encoding N w) (x : Fin N)
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Database N)) :
    Query.markedLookup encode x (Query.markedLookup encode x ψ) = ψ :=
  linearLift_involutive _ (BasisLookup.marked_involutive encode x) ψ

/-- Conjugating one involution by another yields an involution. -/
theorem sandwich_involutive {E : Type*} (P U : E → E)
    (hP : Function.Involutive P) (hU : Function.Involutive U) :
    Function.Involutive (fun v => P (U (P v))) := by
  intro v
  change P (U (P (P (U (P v))))) = v
  rw [hP, hU, hP]

@[simp] theorem flip_involutive {Y : Type*} [Fintype Y]
    (ψ : EuclideanSpace ℂ (Y × Database N)) :
    flip Y (N := N) (flip Y ψ) = ψ := by
  ext ⟨y, I⟩
  change ψ (y, I.inverse.inverse) = ψ (y, I)
  rw [Database.inverse_inverse]

end QuantumOracle.CompressedQuery
