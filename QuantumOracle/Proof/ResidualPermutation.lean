import QuantumOracle.Model.PermutationExtensions
import QuantumOracle.Model.Query
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Actual residual permutations after fixing one answer

Removing input x and output y uses their increasing `Fin.succAbove` labelings.
The resulting bijections identify the genuine answer fiber with permutations
of the remaining N labels, including the boundary N = 0.
-/

noncomputable section

namespace QuantumOracle.ResidualPermutation

open PermutationExtensions

variable {N : ℕ}

/-- A residual permutation extended by the actual edge x ↦ y. -/
def insert (x y : Fin (N + 1)) (σ : Perm N) : Perm (N + 1) :=
  (finSuccEquiv' x).trans (σ.optionCongr.trans (finSuccEquiv' y).symm)

@[simp] theorem insert_at (x y : Fin (N + 1)) (σ : Perm N) :
    insert x y σ x = y := by
  simp [insert]

@[simp] theorem insert_succAbove (x y : Fin (N + 1)) (σ : Perm N) (a : Fin N) :
    insert x y σ (x.succAbove a) = y.succAbove (σ a) := by
  simp [insert]

/-- The genuine permutations answering y at x. -/
abbrev Fiber (x y : Fin (N + 1)) := {π : Perm (N + 1) // π x = y}

/-- Restriction of an actual fiber permutation to the complementary label sets. -/
def complement (x y : Fin (N + 1)) (π : Fiber x y) :
    {a : Fin (N + 1) // a ≠ x} ≃ {b : Fin (N + 1) // b ≠ y} :=
  π.val.subtypeEquiv (fun a => by
    have h : a ≠ x ↔ π.val a ≠ π.val x := π.val.injective.ne_iff.symm
    simpa only [π.property] using h)

/-- Remove the fixed input and output, using the actual increasing residual labels. -/
def remove (x y : Fin (N + 1)) (π : Fiber x y) : Perm N :=
  (finSuccAboveEquiv x).trans ((complement x y π).trans (finSuccAboveEquiv y).symm)

theorem remove_succAbove (x y : Fin (N + 1)) (π : Fiber x y) (a : Fin N) :
    y.succAbove (remove x y π a) = π.val (x.succAbove a) := by
  have h := (finSuccAboveEquiv y).apply_symm_apply
    (complement x y π (finSuccAboveEquiv x a))
  exact congrArg Subtype.val h

@[simp] theorem insert_remove (x y : Fin (N + 1)) (π : Fiber x y) :
    insert x y (remove x y π) = π.val := by
  apply Equiv.ext
  intro a
  by_cases ha : a = x
  · subst a
    rw [insert_at, π.property]
  · obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq ha
    rw [insert_succAbove, remove_succAbove]

@[simp] theorem remove_insert (x y : Fin (N + 1)) (σ : Perm N) :
    remove x y ⟨insert x y σ, insert_at x y σ⟩ = σ := by
  apply Equiv.ext
  intro a
  apply Fin.succAbove_right_injective (p := y)
  rw [remove_succAbove, insert_succAbove]

/-- Residual permutations are exactly the concrete answer fiber. -/
def fiberEquiv (x y : Fin (N + 1)) : Perm N ≃ Fiber x y where
  toFun σ := ⟨insert x y σ, insert_at x y σ⟩
  invFun := remove x y
  left_inv := remove_insert x y
  right_inv π := Subtype.ext (insert_remove x y π)

@[simp] theorem fiberEquiv_apply (x y : Fin (N + 1)) (σ : Perm N) :
    (fiberEquiv x y σ).val = insert x y σ := rfl

@[simp] theorem fiberEquiv_symm_apply (x y : Fin (N + 1)) (π : Fiber x y) :
    (fiberEquiv x y).symm π = remove x y π := rfl

theorem insert_injective (x y : Fin (N + 1)) : Function.Injective (insert x y) := by
  intro σ τ h
  apply (fiberEquiv x y).injective
  exact Subtype.ext h

/-- Split every actual permutation into its answer and its residual permutation. -/
def answerEquiv (x : Fin (N + 1)) : Perm (N + 1) ≃ Σ _ : Fin (N + 1), Perm N :=
  (Equiv.sigmaFiberEquiv (fun π : Perm (N + 1) => π x)).symm.trans
    (Equiv.sigmaCongrRight (fun y => (fiberEquiv x y).symm))

@[simp] theorem answerEquiv_apply (x : Fin (N + 1)) (π : Perm (N + 1)) :
    answerEquiv x π = ⟨π x, remove x (π x) ⟨π, rfl⟩⟩ := rfl

@[simp] theorem answerEquiv_symm_apply (x y : Fin (N + 1)) (σ : Perm N) :
    (answerEquiv x).symm ⟨y, σ⟩ = insert x y σ := rfl

/-- Inverting the full permutation exchanges the removed input and output. -/
@[simp] theorem insert_symm (x y : Fin (N + 1)) (σ : Perm N) :
    (insert x y σ).symm = insert y x σ.symm := by
  simp only [insert, Equiv.optionCongr_symm]
  rfl

/-- Genuine isometric splitting of the exact hidden register into answer sectors. -/
def splitIsometry (x : Fin (N + 1)) :
    EuclideanSpace ℂ (Perm (N + 1)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Σ _ : Fin (N + 1), Perm N) :=
  Query.linearLift (answerEquiv x)

@[simp] theorem splitIsometry_apply (x y : Fin (N + 1))
    (ψ : EuclideanSpace ℂ (Perm (N + 1))) (σ : Perm N) :
    splitIsometry x ψ ⟨y, σ⟩ = ψ (insert x y σ) := rfl

@[simp] theorem splitIsometry_single (x : Fin (N + 1)) (π : Perm (N + 1)) (z : ℂ) :
    splitIsometry x (EuclideanSpace.single π z) =
      EuclideanSpace.single (answerEquiv x π) z :=
  Query.linearLift_single (answerEquiv x) π z

/-- Product-form coordinates for the actual answer and residual permutation. -/
def answerProductEquiv (x : Fin (N + 1)) :
    Perm (N + 1) ≃ Fin (N + 1) × Perm N :=
  (answerEquiv x).trans (Equiv.sigmaEquivProd _ _)

@[simp] theorem answerProductEquiv_apply (x : Fin (N + 1)) (π : Perm (N + 1)) :
    answerProductEquiv x π = (π x, remove x (π x) ⟨π, rfl⟩) := rfl

@[simp] theorem answerProductEquiv_symm_apply (x y : Fin (N + 1)) (σ : Perm N) :
    (answerProductEquiv x).symm (y, σ) = insert x y σ := rfl

/-- Actual exact-register reindexing into answer × residual-permutation coordinates. -/
def reindex (x : Fin (N + 1)) :
    EuclideanSpace ℂ (Perm (N + 1)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin (N + 1) × Perm N) :=
  Query.linearLift (answerProductEquiv x)

@[simp] theorem reindex_apply (x y : Fin (N + 1))
    (ψ : EuclideanSpace ℂ (Perm (N + 1))) (σ : Perm N) :
    reindex x ψ (y, σ) = ψ (insert x y σ) := rfl

@[simp] theorem reindex_symm_apply (x : Fin (N + 1))
    (ψ : EuclideanSpace ℂ (Fin (N + 1) × Perm N)) (π : Perm (N + 1)) :
    (reindex x).symm ψ π = ψ (π x, remove x (π x) ⟨π, rfl⟩) := by
  unfold reindex Query.linearLift
  rw [LinearIsometryEquiv.piLpCongrLeft_symm]
  rfl

@[simp] theorem reindex_single (x : Fin (N + 1)) (π : Perm (N + 1)) (z : ℂ) :
    reindex x (EuclideanSpace.single π z) =
      EuclideanSpace.single (answerProductEquiv x π) z :=
  Query.linearLift_single (answerProductEquiv x) π z

end QuantumOracle.ResidualPermutation
