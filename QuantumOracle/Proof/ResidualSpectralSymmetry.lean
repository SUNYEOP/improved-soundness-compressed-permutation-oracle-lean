import QuantumOracle.Proof.ResidualSpectralDecomposition
import QuantumOracle.Proof.ResidualEquivariance

/-!
# Residual spectral projection preserves the full Specht type

An arbitrary output relabeling transports an actual answer sector to another
and acts there by an actual residual left translation. Residual isotypic
projection commutes with that translation. Its transport to the full register
is therefore a map of regular group-algebra modules, preserving every actual
full Specht block. No branching or distinct-eigenvalue assumption is supplied.
-/

noncomputable section

namespace QuantumOracle.ResidualSpectralSymmetry

open PermutationExtensions ResidualPermutation KernelEquivariance GramConvolution
open ResidualSpectralDecomposition

variable {N : ℕ}

theorem insert_mul (x y z : Fin (N + 1)) (σ τ : Perm N) :
    insert y z τ * insert x y σ = insert x z (τ * σ) := by
  apply Equiv.ext
  intro a
  by_cases ha : a = x
  · subst a
    simp only [Equiv.Perm.mul_apply, insert_at]
  · obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq ha
    simp only [Equiv.Perm.mul_apply, insert_succAbove]

/-- Residual permutation induced by an arbitrary full output relabeling. -/
def outputResidual (β : Perm (N + 1)) (y : Fin (N + 1)) : Perm N :=
  remove y (β y) ⟨β, rfl⟩

theorem outputResidual_insert (β : Perm (N + 1)) (x y : Fin (N + 1)) (σ : Perm N) :
    β * insert x y σ = insert x (β y) (outputResidual β y * σ) := by
  have hb : insert y (β y) (outputResidual β y) = β := insert_remove y (β y) ⟨β, rfl⟩
  calc
    β * insert x y σ = insert y (β y) (outputResidual β y) * insert x y σ := by rw [hb]
    _ = _ := insert_mul x y (β y) σ (outputResidual β y)

/-- Actual answer restriction transforms by an actual residual left translation. -/
theorem restrict_relabel_left (β : Perm (N + 1)) (x y : Fin (N + 1))
    (h : EuclideanSpace ℂ (Perm (N + 1))) :
    ResidualAdjoint.restrict x (β y) (relabelOperator (Equiv.refl _) β h) =
      relabelOperator (Equiv.refl _) (outputResidual β y) (ResidualAdjoint.restrict x y h) := by
  ext σ
  obtain ⟨τ, rfl⟩ := (relabelPerm (Equiv.refl _) (outputResidual β y)).surjective σ
  have he : insert x (β y) (relabelPerm (Equiv.refl _) (outputResidual β y) τ) =
      relabelPerm (Equiv.refl _) β (insert x y τ) :=
    (outputResidual_insert β x y τ).symm
  rw [ResidualAdjoint.restrict_apply, he]
  rw [show relabelOperator (Equiv.refl _) β h
      (relabelPerm (Equiv.refl _) β (insert x y τ)) = h (insert x y τ) from
    Query.linearLift_apply _ _ _]
  rw [show relabelOperator (Equiv.refl _) (outputResidual β y) (ResidualAdjoint.restrict x y h)
      (relabelPerm (Equiv.refl _) (outputResidual β y) τ) = ResidualAdjoint.restrict x y h τ from
    Query.linearLift_apply _ _ _]
  rfl

theorem project_relabel_left (x : Fin (N + 1)) (mu : Nat.Partition N)
    (β : Perm (N + 1)) (h : EuclideanSpace ℂ (Perm (N + 1))) :
    project x mu (relabelOperator (Equiv.refl _) β h) =
      relabelOperator (Equiv.refl _) β (project x mu h) := by
  apply restrict_ext x
  intro y
  obtain ⟨z, rfl⟩ := β.surjective y
  rw [restrict_project, restrict_relabel_left, restrict_relabel_left, restrict_project]
  exact SpechtOrthogonal.projection_relabel_left N mu (outputResidual β z) _

/-- Actual residual projection, transported coefficientwise to the full algebra. -/
def projectionLinear (x : Fin (N + 1)) (mu : Nat.Partition N) :
    GroupAlgebra (N + 1) →ₗ[ℂ] GroupAlgebra (N + 1) :=
  (equiv (N + 1)).toLinearMap.comp
    ((project x mu).comp (equiv (N + 1)).symm.toLinearMap)

@[simp] theorem projectionLinear_apply (x : Fin (N + 1)) (mu : Nat.Partition N)
    (a : GroupAlgebra (N + 1)) :
    projectionLinear x mu a = equiv (N + 1) (project x mu ((equiv (N + 1)).symm a)) := rfl

theorem projectionLinear_mul_basis (x : Fin (N + 1)) (mu : Nat.Partition N)
    (β : Perm (N + 1)) (a : GroupAlgebra (N + 1)) :
    projectionLinear x mu (MonoidAlgebra.of ℂ (Perm (N + 1)) β * a) =
      MonoidAlgebra.of ℂ (Perm (N + 1)) β * projectionLinear x mu a := by
  have he : (equiv (N + 1)).symm (MonoidAlgebra.of ℂ (Perm (N + 1)) β * a) =
      relabelOperator (Equiv.refl _) β ((equiv (N + 1)).symm a) := by
    apply (equiv (N + 1)).injective
    rw [LinearEquiv.apply_symm_apply, equiv_relabel_left, LinearEquiv.apply_symm_apply]
  rw [projectionLinear_apply, he, project_relabel_left, equiv_relabel_left, projectionLinear_apply]

/-- The actual residual projection is a map of full regular modules. -/
def projectionAlgebra (x : Fin (N + 1)) (mu : Nat.Partition N) :
    GroupAlgebra (N + 1) →ₗ[GroupAlgebra (N + 1)] GroupAlgebra (N + 1) where
  toFun := projectionLinear x mu
  map_add' := (projectionLinear x mu).map_add
  map_smul' a b := by
    change projectionLinear x mu (a * b) = a * projectionLinear x mu b
    induction a using MonoidAlgebra.induction_on with
    | hM β => exact projectionLinear_mul_basis x mu β b
    | hadd a c ha hc => rw [add_mul, map_add, ha, hc, add_mul]
    | hsmul c a ha => rw [smul_mul_assoc, map_smul, ha, smul_mul_assoc]

/-- Residual splitting does not mix distinct full-domain Specht types. -/
theorem project_mem_full_space (x : Fin (N + 1)) (mu : Nat.Partition N)
    (la : Nat.Partition (N + 1)) {h : EuclideanSpace ℂ (Perm (N + 1))}
    (hh : h ∈ SpechtIsotypic.space (N + 1) la) :
    project x mu h ∈ SpechtIsotypic.space (N + 1) la := by
  letI := SpechtFoundation.specht_simple (N + 1) la
  have hm := (LinearMap.le_comap_isotypicComponent (SpechtFoundation.specht (N + 1) la)
    (projectionAlgebra x mu)) hh
  change projectionLinear x mu (equiv (N + 1) h) ∈ SpechtIsotypic.component (N + 1) la at hm
  rw [SpechtIsotypic.mem_space]
  simpa only [projectionLinear_apply, LinearEquiv.symm_apply_apply] using hm

end QuantumOracle.ResidualSpectralSymmetry
