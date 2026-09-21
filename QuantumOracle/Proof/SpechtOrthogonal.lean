import QuantumOracle.Proof.SpechtIsotypic

/-!
# Hilbert orthogonality of the actual full Specht isotypic blocks

Actual left translations are unitary. Consequently Hilbert projection onto
an invariant block commutes with those translations and is linear over the
whole group algebra. It therefore preserves every isotypic component. Since
distinct Specht types are nonisomorphic, projection from one full block onto
another is zero. No distinctness of Gram eigenvalues is required.
-/

noncomputable section

namespace QuantumOracle.SpechtOrthogonal

open PermutationExtensions GramConvolution SpechtIsotypic KernelEquivariance
open scoped InnerProductSpace BigOperators

theorem component_ne {N : ℕ} {la mu : Nat.Partition N} (hne : la ≠ mu) :
    component N la ≠ component N mu := by
  letI := SpechtFoundation.specht_simple N la
  letI := SpechtFoundation.specht_simple N mu
  intro he
  have hl : SpechtFoundation.specht N la ≤ component N mu :=
    (specht_le_component N la).trans_eq he
  obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent (GroupAlgebra N) (GroupAlgebra N)
      (SpechtFoundation.specht N mu)) (SpechtFoundation.specht N la) hl
  exact (RepresentationTheory.PartitionLinearEquivBoundsAndMonoidAlgebra.isEmpty_linearEquiv_of_ne_partition
    N la mu hne).false e

theorem component_disjoint {N : ℕ} {la mu : Nat.Partition N} (hne : la ≠ mu) :
    Disjoint (component N la) (component N mu) := by
  have hl : component N la ∈ isotypicComponents (GroupAlgebra N) (GroupAlgebra N) :=
    ⟨SpechtFoundation.specht N la, SpechtFoundation.specht_simple N la, rfl⟩
  have hm : component N mu ∈ isotypicComponents (GroupAlgebra N) (GroupAlgebra N) :=
    ⟨SpechtFoundation.specht N mu, SpechtFoundation.specht_simple N mu, rfl⟩
  exact (sSupIndep_isotypicComponents (GroupAlgebra N) (GroupAlgebra N)).pairwiseDisjoint
    hl hm (component_ne hne)

theorem relabel_left_mem {N : ℕ} (la : Nat.Partition N) (π : Perm N)
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N la) :
    relabelOperator (Equiv.refl _) π h ∈ space N la := by
  rw [mem_space, equiv_relabel_left]
  exact (component N la).smul_mem (MonoidAlgebra.of ℂ (Perm N) π) hh

theorem map_space_relabel_left (N : ℕ) (la : Nat.Partition N) (π : Perm N) :
    (space N la).map (relabelOperator (Equiv.refl _) π).toLinearMap = space N la := by
  apply le_antisymm
  · rintro _ ⟨h, hh, rfl⟩
    exact relabel_left_mem la π hh
  · intro h hh
    refine ⟨relabelOperator (Equiv.refl _) π⁻¹ h, relabel_left_mem la π⁻¹ hh, ?_⟩
    apply (equiv N).injective
    change equiv N (relabelOperator (Equiv.refl _) π
      (relabelOperator (Equiv.refl _) π⁻¹ h)) = equiv N h
    rw [equiv_relabel_left, equiv_relabel_left, ← mul_assoc, ← map_mul]
    simp only [mul_inv_cancel, map_one, one_mul]

/-- The actual Hilbert projection commutes with the actual unitary regular action. -/
theorem projection_relabel_left (N : ℕ) (la : Nat.Partition N) (π : Perm N)
    (h : EuclideanSpace ℂ (Perm N)) :
    (space N la).starProjection (relabelOperator (Equiv.refl _) π h) =
      relabelOperator (Equiv.refl _) π ((space N la).starProjection h) := by
  have he := (relabelOperator (Equiv.refl _) π).toLinearIsometry.map_starProjection
    (space N la) h
  change relabelOperator (Equiv.refl _) π ((space N la).starProjection h) =
    ((space N la).map (relabelOperator (Equiv.refl _) π).toLinearMap).starProjection
      (relabelOperator (Equiv.refl _) π h) at he
  simpa only [map_space_relabel_left] using he.symm

/-- Coefficient transport of the actual Hilbert orthogonal projection. -/
def projectionLinear (N : ℕ) (la : Nat.Partition N) :
    GroupAlgebra N →ₗ[ℂ] GroupAlgebra N :=
  (equiv N).toLinearMap.comp
    (((space N la).starProjection.toLinearMap).comp (equiv N).symm.toLinearMap)

@[simp] theorem projectionLinear_apply (N : ℕ) (la : Nat.Partition N) (a : GroupAlgebra N) :
    projectionLinear N la a = equiv N ((space N la).starProjection ((equiv N).symm a)) := rfl

theorem projectionLinear_mul_basis (N : ℕ) (la : Nat.Partition N)
    (π : Perm N) (a : GroupAlgebra N) :
    projectionLinear N la (MonoidAlgebra.of ℂ (Perm N) π * a) =
      MonoidAlgebra.of ℂ (Perm N) π * projectionLinear N la a := by
  have he : (equiv N).symm (MonoidAlgebra.of ℂ (Perm N) π * a) =
      relabelOperator (Equiv.refl _) π ((equiv N).symm a) := by
    apply (equiv N).injective
    rw [LinearEquiv.apply_symm_apply, equiv_relabel_left, LinearEquiv.apply_symm_apply]
  rw [projectionLinear_apply, he, projection_relabel_left, equiv_relabel_left,
    projectionLinear_apply]

/-- The actual Hilbert projection is linear over the regular group algebra. -/
def projectionAlgebra (N : ℕ) (la : Nat.Partition N) :
    GroupAlgebra N →ₗ[GroupAlgebra N] GroupAlgebra N where
  toFun := projectionLinear N la
  map_add' := (projectionLinear N la).map_add
  map_smul' a b := by
    change projectionLinear N la (a * b) = a * projectionLinear N la b
    induction a using MonoidAlgebra.induction_on with
    | hM π => exact projectionLinear_mul_basis N la π b
    | hadd a c ha hc => rw [add_mul, map_add, ha, hc, add_mul]
    | hsmul c a ha => rw [smul_mul_assoc, map_smul, ha, smul_mul_assoc]

@[simp] theorem projectionAlgebra_apply (N : ℕ) (la : Nat.Partition N) (a : GroupAlgebra N) :
    projectionAlgebra N la a = equiv N ((space N la).starProjection ((equiv N).symm a)) := rfl

/-- As a module map, Hilbert projection preserves every actual isotypic block. -/
theorem projection_mem_space (N : ℕ) (la mu : Nat.Partition N)
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N mu) :
    (space N la).starProjection h ∈ space N mu := by
  letI := SpechtFoundation.specht_simple N mu
  have hm := (LinearMap.le_comap_isotypicComponent (SpechtFoundation.specht N mu)
    (projectionAlgebra N la)) hh
  change projectionAlgebra N la (equiv N h) ∈ component N mu at hm
  rw [mem_space]
  simpa only [projectionAlgebra_apply, LinearEquiv.symm_apply_apply] using hm

theorem projection_eq_zero_of_ne {N : ℕ} {la mu : Nat.Partition N} (hne : la ≠ mu)
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N mu) :
    (space N la).starProjection h = 0 := by
  have hl := (space N la).starProjection_apply_mem h
  have hm := projection_mem_space N la mu hh
  have hz : equiv N ((space N la).starProjection h) ∈ component N la ⊓ component N mu :=
    ⟨hl, hm⟩
  rw [(component_disjoint hne).eq_bot] at hz
  apply (equiv N).injective
  change equiv N ((space N la).starProjection h) = 0 at hz
  exact hz.trans (map_zero _).symm

/-- Distinct partition types are perpendicular in the actual permutation Hilbert space. -/
theorem space_le_orthogonal {N : ℕ} {la mu : Nat.Partition N} (hne : la ≠ mu) :
    space N mu ≤ (space N la)ᗮ := by
  intro h hh
  have ho := (space N la).sub_starProjection_mem_orthogonal h
  rw [projection_eq_zero_of_ne hne hh, sub_zero] at ho
  exact ho

theorem inner_eq_zero {N : ℕ} {la mu : Nat.Partition N} (hne : la ≠ mu)
    {h k : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N la) (hk : k ∈ space N mu) :
    ⟪h, k⟫_ℂ = 0 :=
  Submodule.inner_right_of_mem_orthogonal hh (space_le_orthogonal hne hk)

attribute [local irreducible] SpechtIsotypic.space

local instance blockInnerProductSpace (N : ℕ) :
    (la : Nat.Partition N) → InnerProductSpace ℂ ↥(space N la) := fun _ => inferInstance

/-- The actual full blocks form an orthogonal family, including all multiplicities. -/
theorem orthogonalFamily (N : ℕ) :
    OrthogonalFamily ℂ (fun la : Nat.Partition N => ↥(space N la))
      (fun la => (space N la).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro la mu hne
  exact Submodule.IsOrtho.symm (space_le_orthogonal hne)

/-- Their actual orthogonal projections reconstruct every permutation-register vector. -/
theorem sum_projection (N : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    (∑ la : Nat.Partition N, (space N la).starProjection h) = h := by
  apply (orthogonalFamily N).sum_projection_of_mem_iSup
  rw [iSup_space_eq_top]
  exact Submodule.mem_top

end QuantumOracle.SpechtOrthogonal
