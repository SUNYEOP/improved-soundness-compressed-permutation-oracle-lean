import QuantumOracle.Proof.JointSpectralDecomposition
import QuantumOracle.Proof.SpechtRestrictionHomReverse
import QuantumOracle.Proof.SpechtBranchingPaths

/-! # Actual one-corner support of the residual spectral splitting -/

noncomputable section

namespace QuantumOracle.ResidualBranchSupport

open PermutationExtensions SpechtFoundation SpechtIsotypic
open ResidualPermutation ResidualEquivariance ResidualSpectralSymmetry KernelEquivariance
open scoped BigOperators Classical

theorem component_equiv_copies (N : ℕ) (la : Nat.Partition N) :
    ∃ n : ℕ, Nonempty (component N la ≃ₗ[GroupAlgebra N] (Fin n → specht N la)) := by
  letI := specht_simple N la
  letI : Module.Finite (GroupAlgebra N) (component N la) :=
    Module.Finite.of_restrictScalars_finite ℂ (GroupAlgebra N) (component N la)
  exact (IsIsotypicOfType.isotypicComponent (GroupAlgebra N) (GroupAlgebra N)
    (specht N la)).linearEquiv_fun

theorem component_map_eq_zero_of_not_mem {N : ℕ} (la : Nat.Partition (N + 1))
    (mu : Nat.Partition N) (hm : mu ∉ removeCorners la)
    (f : component (N + 1) la →ₗ[ℂ] component N mu)
    (heq : ∀ σ : Perm N, ∀ v : component (N + 1) la,
      f (MonoidAlgebra.of ℂ (Perm (N + 1)) (includePerm N σ) • v) =
        MonoidAlgebra.of ℂ (Perm N) σ • f v) : f = 0 := by
  obtain ⟨m, ⟨el⟩⟩ := component_equiv_copies (N + 1) la
  obtain ⟨n, ⟨em⟩⟩ := component_equiv_copies N mu
  let F : (Fin m → specht (N + 1) la) →ₗ[ℂ] (Fin n → specht N mu) :=
    (em.restrictScalars ℂ).toLinearMap.comp (f.comp (el.symm.restrictScalars ℂ).toLinearMap)
  have hF (σ : Perm N) (v : Fin m → specht (N + 1) la) :
      F (MonoidAlgebra.of ℂ (Perm (N + 1)) (includePerm N σ) • v) =
        MonoidAlgebra.of ℂ (Perm N) σ • F v := by
    change em (f (el.symm (MonoidAlgebra.of ℂ (Perm (N + 1)) (includePerm N σ) • v))) =
      MonoidAlgebra.of ℂ (Perm N) σ • em (f (el.symm v))
    rw [map_smul, heq, map_smul]
  have hz (i : Fin m) (j : Fin n) (v : specht (N + 1) la) :
      F (Pi.single i v) j = 0 := by
    let g : SpechtRestrictionHomReverse.Hom N mu la :=
      { toLinearMap := (LinearMap.proj j).comp (F.comp (LinearMap.single ℂ _ i))
        isIntertwining' σ := by
          apply LinearMap.ext
          intro v
          change F (Pi.single i (MonoidAlgebra.of ℂ (Perm (N + 1)) (includePerm N σ) • v)) j =
            MonoidAlgebra.of ℂ (Perm N) σ • F (Pi.single i v) j
          rw [Pi.single_smul, hF]
          rfl }
    have hg := SpechtRestrictionHomReverse.hom_eq_zero_of_not_mem N mu la hm g
    exact congrArg (fun k : SpechtRestrictionHomReverse.Hom N mu la => k v) hg
  apply LinearMap.ext
  intro v
  apply em.injective
  rw [LinearMap.zero_apply, map_zero]
  have hFe : F (el v) = em (f v) := by
    change em (f (el.symm (el v))) = em (f v)
    rw [LinearEquiv.symm_apply_apply]
  rw [← hFe]
  rw [← Finset.univ_sum_single (el v), map_sum]
  ext j
  simp only [Finset.sum_apply, Pi.zero_apply, hz, Finset.sum_const_zero]

/-- Project the actual restricted answer into the entire residual Specht block. -/
def projectRestrict {N : ℕ} (x y : Fin (N + 1)) (mu : Nat.Partition N) :
    EuclideanSpace ℂ (Perm (N + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Perm N) :=
  (SpechtIsotypic.space N mu).starProjection.toLinearMap.comp (ResidualAdjoint.restrict x y)

theorem projectRestrict_stabilizer {N : ℕ} (x y : Fin (N + 1))
    (mu : Nat.Partition N) (σ : Perm N) (h : EuclideanSpace ℂ (Perm (N + 1))) :
    projectRestrict x y mu (relabelOperator (Equiv.refl _) (stabilizerEmbed y σ) h) =
      relabelOperator (Equiv.refl _) σ (projectRestrict x y mu h) := by
  have he := ResidualEquivariance.restrict_relabel x y 1 σ h
  rw [map_one] at he
  change (SpechtIsotypic.space N mu).starProjection
      (ResidualAdjoint.restrict x y (relabelOperator 1 (stabilizerEmbed y σ) h)) = _
  rw [he]
  exact SpechtOrthogonal.projection_relabel_left N mu σ _

theorem stabilizerEmbed_last (N : ℕ) (σ : Perm N) :
    stabilizerEmbed (Fin.last N) σ = includePerm N σ :=
  (SpechtBranchingPaths.includePerm_eq_insert N σ).symm

private def restrictionLinear {N : ℕ} (x : Fin (N + 1)) (mu : Nat.Partition N) :
    GroupAlgebra (N + 1) →ₗ[ℂ] GroupAlgebra N :=
  (GramConvolution.equiv N).toLinearMap.comp
    ((projectRestrict x (Fin.last N) mu).comp (GramConvolution.equiv (N + 1)).symm.toLinearMap)

private theorem restrictionLinear_mem {N : ℕ} (x : Fin (N + 1)) (mu : Nat.Partition N)
    (a : GroupAlgebra (N + 1)) : restrictionLinear x mu a ∈ component N mu :=
  (SpechtIsotypic.space N mu).starProjection_apply_mem _

private theorem restrictionLinear_mul_basis {N : ℕ} (x : Fin (N + 1))
    (mu : Nat.Partition N) (σ : Perm N) (a : GroupAlgebra (N + 1)) :
    restrictionLinear x mu (MonoidAlgebra.of ℂ (Perm (N + 1)) (includePerm N σ) * a) =
      MonoidAlgebra.of ℂ (Perm N) σ * restrictionLinear x mu a := by
  have he : (GramConvolution.equiv (N + 1)).symm
      (MonoidAlgebra.of ℂ (Perm (N + 1)) (includePerm N σ) * a) =
      relabelOperator (Equiv.refl _) (stabilizerEmbed (Fin.last N) σ)
        ((GramConvolution.equiv (N + 1)).symm a) := by
    apply (GramConvolution.equiv (N + 1)).injective
    rw [LinearEquiv.apply_symm_apply, GramConvolution.equiv_relabel_left,
      LinearEquiv.apply_symm_apply, stabilizerEmbed_last]
  change GramConvolution.equiv N (projectRestrict x (Fin.last N) mu
      ((GramConvolution.equiv (N + 1)).symm (_ * a))) = _
  rw [he, projectRestrict_stabilizer, GramConvolution.equiv_relabel_left]
  rfl

private def restrictionComponent {N : ℕ} (x : Fin (N + 1))
    (la : Nat.Partition (N + 1)) (mu : Nat.Partition N) :
    component (N + 1) la →ₗ[ℂ] component N mu where
  toFun a := ⟨restrictionLinear x mu a.val, restrictionLinear_mem x mu a.val⟩
  map_add' a b := Subtype.ext ((restrictionLinear x mu).map_add a.val b.val)
  map_smul' c a := Subtype.ext ((restrictionLinear x mu).map_smul c a.val)

theorem projectRestrict_last_eq_zero_of_not_mem {N : ℕ} (x : Fin (N + 1))
    (la : Nat.Partition (N + 1)) (mu : Nat.Partition N) (hm : mu ∉ removeCorners la)
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ SpechtIsotypic.space (N + 1) la) :
    projectRestrict x (Fin.last N) mu h = 0 := by
  have hf := component_map_eq_zero_of_not_mem la mu hm (restrictionComponent x la mu) (by
    intro σ v
    apply Subtype.ext
    exact restrictionLinear_mul_basis x mu σ v.val)
  have he := congrArg
    (fun f : component (N + 1) la →ₗ[ℂ] component N mu =>
      (f ⟨GramConvolution.equiv (N + 1) h, hh⟩).val) hf
  apply (GramConvolution.equiv N).injective
  change restrictionLinear x mu (GramConvolution.equiv (N + 1) h) = 0 at he
  change GramConvolution.equiv N (projectRestrict x (Fin.last N) mu
    ((GramConvolution.equiv (N + 1)).symm (GramConvolution.equiv (N + 1) h))) = 0 at he
  rw [LinearEquiv.symm_apply_apply] at he
  simpa only [map_zero] using he

/-- Transport any actual answer to the last answer without changing residual labels. -/
theorem restrict_move_answer {N : ℕ} (x y : Fin (N + 1))
    (h : EuclideanSpace ℂ (Perm (N + 1))) :
    ResidualAdjoint.restrict x (Fin.last N)
      (relabelOperator (Equiv.refl _) (insert y (Fin.last N) 1) h) =
      ResidualAdjoint.restrict x y h := by
  ext σ
  have hp : relabelPerm (Equiv.refl _) (insert y (Fin.last N) 1) (insert x y σ) =
      insert x (Fin.last N) σ := by
    change insert y (Fin.last N) 1 * insert x y σ = _
    rw [insert_mul, one_mul]
  rw [ResidualAdjoint.restrict_apply, ResidualAdjoint.restrict_apply, ← hp]
  exact Query.linearLift_apply _ _ _

/-- Off the corner relation, every actual answer restriction has zero projection
onto the residual type. This includes all copies of the full Specht module. -/
theorem projectRestrict_eq_zero_of_not_mem {N : ℕ} (x y : Fin (N + 1))
    (la : Nat.Partition (N + 1)) (mu : Nat.Partition N) (hm : mu ∉ removeCorners la)
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ SpechtIsotypic.space (N + 1) la) :
    projectRestrict x y mu h = 0 := by
  have hz := projectRestrict_last_eq_zero_of_not_mem x la mu hm
    (SpechtOrthogonal.relabel_left_mem la (insert y (Fin.last N) 1) hh)
  change (SpechtIsotypic.space N mu).starProjection
    (ResidualAdjoint.restrict x (Fin.last N)
      (relabelOperator (Equiv.refl _) (insert y (Fin.last N) 1) h)) = 0 at hz
  rw [restrict_move_answer] at hz
  exact hz

/-- An actual joint full/residual vector outside the corner relation is zero. -/
theorem joint_eq_zero_of_not_mem {N : ℕ} (x : Fin (N + 1))
    (label : JointSpectralDecomposition.Labels N) (hm : label.2 ∉ removeCorners label.1)
    {h : EuclideanSpace ℂ (Perm (N + 1))}
    (hh : h ∈ JointSpectralDecomposition.space x label) : h = 0 := by
  apply ResidualSpectralDecomposition.restrict_ext x
  intro y
  rw [map_zero]
  have hr := (ResidualSpectralDecomposition.mem_space x label.2 h).mp hh.2 y
  have hz := projectRestrict_eq_zero_of_not_mem x y label.1 label.2 hm hh.1
  change (SpechtIsotypic.space N label.2).starProjection (ResidualAdjoint.restrict x y h) = 0 at hz
  rwa [(SpechtIsotypic.space N label.2).starProjection_eq_self_iff.mpr hr] at hz

/-- Every nonzero actual joint component satisfies the genuine corner condition. -/
theorem mem_removeCorners_of_joint_ne_zero {N : ℕ} (x : Fin (N + 1))
    (label : JointSpectralDecomposition.Labels N)
    {h : EuclideanSpace ℂ (Perm (N + 1))}
    (hh : h ∈ JointSpectralDecomposition.space x label) (hne : h ≠ 0) :
    label.2 ∈ removeCorners label.1 := by
  by_contra hm
  exact hne (joint_eq_zero_of_not_mem x label hm hh)

theorem joint_project_eq_zero_of_not_mem {N : ℕ} (x : Fin (N + 1))
    (label : JointSpectralDecomposition.Labels N) (hm : label.2 ∉ removeCorners label.1)
    (h : EuclideanSpace ℂ (Perm (N + 1))) : JointSpectralDecomposition.project x label h = 0 :=
  joint_eq_zero_of_not_mem x label hm (JointSpectralDecomposition.project_mem x label h)

theorem joint_space_eq_bot_of_not_mem {N : ℕ} (x : Fin (N + 1))
    (label : JointSpectralDecomposition.Labels N) (hm : label.2 ∉ removeCorners label.1) :
    JointSpectralDecomposition.space x label = ⊥ := by
  apply bot_unique
  intro h hh
  exact joint_eq_zero_of_not_mem x label hm hh

end QuantumOracle.ResidualBranchSupport
