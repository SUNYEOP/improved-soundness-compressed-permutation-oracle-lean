import QuantumOracle.Proof.SpechtOrthogonal
import QuantumOracle.Proof.ResidualAdjoint

/-!
# Actual answerwise residual Specht projections

Apply the full residual isotypic projection in every actual answer sector,
then undo the actual answer/residual reindexing. These concrete projections
decompose the whole permutation register orthogonally and supply one common
residual Gram eigenvalue in every answer sector. Compatibility with a fixed
full-domain Specht block is a separate obligation.
-/

noncomputable section

namespace QuantumOracle.ResidualSpectralDecomposition

open PermutationExtensions ResidualPermutation WorkspaceKnowledge SpechtIsotypic
open scoped BigOperators InnerProductSpace

variable {N : ℕ}

/-- The actual vectors whose every residual answer slice has type `mu`. -/
def space (x : Fin (N + 1)) (mu : Nat.Partition N) :
    Submodule ℂ (EuclideanSpace ℂ (Perm (N + 1))) :=
  ⨅ y : Fin (N + 1), (SpechtIsotypic.space N mu).comap (ResidualAdjoint.restrict x y)

@[simp] theorem mem_space (x : Fin (N + 1)) (mu : Nat.Partition N)
    (h : EuclideanSpace ℂ (Perm (N + 1))) :
    h ∈ space x mu ↔ ∀ y, ResidualAdjoint.restrict x y h ∈ SpechtIsotypic.space N mu := by
  simp only [space, Submodule.mem_iInf, Submodule.mem_comap]

private def answerProjection (mu : Nat.Partition N) :
    EuclideanSpace ℂ (Fin (N + 1) × Perm N) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin (N + 1) × Perm N) where
  toFun h := WithLp.toLp 2 (fun p => (SpechtIsotypic.space N mu).starProjection (slice h p.1) p.2)
  map_add' h k := by
    ext ⟨y, σ⟩
    simp only [slice_add, map_add, PiLp.add_apply]
  map_smul' c h := by
    ext ⟨y, σ⟩
    simp only [slice_smul, map_smul, PiLp.smul_apply, RingHom.id_apply]

/-- The actual residual isotypic projector transported to full permutation coordinates. -/
def project (x : Fin (N + 1)) (mu : Nat.Partition N) :
    EuclideanSpace ℂ (Perm (N + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Perm (N + 1)) :=
  (reindex x).symm.toLinearEquiv.toLinearMap.comp
    ((answerProjection mu).comp (reindex x).toLinearEquiv.toLinearMap)

@[simp] theorem restrict_project (x y : Fin (N + 1)) (mu : Nat.Partition N)
    (h : EuclideanSpace ℂ (Perm (N + 1))) :
    ResidualAdjoint.restrict x y (project x mu h) =
      (SpechtIsotypic.space N mu).starProjection (ResidualAdjoint.restrict x y h) := by
  change slice (reindex x ((reindex x).symm (answerProjection mu (reindex x h)))) y = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem project_mem (x : Fin (N + 1)) (mu : Nat.Partition N)
    (h : EuclideanSpace ℂ (Perm (N + 1))) : project x mu h ∈ space x mu := by
  rw [mem_space]
  intro y
  rw [restrict_project]
  exact (SpechtIsotypic.space N mu).starProjection_apply_mem _

theorem restrict_ext (x : Fin (N + 1))
    {h k : EuclideanSpace ℂ (Perm (N + 1))}
    (heq : ∀ y, ResidualAdjoint.restrict x y h = ResidualAdjoint.restrict x y k) : h = k := by
  apply (reindex x).injective
  ext ⟨y, σ⟩
  exact congrArg (fun v => v σ) (heq y)

theorem project_eq_self (x : Fin (N + 1)) (mu : Nat.Partition N)
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ space x mu) : project x mu h = h := by
  apply restrict_ext x
  intro y
  rw [restrict_project]
  exact (SpechtIsotypic.space N mu).starProjection_eq_self_iff.mpr ((mem_space x mu h).mp hh y)

theorem inner_eq_sum_restrict (x : Fin (N + 1))
    (h k : EuclideanSpace ℂ (Perm (N + 1))) :
    ⟪h, k⟫_ℂ = ∑ y : Fin (N + 1),
      ⟪ResidualAdjoint.restrict x y h, ResidualAdjoint.restrict x y k⟫_ℂ := by
  rw [← (reindex x).inner_map_map h k]
  simp only [PiLp.inner_apply, Fintype.sum_prod_type]
  rfl

theorem inner_eq_zero {x : Fin (N + 1)} {la mu : Nat.Partition N} (hne : la ≠ mu)
    {h k : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ space x la) (hk : k ∈ space x mu) :
    ⟪h, k⟫_ℂ = 0 := by
  rw [inner_eq_sum_restrict x]
  exact Finset.sum_eq_zero (fun y _ => SpechtOrthogonal.inner_eq_zero hne
    ((mem_space x la h).mp hh y) ((mem_space x mu k).mp hk y))

theorem sum_project (x : Fin (N + 1)) (h : EuclideanSpace ℂ (Perm (N + 1))) :
    (∑ mu : Nat.Partition N, project x mu h) = h := by
  apply restrict_ext x
  intro y
  rw [map_sum]
  simp only [restrict_project]
  exact SpechtOrthogonal.sum_projection N _

/-- Each actual projected vector has the same residual eigenvalue in all sectors. -/
theorem residual_gram_project (x y : Fin (N + 1)) (mu : Nat.Partition N) (t : ℕ)
    (h : EuclideanSpace ℂ (Perm (N + 1))) :
    GramFiltration.gram N t (ResidualAdjoint.restrict x y (project x mu h)) =
      SpechtCharacter.eigenvalue N t mu • ResidualAdjoint.restrict x y (project x mu h) := by
  apply SpechtIsotypic.gram_eq_eigenvalue
  exact (mem_space x mu _).mp (project_mem x mu h) y

end QuantumOracle.ResidualSpectralDecomposition
