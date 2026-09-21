import QuantumOracle.Model.GramRange
import QuantumOracle.Proof.KernelEquivariance

/-!
# Positivity and invertibility of the concrete extension Gram operator

These facts use the actual extension matrix. They do not assume irreducible
eigenvalues or a normalization formula for the harmonic comparison map.
-/

noncomputable section

namespace QuantumOracle.GramFiltration

open PermutationExtensions ExtensionOperator
open scoped InnerProductSpace

/-- The actual operator `T_{N,t} T_{N,t}†`. -/
def gram (N t : ℕ) :
    EuclideanSpace ℂ (Perm N) →ₗ[ℂ] EuclideanSpace ℂ (Perm N) :=
  (T N t).comp (T N t).adjoint

@[simp] theorem adjoint_gram (N t : ℕ) : (gram N t).adjoint = gram N t := by
  simp only [gram, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]

theorem gram_isSymmetric (N t : ℕ) : (gram N t).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
  exact adjoint_gram N t

theorem range_gram (N t : ℕ) : LinearMap.range (gram N t) = KnowledgeSpace.K N t :=
  GramRange.range_T_comp_adjoint N t

theorem ker_gram (N t : ℕ) :
    LinearMap.ker (gram N t) = (KnowledgeSpace.K N t)ᗮ := by
  rw [← range_gram N t, GramRange.range_orthogonal, adjoint_gram]

theorem inner_gram (N t : ℕ) (v : EuclideanSpace ℂ (Perm N)) :
    ⟪v, gram N t v⟫_ℂ = ⟪(T N t).adjoint v, (T N t).adjoint v⟫_ℂ := by
  change ⟪v, T N t ((T N t).adjoint v)⟫_ℂ = _
  rw [(T N t).adjoint_inner_left]

theorem re_inner_gram_nonneg (N t : ℕ) (v : EuclideanSpace ℂ (Perm N)) :
    0 ≤ (⟪v, gram N t v⟫_ℂ).re := by
  rw [inner_gram]
  exact inner_self_nonneg (𝕜 := ℂ)

theorem adjoint_eq_zero_iff {N t : ℕ} (v : EuclideanSpace ℂ (Perm N)) :
    (T N t).adjoint v = 0 ↔ v ∈ (KnowledgeSpace.K N t)ᗮ := by
  rw [← KnowledgeSpace.range_T, GramRange.range_orthogonal]
  rfl

theorem re_inner_gram_pos_iff {N t : ℕ} (v : EuclideanSpace ℂ (Perm N)) :
    0 < (⟪v, gram N t v⟫_ℂ).re ↔ v ∉ (KnowledgeSpace.K N t)ᗮ := by
  rw [inner_gram]
  change 0 < RCLike.re ⟪(T N t).adjoint v, (T N t).adjoint v⟫_ℂ ↔ _
  rw [re_inner_self_pos, ne_eq, adjoint_eq_zero_iff]

/-- Every nonzero vector of the actual knowledge space has positive Gram energy. -/
theorem re_inner_gram_pos {N t : ℕ} {v : EuclideanSpace ℂ (Perm N)}
    (hv : v ∈ KnowledgeSpace.K N t) (hne : v ≠ 0) :
    0 < (⟪v, gram N t v⟫_ℂ).re := by
  rw [re_inner_gram_pos_iff]
  intro horth
  apply hne
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp (horth v hv)

theorem gram_mem (N t : ℕ) (v : EuclideanSpace ℂ (Perm N)) :
    gram N t v ∈ KnowledgeSpace.K N t := by
  rw [← range_gram]
  exact ⟨v, rfl⟩

/-- Restricting the actual Gram operator to its range. -/
def gramRestrict (N t : ℕ) : KnowledgeSpace.K N t →ₗ[ℂ] KnowledgeSpace.K N t :=
  (gram N t).restrict fun v _ => gram_mem N t v

@[simp] theorem gramRestrict_apply (N t : ℕ) (v : KnowledgeSpace.K N t) :
    (gramRestrict N t v : EuclideanSpace ℂ (Perm N)) = gram N t v := rfl

theorem gramRestrict_injective (N t : ℕ) : Function.Injective (gramRestrict N t) := by
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro v hv
  have hzero : gram N t (v : EuclideanSpace ℂ (Perm N)) = 0 :=
    congrArg Subtype.val hv
  have horth : (v : EuclideanSpace ℂ (Perm N)) ∈ (KnowledgeSpace.K N t)ᗮ := by
    rw [← ker_gram]
    exact hzero
  have hvzero : (v : EuclideanSpace ℂ (Perm N)) = 0 :=
    (inner_self_eq_zero (𝕜 := ℂ)).mp (horth v v.property)
  exact Subtype.ext hvzero

/-- The Gram operator is an actual automorphism on the concrete knowledge space. -/
def gramLinearEquiv (N t : ℕ) : KnowledgeSpace.K N t ≃ₗ[ℂ] KnowledgeSpace.K N t :=
  LinearEquiv.ofInjectiveEndo (gramRestrict N t) (gramRestrict_injective N t)

@[simp] theorem gramLinearEquiv_apply (N t : ℕ) (v : KnowledgeSpace.K N t) :
    (gramLinearEquiv N t v : EuclideanSpace ℂ (Perm N)) = gram N t v := rfl

open KernelEquivariance
open scoped BigOperators

private theorem sum_single {N : ℕ} (v : EuclideanSpace ℂ (Perm N)) :
    ∑ π : Perm N, v π • EuclideanSpace.single π 1 = v := by
  classical
  simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun (Perm N) ℂ).sum_repr v

/-- Translation equivariance determines every Gram column from the identity column. -/
theorem gram_single_from_identity {N : ℕ} (t : ℕ) (σ : Perm N) :
    gram N t (EuclideanSpace.single σ 1) =
      relabelOperator (Equiv.refl _) σ
        (gram N t (EuclideanSpace.single (Equiv.refl _) 1)) := by
  have h := LinearMap.congr_fun (T_adjoint_commutes t (Equiv.refl _) σ)
    (EuclideanSpace.single (Equiv.refl _) 1)
  change gram N t (relabelOperator (Equiv.refl _) σ
      (EuclideanSpace.single (Equiv.refl _) 1)) =
    relabelOperator (Equiv.refl _) σ
      (gram N t (EuclideanSpace.single (Equiv.refl _) 1)) at h
  simpa only [relabelOperator_single, Equiv.refl_symm, Equiv.refl_trans] using h

/-- The actual central Gram operator is a finite linear combination of translations. -/
theorem gram_eq_sum_relabel (N t : ℕ) :
    gram N t = ∑ π : Perm N,
      (gram N t (EuclideanSpace.single (Equiv.refl _) 1) π) •
        (relabelOperator π.symm (Equiv.refl _)).toLinearMap := by
  classical
  apply (EuclideanSpace.basisFun (Perm N) ℂ).toBasis.ext
  intro σ
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  rw [gram_single_from_identity]
  have hv := congrArg (relabelOperator (Equiv.refl _) σ)
    (sum_single (gram N t (EuclideanSpace.single (Equiv.refl _) 1)))
  rw [map_sum] at hv
  rw [← hv]
  apply Finset.sum_congr rfl
  intro π _
  rw [map_smul]
  change _ • relabelOperator (Equiv.refl _) σ (EuclideanSpace.single π 1) =
    _ • relabelOperator π.symm (Equiv.refl _) (EuclideanSpace.single σ 1)
  simp only [relabelOperator_single, Equiv.refl_symm, Equiv.symm_symm,
    Equiv.refl_trans, Equiv.trans_refl]

/-- All actual extension Gram operators commute; no spectral formula is needed. -/
theorem gram_commutes (N s t : ℕ) :
    (gram N t).comp (gram N s) = (gram N s).comp (gram N t) := by
  classical
  rw [gram_eq_sum_relabel N s]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro π _
  have h := LinearMap.congr_fun (T_adjoint_commutes t π.symm (Equiv.refl _)) v
  exact congrArg (fun z => (gram N s (EuclideanSpace.single (Equiv.refl _) 1) π) • z) h

/-- Every Gram operator preserves every knowledge level, not only its own range. -/
theorem gram_mem_knowledge {N s : ℕ} (t : ℕ)
    {v : EuclideanSpace ℂ (Perm N)} (hv : v ∈ KnowledgeSpace.K N s) :
    gram N t v ∈ KnowledgeSpace.K N s := by
  rw [← range_gram N s] at hv
  obtain ⟨w, rfl⟩ := hv
  have h := LinearMap.congr_fun (gram_commutes N s t) w
  change gram N t (gram N s w) = gram N s (gram N t w) at h
  rw [h]
  exact gram_mem N s _

/-- Self-adjointness also preserves each orthogonal complement in the filtration. -/
theorem gram_mem_orthogonal {N s : ℕ} (t : ℕ)
    {v : EuclideanSpace ℂ (Perm N)} (hv : v ∈ (KnowledgeSpace.K N s)ᗮ) :
    gram N t v ∈ (KnowledgeSpace.K N s)ᗮ := by
  intro w hw
  rw [← (gram N t).adjoint_inner_left, adjoint_gram]
  exact hv _ (gram_mem_knowledge t hw)

/-- In particular every difference layer of the actual filtration is invariant. -/
theorem gram_mem_layer {N s r : ℕ} (t : ℕ)
    {v : EuclideanSpace ℂ (Perm N)}
    (hv : v ∈ KnowledgeSpace.K N s ⊓ (KnowledgeSpace.K N r)ᗮ) :
    gram N t v ∈ KnowledgeSpace.K N s ⊓ (KnowledgeSpace.K N r)ᗮ :=
  ⟨gram_mem_knowledge t hv.1, gram_mem_orthogonal t hv.2⟩

end QuantumOracle.GramFiltration
