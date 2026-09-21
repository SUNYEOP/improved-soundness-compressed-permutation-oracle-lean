import QuantumOracle.Proof.GramFiltration
import QuantumOracle.Model.HarmonicLayers

/-!
# The concrete extension Gram operators on actual harmonic layers

Each Gram operator preserves every orthogonal degree space. Its restriction is
self-adjoint and nonnegative, and the own-degree restriction is strictly
positive and invertible. These statements include degree zero and empty
out-of-range layers, with no assumptions about representation-theoretic spectra.
-/

noncomputable section

namespace QuantumOracle.HarmonicGram

open PermutationExtensions HarmonicLayers GramFiltration
open scoped InnerProductSpace

/-- All actual Gram operators preserve every actual harmonic degree. -/
theorem gram_mem_H {N t : ℕ} (s : ℕ) {v : EuclideanSpace ℂ (Perm N)}
    (hv : v ∈ H N t) : gram N s v ∈ H N t := by
  cases t with
  | zero => exact gram_mem_knowledge s hv
  | succ t => exact gram_mem_layer s hv

/-- The actual size-s Gram operator acting within harmonic degree t. -/
def gramOnLayer (N s t : ℕ) : H N t →ₗ[ℂ] H N t :=
  (gram N s).restrict fun _ hv => gram_mem_H s hv

@[simp] theorem gramOnLayer_apply (N s t : ℕ) (v : H N t) :
    (gramOnLayer N s t v : EuclideanSpace ℂ (Perm N)) = gram N s v := rfl

attribute [local irreducible] H KnowledgeSpace.K gram

local instance layerInnerProductSpace (N t : ℕ) : InnerProductSpace ℂ ↥(H N t) :=
  inferInstance

theorem gramOnLayer_isSymmetric (N s t : ℕ) :
    LinearMap.IsSymmetric (E := ↥(H N t)) (gramOnLayer N s t) := by
  intro v z
  change ⟪gram N s (v : EuclideanSpace ℂ (Perm N)), (z : EuclideanSpace ℂ (Perm N))⟫_ℂ =
    ⟪(v : EuclideanSpace ℂ (Perm N)), gram N s (z : EuclideanSpace ℂ (Perm N))⟫_ℂ
  exact gram_isSymmetric N s _ _

@[simp] theorem adjoint_gramOnLayer (N s t : ℕ) :
    (gramOnLayer N s t).adjoint = gramOnLayer N s t :=
  (gramOnLayer_isSymmetric N s t).adjoint_eq

theorem gramOnLayer_isSelfAdjoint (N s t : ℕ) : IsSelfAdjoint (gramOnLayer N s t) :=
  (LinearMap.isSelfAdjoint_iff').mpr (adjoint_gramOnLayer N s t)

theorem inner_gramOnLayer (N s t : ℕ) (v : H N t) :
    ⟪v, gramOnLayer N s t v⟫_ℂ =
      ⟪(ExtensionOperator.T N s).adjoint (v : EuclideanSpace ℂ (Perm N)),
        (ExtensionOperator.T N s).adjoint (v : EuclideanSpace ℂ (Perm N))⟫_ℂ :=
  inner_gram N s v

theorem re_inner_gramOnLayer_nonneg (N s t : ℕ) (v : H N t) :
    0 ≤ (⟪v, gramOnLayer N s t v⟫_ℂ).re :=
  re_inner_gram_nonneg N s v

/-- The own-degree Gram form is strictly positive on every nonzero layer vector. -/
theorem re_inner_gramOnLayer_pos (N t : ℕ) (v : H N t) (hne : v ≠ 0) :
    0 < (⟪v, gramOnLayer N t t v⟫_ℂ).re := by
  apply re_inner_gram_pos (H_le_K N t v.property)
  intro hzero
  exact hne (Subtype.ext hzero)

theorem gramOnLayer_injective (N t : ℕ) : Function.Injective (gramOnLayer N t t) := by
  intro v z h
  have hval : gram N t (v : EuclideanSpace ℂ (Perm N)) =
      gram N t (z : EuclideanSpace ℂ (Perm N)) := by
    simpa only [gramOnLayer_apply] using
      congrArg (fun x : H N t => (x : EuclideanSpace ℂ (Perm N))) h
  have hK :
      gramRestrict N t ⟨v, H_le_K N t v.property⟩ =
        gramRestrict N t ⟨z, H_le_K N t z.property⟩ :=
    Subtype.ext hval
  exact Subtype.ext (congrArg
    (fun x : KnowledgeSpace.K N t => (x : EuclideanSpace ℂ (Perm N)))
    (gramRestrict_injective N t hK))

/-- The own-degree Gram operator is an automorphism of the concrete harmonic layer. -/
def gramLayerEquiv (N t : ℕ) : H N t ≃ₗ[ℂ] H N t :=
  LinearEquiv.ofInjectiveEndo (gramOnLayer N t t) (gramOnLayer_injective N t)

@[simp] theorem gramLayerEquiv_apply (N t : ℕ) (v : H N t) :
    gramLayerEquiv N t v = gramOnLayer N t t v := rfl

@[simp] theorem gramOnLayer_gramLayerEquiv_symm (N t : ℕ) (v : H N t) :
    gramOnLayer N t t ((gramLayerEquiv N t).symm v) = v :=
  (gramLayerEquiv N t).apply_symm_apply v

@[simp] theorem gramLayerEquiv_symm_gramOnLayer (N t : ℕ) (v : H N t) :
    (gramLayerEquiv N t).symm (gramOnLayer N t t v) = v :=
  (gramLayerEquiv N t).symm_apply_apply v

/-- The simultaneous Gram commutation remains true on every harmonic degree. -/
theorem gramOnLayer_commutes (N s r t : ℕ) :
    (gramOnLayer N s t).comp (gramOnLayer N r t) =
      (gramOnLayer N r t).comp (gramOnLayer N s t) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact LinearMap.congr_fun (gram_commutes N r s) v

end QuantumOracle.HarmonicGram
