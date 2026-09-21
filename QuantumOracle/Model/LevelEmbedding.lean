import QuantumOracle.Model.ExtensionOperator

/-!
# Isometric inclusion of each actual database level

A vector indexed by size-t partial injections is extended by zero to the whole
database register. Distinct sizes give orthogonal images. This construction
contains no spectral normalization or soundness estimate.
-/

noncomputable section

namespace QuantumOracle.LevelEmbedding

open ExtensionOperator
open scoped BigOperators InnerProductSpace

variable {N s t : ℕ}

/-- Actual zero padding from one database size to the full database register. -/
def embed (N t : ℕ) :
    EuclideanSpace ℂ (Level N t) →ₗᵢ[ℂ] EuclideanSpace ℂ (Database N) := by
  classical
  exact
    { toFun := fun v => WithLp.toLp 2
        (fun I => if hI : I.size = t then v ⟨I, hI⟩ else 0)
      map_add' := by
        intro v w
        ext I
        by_cases hI : I.size = t <;> simp [hI]
      map_smul' := by
        intro c v
        ext I
        by_cases hI : I.size = t <;> simp [hI]
      norm_map' := by
        intro v
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        rw [← Fintype.sum_subtype_add_sum_subtype (fun I : Database N => I.size = t)]
        have hpos : (∑ I : {I : Database N // I.size = t},
            ‖(if hI : I.val.size = t then v ⟨I.val, hI⟩ else 0)‖ ^ 2) =
            ∑ I : Level N t, ‖v I‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro I _
          simp [I.property]
        have hneg : (∑ I : {I : Database N // ¬ I.size = t},
            ‖(if hI : I.val.size = t then v ⟨I.val, hI⟩ else 0)‖ ^ 2) = 0 := by
          apply Finset.sum_eq_zero
          intro I _
          simp [I.property]
        exact (congrArg₂ (· + ·) hpos hneg).trans (add_zero _) }

@[simp] theorem embed_apply_of_size (N t : ℕ) (v : EuclideanSpace ℂ (Level N t))
    (I : Database N) (hI : I.size = t) :
    embed N t v I = v ⟨I, hI⟩ := by
  classical
  simp [embed, hI]

@[simp] theorem embed_apply_of_ne (N t : ℕ) (v : EuclideanSpace ℂ (Level N t))
    (I : Database N) (hI : I.size ≠ t) :
    embed N t v I = 0 := by
  classical
  simp [embed, hI]

@[simp] theorem embed_norm (N t : ℕ) (v : EuclideanSpace ℂ (Level N t)) :
    ‖embed N t v‖ = ‖v‖ := (embed N t).norm_map v

/-- Every nonzero embedded coefficient belongs to exactly the chosen size. -/
theorem embed_support (N t : ℕ) (v : EuclideanSpace ℂ (Level N t))
    (I : Database N) (hI : embed N t v I ≠ 0) : I.size = t := by
  by_contra h
  exact hI (embed_apply_of_ne N t v I h)

/-- Images of distinct database sizes are orthogonal in the actual register. -/
theorem inner_embed_of_ne (hst : s ≠ t)
    (v : EuclideanSpace ℂ (Level N s)) (w : EuclideanSpace ℂ (Level N t)) :
    ⟪embed N s v, embed N t w⟫_ℂ = 0 := by
  classical
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro I _
  by_cases hI : I.size = s
  · have hIt : I.size ≠ t := fun hIt => hst (hI.symm.trans hIt)
    rw [embed_apply_of_ne N t w I hIt]
    simp
  · rw [embed_apply_of_ne N s v I hI]
    simp

end QuantumOracle.LevelEmbedding
