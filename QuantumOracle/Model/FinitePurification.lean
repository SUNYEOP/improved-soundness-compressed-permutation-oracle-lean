import QuantumOracle.Model.HiddenIsometry
import QuantumOracle.Model.Query

/-!
# Honest finite purifications of actual execution vectors

Finite basis types are reindexed to the `Fin` dimensions of the public
purification-distance semantics. Different hidden registers embed by zero
padding into their disjoint sum. This establishes existence of common
purifications without assuming a harmonic embedding or any soundness bound.
-/

noncomputable section

namespace QuantumOracle.FinitePurification

open scoped BigOperators

variable {A O P : Type*} [Fintype A] [Fintype O] [Fintype P]

/-- Actual workspace reduction, expressed in a numbered finite basis. -/
def reducedFin (ψ : EuclideanSpace ℂ (A × O)) : ReducedState (Fintype.card A) :=
  fun a b => HiddenIsometry.reduced ψ ((Fintype.equivFin A).symm a)
    ((Fintype.equivFin A).symm b)

/-- A change of basis labels only, on both actual registers. -/
def coordinateIsometry (A O : Type*) [Fintype A] [Fintype O] :
    EuclideanSpace ℂ (A × O) ≃ₗᵢ[ℂ]
      PureState (Fintype.card A) (Fintype.card O) :=
  Query.linearLift (Equiv.prodCongr (Fintype.equivFin A) (Fintype.equivFin O))

def coordinateState (ψ : EuclideanSpace ℂ (A × O)) :
    PureState (Fintype.card A) (Fintype.card O) := coordinateIsometry A O ψ

@[simp] theorem coordinateState_apply (ψ : EuclideanSpace ℂ (A × O))
    (a : Fin (Fintype.card A)) (o : Fin (Fintype.card O)) :
    coordinateState ψ (a, o) =
      ψ ((Fintype.equivFin A).symm a, (Fintype.equivFin O).symm o) := rfl

@[simp] theorem coordinateState_norm (ψ : EuclideanSpace ℂ (A × O)) :
    ‖coordinateState ψ‖ = ‖ψ‖ := (coordinateIsometry A O).norm_map ψ

theorem reducedState_coordinateState (ψ : EuclideanSpace ℂ (A × O)) :
    reducedState (coordinateState ψ) = reducedFin ψ := by
  ext a b
  change (∑ o : Fin (Fintype.card O),
    ψ ((Fintype.equivFin A).symm a, (Fintype.equivFin O).symm o) *
      star (ψ ((Fintype.equivFin A).symm b, (Fintype.equivFin O).symm o))) = _
  exact (Fintype.equivFin O).symm.sum_comp (fun o : O =>
    ψ ((Fintype.equivFin A).symm a, o) * star (ψ ((Fintype.equivFin A).symm b, o)))

theorem reducedFin_onOracle
    (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ P)
    (ψ : EuclideanSpace ℂ (A × O)) :
    reducedFin (HiddenIsometry.onOracle A W ψ) = reducedFin ψ := by
  unfold reducedFin
  rw [HiddenIsometry.reduced_onOracle]

/-- Actual vectors already in one hidden space give an honest witness directly. -/
def sameSpace (ψ χ : EuclideanSpace ℂ (A × O))
    (hψ : ‖ψ‖ = 1) (hχ : ‖χ‖ = 1) :
    CommonPurification (reducedFin ψ) (reducedFin χ) where
  ancillaDim := Fintype.card O
  exactVector := coordinateState ψ
  compressedVector := coordinateState χ
  exact_normalized := (coordinateState_norm ψ).trans hψ
  compressed_normalized := (coordinateState_norm χ).trans hχ
  exact_reduction := reducedState_coordinateState ψ
  compressed_reduction := reducedState_coordinateState χ

@[simp] theorem sameSpace_distance (ψ χ : EuclideanSpace ℂ (A × O))
    (hψ : ‖ψ‖ = 1) (hχ : ‖χ‖ = 1) :
    (sameSpace ψ χ hψ hχ).distance = ‖ψ - χ‖ := by
  change ‖coordinateIsometry A O ψ - coordinateIsometry A O χ‖ = _
  rw [← map_sub, (coordinateIsometry A O).norm_map]

theorem purificationDistance_le_norm (ψ χ : EuclideanSpace ℂ (A × O))
    (hψ : ‖ψ‖ = 1) (hχ : ‖χ‖ = 1) :
    purificationDistance (reducedFin ψ) (reducedFin χ) ≤ ‖ψ - χ‖ := by
  simpa only [sameSpace_distance] using
    purificationDistance_le_witness (sameSpace ψ χ hψ hχ)

theorem purificationDistance_self (ψ : EuclideanSpace ℂ (A × O))
    (hψ : ‖ψ‖ = 1) : purificationDistance (reducedFin ψ) (reducedFin ψ) = 0 := by
  apply le_antisymm
  · simpa using purificationDistance_le_norm ψ ψ hψ hψ
  · exact purificationDistance_nonneg ⟨sameSpace ψ ψ hψ hψ⟩

/-- Include the first hidden space into the common disjoint-sum register. -/
def inLeft (O P : Type*) [Fintype O] [Fintype P] :
    EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ (O ⊕ P) where
  toFun ψ := WithLp.toLp 2 (Sum.elim ψ (fun _ => 0))
  map_add' ψ χ := by ext x; cases x <;> simp
  map_smul' c ψ := by ext x; cases x <;> simp
  norm_map' ψ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]

/-- Include the second hidden space into the common disjoint-sum register. -/
def inRight (O P : Type*) [Fintype O] [Fintype P] :
    EuclideanSpace ℂ P →ₗᵢ[ℂ] EuclideanSpace ℂ (O ⊕ P) where
  toFun ψ := WithLp.toLp 2 (Sum.elim (fun _ => 0) ψ)
  map_add' ψ χ := by ext x; cases x <;> simp
  map_smul' c ψ := by ext x; cases x <;> simp
  norm_map' ψ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]

/-- Every two normalized actual finite executions have common purifications. -/
def anyHidden (ψ : EuclideanSpace ℂ (A × O)) (χ : EuclideanSpace ℂ (A × P))
    (hψ : ‖ψ‖ = 1) (hχ : ‖χ‖ = 1) :
    CommonPurification (reducedFin ψ) (reducedFin χ) where
  ancillaDim := Fintype.card (O ⊕ P)
  exactVector := coordinateState (HiddenIsometry.onOracle A (inLeft O P) ψ)
  compressedVector := coordinateState (HiddenIsometry.onOracle A (inRight O P) χ)
  exact_normalized := by rw [coordinateState_norm, HiddenIsometry.norm_onOracle, hψ]
  compressed_normalized := by rw [coordinateState_norm, HiddenIsometry.norm_onOracle, hχ]
  exact_reduction := by rw [reducedState_coordinateState, reducedFin_onOracle]
  compressed_reduction := by rw [reducedState_coordinateState, reducedFin_onOracle]

/-- A genuine hidden isometry yields the usual purification comparison bound. -/
theorem purificationDistance_le_hiddenIsometry
    (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ P)
    (ψ : EuclideanSpace ℂ (A × O)) (χ : EuclideanSpace ℂ (A × P))
    (hψ : ‖ψ‖ = 1) (hχ : ‖χ‖ = 1) :
    purificationDistance (reducedFin ψ) (reducedFin χ) ≤
      ‖HiddenIsometry.onOracle A W ψ - χ‖ := by
  have h := purificationDistance_le_norm (HiddenIsometry.onOracle A W ψ) χ
    ((HiddenIsometry.norm_onOracle W ψ).trans hψ) hχ
  simpa only [reducedFin_onOracle] using h

end QuantumOracle.FinitePurification
