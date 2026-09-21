import QuantumOracle.Model.FinitePurification

/-!
# Discarding part of an actual finite output workspace

A workspace decomposition moves the discarded coordinates into the hidden
register by a genuine linear isometry. Its reduction is the finite partial
trace of the original workspace reduction.
-/

noncomputable section

namespace QuantumOracle.OutputDiscard

open scoped BigOperators

variable {A B D O : Type*} [Fintype A] [Fintype B] [Fintype D] [Fintype O]

/-- Reassociate an actual workspace factor into the hidden register. -/
def discardIsometry (e : A ≃ B × D) :
    EuclideanSpace ℂ (A × O) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (B × (D × O)) :=
  Query.linearLift ((Equiv.prodCongr e (Equiv.refl O)).trans (Equiv.prodAssoc B D O))

def discardVector (e : A ≃ B × D) (ψ : EuclideanSpace ℂ (A × O)) :
    EuclideanSpace ℂ (B × (D × O)) := discardIsometry e ψ

@[simp] theorem discardVector_apply (e : A ≃ B × D)
    (ψ : EuclideanSpace ℂ (A × O)) (b : B) (d : D) (o : O) :
    discardVector e ψ (b, (d, o)) = ψ (e.symm (b, d), o) := rfl

@[simp] theorem norm_discardVector (e : A ≃ B × D)
    (ψ : EuclideanSpace ℂ (A × O)) : ‖discardVector e ψ‖ = ‖ψ‖ :=
  (discardIsometry e).norm_map ψ

theorem discardVector_sub (e : A ≃ B × D)
    (ψ χ : EuclideanSpace ℂ (A × O)) :
    discardVector e (ψ - χ) = discardVector e ψ - discardVector e χ :=
  map_sub (discardIsometry e) ψ χ

@[simp] theorem norm_discardVector_sub (e : A ≃ B × D)
    (ψ χ : EuclideanSpace ℂ (A × O)) :
    ‖discardVector e ψ - discardVector e χ‖ = ‖ψ - χ‖ := by
  rw [← discardVector_sub, norm_discardVector]

/-- Partial trace over the discarded factor in the original numbered basis. -/
def discardMatrix (e : A ≃ B × D) (ρ : ReducedState (Fintype.card A)) :
    ReducedState (Fintype.card B) :=
  fun b c => ∑ d : D,
    ρ (Fintype.equivFin A (e.symm ((Fintype.equivFin B).symm b, d)))
      (Fintype.equivFin A (e.symm ((Fintype.equivFin B).symm c, d)))

/-- Discarding actual vector coordinates agrees with the matrix partial trace. -/
theorem reducedFin_discardVector (e : A ≃ B × D)
    (ψ : EuclideanSpace ℂ (A × O)) :
    FinitePurification.reducedFin (discardVector e ψ) =
      discardMatrix e (FinitePurification.reducedFin ψ) := by
  ext b c
  simp only [FinitePurification.reducedFin, HiddenIsometry.reduced,
    discardMatrix, Fintype.sum_prod_type, discardVector_apply]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro o _
  rw [(Fintype.equivFin A).symm_apply_apply,
    (Fintype.equivFin A).symm_apply_apply]

/-- Keeping the entire workspace is represented by discarding a trivial factor. -/
def keepAllEquiv (A : Type*) : A ≃ A × Unit :=
  (Equiv.prodUnique A Unit).symm

@[simp] theorem discardMatrix_keepAll (ρ : ReducedState (Fintype.card A)) :
    discardMatrix (keepAllEquiv A) ρ = ρ := by
  ext a b
  simp only [discardMatrix, keepAllEquiv, Equiv.symm_symm, Equiv.prodUnique_apply,
    Fintype.sum_unique]
  rw [(Fintype.equivFin A).apply_symm_apply,
    (Fintype.equivFin A).apply_symm_apply]

@[simp] theorem reducedFin_keepAll (ψ : EuclideanSpace ℂ (A × O)) :
    FinitePurification.reducedFin (discardVector (keepAllEquiv A) ψ) =
      FinitePurification.reducedFin ψ := by
  rw [reducedFin_discardVector, discardMatrix_keepAll]

end QuantumOracle.OutputDiscard
