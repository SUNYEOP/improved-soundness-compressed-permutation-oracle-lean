import QuantumOracle.Model.OutputDiscard

/-!
# Purification distance decreases under finite output partial trace

Every common purification before discarding a workspace factor gives a common
purification afterwards, with exactly the same vector distance. Taking the
infimum over all original witnesses proves data processing. No numerical
soundness estimate enters either the state transformation or this argument.
-/

noncomputable section

namespace QuantumOracle.DiscardDistance

variable {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]

/-- Undo only the numbered workspace coordinates of an arbitrary purification. -/
def restoreWorkspaceIsometry (A : Type*) [Fintype A] (n : ℕ) :
    PureState (Fintype.card A) n ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × Fin n) :=
  Query.linearLift (Equiv.prodCongr (Fintype.equivFin A).symm (Equiv.refl (Fin n)))

@[simp] theorem restoreWorkspaceIsometry_apply (n : ℕ)
    (ψ : PureState (Fintype.card A) n) (a : A) (i : Fin n) :
    restoreWorkspaceIsometry A n ψ (a, i) = ψ (Fintype.equivFin A a, i) := rfl

theorem reducedFin_restoreWorkspace (n : ℕ)
    (ψ : PureState (Fintype.card A) n) :
    FinitePurification.reducedFin (restoreWorkspaceIsometry A n ψ) =
      reducedState ψ := by
  ext a b
  simp only [FinitePurification.reducedFin, HiddenIsometry.reduced,
    restoreWorkspaceIsometry_apply, reducedState]
  rw [(Fintype.equivFin A).apply_symm_apply, (Fintype.equivFin A).apply_symm_apply]

/-- Move the discarded factor into the common hidden register of any witness. -/
def discardPurification (e : A ≃ B × D)
    {ρ σ : ReducedState (Fintype.card A)} (p : CommonPurification ρ σ) :
    CommonPurification (OutputDiscard.discardMatrix e ρ)
      (OutputDiscard.discardMatrix e σ) where
  ancillaDim := Fintype.card (D × Fin p.ancillaDim)
  exactVector := FinitePurification.coordinateState
    (OutputDiscard.discardVector e
      (restoreWorkspaceIsometry A p.ancillaDim p.exactVector))
  compressedVector := FinitePurification.coordinateState
    (OutputDiscard.discardVector e
      (restoreWorkspaceIsometry A p.ancillaDim p.compressedVector))
  exact_normalized := by
    rw [FinitePurification.coordinateState_norm, OutputDiscard.norm_discardVector,
      (restoreWorkspaceIsometry A p.ancillaDim).norm_map, p.exact_normalized]
  compressed_normalized := by
    rw [FinitePurification.coordinateState_norm, OutputDiscard.norm_discardVector,
      (restoreWorkspaceIsometry A p.ancillaDim).norm_map, p.compressed_normalized]
  exact_reduction := by
    rw [FinitePurification.reducedState_coordinateState,
      OutputDiscard.reducedFin_discardVector, reducedFin_restoreWorkspace,
      p.exact_reduction]
  compressed_reduction := by
    rw [FinitePurification.reducedState_coordinateState,
      OutputDiscard.reducedFin_discardVector, reducedFin_restoreWorkspace,
      p.compressed_reduction]

@[simp] theorem discardPurification_distance (e : A ≃ B × D)
    {ρ σ : ReducedState (Fintype.card A)} (p : CommonPurification ρ σ) :
    (discardPurification e p).distance = p.distance := by
  change ‖FinitePurification.coordinateIsometry B (D × Fin p.ancillaDim)
      (OutputDiscard.discardVector e
        (restoreWorkspaceIsometry A p.ancillaDim p.exactVector)) -
    FinitePurification.coordinateIsometry B (D × Fin p.ancillaDim)
      (OutputDiscard.discardVector e
        (restoreWorkspaceIsometry A p.ancillaDim p.compressedVector))‖ = _
  rw [← map_sub, (FinitePurification.coordinateIsometry B (D × Fin p.ancillaDim)).norm_map,
    OutputDiscard.norm_discardVector_sub, ← map_sub,
    (restoreWorkspaceIsometry A p.ancillaDim).norm_map]
  rfl

/-- Output partial trace cannot increase the infimum over all common witnesses. -/
theorem purificationDistance_discard_le (e : A ≃ B × D)
    {ρ σ : ReducedState (Fintype.card A)}
    (hex : Nonempty (CommonPurification ρ σ)) :
    purificationDistance (OutputDiscard.discardMatrix e ρ)
      (OutputDiscard.discardMatrix e σ) ≤ purificationDistance ρ σ := by
  obtain ⟨p⟩ := hex
  apply le_csInf ⟨p.distance, Set.mem_range_self p⟩
  rintro _ ⟨p', rfl⟩
  simpa only [discardPurification_distance] using
    purificationDistance_le_witness (discardPurification e p')

end QuantumOracle.DiscardDistance
