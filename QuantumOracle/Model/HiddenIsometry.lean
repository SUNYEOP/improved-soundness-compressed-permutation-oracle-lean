import QuantumOracle.Model.WorkspaceKnowledge
import QuantumOracle.Model.PurificationDistance

/-!
# Isometries of an actual hidden register

Every genuine linear isometry on a finite hidden register lifts to a linear
isometry of the joint workspace and hidden system. The workspace reduction is
unchanged. These statements take an actual isometry as input and do not assert
that any particular harmonic embedding has already been constructed.
-/

noncomputable section

namespace QuantumOracle.HiddenIsometry

open WorkspaceKnowledge
open scoped BigOperators InnerProductSpace

variable {A O P : Type*} [Fintype A] [Fintype O] [Fintype P]

/-- Finite partial trace over the hidden register, on any finite basis types. -/
def reduced (ψ : EuclideanSpace ℂ (A × O)) : Matrix A A ℂ :=
  fun a b => ∑ o : O, ψ (a, o) * star (ψ (b, o))

omit [Fintype A] in
/-- Matrix entries are exactly the inner products of the oracle slices. -/
theorem reduced_eq_inner (ψ : EuclideanSpace ℂ (A × O)) (a b : A) :
    reduced ψ a b = ⟪slice ψ b, slice ψ a⟫_ℂ := rfl

/-- The generic reduction is definitionally the existing finite-index reduction. -/
theorem reduced_eq_reducedState {d n : ℕ} (ψ : PureState d n) :
    reduced ψ = reducedState ψ := rfl

/-- Joint norm squared decomposes into the norms of the hidden-register slices. -/
theorem norm_sq_eq_sum_slices (ψ : EuclideanSpace ℂ (A × O)) :
    ‖ψ‖ ^ 2 = ∑ a : A, ‖slice ψ a‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [EuclideanSpace.norm_sq_eq]
  rfl

/-- Apply an actual hidden-register isometry independently at each workspace coordinate. -/
def onOracle (A : Type*) [Fintype A]
    (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ P) :
    EuclideanSpace ℂ (A × O) →ₗᵢ[ℂ] EuclideanSpace ℂ (A × P) where
  toFun ψ := WithLp.toLp 2 (fun p => W (slice ψ p.1) p.2)
  map_add' ψ φ := by
    ext ⟨a, p⟩
    change W (slice (ψ + φ) a) p = W (slice ψ a) p + W (slice φ a) p
    rw [slice_add, map_add]
    rfl
  map_smul' c ψ := by
    ext ⟨a, p⟩
    change W (slice (c • ψ) a) p = c • W (slice ψ a) p
    rw [slice_smul, map_smul]
    rfl
  norm_map' ψ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_eq_sum_slices, norm_sq_eq_sum_slices]
    apply Finset.sum_congr rfl
    intro a _
    change ‖W (slice ψ a)‖ ^ 2 = ‖slice ψ a‖ ^ 2
    rw [W.norm_map]

@[simp] theorem onOracle_apply
    (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ P)
    (ψ : EuclideanSpace ℂ (A × O)) (a : A) (p : P) :
    onOracle A W ψ (a, p) = W (slice ψ a) p := rfl

@[simp] theorem slice_onOracle
    (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ P)
    (ψ : EuclideanSpace ℂ (A × O)) (a : A) :
    slice (onOracle A W ψ) a = W (slice ψ a) := by
  ext p
  rfl

theorem norm_onOracle
    (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ P)
    (ψ : EuclideanSpace ℂ (A × O)) : ‖onOracle A W ψ‖ = ‖ψ‖ :=
  (onOracle A W).norm_map ψ

/-- The actual workspace density matrix is invariant under a hidden isometry. -/
theorem reduced_onOracle
    (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ P)
    (ψ : EuclideanSpace ℂ (A × O)) : reduced (onOracle A W ψ) = reduced ψ := by
  ext a b
  rw [reduced_eq_inner, reduced_eq_inner, slice_onOracle, slice_onOracle]
  exact W.inner_map_map _ _

/-- The same invariance in the finite dimensions used by `CommonPurification`. -/
theorem reducedState_onOracle {d n m : ℕ}
    (W : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (ψ : PureState d n) :
    reducedState (onOracle (Fin d) W ψ) = reducedState ψ :=
  reduced_onOracle W ψ

/-- Independent operations on the workspace and the hidden register commute. -/
theorem onOracle_onWorkspace
    (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ P)
    (U : EuclideanSpace ℂ A →ₗ[ℂ] EuclideanSpace ℂ A)
    (ψ : EuclideanSpace ℂ (A × O)) :
    onOracle A W (onWorkspace O U ψ) = onWorkspace P U (onOracle A W ψ) := by
  ext ⟨a, p⟩
  have h : slice (onOracle A W (onWorkspace O U ψ)) a =
      slice (onWorkspace P U (onOracle A W ψ)) a := by
    rw [slice_onOracle, slice_onWorkspace, slice_onWorkspace]
    simp only [map_sum, map_smul, slice_onOracle]
  exact congrArg (fun v : EuclideanSpace ℂ P => v p) h

theorem onOracle_productState
    (W : EuclideanSpace ℂ O →ₗᵢ[ℂ] EuclideanSpace ℂ P)
    (w : EuclideanSpace ℂ A) (v : EuclideanSpace ℂ O) :
    onOracle A W (productState w v) = productState w (W v) := by
  ext ⟨a, p⟩
  rw [onOracle_apply, slice_productState, map_smul]
  rfl

end QuantumOracle.HiddenIsometry
