import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Finite Hilbert direct sums, implemented by actual coordinate isometries. -/

noncomputable section

namespace QuantumOracle.BlockOperator

variable {ι : Type*} {κ : ι → Type*} [Fintype ι] [∀ i, Fintype (κ i)]

def restrict (ψ : EuclideanSpace ℂ (Sigma κ)) (i : ι) : EuclideanSpace ℂ (κ i) :=
  WithLp.toLp 2 (fun j => ψ ⟨i, j⟩)

/-- Apply a genuine linear isometry independently on each orthogonal block. -/
def diagonal (U : ∀ i, EuclideanSpace ℂ (κ i) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (κ i)) :
    EuclideanSpace ℂ (Sigma κ) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Sigma κ) :=
  (LinearIsometryEquiv.piLpCurry ℂ 2 (fun _ _ => ℂ)).trans
    ((LinearIsometryEquiv.piLpCongrRight 2 U).trans
      (LinearIsometryEquiv.piLpCurry ℂ 2 (fun _ _ => ℂ)).symm)

@[simp] theorem diagonal_apply
    (U : ∀ i, EuclideanSpace ℂ (κ i) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (κ i))
    (ψ : EuclideanSpace ℂ (Sigma κ)) (i : ι) (j : κ i) :
    diagonal U ψ ⟨i, j⟩ = U i (restrict ψ i) j := rfl

@[simp] theorem restrict_diagonal
    (U : ∀ i, EuclideanSpace ℂ (κ i) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (κ i))
    (ψ : EuclideanSpace ℂ (Sigma κ)) (i : ι) :
    restrict (diagonal U ψ) i = U i (restrict ψ i) := by
  ext j
  rfl

theorem diagonal_involutive
    (U : ∀ i, EuclideanSpace ℂ (κ i) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (κ i))
    (hU : ∀ i, Function.Involutive (U i)) : Function.Involutive (diagonal U) := by
  intro ψ
  ext ⟨i, j⟩
  simp only [diagonal_apply, restrict_diagonal]
  rw [hU i (restrict ψ i)]
  rfl

/-- A zero block stays zero. This will give support preservation for compression. -/
theorem diagonal_zero_block
    (U : ∀ i, EuclideanSpace ℂ (κ i) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (κ i))
    (ψ : EuclideanSpace ℂ (Sigma κ)) (i : ι) (h : restrict ψ i = 0) :
    restrict (diagonal U ψ) i = 0 := by
  rw [restrict_diagonal, h, map_zero]

/-- Reindexing a block direct sum back into a physical basis. -/
def transport {α : Type*} [Fintype α] (e : α ≃ Sigma κ)
    (U : ∀ i, EuclideanSpace ℂ (κ i) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (κ i)) :
    EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α :=
  let R := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  R.trans ((diagonal U).trans R.symm)

theorem transport_involutive {α : Type*} [Fintype α] (e : α ≃ Sigma κ)
    (U : ∀ i, EuclideanSpace ℂ (κ i) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (κ i))
    (hU : ∀ i, Function.Involutive (U i)) : Function.Involutive (transport e U) := by
  intro ψ
  simp only [transport, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  rw [diagonal_involutive U hU _]
  exact LinearIsometryEquiv.symm_apply_apply _ ψ

@[simp] theorem reindex_transport {α : Type*} [Fintype α] (e : α ≃ Sigma κ)
    (U : ∀ i, EuclideanSpace ℂ (κ i) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (κ i))
    (ψ : EuclideanSpace ℂ α) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (transport e U ψ) =
      diagonal U (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e ψ) := by
  simp only [transport, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]

/-- A family of operators controlled by an unchanged finite register. -/
def family {C Y : Type*} [Fintype C] [Fintype Y]
    (U : C → EuclideanSpace ℂ Y ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y) :
    EuclideanSpace ℂ (C × Y) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (C × Y) :=
  transport (Equiv.sigmaEquivProd C Y).symm U

@[simp] theorem family_apply {C Y : Type*} [Fintype C] [Fintype Y]
    (U : C → EuclideanSpace ℂ Y ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y)
    (ψ : EuclideanSpace ℂ (C × Y)) (c : C) (y : Y) :
    family U ψ (c, y) = U c (WithLp.toLp 2 (fun z => ψ (c, z))) y := rfl

theorem family_involutive {C Y : Type*} [Fintype C] [Fintype Y]
    (U : C → EuclideanSpace ℂ Y ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y)
    (hU : ∀ c, Function.Involutive (U c)) : Function.Involutive (family U) :=
  transport_involutive _ U hU

/-- Tensoring with an identity register, in finite product coordinates. -/
def onRight (C : Type*) {Y : Type*} [Fintype C] [Fintype Y]
    (U : EuclideanSpace ℂ Y ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y) :
    EuclideanSpace ℂ (C × Y) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (C × Y) :=
  family (fun _ : C => U)

end QuantumOracle.BlockOperator
