import QuantumOracle.Model.HiddenIsometry

/-! Actual product initializations and their observable reductions. -/

noncomputable section

namespace QuantumOracle.ProductReduction

open WorkspaceKnowledge HiddenIsometry
open scoped InnerProductSpace

variable {A O : Type*} [Fintype A] [Fintype O]

/-- An oracle-independent workspace operation acts on the first factor of a product state. -/
theorem onWorkspace_productState
    (U : EuclideanSpace ℂ A →ₗ[ℂ] EuclideanSpace ℂ A)
    (φ : EuclideanSpace ℂ A) (v : EuclideanSpace ℂ O) :
    onWorkspace O U (productState φ v) = productState (U φ) v := by
  ext ⟨a, o⟩
  change U (WithLp.toLp 2 (fun b => φ b * v o)) a = U φ a * v o
  have h : WithLp.toLp 2 (fun b => φ b * v o) = v o • φ := by
    ext b
    exact mul_comm _ _
  rw [h, map_smul]
  exact mul_comm _ _

omit [Fintype A] in
/-- Tracing a normalized product factor leaves the workspace's pure density matrix. -/
theorem reduced_productState (φ : EuclideanSpace ℂ A) (v : EuclideanSpace ℂ O)
    (hv : ‖v‖ = 1) (a b : A) :
    reduced (productState φ v) a b = φ a * star (φ b) := by
  rw [reduced_eq_inner, slice_productState, slice_productState,
    inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]
  simp [mul_comm]

omit [Fintype A] in
/-- Different normalized hidden product factors give the same observable state. -/
theorem reduced_productState_eq {P : Type*} [Fintype P]
    (φ : EuclideanSpace ℂ A) (v : EuclideanSpace ℂ O) (z : EuclideanSpace ℂ P)
    (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) :
    reduced (productState φ v) = reduced (productState φ z) := by
  ext a b
  rw [reduced_productState φ v hv, reduced_productState φ z hz]

end QuantumOracle.ProductReduction
