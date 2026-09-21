import QuantumOracle.Model.BlockOperator

/-!
# Oracle subspaces in the presence of a workspace

Membership is imposed on every workspace slice of the actual joint vector.
An arbitrary oracle-independent linear operation on the workspace preserves
this property, including coherent superpositions across the workspace basis.
-/

noncomputable section

namespace QuantumOracle.WorkspaceKnowledge

open scoped BigOperators

variable {A O : Type*} [Fintype A] [Fintype O]

/-- Oracle vector at one workspace coordinate. -/
def slice (ψ : EuclideanSpace ℂ (A × O)) (a : A) : EuclideanSpace ℂ O :=
  WithLp.toLp 2 (fun o => ψ (a, o))

omit [Fintype A] [Fintype O] in
@[simp] theorem slice_apply (ψ : EuclideanSpace ℂ (A × O)) (a : A) (o : O) :
    slice ψ a o = ψ (a, o) := rfl

def sliceLinear (a : A) :
    EuclideanSpace ℂ (A × O) →ₗ[ℂ] EuclideanSpace ℂ O where
  toFun ψ := slice ψ a
  map_add' ψ φ := by ext o; rfl
  map_smul' c ψ := by ext o; rfl

@[simp] theorem slice_zero (a : A) : slice (0 : EuclideanSpace ℂ (A × O)) a = 0 :=
  (sliceLinear a).map_zero

@[simp] theorem slice_add (ψ φ : EuclideanSpace ℂ (A × O)) (a : A) :
    slice (ψ + φ) a = slice ψ a + slice φ a := (sliceLinear a).map_add ψ φ

@[simp] theorem slice_smul (c : ℂ) (ψ : EuclideanSpace ℂ (A × O)) (a : A) :
    slice (c • ψ) a = c • slice ψ a := (sliceLinear a).map_smul c ψ

theorem slice_sum {ι : Type*} (s : Finset ι)
    (ψ : ι → EuclideanSpace ℂ (A × O)) (a : A) :
    slice (∑ i ∈ s, ψ i) a = ∑ i ∈ s, slice (ψ i) a :=
  map_sum (sliceLinear a) ψ s

/-- The oracle lies in `K` even when entangled with the workspace. -/
def Supported (K : Submodule ℂ (EuclideanSpace ℂ O))
    (ψ : EuclideanSpace ℂ (A × O)) : Prop := ∀ a, slice ψ a ∈ K

theorem supported_zero (K : Submodule ℂ (EuclideanSpace ℂ O)) :
    Supported K (0 : EuclideanSpace ℂ (A × O)) := by
  intro a
  rw [slice_zero]
  exact K.zero_mem

theorem supported_add {K : Submodule ℂ (EuclideanSpace ℂ O)}
    {ψ φ : EuclideanSpace ℂ (A × O)} (hψ : Supported K ψ) (hφ : Supported K φ) :
    Supported K (ψ + φ) := by
  intro a
  rw [slice_add]
  exact K.add_mem (hψ a) (hφ a)

theorem supported_smul {K : Submodule ℂ (EuclideanSpace ℂ O)}
    (c : ℂ) {ψ : EuclideanSpace ℂ (A × O)} (hψ : Supported K ψ) :
    Supported K (c • ψ) := by
  intro a
  rw [slice_smul]
  exact K.smul_mem c (hψ a)

theorem supported_sum {K : Submodule ℂ (EuclideanSpace ℂ O)} {ι : Type*}
    (s : Finset ι) (ψ : ι → EuclideanSpace ℂ (A × O))
    (hψ : ∀ i ∈ s, Supported K (ψ i)) : Supported K (∑ i ∈ s, ψ i) := by
  intro a
  rw [slice_sum]
  exact K.sum_mem fun i hi => hψ i hi a

omit [Fintype A] in
theorem supported_mono {K L : Submodule ℂ (EuclideanSpace ℂ O)}
    (hKL : K ≤ L) {ψ : EuclideanSpace ℂ (A × O)} (hψ : Supported K ψ) :
    Supported L ψ := fun a => hKL (hψ a)

/-- Apply `U` to the workspace at each unchanged oracle coordinate. -/
def onWorkspace (O : Type*) [Fintype O]
    (U : EuclideanSpace ℂ A →ₗ[ℂ] EuclideanSpace ℂ A) :
    EuclideanSpace ℂ (A × O) →ₗ[ℂ] EuclideanSpace ℂ (A × O) where
  toFun ψ := WithLp.toLp 2 (fun p => U (WithLp.toLp 2 (fun a => ψ (a, p.2))) p.1)
  map_add' ψ φ := by
    ext ⟨a, o⟩
    change U ((WithLp.toLp 2 (fun b => ψ (b, o))) +
      (WithLp.toLp 2 (fun b => φ (b, o)))) a = _
    rw [map_add]
    rfl
  map_smul' c ψ := by
    ext ⟨a, o⟩
    change U (c • (WithLp.toLp 2 (fun b => ψ (b, o)))) a = _
    rw [map_smul]
    rfl

@[simp] theorem onWorkspace_apply
    (U : EuclideanSpace ℂ A →ₗ[ℂ] EuclideanSpace ℂ A)
    (ψ : EuclideanSpace ℂ (A × O)) (a : A) (o : O) :
    onWorkspace O U ψ (a, o) = U (WithLp.toLp 2 (fun b => ψ (b, o))) a := rfl

private theorem sum_apply {ι : Type*} (s : Finset ι)
    (v : ι → EuclideanSpace ℂ O) (o : O) :
    (∑ i ∈ s, v i) o = ∑ i ∈ s, v i o :=
  map_sum (PiLp.projₗ 2 (𝕜 := ℂ) (fun _ : O => ℂ) o) v s

/-- A workspace operation makes linear combinations of the original oracle slices. -/
theorem slice_onWorkspace
    (U : EuclideanSpace ℂ A →ₗ[ℂ] EuclideanSpace ℂ A)
    (ψ : EuclideanSpace ℂ (A × O)) (a : A) :
    slice (onWorkspace O U ψ) a =
      ∑ b : A, U (EuclideanSpace.basisFun A ℂ b) a • slice ψ b := by
  ext o
  rw [sum_apply]
  let v : EuclideanSpace ℂ A := WithLp.toLp 2 (fun b => ψ (b, o))
  have hv := (EuclideanSpace.basisFun A ℂ).sum_repr v
  have heq := congrArg (fun w : EuclideanSpace ℂ A => U w a) hv
  simp only [map_sum, map_smul, sum_apply, PiLp.smul_apply,
    EuclideanSpace.basisFun_repr, smul_eq_mul] at heq
  change U v a = _
  rw [← heq]
  apply Finset.sum_congr rfl
  intro b _
  simp only [PiLp.smul_apply, smul_eq_mul, slice_apply]
  exact mul_comm _ _

theorem supported_onWorkspace (K : Submodule ℂ (EuclideanSpace ℂ O))
    (U : EuclideanSpace ℂ A →ₗ[ℂ] EuclideanSpace ℂ A)
    {ψ : EuclideanSpace ℂ (A × O)} (hψ : Supported K ψ) :
    Supported K (onWorkspace O U ψ) := by
  intro a
  rw [slice_onWorkspace]
  exact K.sum_mem fun b _ => K.smul_mem _ (hψ b)

/-- Actual product of a workspace vector and an oracle vector. -/
def productState (w : EuclideanSpace ℂ A) (v : EuclideanSpace ℂ O) :
    EuclideanSpace ℂ (A × O) := WithLp.toLp 2 (fun p => w p.1 * v p.2)

omit [Fintype A] [Fintype O] in
@[simp] theorem productState_apply (w : EuclideanSpace ℂ A)
    (v : EuclideanSpace ℂ O) (a : A) (o : O) :
    productState w v (a, o) = w a * v o := rfl

omit [Fintype A] [Fintype O] in
@[simp] theorem slice_productState (w : EuclideanSpace ℂ A)
    (v : EuclideanSpace ℂ O) (a : A) : slice (productState w v) a = w a • v := by
  ext o
  rfl

omit [Fintype A] in
theorem supported_productState (K : Submodule ℂ (EuclideanSpace ℂ O))
    (w : EuclideanSpace ℂ A) {v : EuclideanSpace ℂ O} (hv : v ∈ K) :
    Supported K (productState w v) := by
  intro a
  rw [slice_productState]
  exact K.smul_mem _ hv

/-- The same workspace operation, bundled with its genuine isometry. -/
def onWorkspaceIsometry (O : Type*) [Fintype O]
    (U : EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ A) :
    EuclideanSpace ℂ (A × O) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × O) :=
  let swap := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.prodComm A O)
  swap.trans ((BlockOperator.onRight O U).trans swap.symm)

theorem onWorkspaceIsometry_apply
    (U : EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (ψ : EuclideanSpace ℂ (A × O)) :
    onWorkspaceIsometry O U ψ = onWorkspace O U.toLinearEquiv.toLinearMap ψ := by
  ext ⟨a, o⟩
  rfl

theorem norm_onWorkspace
    (U : EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (ψ : EuclideanSpace ℂ (A × O)) :
    ‖onWorkspace O U.toLinearEquiv.toLinearMap ψ‖ = ‖ψ‖ := by
  rw [← onWorkspaceIsometry_apply]
  exact (onWorkspaceIsometry O U).norm_map ψ

end QuantumOracle.WorkspaceKnowledge
