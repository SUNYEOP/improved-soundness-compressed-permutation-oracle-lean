import QuantumOracle.Model.BlockSupport
import QuantumOracle.Model.CompressedCoherentQuery
import QuantumOracle.Model.ExactFinalState

/-!
# Actual compressed-oracle executions

The hidden register starts in the actual empty database. Workspace operations
may coherently mix all query arguments with an arbitrary finite private memory.
-/

noncomputable section

set_option maxRecDepth 4096

namespace QuantumOracle.CompressedExecution

open WorkspaceKnowledge
open scoped BigOperators ComplexOrder

variable {A : Type*} [Fintype A]

/-- An arbitrary workspace vector tensored with the actual empty database ket. -/
def initial (N : ℕ) (φ : EuclideanSpace ℂ A) :
    EuclideanSpace ℂ (A × Database N) := BlockSupport.emptyState φ

@[simp] theorem initial_apply (N : ℕ) (φ : EuclideanSpace ℂ A)
    (a : A) (I : Database N) :
    initial N φ (a, I) = if I = Database.empty then φ a else 0 := rfl

/-- Introducing the empty hidden register preserves the actual workspace norm. -/
theorem initial_norm (N : ℕ) (φ : EuclideanSpace ℂ A) :
    ‖initial N φ‖ = ‖φ‖ := by
  classical
  have hsq : ‖initial N φ‖ ^ 2 = ‖φ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp only [initial_apply]
    simp [apply_ite, ← EuclideanSpace.norm_sq_eq]
  nlinarith [norm_nonneg (initial N φ), norm_nonneg φ]

/-- Actual initialization, bundled as a linear isometry. -/
def initialIsometry (N : ℕ) :
    EuclideanSpace ℂ A →ₗᵢ[ℂ] EuclideanSpace ℂ (A × Database N) where
  toFun := initial N
  map_add' φ χ := by
    ext ⟨a, I⟩
    by_cases hI : I = Database.empty <;> simp [initial_apply, hI]
  map_smul' c φ := by
    ext ⟨a, I⟩
    by_cases hI : I = Database.empty <;> simp [initial_apply, hI]
  norm_map' := initial_norm N

theorem initial_supported (N : ℕ) (φ : EuclideanSpace ℂ A) :
    BlockSupport.Supported 0 (initial N φ) :=
  BlockSupport.supported_emptyState φ

theorem initial_eq_productState (N : ℕ) (φ : EuclideanSpace ℂ A) :
    initial N φ = productState φ (EuclideanSpace.single Database.empty 1) := by
  classical
  ext ⟨a, I⟩
  by_cases hI : I = Database.empty <;>
    simp [initial_apply, productState_apply, EuclideanSpace.single_apply, hI]

/-- Every oracle-independent linear workspace map preserves database degree. -/
theorem supported_onWorkspace {N t : ℕ}
    (U : EuclideanSpace ℂ A →ₗ[ℂ] EuclideanSpace ℂ A)
    {ψ : EuclideanSpace ℂ (A × Database N)}
    (hψ : BlockSupport.Supported t ψ) :
    BlockSupport.Supported t (onWorkspace (Database N) U ψ) := by
  intro a I hI
  rw [onWorkspace_apply]
  have hz : (WithLp.toLp 2 (fun b => ψ (b, I)) : EuclideanSpace ℂ A) = 0 := by
    ext b
    exact hψ b I hI
  rw [hz, map_zero]
  rfl

/-- Actual database sizes are always at most `N`. -/
theorem supported_full {N : ℕ} (ψ : EuclideanSpace ℂ (A × Database N)) :
    BlockSupport.Supported N ψ := by
  intro a I hI
  exact False.elim (Nat.not_lt_of_ge I.size_le hI)

/-- A database support bound may be capped at the actual largest database size. -/
theorem supported_min {N t : ℕ} {ψ : EuclideanSpace ℂ (A × Database N)}
    (hψ : BlockSupport.Supported t ψ) : BlockSupport.Supported (min t N) ψ := by
  by_cases ht : t ≤ N
  · simpa only [min_eq_left ht] using hψ
  · simpa only [min_eq_right (by omega : N ≤ t)] using supported_full ψ

section Execution

open BasisLookup CompressedCoherentQuery

variable {N w : ℕ} {Aux : Type*} [Fintype Aux]

/-- Exactly the same private and coherent query workspace as the exact execution. -/
abbrev Workspace (Aux : Type*) (N w : ℕ) := ExactExecution.Workspace Aux N w

/-- Actual compressed execution, with a workspace unitary before its first query
and after every query. No support-growth hypothesis is part of this definition. -/
def run (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) :
    ℕ → EuclideanSpace ℂ (Workspace Aux N w × Database N)
  | 0 => onWorkspace (Database N) (gates 0).toLinearEquiv.toLinearMap (initial N φ)
  | q + 1 => onWorkspace (Database N) (gates (q + 1)).toLinearEquiv.toLinearMap
      (liftedQuery Aux encode (marked q) (run encode marked gates φ q))

/-- Every compressed prefix preserves the initial vector's norm. -/
theorem run_norm (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) :
    ‖run encode marked gates φ q‖ = ‖φ‖ := by
  induction q with
  | zero => rw [run, norm_onWorkspace, initial_norm]
  | succ q ih =>
    rw [run, norm_onWorkspace, liftedQuery_norm, ih]

theorem run_normalized (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (hφ : ‖φ‖ = 1) (q : ℕ) :
    ‖run encode marked gates φ q‖ = 1 := by
  rw [run_norm, hφ]

/-- The concrete `pC P pC` execution, including arbitrary interleaving workspace
unitaries and mixed ordinary/marked modes, has database degree at most `q`. -/
theorem run_supported (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) :
    BlockSupport.Supported q (run encode marked gates φ q) := by
  induction q with
  | zero =>
    exact supported_onWorkspace _ (initial_supported N φ)
  | succ q ih =>
    exact supported_onWorkspace _ (liftedQuery_supported encode (marked q) ih)

theorem run_supported_min (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) :
    BlockSupport.Supported (min q N) (run encode marked gates φ q) :=
  supported_min (run_supported encode marked gates φ q)

/-- The algorithm's actual final workspace reduction, tracing out all databases. -/
def finalReduced (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) :
    Matrix (Workspace Aux N w) (Workspace Aux N w) ℂ :=
  HiddenIsometry.reduced (run encode marked gates φ q)

@[simp] theorem finalReduced_apply (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) (a b : Workspace Aux N w) :
    finalReduced encode marked gates φ q a b =
      ∑ I : Database N,
        run encode marked gates φ q (a, I) * star (run encode marked gates φ q (b, I)) :=
  rfl

theorem finalReduced_posSemidef (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) :
    (finalReduced encode marked gates φ q).PosSemidef :=
  ExactFinalState.reduced_posSemidef _

theorem finalReduced_isHermitian (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) :
    (finalReduced encode marked gates φ q).IsHermitian :=
  ExactFinalState.reduced_isHermitian _

theorem finalReduced_trace (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) :
    Matrix.trace (finalReduced encode marked gates φ q) = ((‖φ‖ ^ 2 : ℝ) : ℂ) := by
  rw [finalReduced, ExactFinalState.trace_reduced, run_norm]

/-- Every normalized actual compressed execution produces a genuine density matrix. -/
theorem finalReduced_trace_one (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (hφ : ‖φ‖ = 1) (q : ℕ) :
    Matrix.trace (finalReduced encode marked gates φ q) = 1 := by
  rw [finalReduced_trace, hφ]
  norm_num

end Execution

end QuantumOracle.CompressedExecution
