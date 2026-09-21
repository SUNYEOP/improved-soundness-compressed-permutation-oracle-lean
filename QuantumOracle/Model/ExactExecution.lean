import QuantumOracle.Model.KnowledgeSpace
import QuantumOracle.Model.WorkspaceKnowledge
import QuantumOracle.Model.ExactQueryGrowth

/-!
# Concrete exact-oracle executions

The initial permutation register is the normalized uniform state.  The
workspace may have arbitrary finite dimension and arbitrary amplitudes.
-/

noncomputable section

namespace QuantumOracle.ExactExecution

open PermutationExtensions
open scoped BigOperators

variable {A : Type*} [Fintype A]

/-- An arbitrary workspace state tensored with the actual uniform permutation state. -/
def initial (N : ℕ) (φ : EuclideanSpace ℂ A) :
    EuclideanSpace ℂ (A × Perm N) :=
  WithLp.toLp 2 (fun aπ => φ aπ.1 * ConsistentState.vector Database.empty aπ.2)

omit [Fintype A] in
@[simp] theorem initial_apply (N : ℕ) (φ : EuclideanSpace ℂ A) (a : A) (π : Perm N) :
    initial N φ (a, π) = φ a * ConsistentState.vector Database.empty π := rfl

/-- Introducing the actual uniform permutation register preserves the workspace norm. -/
theorem initial_norm (N : ℕ) (φ : EuclideanSpace ℂ A) :
    ‖initial N φ‖ = ‖φ‖ := by
  have hsq : ‖initial N φ‖ ^ 2 = ‖φ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp only [initial_apply, norm_mul, mul_pow]
    simp_rw [← Finset.mul_sum]
    simp_rw [← EuclideanSpace.norm_sq_eq (ConsistentState.vector (Database.empty : Database N)),
      ConsistentState.vector_norm, one_pow]
    simpa using (EuclideanSpace.norm_sq_eq φ).symm
  nlinarith [norm_nonneg (initial N φ), norm_nonneg φ]

/-- The genuine initialization map is linear and isometric. -/
def initialIsometry (N : ℕ) :
    EuclideanSpace ℂ A →ₗᵢ[ℂ] EuclideanSpace ℂ (A × Perm N) where
  toFun := initial N
  map_add' := by
    intro φ χ
    ext ⟨a, π⟩
    simp [initial_apply, add_mul]
  map_smul' := by
    intro z φ
    ext ⟨a, π⟩
    simp [initial_apply, mul_assoc]
  norm_map' := initial_norm N

omit [Fintype A] in
/-- Every oracle slice of the initial state belongs to the genuine level-zero space. -/
theorem initial_supported (N : ℕ) (φ : EuclideanSpace ℂ A) :
    WorkspaceKnowledge.Supported (KnowledgeSpace.K N 0) (initial N φ) :=
  WorkspaceKnowledge.supported_productState _ φ (KnowledgeSpace.vector_empty_mem N)

section Execution

open BasisLookup ExactCoherentQuery ExactQueryGrowth WorkspaceKnowledge

variable {N w : ℕ} {Aux : Type*} [Fintype Aux]

/-- The adversary can jointly manipulate private memory and every query argument. -/
abbrev Workspace (Aux : Type*) (N w : ℕ) := Aux × Args N w

/-- Actual execution with an arbitrary workspace unitary before the first query and
after each subsequent query. The Boolean schedule chooses ordinary or marked
queries; enable, direction, point, marker, and answer remain coherent registers. -/
def run (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) :
    ℕ → EuclideanSpace ℂ (Workspace Aux N w × Perm N)
  | 0 => onWorkspace (Perm N) (gates 0).toLinearEquiv.toLinearMap (initial N φ)
  | q + 1 => onWorkspace (Perm N) (gates (q + 1)).toLinearEquiv.toLinearMap
      (liftedQuery Aux encode (marked q) (run encode marked gates φ q))

/-- Every prefix is a genuine isometric evolution of the initial workspace vector. -/
theorem run_norm (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) :
    ‖run encode marked gates φ q‖ = ‖φ‖ := by
  induction q with
  | zero =>
    rw [run, norm_onWorkspace, initial_norm]
  | succ q ih =>
    rw [run, norm_onWorkspace, (liftedQuery Aux encode (marked q)).norm_map, ih]

theorem run_normalized (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (hφ : ‖φ‖ = 1) (q : ℕ) :
    ‖run encode marked gates φ q‖ = 1 := by
  rw [run_norm, hφ]

/-- The exact-prefix oracle register lies in the actual consistency space, even
after arbitrary entangling workspace unitaries and mixed query modes. At the
terminal level, the proven equality `K N N = ⊤` handles all later queries. -/
theorem run_supported (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) :
    Supported (KnowledgeSpace.K N (min q N)) (run encode marked gates φ q) := by
  induction q with
  | zero =>
    simp only [Nat.zero_min, run]
    exact supported_onWorkspace _ _ (initial_supported N φ)
  | succ q ih =>
    change Supported (KnowledgeSpace.K N (min (q + 1) N))
      (onWorkspace (Perm N) (gates (q + 1)).toLinearEquiv.toLinearMap
        (liftedQuery Aux encode (marked q) (run encode marked gates φ q)))
    apply supported_onWorkspace
    exact liftedQuery_supported_min encode (marked q) q ih

/-- Before the full level, the exact-prefix statement has its usual `K N q` form. -/
theorem run_supported_of_le (encode : Encoding N w) (marked : ℕ → Bool)
    (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Workspace Aux N w))
    (φ : EuclideanSpace ℂ (Workspace Aux N w)) (q : ℕ) (hq : q ≤ N) :
    Supported (KnowledgeSpace.K N q) (run encode marked gates φ q) := by
  simpa only [min_eq_left hq] using run_supported encode marked gates φ q

end Execution

end QuantumOracle.ExactExecution
