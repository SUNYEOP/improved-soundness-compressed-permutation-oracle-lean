import QuantumOracle.Proof.PolarDegree
import QuantumOracle.Model.ExactExecution
import QuantumOracle.Model.HiddenIsometry
import QuantumOracle.Model.BlockSupport

/-!
# Actual exact executions inside the physical database register

The constructed positive polar isometry is applied to every oracle slice of the
actual exact execution, retaining arbitrary private memory and coherent query
arguments. Its physical database support follows from the proved exact knowledge
growth and the proved degree preservation of the actual normalized map.
-/

noncomputable section

namespace QuantumOracle.EmbeddedExecution

open PermutationExtensions HiddenIsometry

/-- Knowledge support of an actual joint state becomes physical database-size support. -/
theorem supported_onOracle {N t : ℕ} {A : Type*} [Fintype A]
    {ψ : EuclideanSpace ℂ (A × Perm N)}
    (hψ : WorkspaceKnowledge.Supported (KnowledgeSpace.K N t) ψ) :
    BlockSupport.Supported t (onOracle A (PolarEmbedding.candidate N) ψ) := by
  intro a I hI
  rw [onOracle_apply]
  exact PolarDegree.candidate_apply_eq_zero_of_mem_K (hψ a) I hI

section Execution

open ExactExecution

variable {N w : ℕ} {Aux : Type*} [Fintype Aux]
variable (encode : BasisLookup.Encoding N w) (marked : ℕ → Bool)
variable (gates : ℕ → EuclideanSpace ℂ (Workspace Aux N w) ≃ₗᵢ[ℂ]
  EuclideanSpace ℂ (Workspace Aux N w))
variable (φ : EuclideanSpace ℂ (Workspace Aux N w))

/-- A genuine exact prefix, embedded using the concrete positive polar isometry. -/
def run (q : ℕ) : BlockSupport.State (Workspace Aux N w) N :=
  onOracle (Workspace Aux N w) (PolarEmbedding.candidate N)
    (ExactExecution.run encode marked gates φ q)

@[simp] theorem run_norm (q : ℕ) : ‖run encode marked gates φ q‖ = ‖φ‖ := by
  rw [run, norm_onOracle, ExactExecution.run_norm]

theorem run_normalized (hφ : ‖φ‖ = 1) (q : ℕ) :
    ‖run encode marked gates φ q‖ = 1 := by
  rw [run_norm, hφ]

/-- Arbitrary coherent exact prefixes occupy only database sizes at most min(q,N). -/
theorem run_supported_min (q : ℕ) :
    BlockSupport.Supported (min q N) (run encode marked gates φ q) :=
  supported_onOracle (ExactExecution.run_supported encode marked gates φ q)

theorem run_supported (q : ℕ) :
    BlockSupport.Supported q (run encode marked gates φ q) :=
  BlockSupport.supported_mono (Nat.min_le_left _ _) (run_supported_min encode marked gates φ q)

/-- Embedding leaves the actual workspace density matrix unchanged. -/
theorem reduced_run (q : ℕ) :
    reduced (run encode marked gates φ q) =
      reduced (ExactExecution.run encode marked gates φ q) :=
  reduced_onOracle (PolarEmbedding.candidate N) _

/-- The next actual coherent exact query, before the following workspace gate. -/
def afterQuery (q : ℕ) : BlockSupport.State (Workspace Aux N w) N :=
  onOracle (Workspace Aux N w) (PolarEmbedding.candidate N)
    (ExactQueryGrowth.liftedQuery Aux encode (marked q)
      (ExactExecution.run encode marked gates φ q))

@[simp] theorem afterQuery_norm (q : ℕ) :
    ‖afterQuery encode marked gates φ q‖ = ‖φ‖ := by
  rw [afterQuery, norm_onOracle,
    (ExactQueryGrowth.liftedQuery Aux encode (marked q)).norm_map,
    ExactExecution.run_norm]

theorem afterQuery_normalized (hφ : ‖φ‖ = 1) (q : ℕ) :
    ‖afterQuery encode marked gates φ q‖ = 1 := by
  rw [afterQuery_norm, hφ]

/-- The next actual query grows the embedded exact-prefix degree by at most one. -/
theorem afterQuery_supported_min (q : ℕ) :
    BlockSupport.Supported (min (q + 1) N) (afterQuery encode marked gates φ q) := by
  apply supported_onOracle
  exact ExactQueryGrowth.liftedQuery_supported_min encode (marked q) q
    (ExactExecution.run_supported encode marked gates φ q)

theorem afterQuery_supported (q : ℕ) :
    BlockSupport.Supported (q + 1) (afterQuery encode marked gates φ q) :=
  BlockSupport.supported_mono (Nat.min_le_left _ _)
    (afterQuery_supported_min encode marked gates φ q)

theorem reduced_afterQuery (q : ℕ) :
    reduced (afterQuery encode marked gates φ q) =
      reduced (ExactQueryGrowth.liftedQuery Aux encode (marked q)
        (ExactExecution.run encode marked gates φ q)) :=
  reduced_onOracle (PolarEmbedding.candidate N) _

end Execution

end QuantumOracle.EmbeddedExecution
