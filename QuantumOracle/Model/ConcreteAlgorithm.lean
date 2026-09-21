import QuantumOracle.Model.ExactExecution

/-!
# The finite pure/unitary algorithm model

An algorithm supplies a finite private-register dimension, normalized initial
workspace vector, ordinary/marked schedule, workspace unitaries, and a query
count. It supplies no oracle states, purifications, local errors, or bounds.
The exact and compressed experiments will execute this same record.
-/

noncomputable section

namespace QuantumOracle.ConcreteExperiment

open ExactCoherentQuery ExactExecution

/-- Finite algorithms in the implemented pure/unitary query model. -/
structure Algorithm (N w : ℕ) where
  auxDim : ℕ
  queries : ℕ
  marked : ℕ → Bool
  gates : ℕ → EuclideanSpace ℂ (Workspace (Fin auxDim) N w) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ (Workspace (Fin auxDim) N w)
  initial : EuclideanSpace ℂ (Workspace (Fin auxDim) N w)
  normalized : ‖initial‖ = 1

abbrev Algorithm.Workspace {N w : ℕ} (a : Algorithm N w) :=
  ExactExecution.Workspace (Fin a.auxDim) N w

/-- A concrete oracle-independent initial basis state for a zero-query algorithm. -/
def zeroWorkspaceKet {N w : ℕ} (x : Fin N) :
    EuclideanSpace ℂ (ExactExecution.Workspace (Fin 1) N w) := by
  classical
  exact EuclideanSpace.single ((0 : Fin 1),
    (false, ((false, x), (false, fun _ => false)))) 1

theorem zeroWorkspaceKet_norm {N w : ℕ} (x : Fin N) :
    ‖zeroWorkspaceKet (w := w) x‖ = 1 := by
  classical
  simp [zeroWorkspaceKet]

/-- A zero-query algorithm with identity workspace gates. -/
def zeroAlgorithm {N w : ℕ} (x : Fin N) : Algorithm N w where
  auxDim := 1
  queries := 0
  marked := fun _ => false
  gates := fun _ => LinearIsometryEquiv.refl ℂ _
  initial := zeroWorkspaceKet x
  normalized := zeroWorkspaceKet_norm x

@[simp] theorem zeroAlgorithm_queries {N w : ℕ} (x : Fin N) :
    (zeroAlgorithm (w := w) x).queries = 0 := rfl

/-- The admissible query-bounded class is nonempty for every positive domain size. -/
theorem exists_algorithm_le {N w : ℕ} (hN : 0 < N) (q : ℕ) :
    ∃ a : Algorithm N w, a.queries ≤ q :=
  ⟨zeroAlgorithm ⟨0, hN⟩, Nat.zero_le q⟩

end QuantumOracle.ConcreteExperiment
