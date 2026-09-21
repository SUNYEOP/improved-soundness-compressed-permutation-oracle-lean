import QuantumOracle.Model.FinitePurification
import QuantumOracle.Model.ExactFinalState

/-!
# Density properties in the numbered finite output basis

The actual reduction of any finite joint vector is positive semidefinite and
Hermitian, with trace equal to its squared norm. These statements apply equally
to exact and compressed runs and to vectors after discarding workspace factors.
-/

noncomputable section

namespace QuantumOracle.FiniteDensity

open FinitePurification
open scoped ComplexOrder

variable {A O : Type*} [Fintype A] [Fintype O]

theorem reducedFin_posSemidef (ψ : EuclideanSpace ℂ (A × O)) :
    (reducedFin ψ).PosSemidef := by
  rw [← reducedState_coordinateState]
  exact ExactFinalState.reduced_posSemidef (coordinateState ψ)

theorem reducedFin_isHermitian (ψ : EuclideanSpace ℂ (A × O)) :
    (reducedFin ψ).IsHermitian := (reducedFin_posSemidef ψ).isHermitian

theorem trace_reducedFin (ψ : EuclideanSpace ℂ (A × O)) :
    Matrix.trace (reducedFin ψ) = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [← reducedState_coordinateState]
  change Matrix.trace (HiddenIsometry.reduced (coordinateState ψ)) = _
  rw [ExactFinalState.trace_reduced, coordinateState_norm]

theorem trace_reducedFin_of_normalized (ψ : EuclideanSpace ℂ (A × O))
    (hψ : ‖ψ‖ = 1) : Matrix.trace (reducedFin ψ) = 1 := by
  rw [trace_reducedFin, hψ]
  norm_num

end QuantumOracle.FiniteDensity
