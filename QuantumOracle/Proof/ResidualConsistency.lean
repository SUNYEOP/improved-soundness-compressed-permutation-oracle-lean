import QuantumOracle.Proof.ResidualPermutation
import QuantumOracle.Proof.ResidualDatabase

/-!
# Actual consistency under insertion of a fixed answer

Residual permutations and residual databases use the same increasing
`Fin.succAbove` coordinates. Their actual extension predicates correspond, and
the inserted database state has exactly the residual consistent amplitudes in
its answer sector and zero amplitudes in all other answer sectors.
-/

noncomputable section

namespace QuantumOracle.ResidualConsistency

open PermutationExtensions

variable {N : ℕ}

/-- Inserting the same actual answer preserves precisely the residual constraints. -/
theorem extends_insert_iff (x y : Fin (N + 1)) (I : Database N) (σ : Perm N) :
    Extends (ResidualDatabase.insert x y I) (ResidualPermutation.insert x y σ) ↔
      Extends I σ := by
  constructor
  · intro h a b hab
    have he := h (x.succAbove a) (y.succAbove b)
      ((ResidualDatabase.mem_insert_succAbove x y I a b).mpr hab)
    rw [ResidualPermutation.insert_succAbove] at he
    exact Fin.succAbove_right_injective he
  · intro h a b hab
    rcases (ResidualDatabase.mem_insert x y I a b).mp hab with ⟨rfl, rfl⟩ | hres
    · exact ResidualPermutation.insert_at _ _ σ
    · obtain ⟨u, v, huv, rfl, rfl⟩ := hres
      rw [ResidualPermutation.insert_succAbove, h u v huv]

/-- Adding one fixed edge also increases the domain size, leaving its factorial amplitude unchanged. -/
@[simp] theorem amplitude_insert (x y : Fin (N + 1)) (I : Database N) :
    ConsistentState.amplitude (ResidualDatabase.insert x y I) =
      ConsistentState.amplitude I := by
  unfold ConsistentState.amplitude
  rw [ResidualDatabase.insert_size, Nat.add_sub_add_right]

/-- Actual normalized consistency coefficients coincide in the matching answer sector. -/
theorem vector_insert_apply (x y : Fin (N + 1)) (I : Database N) (σ : Perm N) :
    ConsistentState.vector (ResidualDatabase.insert x y I) (ResidualPermutation.insert x y σ) =
      ConsistentState.vector I σ := by
  classical
  simp only [ConsistentState.vector_apply, extends_insert_iff, amplitude_insert]

/-- Every permutation giving a different answer has zero inserted-state amplitude. -/
theorem vector_insert_apply_of_answer_ne (x y : Fin (N + 1)) (I : Database N)
    (π : Perm (N + 1)) (hπ : π x ≠ y) :
    ConsistentState.vector (ResidualDatabase.insert x y I) π = 0 := by
  apply ConsistentState.vector_apply_of_not_extends
  intro h
  exact hπ (h x y (ResidualDatabase.insert_contains x y I))

/-- In actual answer/residual coordinates, precisely the prescribed answer survives. -/
theorem reindex_vector_insert (x y z : Fin (N + 1)) (I : Database N) (σ : Perm N) :
    ResidualPermutation.reindex x (ConsistentState.vector (ResidualDatabase.insert x y I))
        (z, σ) = if z = y then ConsistentState.vector I σ else 0 := by
  classical
  rw [ResidualPermutation.reindex_apply]
  by_cases hzy : z = y
  · subst z
    rw [if_pos rfl, vector_insert_apply]
  · rw [if_neg hzy]
    apply vector_insert_apply_of_answer_ne
    simpa only [ResidualPermutation.insert_at] using hzy

end QuantumOracle.ResidualConsistency
