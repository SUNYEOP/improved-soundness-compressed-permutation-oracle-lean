import QuantumOracle.Model.ConsistencyGrowth
import QuantumOracle.Model.Query

/-!
# Selecting an answer-dependent slice of the exact permutation register

An answer register update selects one previous workspace slice for each actual
permutation answer. The selection is the sum of the concrete answer indicators,
so its consistency degree increases by at most one.
-/

noncomputable section

namespace QuantumOracle.AnswerSelection

open PermutationExtensions ConsistentState ConsistencyGrowth KnowledgeSpace
open scoped BigOperators

variable {N t : ℕ}

/-- Forward or inverse answer projection, using the same direction convention as Query. -/
def projection (inverse : Bool) (x y : Fin N) :
    EuclideanSpace ℂ (Perm N) →ₗ[ℂ] EuclideanSpace ℂ (Perm N) :=
  if inverse then inverseAnswerProjection x y else answerProjection x y

@[simp] theorem projection_apply (inverse : Bool) (x y : Fin N)
    (v : EuclideanSpace ℂ (Perm N)) (π : Perm N) :
    projection inverse x y v π =
      if Query.permutationAnswer inverse π x = y then v π else 0 := by
  cases inverse <;> rfl

theorem projection_mem_succ (ht : t < N) (inverse : Bool) (x y : Fin N)
    {v : EuclideanSpace ℂ (Perm N)} (hv : v ∈ K N t) :
    projection inverse x y v ∈ K N (t + 1) := by
  cases inverse
  · exact answerProjection_mem_K_succ ht x y hv
  · exact inverseAnswerProjection_mem_K_succ ht x y hv

/-- Pick a workspace slice according to the actual forward/inverse permutation answer. -/
def select (inverse : Bool) (x : Fin N)
    (v : Fin N → EuclideanSpace ℂ (Perm N)) : EuclideanSpace ℂ (Perm N) :=
  WithLp.toLp 2 (fun π => v (Query.permutationAnswer inverse π x) π)

theorem select_eq_sum (inverse : Bool) (x : Fin N)
    (v : Fin N → EuclideanSpace ℂ (Perm N)) :
    select inverse x v = ∑ y, projection inverse x y (v y) := by
  classical
  ext π
  change v (Query.permutationAnswer inverse π x) π =
    (∑ y, projection inverse x y (v y)) π
  rw [show (∑ y, projection inverse x y (v y)) π =
      ∑ y, projection inverse x y (v y) π from
    map_sum (PiLp.projₗ 2 (𝕜 := ℂ) (fun _ : Perm N => ℂ) π)
      (fun y => projection inverse x y (v y)) Finset.univ]
  simp

/-- Actual answer selection has the proved one-step degree bound. -/
theorem select_mem_succ (ht : t < N) (inverse : Bool) (x : Fin N)
    (v : Fin N → EuclideanSpace ℂ (Perm N)) (hv : ∀ y, v y ∈ K N t) :
    select inverse x v ∈ K N (t + 1) := by
  rw [select_eq_sum]
  exact Submodule.sum_mem _ (fun y _ => projection_mem_succ ht inverse x y (hv y))

end QuantumOracle.AnswerSelection
