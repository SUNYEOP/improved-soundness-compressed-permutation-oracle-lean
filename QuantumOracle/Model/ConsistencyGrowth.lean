import QuantumOracle.Model.KnowledgeSpace

/-!
# Exact answer indicators raise consistency degree by at most one

The proof works with actual consistent-permutation vectors and actual diagonal
answer projections. It does not assume a Specht decomposition, a harmonic
embedding, or a query-error estimate. Forward and inverse answer conditions
are treated on the same permutation register.
-/

noncomputable section

namespace QuantumOracle.ConsistencyGrowth

open PermutationExtensions ConsistentState KnowledgeSpace

variable {N t : ℕ}

/-- A recorded answer rules out every different answer at that input. -/
theorem answerProjection_vector_of_disagrees (I : Database N) (x y z : Fin N)
    (hxz : (x, z) ∈ I.edges) (hne : z ≠ y) :
    answerProjection x y (vector I) = 0 := by
  ext π
  by_cases hext : Extends I π
  · have hneq : π x ≠ y := (hext x z hxz) ▸ hne
    simp [hneq]
  · simp [hext]

/-- Every exact answer sector is a scalar multiple of one genuine consistent
state whose database has grown by at most one. This includes zero sectors and
has no restriction excluding databases of full size. -/
theorem answerProjection_vector_eq_smul (I : Database N) (x y : Fin N) :
    ∃ (J : Database N) (c : ℂ), J.size ≤ I.size + 1 ∧
      answerProjection x y (vector I) = c • vector J := by
  classical
  by_cases hx : x ∈ I.domain
  · obtain ⟨z, hxz⟩ := (Database.mem_domain I x).mp hx
    by_cases hzy : z = y
    · subst z
      exact ⟨I, 1, Nat.le_succ _, by
        simpa using answerProjection_vector_of_mem I x y hxz⟩
    · exact ⟨I, 0, Nat.le_succ _, by
        simpa using answerProjection_vector_of_disagrees I x y z hxz hzy⟩
  · by_cases hy : y ∈ I.image
    · exact ⟨I, 0, Nat.le_succ _, by
        simpa using answerProjection_vector_of_occupied I x y hx hy⟩
    · refine ⟨I.set x y, ((Real.sqrt (N - I.size : ℕ))⁻¹ : ℂ), ?_, ?_⟩
      · exact le_of_eq (Database.set_size_of_fresh I x y hx hy)
      · exact answerProjection_vector_of_fresh I x y hx hy

/-- A version phrased solely as the span of actual bounded-size generators. -/
theorem answerProjection_vector_mem_bounded_span (I : Database N) (x y : Fin N) :
    answerProjection x y (vector I) ∈
      Submodule.span ℂ {v | ∃ J : Database N, J.size ≤ I.size + 1 ∧ vector J = v} := by
  obtain ⟨J, c, hsize, heq⟩ := answerProjection_vector_eq_smul I x y
  rw [heq]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨J, hsize, rfl⟩)

/-- The exact-size spaces in the manuscript grow by at most one under an
ordinary answer indicator, throughout the nonterminal size range. -/
theorem answerProjection_vector_mem_succ (I : Database N) (hI : I.size = t)
    (ht : t < N) (x y : Fin N) :
    answerProjection x y (vector I) ∈ K N (t + 1) := by
  obtain ⟨J, c, hsize, heq⟩ := answerProjection_vector_eq_smul I x y
  rw [heq]
  apply Submodule.smul_mem
  apply KnowledgeSpace.mono (s := J.size) (t := t + 1) (by omega) (by omega)
  exact KnowledgeSpace.vector_mem J rfl

/-- Linear extension of the proved generator action to the full oracle space. -/
theorem answerProjection_map_K_le (ht : t < N) (x y : Fin N) :
    (K N t).map (answerProjection x y) ≤ K N (t + 1) := by
  rw [K, Submodule.map_span_le]
  rintro _ ⟨I, rfl⟩
  exact answerProjection_vector_mem_succ I.val I.property ht x y

theorem answerProjection_mem_K_succ (ht : t < N) (x y : Fin N)
    {v : EuclideanSpace ℂ (Perm N)} (hv : v ∈ K N t) :
    answerProjection x y v ∈ K N (t + 1) :=
  answerProjection_map_K_le ht x y (Submodule.mem_map.mpr ⟨v, hv, rfl⟩)

/-- The inverse-answer condition `π⁻¹(x)=y` on the same exact register. -/
def inverseAnswerProjection (x y : Fin N) :
    EuclideanSpace ℂ (Perm N) →ₗ[ℂ] EuclideanSpace ℂ (Perm N) where
  toFun v := WithLp.toLp 2 (fun π => if π.symm x = y then v π else 0)
  map_add' u v := by
    ext π
    change (if π.symm x = y then u π + v π else 0) =
      (if π.symm x = y then u π else 0) + (if π.symm x = y then v π else 0)
    split_ifs <;> simp
  map_smul' c v := by
    ext π
    change (if π.symm x = y then c * v π else 0) =
      c * (if π.symm x = y then v π else 0)
    split_ifs <;> simp

@[simp] theorem inverseAnswerProjection_apply (x y : Fin N)
    (v : EuclideanSpace ℂ (Perm N)) (π : Perm N) :
    inverseAnswerProjection x y v π = if π.symm x = y then v π else 0 := rfl

/-- Inverse lookup is exactly the ordinary constraint with exchanged endpoints. -/
theorem inverseAnswerProjection_eq (x y : Fin N) :
    inverseAnswerProjection x y = answerProjection y x := by
  ext v π
  have h : (π.symm x = y) ↔ (π y = x) := by
    constructor
    · intro h
      exact (π.symm_apply_eq.mp h).symm
    · intro h
      exact π.symm_apply_eq.mpr h.symm
  simp only [inverseAnswerProjection_apply, answerProjection_apply, h]

theorem inverseAnswerProjection_vector_eq_smul (I : Database N) (x y : Fin N) :
    ∃ (J : Database N) (c : ℂ), J.size ≤ I.size + 1 ∧
      inverseAnswerProjection x y (vector I) = c • vector J := by
  rw [inverseAnswerProjection_eq]
  exact answerProjection_vector_eq_smul I y x

theorem inverseAnswerProjection_map_K_le (ht : t < N) (x y : Fin N) :
    (K N t).map (inverseAnswerProjection x y) ≤ K N (t + 1) := by
  rw [inverseAnswerProjection_eq]
  exact answerProjection_map_K_le ht y x

theorem inverseAnswerProjection_mem_K_succ (ht : t < N) (x y : Fin N)
    {v : EuclideanSpace ℂ (Perm N)} (hv : v ∈ K N t) :
    inverseAnswerProjection x y v ∈ K N (t + 1) := by
  rw [inverseAnswerProjection_eq]
  exact answerProjection_mem_K_succ ht y x hv

end QuantumOracle.ConsistencyGrowth
