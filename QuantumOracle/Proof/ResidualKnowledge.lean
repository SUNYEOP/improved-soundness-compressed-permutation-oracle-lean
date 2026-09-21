import QuantumOracle.Model.ConsistencyGrowth
import QuantumOracle.Proof.ResidualAdjoint
import QuantumOracle.Proof.ResidualRemoval

/-!
# Actual answer restriction preserves the upper knowledge filtration

Selecting an answer first either gives zero or a consistent database state
containing that answer. Removing its prescribed edge then gives a genuine
residual consistent state, with degree no greater than the original degree.
The statements include full and out-of-range source levels and `N = 0`.
-/

noncomputable section

namespace QuantumOracle.ResidualKnowledge

open PermutationExtensions ConsistentState KnowledgeSpace

variable {N t : ℕ}

/-- Every nonzero selected sector is represented by a database that records
the selected answer, and its size has increased by at most one. -/
theorem answerProjection_vector_eq_smul_recording (I : Database N) (x y : Fin N) :
    ∃ (J : Database N) (c : ℂ), J.size ≤ I.size + 1 ∧
      (c = 0 ∨ (x, y) ∈ J.edges) ∧
      answerProjection x y (vector I) = c • vector J := by
  classical
  by_cases hx : x ∈ I.domain
  · obtain ⟨z, hxz⟩ := (Database.mem_domain I x).mp hx
    by_cases hzy : z = y
    · subst z
      exact ⟨I, 1, Nat.le_succ _, Or.inr hxz, by
        simpa using answerProjection_vector_of_mem I x y hxz⟩
    · exact ⟨I, 0, Nat.le_succ _, Or.inl rfl, by
        simpa using ConsistencyGrowth.answerProjection_vector_of_disagrees I x y z hxz hzy⟩
  · by_cases hy : y ∈ I.image
    · exact ⟨I, 0, Nat.le_succ _, Or.inl rfl, by
        simpa using answerProjection_vector_of_occupied I x y hx hy⟩
    · exact ⟨I.set x y, ((Real.sqrt (N - I.size : ℕ))⁻¹ : ℂ),
        le_of_eq (Database.set_size_of_fresh I x y hx hy),
        Or.inr (Database.set_contains I x y),
        answerProjection_vector_of_fresh I x y hx hy⟩

/-- Restricting an actually inserted database returns its residual state with
its normalization unchanged. -/
@[simp] theorem restrict_vector_insert (x y : Fin (N + 1)) (I : Database N) :
    ResidualAdjoint.restrict x y (vector (ResidualDatabase.insert x y I)) =
      vector I := by
  ext σ
  exact ResidualConsistency.vector_insert_apply x y I σ

/-- A recorded edge can be removed directly from the actual consistent state. -/
theorem restrict_vector_of_mem (x y : Fin (N + 1)) (I : Database (N + 1))
    (hxy : (x, y) ∈ I.edges) :
    ResidualAdjoint.restrict x y (vector I) = vector (ResidualRemoval.remove x y I) := by
  rw [← ResidualRemoval.insert_remove x y I hxy, restrict_vector_insert,
    ResidualRemoval.remove_insert]

/-- Every residual restriction of a consistent state is a scalar multiple of
an actual consistent state whose degree is no greater than the source degree. -/
theorem restrict_vector_eq_smul (x y : Fin (N + 1)) (I : Database (N + 1)) :
    ∃ (J : Database N) (c : ℂ), J.size ≤ I.size ∧
      ResidualAdjoint.restrict x y (vector I) = c • vector J := by
  obtain ⟨J, c, hsize, hrecord, hprojection⟩ :=
    answerProjection_vector_eq_smul_recording I x y
  have heq : ResidualAdjoint.restrict x y (vector I) =
      c • ResidualAdjoint.restrict x y (vector J) := by
    rw [← ResidualAdjoint.restrict_answerProjection x y (vector I), hprojection, map_smul]
  rcases hrecord with hc | hxy
  · refine ⟨Database.empty, 0, by simp, ?_⟩
    simpa [hc] using heq
  · refine ⟨ResidualRemoval.remove x y J, c, ?_, ?_⟩
    · have hr := ResidualRemoval.size_remove_add_one x y J hxy
      omega
    · simpa only [restrict_vector_of_mem x y J hxy] using heq

/-- Restriction of a degree-bounded generator lies in the correspondingly
capped residual knowledge space. -/
theorem restrict_vector_mem_K (x y : Fin (N + 1)) (I : Database (N + 1))
    (hI : I.size ≤ t) :
    ResidualAdjoint.restrict x y (vector I) ∈ K N (min t N) := by
  obtain ⟨J, c, hsize, heq⟩ := restrict_vector_eq_smul x y I
  rw [heq]
  apply Submodule.smul_mem
  apply KnowledgeSpace.mono (s := J.size) (t := min t N)
    (Nat.le_min.mpr ⟨hsize.trans hI, J.size_le⟩) (Nat.min_le_right t N)
  exact KnowledgeSpace.vector_mem J rfl

/-- The actual restriction maps every source knowledge space into the
residual space of the same degree, capped at the residual domain size. -/
theorem restrict_map_K_le (x y : Fin (N + 1)) :
    (K (N + 1) t).map (ResidualAdjoint.restrict x y) ≤ K N (min t N) := by
  rw [K, Submodule.map_span_le]
  rintro _ ⟨I, rfl⟩
  exact restrict_vector_mem_K x y I.val (le_of_eq I.property)

theorem restrict_mem_K (x y : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ K (N + 1) t) :
    ResidualAdjoint.restrict x y h ∈ K N (min t N) :=
  restrict_map_K_le x y (Submodule.mem_map.mpr ⟨h, hh, rfl⟩)

/-- Below the residual domain size no capping is needed. -/
theorem restrict_mem_K_of_le (x y : Fin (N + 1)) (ht : t ≤ N)
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ K (N + 1) t) :
    ResidualAdjoint.restrict x y h ∈ K N t := by
  simpa only [Nat.min_eq_left ht] using restrict_mem_K x y hh

end QuantumOracle.ResidualKnowledge
