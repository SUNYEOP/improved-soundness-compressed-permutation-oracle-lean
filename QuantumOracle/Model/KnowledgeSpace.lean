import QuantumOracle.Model.ExtensionOperator

/-!
# Actual oracle knowledge subspaces

The manuscript's `K_{N,t}` is the complex span of the normalized states of
actual size-t databases. These spaces are the ranges of `T_{N,t}`. Their
nesting below the final level is proved by resolving one fresh input into its
actual answer sectors, without representation-theoretic assumptions.
-/

noncomputable section

namespace QuantumOracle.KnowledgeSpace

open PermutationExtensions ConsistentState
open scoped BigOperators

variable {N t : ℕ}

/-- The manuscript's span of size-t consistent-permutation states. -/
def K (N t : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Perm N)) :=
  Submodule.span ℂ (Set.range (fun I : ExtensionOperator.Level N t => vector I.val))

theorem vector_mem (I : Database N) (hI : I.size = t) : vector I ∈ K N t :=
  Submodule.subset_span ⟨⟨I, hI⟩, rfl⟩

/-- The concrete extension operator has exactly the manuscript's oracle space as range. -/
theorem range_T (N t : ℕ) : LinearMap.range (ExtensionOperator.T N t) = K N t := by
  classical
  let b := (EuclideanSpace.basisFun (ExtensionOperator.Level N t) ℂ).toBasis
  rw [← Submodule.map_top, ← b.span_eq, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext I
  exact ExtensionOperator.T_single N t I

/-- Every actual lower-level state resolves into next-level states at a fresh input. -/
theorem vector_mem_succ (I : Database N) (ht : I.size = t) (hlt : t < N) :
    vector I ∈ K N (t + 1) := by
  classical
  have hcard : I.domain.card < (Finset.univ : Finset (Fin N)).card := by
    have hsize : I.domain.card = t := ht
    simpa only [Finset.card_univ, Fintype.card_fin, hsize] using hlt
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [← sum_answerProjection x (vector I)]
  apply Submodule.sum_mem
  intro y _
  by_cases hy : y ∈ I.image
  · rw [answerProjection_vector_of_occupied I x y hx hy]
    exact Submodule.zero_mem _
  · rw [answerProjection_vector_of_fresh I x y hx hy]
    apply Submodule.smul_mem
    apply vector_mem
    rw [Database.set_size_of_fresh I x y hx hy, ht]

/-- Nesting stops at `N`: the set of size-(N+1) databases is empty. -/
theorem le_succ (ht : t < N) : K N t ≤ K N (t + 1) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨I, rfl⟩
  exact vector_mem_succ I.val I.property ht

/-- Monotonicity throughout the valid size range, including the full level. -/
theorem mono {s t : ℕ} (hst : s ≤ t) (ht : t ≤ N) : K N s ≤ K N t := by
  induction t, hst using Nat.le_induction with
  | base => exact le_refl _
  | succ t hst ih =>
    exact (ih (Nat.le_of_succ_le ht)).trans (le_succ (Nat.lt_of_succ_le ht))

/-- A full permutation graph has exactly its own permutation as extension. -/
theorem extends_ofPermutation_iff (π σ : Perm N) :
    Extends (Database.ofPermutation π) σ ↔ σ = π := by
  constructor
  · intro h
    apply Equiv.ext
    intro x
    exact h x (π x) ((Database.mem_ofPermutation π x (π x)).mpr rfl)
  · intro h
    subst σ
    intro x y hxy
    exact (Database.mem_ofPermutation π x y).mp hxy

/-- At the full database level the consistent state is an ordinary permutation ket. -/
theorem vector_ofPermutation (π : Perm N) :
    vector (Database.ofPermutation π) = EuclideanSpace.single π 1 := by
  classical
  ext σ
  simp only [vector_apply, extends_ofPermutation_iff, amplitude,
    Database.size_ofPermutation, Nat.sub_self, Nat.factorial_zero, Nat.cast_one,
    Real.sqrt_one, inv_one, Complex.ofReal_one, EuclideanSpace.single_apply]

/-- The full level spans the whole exact permutation register, including `N = 0`. -/
theorem full_eq_top (N : ℕ) : K N N = ⊤ := by
  classical
  apply top_unique
  let b := (EuclideanSpace.basisFun (Perm N) ℂ).toBasis
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨π, rfl⟩
  have h := vector_mem (Database.ofPermutation π) (Database.size_ofPermutation π)
  rw [vector_ofPermutation] at h
  change EuclideanSpace.basisFun (Perm N) ℂ π ∈ K N N
  simpa only [EuclideanSpace.basisFun_apply] using h

/-- Out-of-range levels have no databases and consequently have zero span. -/
theorem eq_bot_of_gt (ht : N < t) : K N t = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro _ ⟨I, rfl⟩
  have hsize := I.val.size_le
  have hlevel := I.property
  omega

theorem database_eq_empty_of_size_zero (I : Database N) (hI : I.size = 0) :
    I = Database.empty := by
  apply Database.ext
  rw [Database.empty_edges, ← Finset.card_eq_zero, ← I.size_eq_card_edges, hI]

/-- The initial oracle state belongs to level zero. -/
theorem vector_empty_mem (N : ℕ) :
    vector (Database.empty : Database N) ∈ K N 0 :=
  vector_mem Database.empty Database.empty_size

/-- Level zero is exactly the line spanned by the uniform permutation state. -/
theorem zero_eq_span_uniform (N : ℕ) :
    K N 0 = Submodule.span ℂ {UniformState.uniform (Perm N)} := by
  unfold K
  congr 1
  ext v
  constructor
  · rintro ⟨I, rfl⟩
    change vector I.val ∈ {UniformState.uniform (Perm N)}
    rw [database_eq_empty_of_size_zero I.val I.property,
      vector_empty_eq_uniform]
    exact Set.mem_singleton _
  · intro hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    exact ⟨⟨Database.empty, Database.empty_size⟩, vector_empty_eq_uniform⟩

end QuantumOracle.KnowledgeSpace
