import QuantumOracle.Proof.SpechtBranchingMultiplicity
import QuantumOracle.Proof.ResidualPermutation

/-!
# One-corner recursion for actual tuple multiplicities

Appending the last point to a tuple identifies its pointwise stabilizer with
the old stabilizer through the actual last-point-fixing inclusion. Character
restriction and subgroup averaging then give the one-corner recursion for
the actual intertwiner dimensions. No branching count is used as a definition.
-/

noncomputable section

namespace QuantumOracle.SpechtBranchingPaths

open PermutationExtensions SpechtFoundation SpechtMultiplicity SpechtBranchingMultiplicity
open scoped BigOperators Classical

/-- Append the new last point to an actual tuple. -/
def snocTuple {N t : ℕ} (e : Tuple N t) : Tuple (N + 1) (t + 1) where
  toFun := Fin.lastCases (Fin.last N) (fun i => (e i).castSucc)
  inj' := by
    intro i j h
    cases i using Fin.lastCases <;> cases j using Fin.lastCases
    · rfl
    · simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at h
      exact False.elim ((Fin.castSucc_ne_last _ h.symm))
    · simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at h
      exact False.elim ((Fin.castSucc_ne_last _ h))
    · simp only [Fin.lastCases_castSucc] at h
      exact congrArg Fin.castSucc (e.injective (Fin.castSucc_injective _ h))

@[simp] theorem snocTuple_last {N t : ℕ} (e : Tuple N t) :
    snocTuple e (Fin.last t) = Fin.last N := by simp [snocTuple]

@[simp] theorem snocTuple_castSucc {N t : ℕ} (e : Tuple N t) (i : Fin t) :
    snocTuple e i.castSucc = (e i).castSucc := by simp [snocTuple]

theorem includePerm_last (N : ℕ) (σ : Perm N) :
    includePerm N σ (Fin.last N) = Fin.last N := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

theorem includePerm_castSucc (N : ℕ) (σ : Perm N) (i : Fin N) :
    includePerm N σ i.castSucc = (σ i).castSucc :=
  Equiv.Perm.viaEmbedding_apply σ Fin.castSuccEmb i

theorem includePerm_eq_insert (N : ℕ) (σ : Perm N) :
    includePerm N σ = ResidualPermutation.insert (Fin.last N) (Fin.last N) σ := by
  apply Equiv.ext
  intro i
  cases i using Fin.lastCases with
  | last => rw [includePerm_last, ResidualPermutation.insert_at]
  | cast i =>
    rw [includePerm_castSucc]
    simpa only [Fin.succAbove_last] using
      (ResidualPermutation.insert_succAbove (Fin.last N) (Fin.last N) σ i).symm

private def lastFiber {N t : ℕ} (e : Tuple N t)
    (π : pointwiseStabilizer (snocTuple e)) :
    ResidualPermutation.Fiber (Fin.last N) (Fin.last N) :=
  ⟨π.val, by simpa only [snocTuple_last] using π.property (Fin.last t)⟩

/-- Actual stabilizers before and after adding a new fixed last point. -/
def stabilizerSuccEquiv {N t : ℕ} (e : Tuple N t) :
    pointwiseStabilizer e ≃ pointwiseStabilizer (snocTuple e) where
  toFun σ := ⟨ResidualPermutation.insert (Fin.last N) (Fin.last N) σ.val, by
    intro i
    cases i using Fin.lastCases with
    | last => simp only [snocTuple_last, ResidualPermutation.insert_at]
    | cast i =>
      rw [snocTuple_castSucc, ← includePerm_eq_insert, includePerm_castSucc, σ.property i]⟩
  invFun π := ⟨ResidualPermutation.remove (Fin.last N) (Fin.last N) (lastFiber e π), by
    intro i
    apply Fin.castSucc_injective
    have hr := ResidualPermutation.remove_succAbove (Fin.last N) (Fin.last N)
      (lastFiber e π) (e i)
    rw [Fin.succAbove_last] at hr
    change _ = π.val (e i).castSucc at hr
    rw [hr]
    simpa only [snocTuple_castSucc] using π.property i.castSucc⟩
  left_inv σ := by
    apply Subtype.ext
    exact ResidualPermutation.remove_insert (Fin.last N) (Fin.last N) σ.val
  right_inv π := by
    apply Subtype.ext
    exact ResidualPermutation.insert_remove (Fin.last N) (Fin.last N) (lastFiber e π)

@[simp] theorem stabilizerSuccEquiv_apply_val {N t : ℕ} (e : Tuple N t)
    (σ : pointwiseStabilizer e) :
    (stabilizerSuccEquiv e σ).val = includePerm N σ.val :=
  (includePerm_eq_insert N σ.val).symm

/-- The actual invariant dimensions satisfy one-corner branching. -/
theorem stabilizer_finrank_snoc (N t : ℕ) (e : Tuple N t)
    (mu : Nat.Partition (N + 1)) :
    Module.finrank ℂ (stabilizerInvariants mu (snocTuple e)) =
      ∑ la ∈ removeCorners mu, Module.finrank ℂ (stabilizerInvariants la e) := by
  have hc : Nat.card (pointwiseStabilizer (snocTuple e)) =
      Nat.card (pointwiseStabilizer e) := Nat.card_congr (stabilizerSuccEquiv e).symm
  have hs : (∑ π : pointwiseStabilizer (snocTuple e), character (N + 1) mu π.val) =
      ∑ σ : pointwiseStabilizer e, character (N + 1) mu (includePerm N σ.val) := by
    simpa only [stabilizerSuccEquiv_apply_val] using
      (Equiv.sum_comp (stabilizerSuccEquiv e)
        (fun π => character (N + 1) mu π.val)).symm
  apply Nat.cast_injective (R := ℂ)
  simp only [Nat.cast_sum]
  rw [← tupleMultiplicity_eq_stabilizer_finrank (N + 1) (t + 1) mu (snocTuple e),
    tupleMultiplicity_eq_stabilizer_average, hc, hs]
  simp_rw [character_restrict]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro la _
  rw [← tupleMultiplicity_eq_stabilizer_finrank N t la e]
  exact (tupleMultiplicity_eq_stabilizer_average N t la e).symm

/-- The actual tuple-intertwiner multiplicity obeys the manuscript's
`(N + 1, t + 1)` to `(N, t)` one-corner recursion. -/
theorem tupleMultiplicity_succ (N t : ℕ) (ht : t ≤ N)
    (mu : Nat.Partition (N + 1)) :
    tupleMultiplicity (N + 1) (t + 1) mu =
      ∑ la ∈ removeCorners mu, tupleMultiplicity N t la := by
  let e : Tuple N t := Fin.castLEEmb ht
  rw [tupleMultiplicity_eq_stabilizer_finrank (N + 1) (t + 1) mu (snocTuple e),
    stabilizer_finrank_snoc]
  apply Finset.sum_congr rfl
  intro la _
  exact (tupleMultiplicity_eq_stabilizer_finrank N t la e).symm

end QuantumOracle.SpechtBranchingPaths
