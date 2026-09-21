import QuantumOracle.Proof.SpechtBranchingMultiplicity
import QuantumOracle.Proof.SpechtHookBridge
import RepresentationTheory.SymmetricGroup.PartitionSubspaceAuxiliary

/-!
# The actual zero-tuple multiplicity

The actual one-row Specht ideal has dimension one and trivial permutation
action. Character orthogonality therefore evaluates the actual intertwiner
dimension at degree zero. The empty partition and trivial group are included.
-/

noncomputable section

namespace QuantumOracle.SpechtTrivialMultiplicity

open PermutationExtensions SpechtFoundation SpechtMultiplicity
open RepresentationTheory.SymmetricGroup.PartitionSubspaceAuxiliary
open RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
open RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter
open scoped BigOperators Classical

theorem indiscrete_eq_positivePartition (N : ℕ) (hN : 0 < N) :
    Nat.Partition.indiscrete N = positivePartitionAuxiliaryAlt N hN := by
  apply Nat.Partition.ext
  exact Nat.Partition.indiscrete_parts hN.ne'

/-- The actual permutation action on the one-row Specht ideal is the identity. -/
theorem action_indiscrete_eq_id (N : ℕ) (hN : 0 < N) (π : Perm N) :
    action N (Nat.Partition.indiscrete N) π = LinearMap.id := by
  rw [indiscrete_eq_positivePartition N hN]
  apply LinearMap.ext
  intro v
  change (MonoidAlgebra.of ℂ (Perm N) π) • v = v
  exact perm_smul_positivePartitionAuxiliaryAlt_eq_self N hN π v

theorem dimension_indiscrete_pos (N : ℕ) (hN : 0 < N) :
    Module.finrank ℂ (specht N (Nat.Partition.indiscrete N)) = 1 := by
  rw [indiscrete_eq_positivePartition N hN]
  exact finrank_positivePartitionAuxiliaryAlt_eq_one N hN

theorem dimension_zero (la : Nat.Partition 0) : Module.finrank ℂ (specht 0 la) = 1 := by
  have hcard := SpechtHookBridge.diagram_card la
  have hc : (diagram la).cells = ∅ := Finset.card_eq_zero.mp hcard
  have h := dimension_mul_hookProduct 0 la
  simpa only [hookProduct_eq_prod, hc, Finset.prod_empty, mul_one, Nat.factorial_zero] using h

/-- The trace character of the actual one-row action is identically one. -/
theorem character_indiscrete (N : ℕ) (π : Perm N) :
    character N (Nat.Partition.indiscrete N) π = 1 := by
  by_cases hN : 0 < N
  · rw [character_eq_trace, action_indiscrete_eq_id N hN, LinearMap.trace_id,
      dimension_indiscrete_pos N hN, Nat.cast_one]
  · have hzero : N = 0 := by omega
    subst N
    have hπ : π = 1 := Subsingleton.elim _ _
    rw [character_eq_trace, hπ]
    change LinearMap.trace ℂ (specht 0 (Nat.Partition.indiscrete 0))
      (representation 0 (Nat.Partition.indiscrete 0) 1) = 1
    rw [map_one, LinearMap.trace_one, dimension_zero, Nat.cast_one]

/-- Degree-zero multiplicity is computed from the actual character pairing. -/
theorem tupleMultiplicity_zero_eq_indiscrete (N : ℕ) (la : Nat.Partition N) :
    tupleMultiplicity N 0 la = if la = Nat.Partition.indiscrete N then 1 else 0 := by
  have hm := tupleMultiplicity_eq_character_average N 0 la
  simp only [tuple_character, Nat.descFactorial_zero, Nat.cast_one, mul_one] at hm
  have ho := sum_auxiliaryPartitionPermutationValue_mul_inv N la (Nat.Partition.indiscrete N)
  change (∑ π : Perm N, character N la π * character N (Nat.Partition.indiscrete N) π⁻¹) =
    (N.factorial : ℂ) * if la = Nat.Partition.indiscrete N then 1 else 0 at ho
  simp only [character_indiscrete, mul_one] at ho
  rw [ho, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero N), one_mul] at hm
  by_cases h : la = Nat.Partition.indiscrete N
  · simp only [if_pos h] at hm ⊢
    exact_mod_cast hm
  · simp only [if_neg h] at hm ⊢
    exact_mod_cast hm

theorem indiscrete_rowLen_zero (N : ℕ) :
    (diagram (Nat.Partition.indiscrete N)).rowLen 0 = N := by
  by_cases hN : 0 < N
  · rw [indiscrete_eq_positivePartition N hN]
    change (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition
      (positivePartitionAuxiliaryAlt N hN)).rowLen 0 = N
    rw [RepresentationTheory.YoungDiagram.PartitionFormulas.Partition.toYoungDiagram_rowLen_eq_getD,
      positivePartitionAuxiliaryAlt_sortedParts]
    rfl
  · have hz : N = 0 := by omega
    subst N
    rw [show diagram (Nat.Partition.indiscrete 0) = ⊥ by
      apply YoungDiagram.ext
      exact Finset.card_eq_zero.mp (SpechtHookBridge.diagram_card _)]
    simp [YoungDiagram.rowLen]

/-- The geometric one-row condition agrees with the actual indiscrete partition. -/
theorem rowLen_zero_eq_iff_indiscrete (N : ℕ) (la : Nat.Partition N) :
    (diagram la).rowLen 0 = N ↔ la = Nat.Partition.indiscrete N := by
  constructor
  · intro hrow
    by_cases hN : 0 < N
    · have hhead : (auxiliaryPartitionNatList la).getD 0 0 = N := by
        simpa only [diagram,
          RepresentationTheory.YoungDiagram.PartitionFormulas.Partition.toYoungDiagram_rowLen_eq_getD]
          using hrow
      have hsort : (↑(auxiliaryPartitionNatList la) : Multiset ℕ) = la.parts :=
        Multiset.sort_eq _ _
      have hsum : (auxiliaryPartitionNatList la).sum = N := by
        simpa only [Multiset.sum_coe, la.parts_sum] using congrArg Multiset.sum hsort
      have hpos : ∀ x ∈ auxiliaryPartitionNatList la, 0 < x := by
        intro x hx
        apply la.parts_pos
        rw [← hsort]
        exact hx
      have hlist : auxiliaryPartitionNatList la = [N] := by
        cases hl : auxiliaryPartitionNatList la with
        | nil => simp only [hl, List.getD_nil] at hhead; omega
        | cons x xs =>
          have hx : x = N := by simpa only [hl, List.getD_cons_zero] using hhead
          cases xs with
          | nil => simp only [hx] at hl ⊢
          | cons y ys =>
            have hy : 0 < y := hpos y (by simp only [hl, List.mem_cons, true_or, or_true])
            simp only [hl, List.sum_cons] at hsum
            omega
      apply Nat.Partition.ext
      rw [← hsort, hlist, Nat.Partition.indiscrete_parts hN.ne']
      rfl
    · have hz : N = 0 := by omega
      subst N
      exact Subsingleton.elim _ _
  · rintro rfl
    exact indiscrete_rowLen_zero N

/-- The actual zero-tuple intertwiner dimension is one exactly for a single row. -/
theorem tupleMultiplicity_zero_eq_indicator (N : ℕ) (la : Nat.Partition N) :
    tupleMultiplicity N 0 la = if (diagram la).rowLen 0 = N then 1 else 0 := by
  rw [tupleMultiplicity_zero_eq_indiscrete]
  simp only [rowLen_zero_eq_iff_indiscrete]

theorem tupleMultiplicity_zero_of_rowLen_lt (N : ℕ) (la : Nat.Partition N)
    (h : (diagram la).rowLen 0 < N) : tupleMultiplicity N 0 la = 0 := by
  rw [tupleMultiplicity_zero_eq_indicator, if_neg h.ne]

end QuantumOracle.SpechtTrivialMultiplicity
