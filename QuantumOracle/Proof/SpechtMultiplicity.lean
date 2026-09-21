import QuantumOracle.Proof.SpechtCharacter
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.RepresentationTheory.Character

/-!
# Actual tuple multiplicities in the extension Gram spectrum

The permutation representation on ordered tuples of distinct points is
constructed on functions on `Fin t ↪ Fin N`. Its trace counts fixed tuples.
The multiplicity below is the actual dimension of an intertwiner space into
the constructed Specht representation, not a scalar prescribed from Gram.

`SpechtBranchingPaths` proves the branching recurrence for this dimension;
`SpechtMinimalMultiplicity` computes its tableau count at the first degree.
-/

noncomputable section

namespace QuantumOracle.SpechtMultiplicity

open PermutationExtensions SpechtFoundation
open scoped BigOperators Classical

/-- Ordered tuples of distinct points, including the empty tuple. -/
abbrev Tuple (N t : ℕ) := Fin t ↪ Fin N

/-- Relabel every entry of an actual tuple. -/
def tuplePerm (N t : ℕ) (π : Perm N) : Equiv.Perm (Tuple N t) :=
  Equiv.embeddingCongr (Equiv.refl _) π

@[simp] theorem tuplePerm_apply (N t : ℕ) (π : Perm N) (e : Tuple N t) (i : Fin t) :
    tuplePerm N t π e i = π (e i) := rfl

/-- The actual permutation action on tuple-coordinate functions. -/
def tupleRepresentation (N t : ℕ) : Representation ℂ (Perm N) (Tuple N t → ℂ) where
  toFun π := LinearMap.funLeft ℂ ℂ (tuplePerm N t π⁻¹)
  map_one' := by
    apply LinearMap.ext
    intro f
    funext e
    change f (tuplePerm N t 1 e) = f e
    congr 1
  map_mul' π σ := by
    apply LinearMap.ext
    intro f
    funext e
    change f (tuplePerm N t (π * σ)⁻¹ e) =
      f (tuplePerm N t σ⁻¹ (tuplePerm N t π⁻¹ e))
    congr 1

@[simp] theorem tupleRepresentation_apply (N t : ℕ) (π : Perm N)
    (f : Tuple N t → ℂ) (e : Tuple N t) :
    tupleRepresentation N t π f e = f (tuplePerm N t π⁻¹ e) := rfl

/-- A fixed tuple is exactly an injection into the actual fixed-point set. -/
def fixedTupleEquiv (N t : ℕ) (π : Perm N) :
    {e : Tuple N t // tuplePerm N t π e = e} ≃
      (Fin t ↪ {x : Fin N // π x = x}) where
  toFun e :=
    { toFun := fun i => ⟨e.val i, congrArg (fun f : Tuple N t => f i) e.property⟩
      inj' := fun i j h => e.val.injective (congrArg Subtype.val h) }
  invFun f := ⟨f.trans (Function.Embedding.subtype _), by
    apply Function.Embedding.ext
    intro i
    exact (f i).property⟩
  left_inv e := by
    apply Subtype.ext
    ext i
    rfl
  right_inv f := by
    ext i
    rfl

theorem card_fixedTuples (N t : ℕ) (π : Perm N) :
    Fintype.card {e : Tuple N t // tuplePerm N t π e = e} =
      (Fintype.card {x : Fin N // π x = x}).descFactorial t := by
  rw [Fintype.card_congr (fixedTupleEquiv N t π), Fintype.card_embedding_eq,
    Fintype.card_fin]

theorem card_fixedPoints_symm (N : ℕ) (π : Perm N) :
    Fintype.card {x : Fin N // π.symm x = x} =
      Fintype.card {x : Fin N // π x = x} := by
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun x => by
    rw [Equiv.symm_apply_eq]
    exact eq_comm)

/-- The trace of the tuple action counts its fixed injections. -/
theorem tuple_character (N t : ℕ) (π : Perm N) :
    (tupleRepresentation N t).character π =
      ((Fintype.card {x : Fin N // π x = x}).descFactorial t : ℂ) := by
  have htrace : (tupleRepresentation N t).character π =
      (Fintype.card {e : Tuple N t // tuplePerm N t π⁻¹ e = e} : ℂ) := by
    rw [Representation.character,
      LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Tuple N t))]
    simp [Matrix.trace, Pi.single_apply, Fintype.card_subtype, eq_comm]
  rw [htrace, card_fixedTuples]
  change ((Fintype.card {x : Fin N // π.symm x = x}).descFactorial t : ℂ) = _
  rw [card_fixedPoints_symm]

/-- The actual dimension of equivariant maps from the tuple permutation
representation into the actual Specht module. -/
def tupleMultiplicity (N t : ℕ) (la : Nat.Partition N) : ℕ :=
  Module.finrank ℂ
    (Representation.IntertwiningMap (tupleRepresentation N t) (representation N la))

/-- Character orthogonality computes the actual intertwiner dimension. -/
theorem tupleMultiplicity_eq_character_average (N t : ℕ) (la : Nat.Partition N) :
    (tupleMultiplicity N t la : ℂ) =
      (N.factorial : ℂ)⁻¹ * ∑ π : Perm N,
        character N la π * (tupleRepresentation N t).character π⁻¹ := by
  letI : Invertible (Nat.card (Perm N) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  have hm := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (tupleRepresentation N t) (representation N la)
  simpa only [tupleMultiplicity, Representation.character, representation_apply,
    ← character_eq_trace, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin] using hm.symm

/-- The fixed-tuple character average is an actual natural-number dimension. -/
theorem tupleMultiplicity_eq_fixedPoint_average (N t : ℕ) (la : Nat.Partition N) :
    (tupleMultiplicity N t la : ℂ) =
      (N.factorial : ℂ)⁻¹ * ∑ π : Perm N,
        ((Fintype.card {x : Fin N // π.symm x = x}).descFactorial t : ℂ) *
          character N la π := by
  rw [tupleMultiplicity_eq_character_average]
  simp_rw [tuple_character, mul_comm (character N la _)]
  rfl

/-- The counted Gram kernel is the correctly normalized actual tuple character. -/
theorem kernel_coeff_eq_tuple_character (N t : ℕ) (ht : t ≤ N) (π : Perm N) :
    (GramConvolution.kernel N t).coeff π =
      (N.choose t : ℂ) / (N.factorial : ℂ) *
        (tupleRepresentation N t).character π⁻¹ := by
  rw [GramConvolution.kernel_coeff, tuple_character,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hN : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  have hR : ((N - t).factorial : ℂ) ≠ 0 := by exact_mod_cast (N - t).factorial_ne_zero
  have hfactor : (N.choose t : ℂ) * (t.factorial : ℂ) *
      ((N - t).factorial : ℂ) = (N.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial ht
  change _ = _ * ((t.factorial : ℂ) *
    (Nat.choose (Fintype.card {x : Fin N // π.symm x = x}) t : ℂ))
  field_simp
  rw [← hfactor]
  ring

/-- The actual Gram eigenvalue is a binomial coefficient times the actual
tuple-intertwiner multiplicity divided by the actual Specht dimension. -/
theorem eigenvalue_eq_choose_mul_multiplicity (N t : ℕ) (ht : t ≤ N)
    (la : Nat.Partition N) :
    SpechtCharacter.eigenvalue N t la =
      (N.choose t : ℂ) * (tupleMultiplicity N t la : ℂ) /
        (Module.finrank ℂ (specht N la) : ℂ) := by
  rw [SpechtCharacter.eigenvalue, tupleMultiplicity_eq_character_average]
  congr 1
  simp_rw [kernel_coeff_eq_tuple_character N t ht]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  ring

theorem gram_eq_choose_mul_multiplicity (N t : ℕ) (ht : t ≤ N)
    (la : Nat.Partition N) {h : EuclideanSpace ℂ (Perm N)}
    (hh : h ∈ SpechtGram.space N la) :
    GramFiltration.gram N t h =
      ((N.choose t : ℂ) * (tupleMultiplicity N t la : ℂ) /
        (Module.finrank ℂ (specht N la) : ℂ)) • h := by
  rw [SpechtCharacter.gram_eq_eigenvalue N t la hh,
    eigenvalue_eq_choose_mul_multiplicity N t ht la]

end QuantumOracle.SpechtMultiplicity
