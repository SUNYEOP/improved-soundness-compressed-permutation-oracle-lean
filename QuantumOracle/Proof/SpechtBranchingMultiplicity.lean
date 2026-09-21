import QuantumOracle.Proof.SpechtMultiplicity
import Mathlib.Logic.Equiv.Fintype

/-!
# Actual tuple multiplicities and pointwise stabilizer invariants

Evaluation at an actual tuple basis vector identifies the intertwiner space
with the actual Specht vectors fixed by that tuple's pointwise stabilizer.
The inverse is constructed by transporting a fixed vector along permutations
that send the base tuple to each tuple. No desired dimension is prescribed.
-/

noncomputable section

namespace QuantumOracle.SpechtBranchingMultiplicity

open PermutationExtensions SpechtFoundation SpechtMultiplicity
open scoped BigOperators Classical

/-- Permutations fixing each entry of the chosen ordered tuple. -/
def pointwiseStabilizer {N t : ℕ} (e₀ : Tuple N t) : Subgroup (Perm N) where
  carrier := {π | ∀ i, π (e₀ i) = e₀ i}
  one_mem' := fun _ => rfl
  mul_mem' := fun hπ hσ i => by simp only [Equiv.Perm.mul_apply, hσ i, hπ i]
  inv_mem' := fun {π} hπ i => by
    change π.symm (e₀ i) = e₀ i
    rw [Equiv.symm_apply_eq]
    exact (hπ i).symm

@[simp] theorem mem_pointwiseStabilizer {N t : ℕ} (e₀ : Tuple N t) (π : Perm N) :
    π ∈ pointwiseStabilizer e₀ ↔ ∀ i, π (e₀ i) = e₀ i := Iff.rfl

/-- The actual fixed subspace of the restricted Specht representation. -/
def stabilizerInvariants {N t : ℕ} (la : Nat.Partition N) (e₀ : Tuple N t) :
    Submodule ℂ (specht N la) :=
  Representation.invariants ((representation N la).comp (pointwiseStabilizer e₀).subtype)

@[simp] theorem mem_stabilizerInvariants {N t : ℕ} (la : Nat.Partition N)
    (e₀ : Tuple N t) (v : specht N la) :
    v ∈ stabilizerInvariants la e₀ ↔
      ∀ π : pointwiseStabilizer e₀, representation N la π.val v = v := Iff.rfl

def tupleBasis {N t : ℕ} (e : Tuple N t) : Tuple N t → ℂ := Pi.single e 1

theorem tupleRepresentation_single (N t : ℕ) (π : Perm N) (e : Tuple N t) :
    tupleRepresentation N t π (tupleBasis e) = tupleBasis (tuplePerm N t π e) := by
  funext f
  rw [tupleRepresentation_apply]
  change tupleBasis e ((tuplePerm N t π).symm f) = tupleBasis (tuplePerm N t π e) f
  simp only [tupleBasis, Pi.single_apply, Equiv.symm_apply_eq]

theorem exists_moveTuple {N t : ℕ} (e₀ e : Tuple N t) :
    ∃ π : Perm N, ∀ i, π (e₀ i) = e i :=
  Equiv.Perm.exists_extending_pair e₀ e e₀.injective e.injective

private def moveTuple {N t : ℕ} (e₀ e : Tuple N t) : Perm N :=
  (exists_moveTuple e₀ e).choose

private theorem moveTuple_apply {N t : ℕ} (e₀ e : Tuple N t) (i : Fin t) :
    moveTuple e₀ e (e₀ i) = e i :=
  (exists_moveTuple e₀ e).choose_spec i

private def transport {N t : ℕ} (la : Nat.Partition N) (e₀ : Tuple N t)
    (v : stabilizerInvariants la e₀) (e : Tuple N t) : specht N la :=
  representation N la (moveTuple e₀ e) v.val

private theorem transport_eq {N t : ℕ} (la : Nat.Partition N) (e₀ : Tuple N t)
    (v : stabilizerInvariants la e₀) (e : Tuple N t) (π : Perm N)
    (hπ : ∀ i, π (e₀ i) = e i) :
    transport la e₀ v e = representation N la π v.val := by
  have hfix : (moveTuple e₀ e)⁻¹ * π ∈ pointwiseStabilizer e₀ := by
    intro i
    change (moveTuple e₀ e).symm (π (e₀ i)) = e₀ i
    rw [hπ i, Equiv.symm_apply_eq, moveTuple_apply]
  have hv := v.property ⟨(moveTuple e₀ e)⁻¹ * π, hfix⟩
  change representation N la ((moveTuple e₀ e)⁻¹ * π) v.val = v.val at hv
  symm
  calc
    representation N la π v.val = representation N la (moveTuple e₀ e)
        (representation N la ((moveTuple e₀ e)⁻¹ * π) v.val) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = transport la e₀ v e := by rw [hv]; rfl

private theorem transport_base {N t : ℕ} (la : Nat.Partition N) (e₀ : Tuple N t)
    (v : stabilizerInvariants la e₀) : transport la e₀ v e₀ = v.val := by
  rw [transport_eq la e₀ v e₀ 1 (fun _ => rfl), map_one]
  rfl

private theorem transport_equivariant {N t : ℕ} (la : Nat.Partition N)
    (e₀ : Tuple N t) (v : stabilizerInvariants la e₀) (π : Perm N) (e : Tuple N t) :
    transport la e₀ v (tuplePerm N t π e) = representation N la π (transport la e₀ v e) := by
  rw [transport_eq la e₀ v (tuplePerm N t π e) (π * moveTuple e₀ e) (fun i => by
    simp only [Equiv.Perm.mul_apply, moveTuple_apply, tuplePerm_apply]), map_mul]
  rfl

/-- Evaluate an actual equivariant map at the chosen tuple basis vector. -/
def evaluation {N t : ℕ} (la : Nat.Partition N) (e₀ : Tuple N t) :
    Representation.IntertwiningMap (tupleRepresentation N t) (representation N la) →ₗ[ℂ]
      stabilizerInvariants la e₀ where
  toFun f := ⟨f (tupleBasis e₀), fun π => by
    have hs : tuplePerm N t π.val e₀ = e₀ := by
      apply Function.Embedding.ext
      exact π.property
    have hf := Representation.IntertwiningMap.isIntertwining _ _ f π.val (tupleBasis e₀)
    rw [tupleRepresentation_single, hs] at hf
    exact hf.symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluation_injective {N t : ℕ} (la : Nat.Partition N) (e₀ : Tuple N t) :
    Function.Injective (evaluation la e₀) := by
  intro f g h
  have hb : f (tupleBasis e₀) = g (tupleBasis e₀) := congrArg Subtype.val h
  apply Representation.IntertwiningMap.ext
  apply (Pi.basisFun ℂ (Tuple N t)).ext
  intro e
  simp only [Pi.basisFun_apply]
  change f (tupleBasis e) = g (tupleBasis e)
  obtain ⟨π, hπ⟩ := exists_moveTuple e₀ e
  have he : tuplePerm N t π e₀ = e := by
    apply Function.Embedding.ext
    exact hπ
  rw [← he, ← tupleRepresentation_single,
    Representation.IntertwiningMap.isIntertwining _ _ f,
    Representation.IntertwiningMap.isIntertwining _ _ g, hb]

private def liftFixedVector {N t : ℕ} (la : Nat.Partition N) (e₀ : Tuple N t)
    (v : stabilizerInvariants la e₀) :
    Representation.IntertwiningMap (tupleRepresentation N t) (representation N la) where
  toFun f := ∑ e, f e • transport la e₀ v e
  map_add' f g := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  isIntertwining' π := by
    apply LinearMap.ext
    intro f
    change (∑ e, f (tuplePerm N t π⁻¹ e) • transport la e₀ v e) =
      representation N la π (∑ e, f e • transport la e₀ v e)
    calc
      (∑ e, f (tuplePerm N t π⁻¹ e) • transport la e₀ v e) =
          ∑ e, f e • transport la e₀ v (tuplePerm N t π e) := by
        simpa only [show tuplePerm N t π⁻¹ = (tuplePerm N t π).symm from rfl,
          Equiv.symm_apply_apply] using
          (Equiv.sum_comp (tuplePerm N t π)
            (fun e => f (tuplePerm N t π⁻¹ e) • transport la e₀ v e)).symm
      _ = _ := by simp only [transport_equivariant, map_sum, map_smul]

theorem evaluation_surjective {N t : ℕ} (la : Nat.Partition N) (e₀ : Tuple N t) :
    Function.Surjective (evaluation la e₀) := by
  intro v
  refine ⟨liftFixedVector la e₀ v, ?_⟩
  apply Subtype.ext
  change (∑ e, tupleBasis e₀ e • transport la e₀ v e) = v.val
  simp [tupleBasis, Pi.single_apply, transport_base]

/-- Concrete Frobenius reciprocity for the actual tuple permutation representation. -/
def evaluationEquiv {N t : ℕ} (la : Nat.Partition N) (e₀ : Tuple N t) :
    Representation.IntertwiningMap (tupleRepresentation N t) (representation N la) ≃ₗ[ℂ]
      stabilizerInvariants la e₀ :=
  LinearEquiv.ofBijective (evaluation la e₀)
    ⟨evaluation_injective la e₀, evaluation_surjective la e₀⟩

theorem tupleMultiplicity_eq_stabilizer_finrank (N t : ℕ) (la : Nat.Partition N)
    (e₀ : Tuple N t) :
    tupleMultiplicity N t la = Module.finrank ℂ (stabilizerInvariants la e₀) :=
  (evaluationEquiv la e₀).finrank_eq

/-- The first `t` points give a canonical pointwise-stabilizer expression. -/
theorem tupleMultiplicity_eq_initialStabilizer_finrank (N t : ℕ) (ht : t ≤ N)
    (la : Nat.Partition N) :
    tupleMultiplicity N t la =
      Module.finrank ℂ (stabilizerInvariants la (Fin.castLEEmb ht)) :=
  tupleMultiplicity_eq_stabilizer_finrank N t la (Fin.castLEEmb ht)

/-- The actual multiplicity is the normalized character sum over the actual
pointwise stabilizer, by the invariant-space averaging projection. -/
theorem tupleMultiplicity_eq_stabilizer_average (N t : ℕ) (la : Nat.Partition N)
    (e₀ : Tuple N t) :
    (tupleMultiplicity N t la : ℂ) =
      (Nat.card (pointwiseStabilizer e₀) : ℂ)⁻¹ *
        ∑ π : pointwiseStabilizer e₀, character N la π.val := by
  letI : Invertible (Nat.card (pointwiseStabilizer e₀) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  rw [tupleMultiplicity_eq_stabilizer_finrank N t la e₀]
  exact (Representation.card_inv_mul_sum_char_eq_finrank
    ((representation N la).comp (pointwiseStabilizer e₀).subtype)).symm

/-- Weighted fixed-point character averaging equals actual stabilizer averaging. -/
theorem fixedPoint_average_eq_stabilizer_average (N t : ℕ) (la : Nat.Partition N)
    (e₀ : Tuple N t) :
    (N.factorial : ℂ)⁻¹ * ∑ π : Perm N,
        ((Fintype.card {x : Fin N // π.symm x = x}).descFactorial t : ℂ) *
          character N la π =
      (Nat.card (pointwiseStabilizer e₀) : ℂ)⁻¹ *
        ∑ π : pointwiseStabilizer e₀, character N la π.val := by
  rw [← tupleMultiplicity_eq_fixedPoint_average,
    tupleMultiplicity_eq_stabilizer_average N t la e₀]

/-- At degree zero the actual multiplicity is the dimension of the full
permutation-invariant part of the actual Specht module. -/
theorem tupleMultiplicity_zero (N : ℕ) (la : Nat.Partition N) :
    tupleMultiplicity N 0 la =
      Module.finrank ℂ (Representation.invariants (representation N la)) := by
  letI : Invertible (Nat.card (Perm N) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  have h := Representation.card_inv_mul_sum_char_eq_finrank (representation N la)
  have hm := tupleMultiplicity_eq_character_average N 0 la
  simp only [tuple_character, Nat.descFactorial_zero, Nat.cast_one, mul_one] at hm
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h
  have he : (tupleMultiplicity N 0 la : ℂ) =
      (Module.finrank ℂ (Representation.invariants (representation N la)) : ℂ) :=
    hm.trans h
  exact_mod_cast he

end QuantumOracle.SpechtBranchingMultiplicity
