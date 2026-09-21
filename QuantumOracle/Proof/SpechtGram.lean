import QuantumOracle.Proof.GramConvolution
import QuantumOracle.Proof.SpechtFoundation

/-!
# Actual Gram invariance and scalar action on constructed Specht ideals

The concrete Specht left ideal is transported coefficientwise to the actual
permutation register. The actual extension Gram operator preserves it because
its group-algebra convolution element is central. Schur's lemma then proves
existence of a scalar for this actual restricted operator. This does not compute
the scalar, identify a harmonic degree, or assert the manuscript eigenvalue.
-/

noncomputable section

namespace QuantumOracle.SpechtGram

open PermutationExtensions GramConvolution

/-- The constructed Specht ideal, with its actual coefficients in the permutation register. -/
def space (N : ℕ) (la : Nat.Partition N) :
    Submodule ℂ (EuclideanSpace ℂ (Perm N)) :=
  ((SpechtFoundation.specht N la).restrictScalars ℂ).comap (equiv N).toLinearMap

@[simp] theorem mem_space (N : ℕ) (la : Nat.Partition N)
    (h : EuclideanSpace ℂ (Perm N)) :
    h ∈ space N la ↔ equiv N h ∈ SpechtFoundation.specht N la := Iff.rfl

/-- The actual Gram operator preserves this actual transported Specht ideal. -/
theorem gram_mem (N t : ℕ) (la : Nat.Partition N)
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N la) :
    GramFiltration.gram N t h ∈ space N la :=
  gram_mem_leftIdeal N t (SpechtFoundation.specht N la) hh

/-- The actual restriction of `T T†` to this permutation-register subspace. -/
def restrictedGram (N t : ℕ) (la : Nat.Partition N) :
    space N la →ₗ[ℂ] space N la :=
  (GramFiltration.gram N t).restrict (fun _ hh => gram_mem N t la hh)

@[simp] theorem restrictedGram_apply_val (N t : ℕ) (la : Nat.Partition N)
    (v : space N la) :
    (restrictedGram N t la v).val = GramFiltration.gram N t v.val := rfl

/-- Multiplication by the actual central Gram element is linear over the whole
group algebra, not only over the scalar field. -/
def algebraGram (N t : ℕ) (la : Nat.Partition N) :
    Module.End (GroupAlgebra N) (SpechtFoundation.specht N la) := by
  let L : GroupAlgebra N →ₗ[GroupAlgebra N] GroupAlgebra N :=
    { toFun := fun a => kernel N t * a
      map_add' := fun a b => mul_add _ _ _
      map_smul' := fun a b => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← mul_assoc, kernel_commutes, mul_assoc] }
  exact L.restrict (fun _ hv => (SpechtFoundation.specht N la).smul_mem (kernel N t) hv)

@[simp] theorem algebraGram_apply_val (N t : ℕ) (la : Nat.Partition N)
    (v : SpechtFoundation.specht N la) :
    (algebraGram N t la v).val = kernel N t * v.val := rfl

/-- Schur scalarity for the actual central-convolution restriction, with no
supplied scalar-action or eigenvector premise. -/
theorem algebraGram_scalar (N t : ℕ) (la : Nat.Partition N) :
    ∃ c : ℂ, ∀ v : SpechtFoundation.specht N la, algebraGram N t la v = c • v := by
  letI := SpechtFoundation.specht_simple N la
  obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
    (k := ℂ) (A := GroupAlgebra N) (V := SpechtFoundation.specht N la)).surjective
      (algebraGram N t la)
  refine ⟨c, fun v => ?_⟩
  rw [← hc]
  simp

/-- The original `T T†` acts by one scalar on every vector of the constructed
Specht subspace. The scalar's numerical value is deliberately not asserted. -/
theorem gram_scalar (N t : ℕ) (la : Nat.Partition N) :
    ∃ c : ℂ, ∀ h ∈ space N la, GramFiltration.gram N t h = c • h := by
  obtain ⟨c, hc⟩ := algebraGram_scalar N t la
  refine ⟨c, fun h hh => ?_⟩
  apply (equiv N).injective
  rw [equiv_gram_left, map_smul]
  exact congrArg Subtype.val (hc ⟨equiv N h, hh⟩)

theorem restrictedGram_scalar (N t : ℕ) (la : Nat.Partition N) :
    ∃ c : ℂ, ∀ v : space N la, restrictedGram N t la v = c • v := by
  obtain ⟨c, hc⟩ := gram_scalar N t la
  refine ⟨c, fun v => ?_⟩
  apply Subtype.ext
  exact hc v.val v.property

end QuantumOracle.SpechtGram
