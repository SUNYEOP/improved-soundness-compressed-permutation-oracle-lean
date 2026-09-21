import QuantumOracle.Proof.SpechtGram

/-!
# The actual Gram eigenvalue as a finite character sum

The scalar is computed from the trace of the actual restricted convolution.
The character is the trace of the actual Specht permutation action.
`SpechtMinimalMultiplicity` evaluates the sum at the first harmonic degree.
-/

noncomputable section

namespace QuantumOracle.SpechtCharacter

open PermutationExtensions GramConvolution SpechtFoundation SpechtGram
open scoped BigOperators

theorem kernel_eq_sum (N t : ℕ) :
    kernel N t = ∑ π : Perm N, (kernel N t).coeff π • MonoidAlgebra.of ℂ (Perm N) π := by
  simpa only [kernel, equiv_coeff] using
    (sum_coeff_basis N (GramFiltration.gram N t (EuclideanSpace.single (Equiv.refl _) 1))).symm

theorem algebraGram_eq_sum_action (N t : ℕ) (la : Nat.Partition N) :
    (algebraGram N t la).restrictScalars ℂ =
      ∑ π : Perm N, (kernel N t).coeff π • action N la π := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  simp only [LinearMap.restrictScalars_apply, algebraGram_apply_val,
    LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    action_apply_val]
  conv_lhs => rw [kernel_eq_sum]
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc]

theorem trace_algebraGram (N t : ℕ) (la : Nat.Partition N) :
    LinearMap.trace ℂ (specht N la) ((algebraGram N t la).restrictScalars ℂ) =
      ∑ π : Perm N, (kernel N t).coeff π * character N la π := by
  rw [algebraGram_eq_sum_action, map_sum]
  simp only [map_smul, smul_eq_mul, ← character_eq_trace]

theorem dimension_ne_zero (N : ℕ) (la : Nat.Partition N) :
    Module.finrank ℂ (specht N la) ≠ 0 := by
  intro hz
  have hd := dimension_mul_hookProduct N la
  rw [hz, zero_mul] at hd
  exact Nat.factorial_ne_zero N hd.symm

/-- An explicit finite sum of actual kernel coefficients and actual trace characters. -/
def eigenvalue (N t : ℕ) (la : Nat.Partition N) : ℂ :=
  (∑ π : Perm N, (kernel N t).coeff π * character N la π) /
    (Module.finrank ℂ (specht N la) : ℂ)

theorem scalar_eq_eigenvalue (N t : ℕ) (la : Nat.Partition N) (c : ℂ)
    (hc : ∀ v : specht N la, algebraGram N t la v = c • v) :
    c = eigenvalue N t la := by
  have he : (algebraGram N t la).restrictScalars ℂ = c • LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact hc v
  have ht := congrArg (LinearMap.trace ℂ (specht N la)) he
  rw [trace_algebraGram, map_smul, LinearMap.trace_id, smul_eq_mul] at ht
  have hd : (Module.finrank ℂ (specht N la) : ℂ) ≠ 0 := by
    exact_mod_cast dimension_ne_zero N la
  exact (eq_div_iff hd).mpr ht.symm

/-- The original Gram operator acts by the explicit character sum; no eigenvector
or scalar-action hypothesis is supplied by the caller. -/
theorem gram_eq_eigenvalue (N t : ℕ) (la : Nat.Partition N)
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N la) :
    GramFiltration.gram N t h = eigenvalue N t la • h := by
  obtain ⟨c, hc⟩ := algebraGram_scalar N t la
  have he : GramFiltration.gram N t h = c • h := by
    apply (equiv N).injective
    rw [equiv_gram_left, map_smul]
    exact congrArg Subtype.val (hc ⟨equiv N h, hh⟩)
  rw [scalar_eq_eigenvalue N t la c hc] at he
  exact he

theorem eigenvalue_eq_fixedPoint_character_sum (N t : ℕ) (la : Nat.Partition N) :
    eigenvalue N t la =
      (∑ π : Perm N,
        (((Nat.choose (Fintype.card {x : Fin N // π.symm x = x}) t : ℕ) : ℂ) /
          ((N - t).factorial : ℂ)) * character N la π) /
        (Module.finrank ℂ (specht N la) : ℂ) := by
  simp only [eigenvalue, kernel_coeff]

end QuantumOracle.SpechtCharacter
