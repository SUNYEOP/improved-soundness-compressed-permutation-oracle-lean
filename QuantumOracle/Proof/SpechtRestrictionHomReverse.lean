import QuantumOracle.Proof.SpechtRestrictionHom

/-!
# Actual maps from a restricted Specht module to a smaller Specht module

The opposite orientation of the restriction intertwiner space has the same
one-corner dimension. This orientation applies directly to actual restriction
followed by a residual Specht projection.
-/

noncomputable section

namespace QuantumOracle.SpechtRestrictionHomReverse

open SpechtFoundation
open SpechtRestrictionHom (restricted)
open scoped BigOperators Classical

/-- Actual equivariant maps out of the larger restricted Specht representation. -/
abbrev Hom (N : ℕ) (mu : Nat.Partition N) (la : Nat.Partition (N + 1)) :=
  Representation.IntertwiningMap (restricted N la) (representation N mu)

/-- Character averaging in this orientation gives the actual one-corner dimension. -/
theorem finrank_eq_indicator (N : ℕ) (mu : Nat.Partition N)
    (la : Nat.Partition (N + 1)) :
    Module.finrank ℂ (Hom N mu la) = if mu ∈ removeCorners la then 1 else 0 := by
  letI : Invertible (Nat.card (Equiv.Perm (Fin N)) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have havg := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (restricted N la) (representation N mu)
  rw [Nat.card_eq_fintype_card] at havg
  change characterPairing N (character N mu)
    (fun π => character (N + 1) la (includePerm N π)) =
      (Module.finrank ℂ (Hom N mu la) : ℂ) at havg
  rw [branching_multiplicity] at havg
  by_cases hm : mu ∈ removeCorners la
  · have hle := (mem_removeCorners mu la).mp hm
    rw [if_pos hle] at havg
    rw [if_pos hm]
    exact_mod_cast havg.symm
  · have hle : ¬ diagram mu ≤ diagram la := fun h => hm ((mem_removeCorners mu la).mpr h)
    rw [if_neg hle] at havg
    rw [if_neg hm]
    exact_mod_cast havg.symm

theorem finrank_eq_zero_of_not_mem (N : ℕ) (mu : Nat.Partition N)
    (la : Nat.Partition (N + 1)) (hm : mu ∉ removeCorners la) :
    Module.finrank ℂ (Hom N mu la) = 0 := by
  rw [finrank_eq_indicator, if_neg hm]

/-- Every actual map to an off-corner residual Specht module is zero. -/
theorem hom_eq_zero_of_not_mem (N : ℕ) (mu : Nat.Partition N)
    (la : Nat.Partition (N + 1)) (hm : mu ∉ removeCorners la) (f : Hom N mu la) :
    f = 0 := by
  letI : Subsingleton (Hom N mu la) :=
    (Module.finrank_zero_iff (R := ℂ)).mp (finrank_eq_zero_of_not_mem N mu la hm)
  exact Subsingleton.elim _ _

theorem mem_removeCorners_of_ne_zero {N : ℕ} {mu : Nat.Partition N}
    {la : Nat.Partition (N + 1)} {f : Hom N mu la} (hf : f ≠ 0) :
    mu ∈ removeCorners la := by
  by_contra hm
  exact hf (hom_eq_zero_of_not_mem N mu la hm f)

theorem exists_ne_zero_iff_mem (N : ℕ) (mu : Nat.Partition N)
    (la : Nat.Partition (N + 1)) :
    (∃ f : Hom N mu la, f ≠ 0) ↔ mu ∈ removeCorners la := by
  constructor
  · rintro ⟨f, hf⟩
    exact mem_removeCorners_of_ne_zero hf
  · intro hm
    apply (Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := Hom N mu la)).mp
    rw [finrank_eq_indicator, if_pos hm]
    exact Nat.zero_lt_one

end QuantumOracle.SpechtRestrictionHomReverse
