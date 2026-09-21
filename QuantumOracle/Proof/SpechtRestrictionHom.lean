import QuantumOracle.Proof.SpechtFoundation
import Mathlib.RepresentationTheory.Character

/-!
# Actual one-corner restriction intertwiner spaces

Character averaging computes the dimension of maps from the actual smaller
Specht module into the actual larger Specht module restricted along the
last-point stabilizer. Off the corner relation every such map is zero.
-/

noncomputable section

namespace QuantumOracle.SpechtRestrictionHom

open SpechtFoundation
open scoped BigOperators Classical

/-- The actual larger Specht representation restricted to the last-point stabilizer. -/
abbrev restricted (N : ℕ) (la : Nat.Partition (N + 1)) :
    Representation ℂ (Equiv.Perm (Fin N)) (specht (N + 1) la) :=
  (representation (N + 1) la).comp (includePerm N)

/-- Actual equivariant linear maps into that restricted Specht representation. -/
abbrev Hom (N : ℕ) (mu : Nat.Partition N) (la : Nat.Partition (N + 1)) :=
  Representation.IntertwiningMap (representation N mu) (restricted N la)

/-- The actual intertwiner dimension is exactly the one-corner indicator. -/
theorem finrank_eq_indicator (N : ℕ) (mu : Nat.Partition N)
    (la : Nat.Partition (N + 1)) :
    Module.finrank ℂ (Hom N mu la) = if mu ∈ removeCorners la then 1 else 0 := by
  letI : Invertible (Nat.card (Equiv.Perm (Fin N)) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have havg := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (representation N mu) (restricted N la)
  change (Nat.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ *
      (∑ π : Equiv.Perm (Fin N), character (N + 1) la (includePerm N π) *
        character N mu π⁻¹) = (Module.finrank ℂ (Hom N mu la) : ℂ) at havg
  have hsum : (∑ π : Equiv.Perm (Fin N), character (N + 1) la (includePerm N π) *
        character N mu π⁻¹) =
      ∑ π : Equiv.Perm (Fin N), character N mu π *
        character (N + 1) la (includePerm N π⁻¹) := by
    have h := Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin N)))
      (fun π => character (N + 1) la (includePerm N π) * character N mu π⁻¹)
    simpa only [Equiv.inv_apply, inv_inv, mul_comm] using h.symm
  rw [hsum, Nat.card_eq_fintype_card] at havg
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

/-- There is no nonzero actual intertwiner outside the one-corner relation. -/
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

/-- Actual nonzero maps exist precisely for removal of one actual corner. -/
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

end QuantumOracle.SpechtRestrictionHom
