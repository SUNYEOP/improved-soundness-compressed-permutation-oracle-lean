import QuantumOracle.Model.Database
import Mathlib.Data.Fintype.Perm

/-! Actual permutations extending an injective database. No extension-count or
representation-theoretic assertion is assumed in these definitions. -/

noncomputable section

namespace QuantumOracle.PermutationExtensions

abbrev Perm (N : ℕ) := Equiv.Perm (Fin N)

variable {N : ℕ}

/-- A genuine permutation agrees with every recorded edge of the database. -/
def Extends (I : Database N) (π : Perm N) : Prop :=
  ∀ x y, (x, y) ∈ I.edges → π x = y

abbrev Extensions (I : Database N) := {π : Perm N // Extends I π}

noncomputable instance extensionsFintype (I : Database N) : Fintype (Extensions I) :=
  Fintype.ofFinite _

@[simp] theorem extends_empty (π : Perm N) : Extends Database.empty π := by
  intro x y h
  simp at h

theorem extends_iff_edges_subset (I : Database N) (π : Perm N) :
    Extends I π ↔ I.edges ⊆ (Database.ofPermutation π).edges := by
  constructor
  · intro h e he
    exact (Database.mem_ofPermutation π e.1 e.2).mpr (h e.1 e.2 he)
  · intro h x y hxy
    exact (Database.mem_ofPermutation π x y).mp (h hxy)

theorem extends_erase {I : Database N} {π : Perm N} (h : Extends I π) (x : Fin N) :
    Extends (I.erase x) π := by
  intro a b hab
  exact h a b ((Database.mem_erase I x a b).mp hab).1

theorem extends_set_iff_of_fresh (I : Database N) (x y : Fin N)
    (hx : x ∉ I.domain) (hy : y ∉ I.image) (π : Perm N) :
    Extends (I.set x y) π ↔ Extends I π ∧ π x = y := by
  unfold Extends
  rw [Database.set_edges_of_fresh I x y hx hy]
  constructor
  · intro h
    exact ⟨fun a b hab => h a b (Finset.mem_insert_of_mem hab),
      h x y (Finset.mem_insert_self _ _)⟩
  · rintro ⟨h, hxy⟩ a b hab
    rcases Finset.mem_insert.mp hab with heq | hold
    · cases Prod.mk.inj heq with
      | intro ha hb => simpa only [ha, hb] using hxy
    · exact h a b hold

/-- Forward and inverse constraints describe the same actual permutation edges. -/
theorem extends_inverse_iff (I : Database N) (π : Perm N) :
    Extends I.inverse π.symm ↔ Extends I π := by
  constructor
  · intro h x y hxy
    have h' := h y x ((Database.mem_inverse I y x).mpr hxy)
    exact (π.symm_apply_eq.mp h').symm
  · intro h x y hxy
    have h' := h y x ((Database.mem_inverse I x y).mp hxy)
    exact π.symm_apply_eq.mpr h'.symm

end QuantumOracle.PermutationExtensions
