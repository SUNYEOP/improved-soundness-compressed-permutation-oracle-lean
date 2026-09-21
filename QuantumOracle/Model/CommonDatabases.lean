import QuantumOracle.Model.PermutationExtensions
import Mathlib.Data.Finset.Powerset

/-!
# Common consistent databases

The combinatorial count in Appendix A, `eq:central-kernel`: size-`t`
partial injections simultaneously consistent with two actual permutations
are in bijection with `t`-element subsets of their agreeing input points.
This proves the count for every `N` and `t`, including empty and oversized
levels; no representation-theoretic spectrum is asserted here.
-/

namespace QuantumOracle.CommonDatabases

open PermutationExtensions

variable {N : ℕ}

/-- The graph of an actual permutation restricted to an input subset. -/
def restrict (π : Perm N) (S : Finset (Fin N)) : Database N where
  edges := S.image (fun x => (x, π x))
  functional := by
    intro e f he hf h
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hf
    exact congrArg π h
  injective := by
    intro e f he hf h
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hf
    exact π.injective h

@[simp] theorem mem_restrict (π : Perm N) (S : Finset (Fin N)) (x y : Fin N) :
    (x, y) ∈ (restrict π S).edges ↔ x ∈ S ∧ π x = y := by
  simp [restrict, Finset.mem_image, Prod.ext_iff]

@[simp] theorem domain_restrict (π : Perm N) (S : Finset (Fin N)) :
    (restrict π S).domain = S := by
  ext x
  simp [Database.mem_domain]

@[simp] theorem size_restrict (π : Perm N) (S : Finset (Fin N)) :
    (restrict π S).size = S.card := by
  simp [Database.size]

theorem extends_restrict (π : Perm N) (S : Finset (Fin N)) :
    Extends (restrict π S) π := by
  intro x y h
  exact (mem_restrict π S x y).mp h |>.2

/-- A consistent database is uniquely recovered from its input domain. -/
theorem restrict_domain (I : Database N) (π : Perm N) (h : Extends I π) :
    restrict π I.domain = I := by
  ext ⟨x, y⟩
  rw [mem_restrict]
  constructor
  · rintro ⟨hx, hxy⟩
    obtain ⟨z, hz⟩ := (Database.mem_domain I x).mp hx
    have hyz : z = y := (h x z hz).symm.trans hxy
    simpa only [hyz] using hz
  · intro hxy
    exact ⟨(Database.mem_domain I x).mpr ⟨y, hxy⟩, h x y hxy⟩

/-- The points at which two permutations have the same output. -/
def agreeingInputs (π σ : Perm N) : Finset (Fin N) :=
  Finset.univ.filter (fun x => π x = σ x)

@[simp] theorem mem_agreeingInputs (π σ : Perm N) (x : Fin N) :
    x ∈ agreeingInputs π σ ↔ π x = σ x := by
  simp [agreeingInputs]

theorem domain_subset_agreeingInputs (I : Database N) (π σ : Perm N)
    (hπ : Extends I π) (hσ : Extends I σ) :
    I.domain ⊆ agreeingInputs π σ := by
  intro x hx
  obtain ⟨y, hy⟩ := (Database.mem_domain I x).mp hx
  exact (mem_agreeingInputs π σ x).mpr ((hπ x y hy).trans (hσ x y hy).symm)

theorem extends_restrict_of_subset (π σ : Perm N) (S : Finset (Fin N))
    (hS : S ⊆ agreeingInputs π σ) : Extends (restrict π S) σ := by
  intro x y hxy
  obtain ⟨hx, hy⟩ := (mem_restrict π S x y).mp hxy
  exact ((mem_agreeingInputs π σ x).mp (hS hx)).symm.trans hy

/-- Actual databases of level `t` consistent with both permutations. -/
def CommonLevel (π σ : Perm N) (t : ℕ) :=
  {I : Database N // I.size = t ∧ Extends I π ∧ Extends I σ}

noncomputable instance (π σ : Perm N) (t : ℕ) : Fintype (CommonLevel π σ t) :=
  by unfold CommonLevel; exact Fintype.ofFinite _

/-- The bijection behind the binomial central kernel. -/
def commonLevelEquiv (π σ : Perm N) (t : ℕ) :
    CommonLevel π σ t ≃ {S // S ∈ (agreeingInputs π σ).powersetCard t} where
  toFun := fun I => ⟨I.1.domain, Finset.mem_powersetCard.mpr
    ⟨domain_subset_agreeingInputs I.1 π σ I.2.2.1 I.2.2.2, I.2.1⟩⟩
  invFun := fun S => ⟨restrict π S.1, ⟨by
    rw [size_restrict]
    exact (Finset.mem_powersetCard.mp S.2).2,
    extends_restrict π S.1,
    extends_restrict_of_subset π σ S.1 (Finset.mem_powersetCard.mp S.2).1⟩⟩
  left_inv := by
    intro I
    apply Subtype.ext
    exact restrict_domain I.1 π I.2.2.1
  right_inv := by
    intro S
    apply Subtype.ext
    exact domain_restrict π S.1

/-- Appendix A's common-database count, valid for all levels. -/
theorem card_commonLevel (π σ : Perm N) (t : ℕ) :
    Fintype.card (CommonLevel π σ t) = Nat.choose (agreeingInputs π σ).card t := by
  rw [Fintype.card_congr (commonLevelEquiv π σ t)]
  rw [Fintype.card_coe, Finset.card_powersetCard]

/-- Reindexing the same common databases as a predicate on the fixed level. -/
def levelCommonEquiv (π σ : Perm N) (t : ℕ) :
    {I : Database.level N t // Extends I.1 π ∧ Extends I.1 σ} ≃
      CommonLevel π σ t where
  toFun := fun I => ⟨I.1.1, I.1.2, I.2⟩
  invFun := fun I => ⟨⟨I.1, I.2.1⟩, I.2.2⟩
  left_inv := by intro I; rfl
  right_inv := by intro I; rfl

/-- A form convenient for the matrix sum defining `T T†`. -/
theorem card_level_common (π σ : Perm N) (t : ℕ)
    [Fintype {I : Database.level N t // Extends I.1 π ∧ Extends I.1 σ}] :
    Fintype.card {I : Database.level N t // Extends I.1 π ∧ Extends I.1 σ} =
      Nat.choose (agreeingInputs π σ).card t := by
  rw [Fintype.card_congr (levelCommonEquiv π σ t), card_commonLevel]

/-- Agreement is the fixed-point condition for `π⁻¹ ∘ σ`.
`Equiv.trans` applies its left argument first. -/
theorem agreeingInputs_eq_fixedPoints (π σ : Perm N) :
    agreeingInputs π σ = Finset.univ.filter (fun x => (σ.trans π.symm) x = x) := by
  ext x
  simp only [mem_agreeingInputs, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.trans_apply]
  exact ⟨fun h => π.symm_apply_eq.mpr h.symm,
    fun h => (π.symm_apply_eq.mp h).symm⟩

theorem card_agreeingInputs_eq_fixedPoints (π σ : Perm N) :
    (agreeingInputs π σ).card = Fintype.card {x : Fin N // (σ.trans π.symm) x = x} := by
  rw [agreeingInputs_eq_fixedPoints, Fintype.card_subtype]

/-- The common count depends only on the fixed points of the relative permutation. -/
theorem card_commonLevel_fixedPoints (π σ : Perm N) (t : ℕ) :
    Fintype.card (CommonLevel π σ t) =
      Nat.choose (Fintype.card {x : Fin N // (σ.trans π.symm) x = x}) t := by
  rw [card_commonLevel, card_agreeingInputs_eq_fixedPoints]

/-- Relabeling every output preserves the agreement set. -/
theorem agreeingInputs_postcomp (π σ β : Perm N) :
    agreeingInputs (π.trans β) (σ.trans β) = agreeingInputs π σ := by
  ext x
  simp only [mem_agreeingInputs, Equiv.trans_apply]
  exact β.injective.eq_iff

/-- Relabeling every input transports the agreement set by the inverse label map. -/
theorem agreeingInputs_precomp (π σ α : Perm N) :
    agreeingInputs (α.trans π) (α.trans σ) =
      (agreeingInputs π σ).image α.symm := by
  ext x
  rw [mem_agreeingInputs, Finset.mem_image]
  constructor
  · intro h
    exact ⟨α x, (mem_agreeingInputs π σ (α x)).mpr h, α.symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using
      (mem_agreeingInputs π σ y).mp hy

/-- The kernel's combinatorial parameter is invariant under simultaneous
input and output relabeling, as claimed after Appendix A's central-kernel formula. -/
theorem card_agreeingInputs_relabel (π σ α β : Perm N) :
    (agreeingInputs ((α.trans π).trans β) ((α.trans σ).trans β)).card =
      (agreeingInputs π σ).card := by
  rw [agreeingInputs_postcomp, agreeingInputs_precomp]
  exact Finset.card_image_of_injective _ α.symm.injective

theorem card_commonLevel_relabel (π σ α β : Perm N) (t : ℕ) :
    Fintype.card (CommonLevel ((α.trans π).trans β) ((α.trans σ).trans β) t) =
      Fintype.card (CommonLevel π σ t) := by
  rw [card_commonLevel, card_commonLevel, card_agreeingInputs_relabel]

end QuantumOracle.CommonDatabases
