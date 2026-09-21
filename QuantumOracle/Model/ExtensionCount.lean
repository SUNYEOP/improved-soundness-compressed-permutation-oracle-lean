import QuantumOracle.Model.PermutationExtensions
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype

/-!
# Counting actual permutation extensions

The permutation extensions of a partial injection are in explicit bijection with
bijections between its unused inputs and unused outputs. This proves the exact
factorial normalization in manuscript Section 3.1, without a counting axiom.
-/

namespace QuantumOracle.PermutationExtensions

variable {N : ℕ}

/-- Inputs outside the actual graph domain. -/
abbrev UnusedDomain (I : Database N) := {x : Fin N // x ∉ I.domain}

/-- Outputs outside the actual graph image. -/
abbrev UnusedImage (I : Database N) := {y : Fin N // y ∉ I.image}

noncomputable instance unusedDomainFintype (I : Database N) : Fintype (UnusedDomain I) :=
  Fintype.ofFinite _

noncomputable instance unusedImageFintype (I : Database N) : Fintype (UnusedImage I) :=
  Fintype.ofFinite _

/-- The actual graph is a bijection between its domain and image. -/
noncomputable def definedEquiv (I : Database N) : I.domain ≃ I.image := by
  classical
  let f : I.domain → I.image := fun x =>
    ⟨(Database.mem_domain I x.val).mp x.property |>.choose,
      (Database.mem_image I _).mpr
        ⟨x.val, (Database.mem_domain I x.val).mp x.property |>.choose_spec⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x x' heq
    apply Subtype.ext
    exact I.injective ((Database.mem_domain I x.val).mp x.property).choose_spec
      ((Database.mem_domain I x'.val).mp x'.property).choose_spec
      (congrArg Subtype.val heq)
  · intro y
    obtain ⟨x, hx⟩ := (Database.mem_image I y.val).mp y.property
    refine ⟨⟨x, (Database.mem_domain I x).mpr ⟨y.val, hx⟩⟩, ?_⟩
    apply Subtype.ext
    exact I.functional
      ((Database.mem_domain I x).mp ((Database.mem_domain I x).mpr ⟨y.val, hx⟩)).choose_spec
      hx rfl

theorem definedEquiv_apply_of_edge (I : Database N) (x y : Fin N)
    (hxy : (x, y) ∈ I.edges) (hx : x ∈ I.domain) :
    (definedEquiv I ⟨x, hx⟩).val = y := by
  exact I.functional ((Database.mem_domain I x).mp hx).choose_spec hxy rfl

/-- Glue a freely chosen residual bijection to the database's fixed edges. -/
noncomputable def complete (I : Database N) (e : UnusedDomain I ≃ UnusedImage I) :
    Perm N := Equiv.subtypeCongr (definedEquiv I) e

theorem complete_apply_defined (I : Database N) (e : UnusedDomain I ≃ UnusedImage I)
    (x : Fin N) (hx : x ∈ I.domain) :
    complete I e x = (definedEquiv I ⟨x, hx⟩).val := by
  classical
  simp only [complete, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply]
  rw [Equiv.sumCompl_symm_apply_of_pos hx, Sum.map_inl,
    Equiv.sumCompl_apply_inl]

theorem complete_apply_unused (I : Database N) (e : UnusedDomain I ≃ UnusedImage I)
    (x : Fin N) (hx : x ∉ I.domain) : complete I e x = (e ⟨x, hx⟩).val := by
  classical
  simp only [complete, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply]
  rw [Equiv.sumCompl_symm_apply_of_neg hx, Sum.map_inr,
    Equiv.sumCompl_apply_inr]

theorem complete_extends (I : Database N) (e : UnusedDomain I ≃ UnusedImage I) :
    Extends I (complete I e) := by
  intro x y hxy
  rw [complete_apply_defined I e x ((Database.mem_domain I x).mpr ⟨y, hxy⟩)]
  exact definedEquiv_apply_of_edge I x y hxy _

theorem extends_image_iff_domain (I : Database N) (π : Extensions I) (x : Fin N) :
    π.val x ∈ I.image ↔ x ∈ I.domain := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (Database.mem_image I (π.val x)).mp hx
    have hax : a = x := π.val.injective (π.property a (π.val x) ha)
    subst a
    exact (Database.mem_domain I x).mpr ⟨π.val x, ha⟩
  · intro hx
    obtain ⟨y, hy⟩ := (Database.mem_domain I x).mp hx
    rw [π.property x y hy]
    exact (Database.mem_image I y).mpr ⟨x, hy⟩

/-- Restrict an actual consistent permutation to the two unused complements. -/
noncomputable def restrictUnused (I : Database N) (π : Extensions I) :
    UnusedDomain I ≃ UnusedImage I :=
  π.val.subtypeEquiv (fun x => not_congr (extends_image_iff_domain I π x).symm)

/-- Concrete completions of the database are exactly the arbitrary residual bijections. -/
noncomputable def extensionsEquivUnused (I : Database N) :
    Extensions I ≃ (UnusedDomain I ≃ UnusedImage I) where
  toFun := restrictUnused I
  invFun := fun e => ⟨complete I e, complete_extends I e⟩
  left_inv := by
    intro π
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ I.domain
    · obtain ⟨y, hy⟩ := (Database.mem_domain I x).mp hx
      rw [complete_apply_defined I (restrictUnused I π) x hx,
        definedEquiv_apply_of_edge I x y hy hx, π.property x y hy]
    · exact complete_apply_unused I (restrictUnused I π) x hx
  right_inv := by
    intro e
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact complete_apply_unused I e x.val x.property

theorem card_unusedDomain (I : Database N) :
    Fintype.card (UnusedDomain I) = N - I.size := by
  classical
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin, Fintype.card_coe, Database.size]

theorem card_unusedImage (I : Database N) :
    Fintype.card (UnusedImage I) = N - I.size := by
  classical
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin, Fintype.card_coe, I.card_image_eq_size]

/-- Every partial injection on an N-point set has exactly `(N - |I|)!` extensions. -/
theorem card_extensions (I : Database N) :
    Fintype.card (Extensions I) = (N - I.size).factorial := by
  classical
  rw [Fintype.card_congr (extensionsEquivUnused I)]
  rw [Fintype.card_equiv (Fintype.equivOfCardEq
    ((card_unusedDomain I).trans (card_unusedImage I).symm)), card_unusedDomain]

/-- Extension existence holds also for full databases and the empty domain. -/
theorem extensions_nonempty (I : Database N) : Nonempty (Extensions I) := by
  apply Fintype.card_pos_iff.mp
  rw [card_extensions]
  exact Nat.factorial_pos _

theorem exists_extension (I : Database N) : ∃ π : Perm N, Extends I π := by
  obtain ⟨π⟩ := extensions_nonempty I
  exact ⟨π.val, π.property⟩

/-- Conditioning on a fresh edge is literally extension of the enlarged graph. -/
noncomputable def edgeFiberEquiv (I : Database N) (x y : Fin N)
    (hx : x ∉ I.domain) (hy : y ∉ I.image) :
    {π : Extensions I // π.val x = y} ≃ Extensions (I.set x y) where
  toFun := fun π => ⟨π.val.val,
    (extends_set_iff_of_fresh I x y hx hy π.val.val).mpr ⟨π.val.property, π.property⟩⟩
  invFun := fun π =>
    ⟨⟨π.val, ((extends_set_iff_of_fresh I x y hx hy π.val).mp π.property).1⟩,
      ((extends_set_iff_of_fresh I x y hx hy π.val).mp π.property).2⟩
  left_inv := by intro π; rfl
  right_inv := by intro π; rfl

/-- Exact number of consistent permutations realizing any given fresh output. -/
theorem card_edgeFiber (I : Database N) (x y : Fin N)
    (hx : x ∉ I.domain) (hy : y ∉ I.image) :
    Fintype.card {π : Extensions I // π.val x = y} =
      (N - I.size - 1).factorial := by
  classical
  rw [Fintype.card_congr (edgeFiberEquiv I x y hx hy), card_extensions,
    Database.set_size_of_fresh I x y hx hy, Nat.sub_add_eq]

/-- The conditioning fibers all have fraction `1 / (N - |I|)` of the extensions,
stated without division or numerical approximation. -/
theorem extensions_card_eq_mul_edgeFiber (I : Database N) (x y : Fin N)
    (hx : x ∉ I.domain) (hy : y ∉ I.image) :
    Fintype.card (Extensions I) = (N - I.size) *
      Fintype.card {π : Extensions I // π.val x = y} := by
  classical
  rw [card_extensions, card_edgeFiber I x y hx hy]
  have hcard : (insert x I.domain).card ≤ N :=
    (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  rw [Finset.card_insert_of_notMem hx] at hcard
  have hpos : 0 < N - I.size := Nat.sub_pos_of_lt hcard
  exact (Nat.mul_factorial_pred (Nat.ne_of_gt hpos)).symm

end QuantumOracle.PermutationExtensions
