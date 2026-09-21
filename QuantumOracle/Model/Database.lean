import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Aesop

/-!
# Finite partial injective databases

This file formalizes the databases of manuscript Section 2.2
(`sec:carolan-oracle`). `Fin N` is the zero-based encoding of `[N]`.
An edge graph gives an actual partial injection, rather than an abstract
database interface whose mathematical properties have to be assumed.

This file does not define the Hilbert space compression operator `pC`.
-/

namespace QuantumOracle

/-- A finite graph representing a partial injective function on `Fin N`. -/
structure Database (N : ℕ) where
  edges : Finset (Fin N × Fin N)
  functional : ∀ ⦃e f⦄, e ∈ edges → f ∈ edges → e.1 = f.1 → e.2 = f.2
  injective : ∀ ⦃e f⦄, e ∈ edges → f ∈ edges → e.2 = f.2 → e.1 = f.1
  deriving DecidableEq

namespace Database

variable {N : ℕ}

@[ext]
theorem ext {I J : Database N} (h : I.edges = J.edges) : I = J := by
  cases I
  cases J
  cases h
  rfl

instance : Finite (Database N) :=
  Finite.of_injective Database.edges (fun _ _ h => ext h)

noncomputable instance : Fintype (Database N) := Fintype.ofFinite _

/-- The empty database, denoted `⊥_I` in the manuscript. -/
def empty : Database N where
  edges := ∅
  functional := by simp
  injective := by simp

/-- The input points on which a database is defined. -/
def domain (I : Database N) : Finset (Fin N) := I.edges.image Prod.fst

/-- The values attained by a database. -/
def image (I : Database N) : Finset (Fin N) := I.edges.image Prod.snd

/-- Database size is its domain cardinality, as in the manuscript. -/
def size (I : Database N) : ℕ := I.domain.card

@[simp] theorem empty_edges : (empty : Database N).edges = ∅ := rfl
@[simp] theorem empty_domain : (empty : Database N).domain = ∅ := by simp [domain]
@[simp] theorem empty_image : (empty : Database N).image = ∅ := by simp [image]
@[simp] theorem empty_size : (empty : Database N).size = 0 := by simp [size]

theorem mem_domain (I : Database N) (x : Fin N) :
    x ∈ I.domain ↔ ∃ y, (x, y) ∈ I.edges := by
  constructor
  · intro hx
    obtain ⟨⟨a, b⟩, hab, ha⟩ := Finset.mem_image.mp hx
    change a = x at ha
    subst a
    exact ⟨b, hab⟩
  · rintro ⟨y, hy⟩
    exact Finset.mem_image.mpr ⟨(x, y), hy, rfl⟩

theorem mem_image (I : Database N) (y : Fin N) :
    y ∈ I.image ↔ ∃ x, (x, y) ∈ I.edges := by
  constructor
  · intro hy
    obtain ⟨⟨a, b⟩, hab, hb⟩ := Finset.mem_image.mp hy
    change b = y at hb
    subst b
    exact ⟨a, hab⟩
  · rintro ⟨x, hx⟩
    exact Finset.mem_image.mpr ⟨(x, y), hx, rfl⟩

/-- The option-valued partial function encoded by the edge graph. -/
noncomputable def lookup (I : Database N) (x : Fin N) : Option (Fin N) :=
  if h : ∃ y, (x, y) ∈ I.edges then some h.choose else none

@[simp] theorem lookup_eq_some (I : Database N) (x y : Fin N) :
    I.lookup x = some y ↔ (x, y) ∈ I.edges := by
  classical
  unfold lookup
  split_ifs with h
  · constructor
    · intro heq
      exact (Option.some.inj heq) ▸ h.choose_spec
    · intro hxy
      congr 1
      exact I.functional h.choose_spec hxy rfl
  · constructor
    · intro heq
      cases heq
    · intro hxy
      exact False.elim (h ⟨y, hxy⟩)

@[simp] theorem lookup_eq_none (I : Database N) (x : Fin N) :
    I.lookup x = none ↔ x ∉ I.domain := by
  classical
  simp [lookup, mem_domain]

theorem size_eq_card_edges (I : Database N) : I.size = I.edges.card := by
  apply Finset.card_image_of_injOn
  intro e he f hf h
  exact Prod.ext h (I.functional he hf h)

theorem card_image_eq_size (I : Database N) : I.image.card = I.size := by
  rw [size_eq_card_edges]
  apply Finset.card_image_of_injOn
  intro e he f hf h
  exact Prod.ext (I.injective he hf h) h

theorem size_le (I : Database N) : I.size ≤ N := by
  exact (Finset.card_le_card (Finset.subset_univ I.domain)).trans_eq (by simp)

/-- Inversion exchanges input and output coordinates. -/
def inverse (I : Database N) : Database N where
  edges := I.edges.image Prod.swap
  functional := by
    intro e f he hf h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
    exact I.injective ha hb h
  injective := by
    intro e f he hf h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
    exact I.functional ha hb h

@[simp] theorem mem_inverse (I : Database N) (x y : Fin N) :
    (x, y) ∈ I.inverse.edges ↔ (y, x) ∈ I.edges := by
  simp [inverse, Finset.mem_image, Prod.exists, Prod.ext_iff]

@[simp] theorem inverse_inverse (I : Database N) : I.inverse.inverse = I := by
  ext ⟨x, y⟩
  simp

@[simp] theorem inverse_domain (I : Database N) : I.inverse.domain = I.image := by
  ext x
  simp only [mem_domain, mem_image, mem_inverse]

@[simp] theorem inverse_image (I : Database N) : I.inverse.image = I.domain := by
  ext x
  simp only [mem_domain, mem_image, mem_inverse]

@[simp] theorem inverse_size (I : Database N) : I.inverse.size = I.size := by
  simp only [size, inverse_domain]
  exact I.card_image_eq_size

@[simp] theorem inverse_empty : (empty : Database N).inverse = empty := by
  apply ext
  simp [inverse]

/-- Delete the edge at input `x`: manuscript `I[x → ⊥]`. -/
def erase (I : Database N) (x : Fin N) : Database N where
  edges := I.edges.filter (fun e => e.1 ≠ x)
  functional := by
    intro e f he hf h
    exact I.functional (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 h
  injective := by
    intro e f he hf h
    exact I.injective (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 h

@[simp] theorem mem_erase (I : Database N) (x a b : Fin N) :
    (a, b) ∈ (I.erase x).edges ↔ (a, b) ∈ I.edges ∧ a ≠ x := by
  simp [erase]

@[simp] theorem erase_domain (I : Database N) (x : Fin N) :
    (I.erase x).domain = I.domain.erase x := by
  ext a
  simp only [mem_domain, mem_erase, Finset.mem_erase, ne_eq]
  aesop

@[simp] theorem erase_undefined (I : Database N) (x : Fin N) :
    x ∉ (I.erase x).domain := by simp

@[simp] theorem erase_erase (I : Database N) (x : Fin N) :
    (I.erase x).erase x = I.erase x := by
  ext ⟨a, b⟩
  simp

theorem erase_eq_self_of_undefined (I : Database N) (x : Fin N)
    (hx : x ∉ I.domain) : I.erase x = I := by
  apply ext
  apply Finset.filter_eq_self.mpr
  intro e he h
  exact hx (Finset.mem_image.mpr ⟨e, he, h⟩)

theorem erase_size_le (I : Database N) (x : Fin N) : (I.erase x).size ≤ I.size := by
  simp only [size, erase_domain]
  exact Finset.card_le_card (Finset.erase_subset _ _)

/-- Set the edge at `x` to `y`, deleting the former edge at `x` and
any conflicting preimage of `y`, exactly as in Section 2.2. -/
def set (I : Database N) (x y : Fin N) : Database N where
  edges := insert (x, y) (I.edges.filter (fun e => e.1 ≠ x ∧ e.2 ≠ y))
  functional := by
    intro e f he hf h
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · rfl
      · exact False.elim ((Finset.mem_filter.mp hf).2.1 h.symm)
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact False.elim ((Finset.mem_filter.mp he).2.1 h)
      · exact I.functional (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 h
  injective := by
    intro e f he hf h
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · rfl
      · exact False.elim ((Finset.mem_filter.mp hf).2.2 h.symm)
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact False.elim ((Finset.mem_filter.mp he).2.2 h)
      · exact I.injective (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 h

/-- The manuscript's update, including deletion for an undefined value. -/
def update (I : Database N) (x : Fin N) : Option (Fin N) → Database N
  | none => I.erase x
  | some y => I.set x y

@[simp] theorem update_none (I : Database N) (x : Fin N) :
    I.update x none = I.erase x := rfl

@[simp] theorem update_some (I : Database N) (x y : Fin N) :
    I.update x (some y) = I.set x y := rfl

@[simp] theorem mem_set (I : Database N) (x y a b : Fin N) :
    (a, b) ∈ (I.set x y).edges ↔
      (a = x ∧ b = y) ∨ ((a, b) ∈ I.edges ∧ a ≠ x ∧ b ≠ y) := by
  simp [set, Prod.ext_iff]

@[simp] theorem set_contains (I : Database N) (x y : Fin N) :
    (x, y) ∈ (I.set x y).edges := by simp

theorem set_size_le (I : Database N) (x y : Fin N) :
    (I.set x y).size ≤ I.size + 1 := by
  rw [size_eq_card_edges, size_eq_card_edges]
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_filter_le _ _) 1)

theorem inverse_set (I : Database N) (x y : Fin N) :
    (I.set x y).inverse = I.inverse.set y x := by
  ext ⟨a, b⟩
  simp only [mem_inverse, mem_set]
  aesop

/-- If no input or image conflict exists, updating simply adjoins an edge. -/
theorem set_edges_of_fresh (I : Database N) (x y : Fin N)
    (hx : x ∉ I.domain) (hy : y ∉ I.image) :
    (I.set x y).edges = insert (x, y) I.edges := by
  apply congrArg (insert (x, y))
  apply Finset.filter_eq_self.mpr
  intro e he
  constructor
  · intro h
    apply hx
    exact Finset.mem_image.mpr ⟨e, he, h⟩
  · intro h
    apply hy
    exact Finset.mem_image.mpr ⟨e, he, h⟩

theorem set_size_of_fresh (I : Database N) (x y : Fin N)
    (hx : x ∉ I.domain) (hy : y ∉ I.image) :
    (I.set x y).size = I.size + 1 := by
  rw [size_eq_card_edges, set_edges_of_fresh I x y hx hy, size_eq_card_edges]
  apply Finset.card_insert_of_notMem
  intro h
  exact hx ((mem_domain I x).mpr ⟨y, h⟩)

theorem erase_set_of_fresh (I : Database N) (x y : Fin N)
    (hx : x ∉ I.domain) (hy : y ∉ I.image) :
    (I.set x y).erase x = I := by
  apply ext
  change ((I.set x y).edges.filter (fun e => e.1 ≠ x)) = I.edges
  rw [set_edges_of_fresh I x y hx hy]
  rw [Finset.filter_insert]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  exact congrArg Database.edges (erase_eq_self_of_undefined I x hx)

theorem set_erase_of_mem (I : Database N) (x y : Fin N)
    (hxy : (x, y) ∈ I.edges) : (I.erase x).set x y = I := by
  ext ⟨a, b⟩
  simp only [mem_set, mem_erase]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨⟨h, _⟩, _, _⟩)
    · exact hxy
    · exact h
  · intro h
    by_cases ha : a = x
    · exact Or.inl ⟨ha, I.functional h hxy ha⟩
    · refine Or.inr ⟨⟨h, ha⟩, ha, ?_⟩
      intro hb
      exact ha (I.injective h hxy hb)

theorem erased_value_fresh (I : Database N) (x y : Fin N)
    (hxy : (x, y) ∈ I.edges) : y ∉ (I.erase x).image := by
  intro h
  obtain ⟨a, ha⟩ := (mem_image _ _).mp h
  obtain ⟨ha, hax⟩ := (mem_erase I x a y).mp ha
  exact hax (I.injective ha hxy rfl)

/-- The actual block `J|^x`, described as the fiber of deletion at `x`. -/
noncomputable def block (x : Fin N) (J : Database N) : Finset (Database N) :=
  Finset.univ.filter (fun I => I.erase x = J)

@[simp] theorem mem_block (x : Fin N) (I J : Database N) :
    I ∈ block x J ↔ I.erase x = J := by
  classical
  simp [block]

/-- Every database has exactly one base database for its compression block. -/
theorem block_base_unique (x : Fin N) (I : Database N) :
    ∃! J, x ∉ J.domain ∧ I ∈ block x J := by
  refine ⟨I.erase x, ⟨erase_undefined I x, ?_⟩, ?_⟩
  · exact (mem_block x I _).mpr rfl
  · intro J hJ
    exact ((mem_block x I J).mp hJ.2).symm

/-- The fiber description is the manuscript's base plus all fresh updates. -/
theorem mem_block_iff (x : Fin N) (I J : Database N) (hx : x ∉ J.domain) :
    I ∈ block x J ↔ I = J ∨ ∃ y, y ∉ J.image ∧ I = J.set x y := by
  rw [mem_block]
  constructor
  · intro h
    by_cases hi : x ∈ I.domain
    · obtain ⟨y, hy⟩ := (mem_domain I x).mp hi
      right
      refine ⟨y, ?_, ?_⟩
      · rw [← h]
        exact erased_value_fresh I x y hy
      · rw [← h]
        exact (set_erase_of_mem I x y hy).symm
    · left
      rw [erase_eq_self_of_undefined I x hi] at h
      exact h
  · rintro (rfl | ⟨y, hy, rfl⟩)
    · exact erase_eq_self_of_undefined _ x hx
    · exact erase_set_of_fresh J x y hx hy

/-- Embed a genuine permutation as a full database. -/
def ofPermutation (φ : Equiv.Perm (Fin N)) : Database N where
  edges := Finset.univ.image (fun x => (x, φ x))
  functional := by
    intro e f he hf h
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hf
    exact congrArg φ h
  injective := by
    intro e f he hf h
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hf
    exact φ.injective h

@[simp] theorem mem_ofPermutation (φ : Equiv.Perm (Fin N)) (x y : Fin N) :
    (x, y) ∈ (ofPermutation φ).edges ↔ φ x = y := by
  simp [ofPermutation, Finset.mem_image, Prod.ext_iff]

@[simp] theorem lookup_ofPermutation (φ : Equiv.Perm (Fin N)) (x : Fin N) :
    (ofPermutation φ).lookup x = some (φ x) := by simp

@[simp] theorem domain_ofPermutation (φ : Equiv.Perm (Fin N)) :
    (ofPermutation φ).domain = Finset.univ := by
  ext x
  simp only [mem_domain, mem_ofPermutation, Finset.mem_univ, iff_true]
  exact ⟨φ x, rfl⟩

@[simp] theorem size_ofPermutation (φ : Equiv.Perm (Fin N)) :
    (ofPermutation φ).size = N := by simp [size]

@[simp] theorem inverse_ofPermutation (φ : Equiv.Perm (Fin N)) :
    (ofPermutation φ).inverse = ofPermutation φ.symm := by
  ext ⟨x, y⟩
  simp only [mem_inverse, mem_ofPermutation]
  exact ⟨fun h => (φ.symm_apply_eq.mpr h.symm),
    fun h => (φ.eq_symm_apply.mp h.symm)⟩

/-- The databases at a fixed level of the manuscript's direct sum. -/
def level (N t : ℕ) := {I : Database N // I.size = t}

/-- The databases supported on levels up to `t`. -/
def atMost (N t : ℕ) := {I : Database N // I.size ≤ t}

end Database

/-!
## Basis permutations for the extended lookup

These act on arbitrary output-register values, as in Section 2.3.
Their linear lifts and conjugation by `pC` are not implemented here.
-/

namespace BasisLookup

variable {N w : ℕ}

/-- A fixed-length bit string. -/
abbrev Bits (w : ℕ) := Fin w → Bool

def xor (z a : Bits w) : Bits w := fun i => Bool.xor (z i) (a i)

@[simp] theorem xor_twice (z a : Bits w) : xor (xor z a) a = z := by
  funext i
  change Bool.xor (Bool.xor (z i) (a i)) (a i) = z i
  cases z i <;> cases a i <;> rfl

@[simp] theorem xor_zero (z : Bits w) : xor z (fun _ => false) = z := by
  funext i
  change Bool.xor (z i) false = z i
  cases z i <;> rfl

/-- XOR with a fixed bit string is an actual permutation. -/
def xorPerm (a : Bits w) : Equiv.Perm (Bits w) where
  toFun := fun z => xor z a
  invFun := fun z => xor z a
  left_inv := fun z => xor_twice z a
  right_inv := fun z => xor_twice z a

def bitXorPerm (a : Bool) : Equiv.Perm Bool where
  toFun := fun z => Bool.xor z a
  invFun := fun z => Bool.xor z a
  left_inv := by intro z; cases z <;> cases a <;> rfl
  right_inv := by intro z; cases z <;> cases a <;> rfl

/-- Apply a database-dependent output permutation, keeping the database. -/
def liftLookup {Y : Type*} (action : Database N → Equiv.Perm Y) :
    Equiv.Perm (Y × Database N) where
  toFun := fun zI => (action zI.2 zI.1, zI.2)
  invFun := fun zI => ((action zI.2).symm zI.1, zI.2)
  left_inv := by rintro ⟨z, I⟩; simp
  right_inv := by rintro ⟨z, I⟩; simp

@[simp] theorem liftLookup_database {Y : Type*}
    (action : Database N → Equiv.Perm Y) (zI : Y × Database N) :
    (liftLookup action zI).2 = zI.2 := rfl

/-- Every extended basis lookup preserves the fiber used for compression. -/
theorem liftLookup_preserves_block {Y : Type*}
    (action : Database N → Equiv.Perm Y) (zI : Y × Database N)
    (x : Fin N) (J : Database N) :
    (liftLookup action zI).2 ∈ Database.block x J ↔ zI.2 ∈ Database.block x J :=
  Iff.rfl

/-- A representation by distinct bit strings, as required in Section 2.1. -/
abbrev Encoding (N w : ℕ) := Fin N ↪ Bits w

noncomputable def ordinaryAnswer (encode : Encoding N w) (I : Database N)
    (x : Fin N) : Bits w :=
  match I.lookup x with
  | none => fun _ => false
  | some y => encode y

/-- Marked answers encode a defined value as `(true, encode y)` and
an undefined value as `(false, 0)`. -/
noncomputable def markedAnswer (encode : Encoding N w) (I : Database N)
    (x : Fin N) : Bool × Bits w :=
  match I.lookup x with
  | none => (false, fun _ => false)
  | some y => (true, encode y)

/-- The manuscript's ordinary extended lookup `P_x` on basis states. -/
noncomputable def ordinary (encode : Encoding N w) (x : Fin N) :
    Equiv.Perm (Bits w × Database N) :=
  liftLookup (fun I => xorPerm (ordinaryAnswer encode I x))

/-- The marked extended lookup, including an arbitrary marker-qubit value. -/
noncomputable def marked (encode : Encoding N w) (x : Fin N) :
    Equiv.Perm ((Bool × Bits w) × Database N) :=
  liftLookup (fun I =>
    Equiv.prodCongr (bitXorPerm (markedAnswer encode I x).1)
      (xorPerm (markedAnswer encode I x).2))

theorem ordinary_defined (encode : Encoding N w) (x y : Fin N)
    (I : Database N) (h : (x, y) ∈ I.edges) (z : Bits w) :
    ordinary encode x (z, I) = (xor z (encode y), I) := by
  simp [ordinary, liftLookup, ordinaryAnswer, (Database.lookup_eq_some I x y).mpr h,
    xorPerm]

theorem ordinary_undefined (encode : Encoding N w) (x : Fin N)
    (I : Database N) (h : x ∉ I.domain) (z : Bits w) :
    ordinary encode x (z, I) = (z, I) := by
  simp [ordinary, liftLookup, ordinaryAnswer, (Database.lookup_eq_none I x).mpr h,
    xorPerm]

theorem marked_defined (encode : Encoding N w) (x y : Fin N)
    (I : Database N) (h : (x, y) ∈ I.edges) (z : Bool × Bits w) :
    marked encode x (z, I) = ((Bool.xor z.1 true, xor z.2 (encode y)), I) := by
  rcases z with ⟨marker, bits⟩
  simp [marked, liftLookup, markedAnswer, (Database.lookup_eq_some I x y).mpr h,
    xorPerm, bitXorPerm]

theorem marked_undefined (encode : Encoding N w) (x : Fin N)
    (I : Database N) (h : x ∉ I.domain) (z : Bool × Bits w) :
    marked encode x (z, I) = (z, I) := by
  rcases z with ⟨marker, bits⟩
  simp [marked, liftLookup, markedAnswer, (Database.lookup_eq_none I x).mpr h,
    xorPerm, bitXorPerm]

theorem ordinary_involutive (encode : Encoding N w) (x : Fin N) :
    Function.Involutive (ordinary encode x) := by
  rintro ⟨z, I⟩
  change (xor (xor z (ordinaryAnswer encode I x)) (ordinaryAnswer encode I x), I) =
    (z, I)
  rw [xor_twice]

theorem marked_involutive (encode : Encoding N w) (x : Fin N) :
    Function.Involutive (marked encode x) := by
  rintro ⟨⟨b, z⟩, I⟩
  change ((Bool.xor (Bool.xor b (markedAnswer encode I x).1)
      (markedAnswer encode I x).1,
    xor (xor z (markedAnswer encode I x).2) (markedAnswer encode I x).2), I) =
      ((b, z), I)
  rw [xor_twice]
  cases b <;> cases (markedAnswer encode I x).1 <;> rfl

/-- Database inversion, with an arbitrary unchanged output register. -/
def flip {Y : Type*} : Equiv.Perm (Y × Database N) where
  toFun := fun zI => (zI.1, zI.2.inverse)
  invFun := fun zI => (zI.1, zI.2.inverse)
  left_inv := by intro zI; simp
  right_inv := by intro zI; simp

/-- Inverse-direction block obtained by database-inversion conjugation. -/
noncomputable def inverseOrdinary (encode : Encoding N w) (x : Fin N) :
    Equiv.Perm (Bits w × Database N) :=
  (flip.trans (ordinary encode x)).trans flip

noncomputable def inverseMarked (encode : Encoding N w) (x : Fin N) :
    Equiv.Perm ((Bool × Bits w) × Database N) :=
  (flip.trans (marked encode x)).trans flip

theorem inverseOrdinary_defined (encode : Encoding N w) (x y : Fin N)
    (I : Database N) (h : (y, x) ∈ I.edges) (z : Bits w) :
    inverseOrdinary encode x (z, I) = (xor z (encode y), I) := by
  change flip (ordinary encode x (z, I.inverse)) = _
  rw [ordinary_defined encode x y I.inverse ((Database.mem_inverse I x y).mpr h)]
  simp [flip]

theorem inverseMarked_defined (encode : Encoding N w) (x y : Fin N)
    (I : Database N) (h : (y, x) ∈ I.edges) (z : Bool × Bits w) :
    inverseMarked encode x (z, I) = ((Bool.xor z.1 true, xor z.2 (encode y)), I) := by
  change flip (marked encode x (z, I.inverse)) = _
  rw [marked_defined encode x y I.inverse ((Database.mem_inverse I x y).mpr h)]
  simp [flip]

/-- A coherent-control basis permutation. Its linear lift remains to be proved. -/
def controlled {Y : Type*} (e : Equiv.Perm Y) : Equiv.Perm (Bool × Y) where
  toFun := fun cy => (cy.1, if cy.1 then e cy.2 else cy.2)
  invFun := fun cy => (cy.1, if cy.1 then e.symm cy.2 else cy.2)
  left_inv := by rintro ⟨b, y⟩; cases b <;> simp
  right_inv := by rintro ⟨b, y⟩; cases b <;> simp

@[simp] theorem controlled_false {Y : Type*} (e : Equiv.Perm Y) (y : Y) :
    controlled e (false, y) = (false, y) := rfl

@[simp] theorem controlled_true {Y : Type*} (e : Equiv.Perm Y) (y : Y) :
    controlled e (true, y) = (true, e y) := rfl

end BasisLookup
end QuantumOracle
