import QuantumOracle.Model.Database
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sigma

/-!
# Actual database indexing for compression blocks

For a fixed query input `x`, a compression block consists of its base database
`J`, with `x` undefined, and one additional basis vector for each unused output
of `J`. The equivalence below is proved from the actual partial-injective graph
definition of `Database`; it introduces no assumptions about the oracle.
-/

namespace QuantumOracle.CompressionIndex

variable {N : ℕ}

/-- A base database for compression at input `x`. -/
abbrev Base (x : Fin N) := {J : Database N // x ∉ J.domain}

/-- Unused output values of an actual partial-injective database. -/
abbrev Fresh (J : Database N) := {y : Fin N // y ∉ J.image}

noncomputable instance baseFintype (x : Fin N) : Fintype (Base x) :=
  Fintype.ofFinite _

noncomputable instance freshFintype (J : Database N) : Fintype (Fresh J) :=
  Fintype.ofFinite _

/-- One undefined basis vector, followed by one vector for each fresh output. -/
abbrev Index (x : Fin N) := Σ J : Base x, Option (Fresh J.val)

theorem card_fresh (J : Database N) :
    Fintype.card (Fresh J) = N - J.size := by
  classical
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin, Fintype.card_coe, J.card_image_eq_size]

theorem base_size_lt {x : Fin N} (J : Base x) : J.val.size < N := by
  have hcard : (insert x J.val.domain).card ≤ N :=
    (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  rw [Finset.card_insert_of_notMem J.property] at hcard
  exact hcard

theorem fresh_card_pos {x : Fin N} (J : Base x) :
    0 < Fintype.card (Fresh J.val) := by
  rw [card_fresh]
  exact Nat.sub_pos_of_lt (base_size_lt J)

theorem fresh_nonempty {x : Fin N} (J : Base x) : Nonempty (Fresh J.val) :=
  Fintype.card_pos_iff.mp (fresh_card_pos J)

/-- Interpret block coordinates as actual databases. -/
def decode (x : Fin N) : Index x → Database N
  | ⟨J, none⟩ => J.val
  | ⟨J, some y⟩ => J.val.set x y.val

@[simp] theorem decode_none (x : Fin N) (J : Base x) :
    decode x ⟨J, none⟩ = J.val := rfl

@[simp] theorem decode_some (x : Fin N) (J : Base x) (y : Fresh J.val) :
    decode x ⟨J, some y⟩ = J.val.set x y.val := rfl

@[simp] theorem erase_decode (x : Fin N) (i : Index x) :
    (decode x i).erase x = i.1.val := by
  rcases i with ⟨J, _ | y⟩
  · exact Database.erase_eq_self_of_undefined J.val x J.property
  · exact Database.erase_set_of_fresh J.val x y.val J.property y.property

@[simp] theorem lookup_decode (x : Fin N) (i : Index x) :
    (decode x i).lookup x = i.2.map Subtype.val := by
  rcases i with ⟨J, _ | y⟩
  · exact (Database.lookup_eq_none J.val x).mpr J.property
  · exact (Database.lookup_eq_some _ x y.val).mpr (Database.set_contains _ _ _)

theorem decode_injective (x : Fin N) : Function.Injective (decode x) := by
  rintro ⟨I, i⟩ ⟨J, j⟩ h
  have hbase : I = J := by
    apply Subtype.ext
    simpa only [erase_decode] using congrArg (fun K : Database N => K.erase x) h
  subst J
  have hout := congrArg (fun K : Database N => K.lookup x) h
  simp only [lookup_decode] at hout
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some y => cases hout
  | some y =>
    cases j with
    | none => cases hout
    | some z =>
      have hyz : y = z := Subtype.ext (Option.some.inj hout)
      cases hyz
      rfl

theorem decode_surjective (x : Fin N) : Function.Surjective (decode x) := by
  intro I
  let J : Base x := ⟨I.erase x, I.erase_undefined x⟩
  by_cases hx : x ∈ I.domain
  · obtain ⟨y, hy⟩ := (Database.mem_domain I x).mp hx
    refine ⟨⟨J, some ⟨y, Database.erased_value_fresh I x y hy⟩⟩, ?_⟩
    exact Database.set_erase_of_mem I x y hy
  · refine ⟨⟨J, none⟩, ?_⟩
    exact Database.erase_eq_self_of_undefined I x hx

/-- The genuine database basis is partitioned into its compression blocks. -/
noncomputable def databaseEquiv (x : Fin N) : Database N ≃ Index x :=
  (Equiv.ofBijective (decode x) ⟨decode_injective x, decode_surjective x⟩).symm

@[simp] theorem databaseEquiv_symm_apply (x : Fin N) (i : Index x) :
    (databaseEquiv x).symm i = decode x i := rfl

@[simp] theorem databaseEquiv_symm_none (x : Fin N) (J : Base x) :
    (databaseEquiv x).symm ⟨J, none⟩ = J.val := rfl

@[simp] theorem databaseEquiv_symm_some (x : Fin N) (J : Base x)
    (y : Fresh J.val) : (databaseEquiv x).symm ⟨J, some y⟩ = J.val.set x y.val := rfl

/-- The first coordinate is exactly deletion at `x`. -/
@[simp] theorem databaseEquiv_base (x : Fin N) (I : Database N) :
    (databaseEquiv x I).1.val = I.erase x := by
  have h := erase_decode x (databaseEquiv x I)
  rw [← databaseEquiv_symm_apply, Equiv.symm_apply_apply] at h
  exact h.symm

/-- The optional fresh value is exactly the actual database lookup. -/
@[simp] theorem databaseEquiv_lookup (x : Fin N) (I : Database N) :
    (databaseEquiv x I).2.map Subtype.val = I.lookup x := by
  have h := lookup_decode x (databaseEquiv x I)
  rw [← databaseEquiv_symm_apply, Equiv.symm_apply_apply] at h
  exact h.symm

@[simp] theorem decode_none_size (x : Fin N) (J : Base x) :
    (decode x ⟨J, none⟩).size = J.val.size := rfl

@[simp] theorem decode_some_size (x : Fin N) (J : Base x) (y : Fresh J.val) :
    (decode x ⟨J, some y⟩).size = J.val.size + 1 :=
  Database.set_size_of_fresh J.val x y.val J.property y.property

theorem decode_mem_block (x : Fin N) (i : Index x) :
    decode x i ∈ Database.block x i.1.val := by
  rw [Database.mem_block, erase_decode]

end QuantumOracle.CompressionIndex
