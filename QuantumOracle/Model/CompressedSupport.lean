import QuantumOracle.Model.CompressedQuery
import QuantumOracle.Model.BlockSupport

/-!
# Proved degree growth for the actual compressed permutation queries

This connects the concrete `pC P pC` operators to the graph-based support
lemmas. In particular the degree bound is not an assumption about the oracle.
-/

noncomputable section

namespace QuantumOracle.CompressedSupport

open BlockSupport CompressionIndex BasisLookup

variable {N w : ℕ} {Y : Type*} [Fintype Y]

/-- Compression on the actual database space preserves its deletion blocks. -/
theorem compression_preservesBlocks (Y : Type*) [Fintype Y] (x : Fin N) :
    PreservesBlocks x (CompressedQuery.compression Y x) := by
  intro J ψ hψ y I hI
  let i := databaseEquiv x I
  let φ : Compression.State N := WithLp.toLp 2 (fun K => ψ (y, K))
  have hbase : i.1.val = J := by
    change (databaseEquiv x I).1.val = J
    rw [databaseEquiv_base, hI]
  have hz : Compression.coordinates x φ i.1 = 0 := by
    ext o
    change ψ (y, decode x ⟨i.1, o⟩) = 0
    apply hψ y
    rw [erase_decode, hbase]
  have h := congrArg (fun v => v i.2) (Compression.pC_zero_block x φ i.1 hz)
  change Compression.pC x φ (decode x ⟨i.1, i.2⟩) = 0 at h
  have hi : decode x ⟨i.1, i.2⟩ = I := by
    change (databaseEquiv x).symm (databaseEquiv x I) = I
    exact Equiv.symm_apply_apply _ _
  rw [hi] at h
  rw [CompressedQuery.compression_apply]
  exact h

/-- Any database-controlled answer permutation preserves every deletion block. -/
theorem liftLookup_preservesBlocks (x : Fin N)
    (action : Database N → Equiv.Perm Y) :
    PreservesBlocks x (Query.linearLift (BasisLookup.liftLookup action)) := by
  intro J ψ hψ y I hI
  change ψ ((action I).symm y, I) = 0
  exact hψ _ I hI

theorem ordinaryLookup_preservesBlocks (encode : Encoding N w) (x : Fin N) :
    PreservesBlocks x (Query.ordinaryLookup encode x) :=
  liftLookup_preservesBlocks x _

theorem markedLookup_preservesBlocks (encode : Encoding N w) (x : Fin N) :
    PreservesBlocks x (Query.markedLookup encode x) :=
  liftLookup_preservesBlocks x _

/-- The full `pC P pC` query stays in one deletion block. -/
theorem ordinary_preservesBlocks (encode : Encoding N w) (x : Fin N) :
    PreservesBlocks x (CompressedQuery.ordinary encode x) := by
  intro J ψ hψ
  rw [CompressedQuery.ordinary_apply]
  exact compression_preservesBlocks _ x J _
    (ordinaryLookup_preservesBlocks encode x J _
      (compression_preservesBlocks _ x J ψ hψ))

theorem marked_preservesBlocks (encode : Encoding N w) (x : Fin N) :
    PreservesBlocks x (CompressedQuery.marked encode x) := by
  intro J ψ hψ
  rw [CompressedQuery.marked_apply]
  exact compression_preservesBlocks _ x J _
    (markedLookup_preservesBlocks encode x J _
      (compression_preservesBlocks _ x J ψ hψ))

/-- One actual ordinary compressed query grows database degree by at most one. -/
theorem ordinary_supported (encode : Encoding N w) (x : Fin N)
    {t : ℕ} {ψ : State (Bits w) N} (hψ : Supported t ψ) :
    Supported (t + 1) (CompressedQuery.ordinary encode x ψ) :=
  supported_succ_of_preservesBlocks (ordinary_preservesBlocks encode x) hψ

/-- Marking the answer does not change the proved one-query degree bound. -/
theorem marked_supported (encode : Encoding N w) (x : Fin N)
    {t : ℕ} {ψ : State (Bool × Bits w) N} (hψ : Supported t ψ) :
    Supported (t + 1) (CompressedQuery.marked encode x ψ) :=
  supported_succ_of_preservesBlocks (marked_preservesBlocks encode x) hψ

theorem inverseOrdinary_supported (encode : Encoding N w) (x : Fin N)
    {t : ℕ} {ψ : State (Bits w) N} (hψ : Supported t ψ) :
    Supported (t + 1) (CompressedQuery.inverseOrdinary encode x ψ) :=
  supported_flip (ordinary_supported encode x (supported_flip hψ))

theorem inverseMarked_supported (encode : Encoding N w) (x : Fin N)
    {t : ℕ} {ψ : State (Bool × Bits w) N} (hψ : Supported t ψ) :
    Supported (t + 1) (CompressedQuery.inverseMarked encode x ψ) :=
  supported_flip (marked_supported encode x (supported_flip hψ))

/-- A genuine schedule of forward or inverse ordinary queries starts at
degree zero and reaches degree at most its query count. -/
theorem ordinary_schedule_supported (encode : Encoding N w)
    (query : ℕ → Bool × Fin N) (ψ : EuclideanSpace ℂ (Bits w)) (q : ℕ) :
    Supported q
      (run (fun k => if (query k).1 then CompressedQuery.inverseOrdinary encode (query k).2
        else CompressedQuery.ordinary encode (query k).2) (emptyState ψ) q) := by
  simpa only [Nat.zero_add] using
    (supported_run (t := 0)
      (U := fun k => if (query k).1 then CompressedQuery.inverseOrdinary encode (query k).2
        else CompressedQuery.ordinary encode (query k).2)
      (fun k s φ hφ => by
        cases h : (query k).1
        · simp only [h, Bool.false_eq_true, ↓reduceIte]
          exact ordinary_supported encode (query k).2 hφ
        · simp only [h, ↓reduceIte]
          exact inverseOrdinary_supported encode (query k).2 hφ)
      (supported_emptyState ψ) q)

section Coherent

variable {C : Type*} [Fintype C]

/-- Change product parentheses to place the database last for `Supported`. -/
def associate (ψ : EuclideanSpace ℂ (C × (Y × Database N))) : State (C × Y) N :=
  WithLp.toLp 2 (fun p => ψ (p.1.1, (p.1.2, p.2)))

@[simp] theorem associate_apply (ψ : EuclideanSpace ℂ (C × (Y × Database N)))
    (c : C) (y : Y) (I : Database N) : associate ψ ((c, y), I) = ψ (c, (y, I)) := rfl

/-- The actual coherent linear isometry family has precisely the coordinate
action used in the proved support lemma. -/
theorem associate_family
    (U : C → State Y N ≃ₗᵢ[ℂ] State Y N)
    (ψ : EuclideanSpace ℂ (C × (Y × Database N))) :
    associate (BlockOperator.family U ψ) =
      indexed (fun c => U c) (associate ψ) := by
  ext ⟨⟨c, y⟩, I⟩
  rfl

theorem family_supported {t s : ℕ}
    (U : C → State Y N ≃ₗᵢ[ℂ] State Y N)
    (hU : ∀ c φ, Supported t φ → Supported s (U c φ))
    {ψ : EuclideanSpace ℂ (C × (Y × Database N))}
    (hψ : Supported t (associate ψ)) :
    Supported s (associate (BlockOperator.family U ψ)) := by
  rw [associate_family]
  exact supported_indexed hU hψ

/-- Point and direction registers may be in arbitrary coherent superposition. -/
theorem ordinaryTwoSided_supported (encode : Encoding N w) {t : ℕ}
    {ψ : EuclideanSpace ℂ ((Bool × Fin N) × (Bits w × Database N))}
    (hψ : Supported t (associate ψ)) :
    Supported (t + 1) (associate (CompressedQuery.ordinaryTwoSided encode ψ)) := by
  apply family_supported _ ?_ hψ
  intro bx φ hφ
  cases bx.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ordinary_supported encode bx.2 hφ
  · simp only [↓reduceIte]
    exact inverseOrdinary_supported encode bx.2 hφ

theorem markedTwoSided_supported (encode : Encoding N w) {t : ℕ}
    {ψ : EuclideanSpace ℂ ((Bool × Fin N) × ((Bool × Bits w) × Database N))}
    (hψ : Supported t (associate ψ)) :
    Supported (t + 1) (associate (CompressedQuery.markedTwoSided encode ψ)) := by
  apply family_supported _ ?_ hψ
  intro bx φ hφ
  cases bx.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact marked_supported encode bx.2 hφ
  · simp only [↓reduceIte]
    exact inverseMarked_supported encode bx.2 hφ

/-- Coherent on/off control preserves any proved one-query support bound. -/
theorem controlled_supported
    (U : State Y N ≃ₗᵢ[ℂ] State Y N) {t : ℕ}
    (hU : ∀ φ, Supported t φ → Supported (t + 1) (U φ))
    {ψ : EuclideanSpace ℂ (Bool × (Y × Database N))}
    (hψ : Supported t (associate ψ)) :
    Supported (t + 1) (associate (CompressedQuery.controlled U ψ)) := by
  apply family_supported _ ?_ hψ
  intro b φ hφ
  cases b
  · exact supported_mono (Nat.le_succ t) hφ
  · exact hU φ hφ

theorem controlledOrdinary_supported (encode : Encoding N w) (x : Fin N) {t : ℕ}
    {ψ : EuclideanSpace ℂ (Bool × (Bits w × Database N))}
    (hψ : Supported t (associate ψ)) :
    Supported (t + 1)
      (associate (CompressedQuery.controlled (CompressedQuery.ordinary encode x) ψ)) :=
  controlled_supported _ (fun _ h => ordinary_supported encode x h) hψ

theorem controlledMarked_supported (encode : Encoding N w) (x : Fin N) {t : ℕ}
    {ψ : EuclideanSpace ℂ (Bool × ((Bool × Bits w) × Database N))}
    (hψ : Supported t (associate ψ)) :
    Supported (t + 1)
      (associate (CompressedQuery.controlled (CompressedQuery.marked encode x) ψ)) :=
  controlled_supported _ (fun _ h => marked_supported encode x h) hψ

/-- Coordinate association for an additional coherent on/off control. -/
def associateControlled
    (ψ : EuclideanSpace ℂ (Bool × (C × (Y × Database N)))) :
    State ((Bool × C) × Y) N :=
  WithLp.toLp 2 (fun p => ψ (p.1.1.1, (p.1.1.2, (p.1.2, p.2))))

theorem controlled_grouped_supported
    (U : EuclideanSpace ℂ (C × (Y × Database N)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (C × (Y × Database N))) {t : ℕ}
    (hU : ∀ φ, Supported t (associate φ) → Supported (t + 1) (associate (U φ)))
    {ψ : EuclideanSpace ℂ (Bool × (C × (Y × Database N)))}
    (hψ : Supported t (associateControlled ψ)) :
    Supported (t + 1) (associateControlled (CompressedQuery.controlled U ψ)) := by
  rintro ⟨⟨b, c⟩, y⟩ I hI
  let φ : EuclideanSpace ℂ (C × (Y × Database N)) :=
    WithLp.toLp 2 (fun z => ψ (b, z))
  have hφ : Supported t (associate φ) := by
    intro cY K hK
    exact hψ ((b, cY.1), cY.2) K hK
  change (if b then U else LinearIsometryEquiv.refl ℂ _) φ (c, (y, I)) = 0
  cases b
  · exact supported_mono (Nat.le_succ t) hφ (c, y) I hI
  · exact hU φ hφ (c, y) I hI

/-- Arbitrary coherent point, direction, and on/off-control registers together. -/
theorem controlledOrdinaryTwoSided_supported (encode : Encoding N w) {t : ℕ}
    {ψ : EuclideanSpace ℂ (Bool × ((Bool × Fin N) × (Bits w × Database N)))}
    (hψ : Supported t (associateControlled ψ)) :
    Supported (t + 1) (associateControlled
      (CompressedQuery.controlled (CompressedQuery.ordinaryTwoSided encode) ψ)) :=
  controlled_grouped_supported _ (fun _ h => ordinaryTwoSided_supported encode h) hψ

theorem controlledMarkedTwoSided_supported (encode : Encoding N w) {t : ℕ}
    {ψ : EuclideanSpace ℂ (Bool × ((Bool × Fin N) × ((Bool × Bits w) × Database N)))}
    (hψ : Supported t (associateControlled ψ)) :
    Supported (t + 1) (associateControlled
      (CompressedQuery.controlled (CompressedQuery.markedTwoSided encode) ψ)) :=
  controlled_grouped_supported _ (fun _ h => markedTwoSided_supported encode h) hψ

end Coherent

end QuantumOracle.CompressedSupport
