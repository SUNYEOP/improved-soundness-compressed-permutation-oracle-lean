import QuantumOracle.Proof.HookRowFactorization
import QuantumOracle.Proof.SpechtHookBridge

/-! # Corner branching below the first row

Actual partitions obtained by removing a corner while preserving the first row
are in bijection with removable corners of the actual tail diagram.
-/

noncomputable section

namespace QuantumOracle.TailBranching

open SpechtFoundation HookRowFactorization
open AtlasKnownTheorems.HookLengthFormula
open scoped BigOperators Classical

private abbrev CS := RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellPredicate

theorem diagram_injective (N : ℕ) : Function.Injective (diagram (N := N)) := by
  intro la mu h
  have hp (nu : Nat.Partition N) : (diagram nu).rowLens = nu.parts.sort (· ≥ ·) := by
    apply YoungDiagram.rowLens_ofRowLens_eq_self
    intro x hx
    exact nu.parts_pos (by simpa only [Multiset.mem_sort] using hx)
  have hh := congrArg YoungDiagram.rowLens h
  rw [hp la, hp mu] at hh
  apply Nat.Partition.ext
  simpa only [Multiset.sort_eq] using congrArg (fun l : List ℕ => (l : Multiset ℕ)) hh

/-- A corner of the tail is an actual corner one row lower in the full diagram. -/
theorem tail_corner_shift (mu : YoungDiagram) (c : CornerCells (tail mu)) :
    CS mu (c.1.val.1 + 1) c.1.val.2 := by
  refine ⟨(mem_tail mu c.1.val).mp c.1.property, ?_, ?_⟩
  · intro hm
    have hd : (c.1.val.1 + 1, c.1.val.2) ∈ (tail mu).cells :=
      (mem_tail mu _).mpr hm
    have he := c.2 ⟨_, hd⟩ (by exact ⟨Nat.le_succ _, le_rfl⟩)
    have := congrArg (fun d : Cell (tail mu) => d.val.1) he
    dsimp at this
    omega
  · intro hm
    have hd : (c.1.val.1, c.1.val.2 + 1) ∈ (tail mu).cells :=
      (mem_tail mu _).mpr hm
    have he := c.2 ⟨_, hd⟩ (by exact ⟨le_rfl, Nat.le_succ _⟩)
    have := congrArg (fun d : Cell (tail mu) => d.val.2) he
    dsimp at this
    omega

/-- Delete the shifted tail corner using the concrete partition constructor. -/
def removeTailCorner {N : ℕ} (mu : Nat.Partition (N + 1))
    (c : CornerCells (tail (diagram mu))) : Nat.Partition N :=
  RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.auxiliaryAtOuterCorner
    mu (shiftRow c.1.val) (tail_corner_shift (diagram mu) c)

theorem removeTailCorner_cells {N : ℕ} (mu : Nat.Partition (N + 1))
    (c : CornerCells (tail (diagram mu))) :
    (diagram (removeTailCorner mu c)).cells = (diagram mu).cells.erase (shiftRow c.1.val) := by
  exact congrArg YoungDiagram.cells
    (RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.toYoungDiagram_auxiliaryAtOuterCorner
      mu (shiftRow c.1.val) (tail_corner_shift (diagram mu) c))

theorem removeTailCorner_mem {N : ℕ} (mu : Nat.Partition (N + 1))
    (c : CornerCells (tail (diagram mu))) : removeTailCorner mu c ∈ removeCorners mu := by
  apply (mem_removeCorners _ _).mpr
  intro p hp
  change p ∈ (diagram (removeTailCorner mu c)).cells at hp
  rw [removeTailCorner_cells] at hp
  exact (Finset.mem_erase.mp hp).2

theorem removeTailCorner_rowLen {N : ℕ} (mu : Nat.Partition (N + 1))
    (c : CornerCells (tail (diagram mu))) :
    (diagram (removeTailCorner mu c)).rowLen 0 = (diagram mu).rowLen 0 := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, ← YoungDiagram.mem_iff_lt_rowLen]
  change (0,j) ∈ (diagram (removeTailCorner mu c)).cells ↔ (0,j) ∈ (diagram mu).cells
  rw [removeTailCorner_cells, Finset.mem_erase]
  simp [shiftRow]

theorem tail_removeTailCorner {N : ℕ} (mu : Nat.Partition (N + 1))
    (c : CornerCells (tail (diagram mu))) :
    tail (diagram (removeTailCorner mu c)) = eraseCorner (tail (diagram mu)) c.1 c.2 := by
  ext p
  simp only [YoungDiagram.mem_cells, mem_tail]
  change shiftRow p ∈ (diagram (removeTailCorner mu c)).cells ↔ _
  rw [removeTailCorner_cells, Finset.mem_erase]
  change (shiftRow p ≠ shiftRow c.1.val ∧ shiftRow p ∈ diagram mu) ↔
    p ∈ (eraseCorner (tail (diagram mu)) c.1 c.2).cells
  rw [eraseCorner_cells, Finset.mem_erase]
  change (shiftRow p ≠ shiftRow c.1.val ∧ shiftRow p ∈ diagram mu) ↔
    (p ≠ c.1.val ∧ p ∈ tail (diagram mu))
  rw [mem_tail]
  exact and_congr shiftRow.injective.ne_iff Iff.rfl

theorem removeTailCorner_injective {N : ℕ} (mu : Nat.Partition (N + 1)) :
    Function.Injective (removeTailCorner mu) := by
  intro c d he
  have hh := congrArg (fun la : Nat.Partition N => (diagram la).cells) he
  rw [removeTailCorner_cells, removeTailCorner_cells] at hh
  have hcd := (Finset.erase_inj _ ((mem_tail _ _).mp c.1.property)).mp hh
  exact Subtype.ext (Subtype.ext (shiftRow.injective hcd))

/-- Containment with a one-cell cardinality difference removes one actual corner. -/
theorem exists_erased_corner {mu nu : YoungDiagram} (hle : nu ≤ mu)
    (hcard : nu.card + 1 = mu.card) :
    ∃ c : CornerCells mu, nu.cells = mu.cells.erase c.1.val := by
  have hsub : nu.cells ⊆ mu.cells := hle
  have hdiff : (mu.cells \ nu.cells).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub]
    change mu.card - nu.card = 1
    omega
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hdiff
  have hp' : p ∈ mu.cells ∧ p ∉ nu.cells := by
    apply Finset.mem_sdiff.mp
    rw [hp]
    exact Finset.mem_singleton_self p
  have hmem {q : ℕ × ℕ} (hq : q ∈ mu.cells) (hne : q ≠ p) : q ∈ nu.cells := by
    by_contra hn
    have hd := Finset.mem_sdiff.mpr ⟨hq, hn⟩
    rw [hp, Finset.mem_singleton] at hd
    exact hne hd
  have hc : IsCornerCell mu ⟨p, hp'.1⟩ := by
    intro d hd
    apply Subtype.ext
    by_contra hne
    exact hp'.2 (nu.isLowerSet hd (hmem d.property hne))
  refine ⟨⟨⟨p, hp'.1⟩, hc⟩, ?_⟩
  ext q
  simp only [Finset.mem_erase]
  constructor
  · intro hq
    exact ⟨fun he => hp'.2 (he ▸ hq), hsub hq⟩
  · rintro ⟨hne, hq⟩
    exact hmem hq hne

/-- Every corner deletion preserving the first row deletes a shifted tail corner. -/
theorem removeTailCorner_surjective {N : ℕ} (mu : Nat.Partition (N + 1))
    (la : Nat.Partition N) (hla : la ∈ removeCorners mu)
    (hrow : (diagram la).rowLen 0 = (diagram mu).rowLen 0) :
    ∃ c : CornerCells (tail (diagram mu)), removeTailCorner mu c = la := by
  obtain ⟨d, hd⟩ := exists_erased_corner ((mem_removeCorners la mu).mp hla)
    (by rw [SpechtHookBridge.diagram_card, SpechtHookBridge.diagram_card])
  have hnot : d.1.val ∉ (diagram la).cells := by
    rw [hd]
    exact Finset.notMem_erase _ _
  have hrowpos : d.1.val.1 ≠ 0 := by
    intro hz
    apply hnot
    apply YoungDiagram.mem_iff_lt_rowLen.mpr
    rw [hz, hrow]
    have hh := YoungDiagram.mem_iff_lt_rowLen.mp d.1.property
    simpa only [hz] using hh
  let p : ℕ × ℕ := (d.1.val.1 - 1, d.1.val.2)
  have hshift : shiftRow p = d.1.val := by
    apply Prod.ext
    · change d.1.val.1 - 1 + 1 = d.1.val.1
      omega
    · rfl
  have hp : p ∈ (tail (diagram mu)).cells := by
    rw [YoungDiagram.mem_cells, mem_tail, hshift]
    exact d.1.property
  have hc : IsCornerCell (tail (diagram mu)) ⟨p, hp⟩ := by
    intro e he
    have hem := (mem_tail _ _).mp e.property
    have heq := d.2 ⟨shiftRow e.val, hem⟩ (by
      change d.1.val.1 ≤ (shiftRow e.val).1 ∧ d.1.val.2 ≤ (shiftRow e.val).2
      rw [← hshift]
      exact ⟨Nat.add_le_add_right he.1 1, he.2⟩)
    apply Subtype.ext
    apply shiftRow.injective
    exact (congrArg Subtype.val heq).trans hshift.symm
  refine ⟨⟨⟨p, hp⟩, hc⟩, diagram_injective N ?_⟩
  apply YoungDiagram.ext
  rw [removeTailCorner_cells, hshift, hd]

/-- Reindex corner branching through the actual tail diagram. -/
theorem sum_preserving_firstRow {N : ℕ} (mu : Nat.Partition (N + 1))
    {M : Type*} [AddCommMonoid M] (f : YoungDiagram → M) :
    (∑ la ∈ (removeCorners mu).filter
        (fun la => (diagram la).rowLen 0 = (diagram mu).rowLen 0),
      f (tail (diagram la))) =
    ∑ c : CornerCells (tail (diagram mu)), f (eraseCorner (tail (diagram mu)) c.1 c.2) := by
  symm
  apply Finset.sum_bij (fun c _ => removeTailCorner mu c)
  · intro c _
    exact Finset.mem_filter.mpr ⟨removeTailCorner_mem mu c, removeTailCorner_rowLen mu c⟩
  · intro c _ d _ he
    exact removeTailCorner_injective mu he
  · intro la hla
    obtain ⟨hm, hr⟩ := Finset.mem_filter.mp hla
    obtain ⟨c, hc⟩ := removeTailCorner_surjective mu la hm hr
    exact ⟨c, Finset.mem_univ _, hc⟩
  · intro c _
    rw [tail_removeTailCorner]

end QuantumOracle.TailBranching
