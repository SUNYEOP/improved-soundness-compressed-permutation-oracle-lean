import QuantumOracle.Proof.TailBranching

/-! # The two actual corner-branching cases

Removing a corner either shortens the first row and leaves the tail unchanged,
or preserves the first row and removes one actual corner of the tail. The
corresponding quotients of actual normalized row products satisfy the sparse
degree estimates, without any eigenvalue or overlap hypothesis.
-/

noncomputable section

namespace QuantumOracle.YoungBranchCases

open SpechtFoundation HookRowFactorization HookRatioProducts HookRatioBounds
open AtlasKnownTheorems.HookLengthFormula
open scoped BigOperators Classical

theorem tail_eq_of_erase_firstRow {mu nu : YoungDiagram} {p : ℕ × ℕ}
    (hp : p.1 = 0) (hc : nu.cells = mu.cells.erase p) : tail nu = tail mu := by
  ext q
  simp only [YoungDiagram.mem_cells, mem_tail]
  change shiftRow q ∈ nu.cells ↔ shiftRow q ∈ mu.cells
  rw [hc, Finset.mem_erase]
  have hne : shiftRow q ≠ p := by
    intro he
    have := congrArg Prod.fst he
    change q.1 + 1 = p.1 at this
    omega
  exact and_iff_right hne

theorem rowLen_eq_of_erase_below {mu nu : YoungDiagram} {p : ℕ × ℕ}
    (hp : p.1 ≠ 0) (hc : nu.cells = mu.cells.erase p) :
    nu.rowLen 0 = mu.rowLen 0 := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, ← YoungDiagram.mem_iff_lt_rowLen]
  change (0, j) ∈ nu.cells ↔ (0, j) ∈ mu.cells
  rw [hc, Finset.mem_erase]
  have hne : (0, j) ≠ p := by
    intro he
    exact hp (congrArg Prod.fst he).symm
  exact and_iff_right hne

/-- This is the exact corner classification; no sparsity assumption is needed. -/
theorem branching_cases {N : ℕ} (la : Nat.Partition (N + 1))
    (mu : Nat.Partition N) (hmu : mu ∈ removeCorners la) :
    ((diagram mu).rowLen 0 + 1 = (diagram la).rowLen 0 ∧
      tail (diagram mu) = tail (diagram la)) ∨
    ((diagram mu).rowLen 0 = (diagram la).rowLen 0 ∧
      ∃ c : CornerCells (tail (diagram la)),
        tail (diagram mu) = eraseCorner (tail (diagram la)) c.1 c.2) := by
  obtain ⟨c, hc⟩ := TailBranching.exists_erased_corner
    ((mem_removeCorners mu la).mp hmu)
    (by rw [SpechtHookBridge.diagram_card, SpechtHookBridge.diagram_card])
  by_cases hrow : c.1.val.1 = 0
  · left
    have ht := tail_eq_of_erase_firstRow hrow hc
    refine ⟨?_, ht⟩
    have hla := card_eq_firstRow_add_tail (diagram la)
    have hmu := card_eq_firstRow_add_tail (diagram mu)
    rw [SpechtHookBridge.diagram_card] at hla hmu
    rw [ht] at hmu
    omega
  · right
    have hr := rowLen_eq_of_erase_below hrow hc
    refine ⟨hr, ?_⟩
    obtain ⟨d, hd⟩ := TailBranching.removeTailCorner_surjective la mu hmu hr
    refine ⟨d, ?_⟩
    rw [← hd, TailBranching.tail_removeTailCorner]

theorem firstRow_case_of_ne {N : ℕ} (la : Nat.Partition (N + 1))
    (mu : Nat.Partition N) (hmu : mu ∈ removeCorners la)
    (hne : (diagram mu).rowLen 0 ≠ (diagram la).rowLen 0) :
    (diagram mu).rowLen 0 = (diagram la).rowLen 0 - 1 ∧
      tail (diagram mu) = tail (diagram la) := by
  rcases branching_cases la mu hmu with ⟨hr, ht⟩ | ⟨hr, _⟩
  · exact ⟨by omega, ht⟩
  · exact False.elim (hne hr)

theorem tail_case_of_eq {N : ℕ} (la : Nat.Partition (N + 1))
    (mu : Nat.Partition N) (hmu : mu ∈ removeCorners la)
    (heq : (diagram mu).rowLen 0 = (diagram la).rowLen 0) :
    ∃ c : CornerCells (tail (diagram la)),
      tail (diagram mu) = eraseCorner (tail (diagram la)) c.1 c.2 := by
  rcases branching_cases la mu hmu with ⟨hr, _⟩ | ⟨_, hc⟩
  · omega
  · exact hc

theorem firstRow_product_ratio {N : ℕ} (la : Nat.Partition (N + 1))
    (mu : Nat.Partition N) (hmu : mu ∈ removeCorners la)
    (ha : (tail (diagram la)).card < (diagram la).rowLen 0)
    (hne : (diagram mu).rowLen 0 ≠ (diagram la).rowLen 0) :
    normalizedRowProduct ((diagram la).rowLen 0) (tail (diagram la)) /
        normalizedRowProduct ((diagram mu).rowLen 0) (tail (diagram mu)) =
      firstRowRatioSq ((diagram la).rowLen 0) (tail (diagram la)) := by
  obtain ⟨hr, ht⟩ := firstRow_case_of_ne la mu hmu hne
  rw [hr, ht]
  exact normalizedRowProduct_firstRow_ratio _ _ ha

theorem tail_product_ratio {N : ℕ} (la : Nat.Partition (N + 1))
    (mu : Nat.Partition N) (hmu : mu ∈ removeCorners la)
    (ha : (tail (diagram la)).card < (diagram la).rowLen 0)
    (heq : (diagram mu).rowLen 0 = (diagram la).rowLen 0) :
    ∃ c : CornerCells (tail (diagram la)),
      tail (diagram mu) = eraseCorner (tail (diagram la)) c.1 c.2 ∧
      normalizedRowProduct ((diagram mu).rowLen 0) (tail (diagram mu)) /
          normalizedRowProduct ((diagram la).rowLen 0) (tail (diagram la)) =
        tailCornerRatioSq ((diagram la).rowLen 0) (tail (diagram la)) c := by
  obtain ⟨c, hc⟩ := tail_case_of_eq la mu hmu heq
  refine ⟨c, hc, ?_⟩
  rw [heq, hc]
  exact normalizedRowProduct_tailCorner_ratio _ _ ha c

/-- The quotient orientation specified by which actual row the branch removes. -/
def branchRatio {N : ℕ} (la : Nat.Partition (N + 1)) (mu : Nat.Partition N) : ℝ :=
  if (diagram mu).rowLen 0 = (diagram la).rowLen 0 then
    normalizedRowProduct ((diagram mu).rowLen 0) (tail (diagram mu)) /
      normalizedRowProduct ((diagram la).rowLen 0) (tail (diagram la))
  else
    normalizedRowProduct ((diagram la).rowLen 0) (tail (diagram la)) /
      normalizedRowProduct ((diagram mu).rowLen 0) (tail (diagram mu))

theorem branchRatio_pos {N : ℕ} (la : Nat.Partition (N + 1))
    (mu : Nat.Partition N) : 0 < branchRatio la mu := by
  have hla := normalizedRowProduct_pos _ _ (tail_rowLen_le (diagram la))
  have hmu := normalizedRowProduct_pos _ _ (tail_rowLen_le (diagram mu))
  unfold branchRatio
  split <;> exact div_pos (by assumption) (by assumption)

/-- The two manuscript scalar estimates applied to actual partition branches. -/
theorem branchRatio_deficit_le_two_div {N : ℕ} (la : Nat.Partition (N + 1))
    (mu : Nat.Partition N) (hmu : mu ∈ removeCorners la)
    (hsparse : 4 * (tail (diagram la)).card ≤ N + 1) :
    1 - branchRatio la mu ≤ 2 / ((N + 1 : ℕ) : ℝ) := by
  have hcard := card_eq_firstRow_add_tail (diagram la)
  rw [SpechtHookBridge.diagram_card] at hcard
  have hr : (diagram la).rowLen 0 = N + 1 - (tail (diagram la)).card := by omega
  unfold branchRatio
  split
  · rename_i heq
    obtain ⟨c, hc⟩ := tail_case_of_eq la mu hmu heq
    rw [heq, hc, hr]
    exact tailCorner_quotient_deficit_le_two_div _ (by omega) hsparse c
  · rename_i hne
    obtain ⟨hm, ht⟩ := firstRow_case_of_ne la mu hmu hne
    rw [hm, ht, hr]
    exact firstRow_quotient_deficit_le_two_div _ (by omega) hsparse

end QuantumOracle.YoungBranchCases
