import QuantumOracle.Model.HarmonicLayers
import QuantumOracle.Proof.ResidualKnowledge

/-!
# Two adjacent residual harmonic degrees

The geometry uses the actual consistency-space filtration and orthogonal
complements. No representation-theoretic branching rule is assumed.
-/

noncomputable section

namespace QuantumOracle.ResidualLayers

open PermutationExtensions HarmonicLayers KnowledgeSpace
open scoped InnerProductSpace

attribute [local irreducible] HarmonicLayers.H KnowledgeSpace.K

/-- Inside a valid filtration level, orthogonality two levels below leaves
exactly the two adjacent orthogonal increments. -/
theorem mem_two_layers_of_mem_K {N s : ℕ} (hs : s + 2 ≤ N)
    {v : EuclideanSpace ℂ (Perm N)} (hv : v ∈ K N (s + 2))
    (horth : v ∈ (K N s)ᗮ) : v ∈ H N (s + 1) ⊔ H N (s + 2) := by
  have hs' : s + 1 < N := by omega
  rw [show s + 2 = (s + 1) + 1 by omega, K_succ_eq_sup hs'] at hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have hborth : b ∈ (K N s)ᗮ :=
    Submodule.orthogonal_le (KnowledgeSpace.mono (Nat.le_succ s) (by omega))
      (H_succ_le_orthogonal N (s + 1) hb)
  have haorth : a ∈ (K N s)ᗮ := by
    simpa only [add_sub_cancel_right] using (K N s)ᗮ.sub_mem horth hborth
  apply Submodule.mem_sup.mpr
  refine ⟨a, ?_, b, hb, rfl⟩
  rw [H_succ]
  exact ⟨ha, haorth⟩

/-- Saturation of the residual space at its full level also covers the last
possible input degree, where only the lower of the two residual layers remains. -/
theorem mem_two_layers_of_mem_K_min {N s : ℕ} (hs : s + 1 ≤ N)
    {v : EuclideanSpace ℂ (Perm N)} (hv : v ∈ K N (min (s + 2) N))
    (horth : v ∈ (K N s)ᗮ) : v ∈ H N (s + 1) ⊔ H N (s + 2) := by
  by_cases htop : s + 2 ≤ N
  · apply mem_two_layers_of_mem_K htop
    · simpa only [min_eq_left htop] using hv
    · exact horth
  · have hN : N = s + 1 := by omega
    apply (show H N (s + 1) ≤ H N (s + 1) ⊔ H N (s + 2) from le_sup_left)
    rw [H_succ]
    refine ⟨?_, horth⟩
    change v ∈ K N (s + 1)
    have hmin : min (s + 2) N = s + 1 := by omega
    simpa only [hmin] using hv

/-- At degree one there is no lower orthogonality condition. -/
theorem knowledge_one_le_two_layers (N : ℕ) :
    K N (min 1 N) ≤ H N 0 ⊔ H N 1 := by
  by_cases hN : 0 < N
  · rw [min_eq_left hN, H_zero, K_succ_eq_sup hN]
  · have hNzero : N = 0 := by omega
    rw [hNzero, Nat.min_zero, H_zero]
    exact le_sup_left

/-- Restricting the actual degree-zero subspace stays in residual degree zero. -/
theorem restrict_mem_zero {N : ℕ} (x y : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) 0) :
    ResidualAdjoint.restrict x y h ∈ H N 0 := by
  rw [H_zero] at hh ⊢
  simpa only [Nat.zero_min] using ResidualKnowledge.restrict_mem_K x y hh

/-- Actual answer restriction has only the two adjacent residual harmonic
degrees. This includes the terminal degree and the zero out-of-range spaces. -/
theorem restrict_mem_two_layers {N t : ℕ} (x y : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (ht : 0 < t) (hh : h ∈ H (N + 1) t) :
    ResidualAdjoint.restrict x y h ∈ H N (t - 1) ⊔ H N t := by
  by_cases hbound : t ≤ N + 1
  · have hupper := ResidualKnowledge.restrict_mem_K x y (H_le_K (N + 1) t hh)
    cases t with
    | zero => omega
    | succ t =>
      cases t with
      | zero => exact knowledge_one_le_two_layers N hupper
      | succ s =>
        change ResidualAdjoint.restrict x y h ∈ H N (s + 1) ⊔ H N (s + 2)
        apply mem_two_layers_of_mem_K_min (by omega) hupper
        exact ResidualAdjoint.restrict_mem_orthogonal x y h
          (H_succ_le_orthogonal (N + 1) (s + 1) hh)
  · have hz : h = 0 := by
      simpa only [H_eq_bot_of_gt (Nat.lt_of_not_ge hbound), Submodule.mem_bot] using hh
    rw [hz, map_zero]
    exact Submodule.zero_mem _

theorem restrict_decomposition {N t : ℕ} (x y : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (ht : 0 < t) (hh : h ∈ H (N + 1) t) :
    ∃ a ∈ H N (t - 1), ∃ b ∈ H N t, a + b = ResidualAdjoint.restrict x y h :=
  Submodule.mem_sup.mp (restrict_mem_two_layers x y ht hh)

end QuantumOracle.ResidualLayers
