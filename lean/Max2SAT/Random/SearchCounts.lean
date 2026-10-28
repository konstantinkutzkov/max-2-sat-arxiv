import Max2SAT.Random.PathBudget
import Max2SAT.Random.CandidateProbability

/-! Output counts are upper-bounded by the comparisons constructed on full
paths, including paths rejected before the stopping depth. -/
namespace Max2SAT.Random
noncomputable section
attribute [local instance] Classical.propDecidable

def pathCandidates (F : Formula n) (w : Fin n → ℚ) (suffix pre : List (Fin n))
    (base : Assignment n) : Finset (Assignment n) :=
  Finset.univ.filter (fun y => Compatible (pre++suffix).toFinset base y ∧
    pathExcess F w suffix pre y≤0)

theorem enumerate_length_le_candidates (F : Formula n) (w : Fin n → ℚ)
    (suffix pre : List (Fin n)) (base : Assignment n) (hn : (pre++suffix).Nodup) :
    (enumerate F w suffix pre base []).length≤(pathCandidates F w suffix pre base).card := by
  rw [←List.toFinset_card_of_nodup (enumerate_nodup F w suffix pre base [] hn)]
  apply Finset.card_le_card
  intro y hy
  have hm := List.mem_toFinset.mp hy
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,output_compatible F w suffix pre base y [] hn hm,?_⟩
  have h := output_path_budget F w suffix pre base y [] hn hm
  simpa [Weighted.sum,Weighted.Budget.lhs] using h

def candidateCount (F : Formula n) : ℕ :=
  let U := Bias.ordered (active F)
  (pathCandidates (preprocess (core F)).1 (weight F) (U.drop ((U.length+1)/2))
    (U.take ((U.length+1)/2)) (initial F)).card

theorem outputs_le_candidates (F : Formula n) : (outputs F).length≤candidateCount F := by
  apply enumerate_length_le_candidates
  simpa using Bias.ordered_nodup (active F)

theorem nodes_le_candidates (F : Formula n) :
    nodeCount F≤2^(((active F).card+1)/2+1)-1+2*(active F).card*candidateCount F := by
  apply (nodeCount_bound F).trans
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (outputs_le_candidates F)) _

/-- Counts and initialization are present in the node model. The analytic
candidate expectation is still explicit here and discharged separately. -/
theorem expected_nodes_of_candidates {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw.Law Ω) (F : Ω → Formula n) (r : ℕ) (hactive : ∀ z, (active (F z)).card≤r)
    (B : ℝ) (hB : FiniteLaw.expect p (fun z => (candidateCount (F z):ℝ))≤B) :
    FiniteLaw.expect p (fun z => (nodeCount (F z):ℝ))≤
      (2:ℝ)^((r+1)/2+1)+2*r*B := by
  have hp : ∀ z, (nodeCount (F z):ℝ)≤
      (2:ℝ)^((r+1)/2+1)+2*r*(candidateCount (F z):ℝ) := by
    intro z
    have h := (nodes_le_candidates (F z)).trans
      (Nat.add_le_add (Nat.sub_le _ _) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (hactive z))))
    have he : ((active (F z)).card+1)/2+1≤(r+1)/2+1 := by
      have hh := hactive z; omega
    have hpow := Nat.pow_le_pow_right (by omega : 0<2) he
    exact_mod_cast h.trans (Nat.add_le_add_right hpow _)
  apply (FiniteLaw.expect_mono p hp).trans
  have he : FiniteLaw.expect p (fun z =>
      (2:ℝ)^((r+1)/2+1)+2*r*(candidateCount (F z):ℝ)) =
      (2:ℝ)^((r+1)/2+1)+2*r*FiniteLaw.expect p (fun z => (candidateCount (F z):ℝ)) := by
    rw [FiniteLaw.expect_add,FiniteLaw.expect_const]
    simp only [FiniteLaw.expect,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [he]
  gcongr

end
end Max2SAT.Random
