import Max2SAT.Random.SupportAveraging

namespace Max2SAT.Random
noncomputable section

theorem nodes_le_input_candidates (F : Formula n) :
    (nodeCount F:ℝ)≤(2:ℝ)^((n+1)/2+1)+2*n*(candidateCount F:ℝ) := by
  have ha : (active F).card≤n := by simpa using Finset.card_le_univ (active F)
  have he : ((active F).card+1)/2+1≤(n+1)/2+1 := by omega
  have hp := Nat.pow_le_pow_right (by omega : 0<2) he
  have h := (nodes_le_candidates F).trans (Nat.add_le_add
    ((Nat.sub_le _ _).trans hp) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 ha)))
  exact_mod_cast h

end
end Max2SAT.Random

namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

theorem all_support_search_expectation (p : E → PairLaw m κ)
    (hm : 0<m) (hk : 0<κ) (hκ : κ≤(m:ℝ)^2) (units : List (Literal n)) :
    expect (product (fun e => (p e).law)) (fun K => (Random.nodeCount (generate E K units):ℝ))≤
      (2:ℝ)^((n+1)/2+1)+6*n*(2:ℝ)^n*Real.exp (-runtimeConstant m κ*n) := by
  have h := Random.expected_nodes_of_candidates (product (fun e => (p e).law))
    (fun K => generate E K units) n
    (fun K => by simpa using Finset.card_le_univ (Random.active (generate E K units)))
    _ (all_support_candidate_expectation p hm hk hκ units)
  convert h using 1
  ring

theorem all_support_search_tail (p : E → PairLaw m κ)
    (hm : 0<m) (hk : 0<κ) (hκ : κ≤(m:ℝ)^2) (units : List (Literal n)) :
    prob (product (fun e => (p e).law)) (fun K =>
      (2:ℝ)^((n+1)/2+1)+2*n*(2:ℝ)^n*Real.exp (-runtimeConstant m κ*n/2)<
        (Random.nodeCount (generate E K units):ℝ))≤
      3*Real.exp (-runtimeConstant m κ*n/2) := by
  apply (prob_mono_support (product (fun e => (p e).law)) _
    (fun K => (2:ℝ)^n*Real.exp (-runtimeConstant m κ*n/2)<
      (Random.candidateCount (generate E K units):ℝ)) ?_).trans
  · exact all_support_candidate_tail p hm hk hκ units
  · intro K _ hbad
    have hn := Random.nodes_le_input_candidates (generate E K units)
    by_contra hc
    have h := mul_le_mul_of_nonneg_left (le_of_not_gt hc) (show (0:ℝ)≤2*n by positivity)
    nlinarith

theorem prefix_absorbed (c : ℝ) (hc : c≤Real.log 2/2) (N : ℕ) :
    (2:ℝ)^((N+1)/2+1)≤4*(2:ℝ)^N*Real.exp (-c*N) := by
  have he : Counts.exponent (1/2) c=Real.log 2-c := by
    unfold Counts.exponent
    apply max_eq_right
    linarith
  have hb : (Counts.exponentialBase (1/2) c)^N=(2:ℝ)^N*Real.exp (-c*N) := by
    rw [Counts.exponentialBase,he,←Real.exp_nat_mul,count_decay_identity]
    congr 1
    ring
  have h := (prefix_candidate_rate N c).1
  rw [hb] at h
  simpa only [mul_assoc] using h

/-- The paper's complete arbitrary-support expected node bound. All
conditioning, active-label and count estimates have been discharged. -/
theorem random_sign_expected_nodes (p : E → PairLaw m κ)
    (hm : 0<m) (hk : 0<κ) (hκ : κ≤(m:ℝ)^2) (units : List (Literal n)) :
    expect (product (fun e => (p e).law)) (fun K => (Random.nodeCount (generate E K units):ℝ))≤
      (4+6*n)*(2:ℝ)^n*Real.exp (-runtimeConstant m κ*n) := by
  have h := all_support_search_expectation p hm hk hκ units
  have hp := prefix_absorbed (runtimeConstant m κ) (runtime_constant_small hm hk hκ).2.le n
  nlinarith

/-- The stated exponential failure probability, for the actual search on
the original labels. The threshold includes all rejected calls. -/
theorem random_sign_nodes_tail (p : E → PairLaw m κ)
    (hm : 0<m) (hk : 0<κ) (hκ : κ≤(m:ℝ)^2) (units : List (Literal n)) :
    prob (product (fun e => (p e).law)) (fun K =>
      (4+2*n)*(2:ℝ)^n*Real.exp (-runtimeConstant m κ*n/2)<
        (Random.nodeCount (generate E K units):ℝ))≤
      3*Real.exp (-runtimeConstant m κ*n/2) := by
  have hs := runtime_constant_small hm hk hκ
  have hc : runtimeConstant m κ/2≤Real.log 2/2 := by linarith
  have hp := prefix_absorbed (runtimeConstant m κ/2) hc n
  rw [show -(runtimeConstant m κ/2)*(n:ℝ)= -runtimeConstant m κ*n/2 by ring] at hp
  apply (prob_mono_support (product (fun e => (p e).law)) _
    (fun K => (2:ℝ)^((n+1)/2+1)+2*n*(2:ℝ)^n*Real.exp (-runtimeConstant m κ*n/2)<
      (Random.nodeCount (generate E K units):ℝ)) ?_).trans
  · exact all_support_search_tail p hm hk hκ units
  · intro K _ hbad
    nlinarith

theorem random_sign_base_lt_two (hm : 0<m) (hk : 0<κ) :
    2*Real.exp (-runtimeConstant m κ)<2 := by
  have h := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (runtime_constant_pos hm hk))
  linarith

end
end Max2SAT.RandomInput
