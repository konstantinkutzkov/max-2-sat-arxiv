import Max2SAT.Random.ObservedPartition

namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

theorem runtime_constant_small (hm : 0<m) (hk : 0<κ) (hκ : κ≤(m:ℝ)^2) :
    0<runtimeConstant m κ ∧ runtimeConstant m κ<Real.log 2/2 := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hc := requirement_constant_pos hm hk
  have hb := requirement_constant_bound hm hk
  have hdiv : κ/(4*(m:ℝ))≤(m:ℝ)/4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hs : runtimeConstant m κ≤1/173056 := by
    unfold runtimeConstant
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := hb.trans hdiv
    nlinarith
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hl
  exact ⟨runtime_constant_pos hm hk,by linarith⟩

theorem count_decay_identity (c : ℝ) (r : ℕ) :
    (2:ℝ)^r*Real.exp (-c*r)=Real.exp ((Real.log 2-c)*r) := by
  have ht : (2:ℝ)=Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
  rw [ht,←Real.exp_nat_mul,←Real.exp_add]
  simp only [Real.log_exp]
  congr 1
  ring

theorem count_decay_mono (c : ℝ) (hc : c≤Real.log 2) (r N : ℕ) (hr : r≤N) :
    (2:ℝ)^r*Real.exp (-c*r)≤(2:ℝ)^N*Real.exp (-c*N) := by
  rw [count_decay_identity,count_decay_identity]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hr) (sub_nonneg.mpr hc)

theorem all_support_candidate_expectation (p : E → PairLaw m κ)
    (hm : 0<m) (hk : 0<κ) (hκ : κ≤(m:ℝ)^2) (units : List (Literal n)) :
    expect (product (fun e => (p e).law)) (fun K => (Random.candidateCount (generate E K units):ℝ))≤
      3*(2:ℝ)^n*Real.exp (-runtimeConstant m κ*n) := by
  let q := product (fun e => (p e).law)
  have hsmall := (runtime_constant_small hm hk hκ).2
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hc : runtimeConstant m κ≤Real.log 2 := by linarith
  rw [←expect_conditional q (observedEdges E) (fun K => (Random.candidateCount (generate E K units):ℝ))]
  apply (expect_mono_support q (fun K hK => ?_)).trans_eq (expect_const q _)
  have hs := observed_edges_subset K
  have hp := fiber_event_positive q (observedEdges E) K hK
  have he : (fun L : E → Pattern m => observedEdges E L=observedEdges E K)=
      observedEvent (fun e : E => e.val∈observedEdges E K) := by
    funext L
    exact propext (observed_edges_event hs L)
  rw [fiber_eq q (observedEdges E) _ hp]
  simp only [he] at hp ⊢
  have h := conditional_candidate_expectation p hm hk units hs hp
  have hr : (activeVertices (observedEdges E K)).card≤n := by
    simpa using Finset.card_le_univ (activeVertices (observedEdges E K))
  have hb := count_decay_mono (runtimeConstant m κ) hc _ n hr
  apply h.trans
  nlinarith

theorem all_support_candidate_tail (p : E → PairLaw m κ)
    (hm : 0<m) (hk : 0<κ) (hκ : κ≤(m:ℝ)^2) (units : List (Literal n)) :
    prob (product (fun e => (p e).law)) (fun K =>
      (2:ℝ)^n*Real.exp (-runtimeConstant m κ*n/2)<
        (Random.candidateCount (generate E K units):ℝ))≤
      3*Real.exp (-runtimeConstant m κ*n/2) := by
  have ht := nonnegative_markov (product (fun e => (p e).law))
    (fun K => (Random.candidateCount (generate E K units):ℝ))
    (fun _ => Nat.cast_nonneg _) ((2:ℝ)^n*Real.exp (-runtimeConstant m κ*n/2)) (by positivity)
  have he := all_support_candidate_expectation p hm hk hκ units
  apply ht.trans
  apply (div_le_div_of_nonneg_right he (by positivity)).trans_eq
  have hexp : Real.exp (-runtimeConstant m κ*n)=
      Real.exp (-runtimeConstant m κ*n/2)*Real.exp (-runtimeConstant m κ*n/2) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [hexp]
  field_simp

end
end Max2SAT.RandomInput
