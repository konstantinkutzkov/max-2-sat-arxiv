import Max2SAT.Random.FixedSupportNodes
import Max2SAT.Counts.Resources

namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

theorem runtime_constant_pos (hm : 0<m) (hk : 0<κ) : 0<runtimeConstant m κ := by
  have hc := requirement_constant_pos hm hk
  unfold runtimeConstant
  positivity

/-- Ceil(n/2) prefix branching and the decaying candidate term are bounded
by one fixed exponential base. The factor four includes the rounding. -/
theorem prefix_candidate_rate (n : ℕ) (c : ℝ) :
    (2:ℝ)^((n+1)/2+1)≤4*(Counts.exponentialBase (1/2) c)^n ∧
    (2:ℝ)^n*Real.exp (-c*n)≤(Counts.exponentialBase (1/2) c)^n := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have he : (Counts.exponentialBase (1/2) c)^n=Real.exp (Counts.exponent (1/2) c*n) := by
    rw [Counts.exponentialBase,←Real.exp_nat_mul]
    congr 1
    ring
  have htwo : (2:ℝ)=Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
  have hp (j : ℕ) : (2:ℝ)^j=Real.exp (j*Real.log 2) := by
    calc
      (2:ℝ)^j=(Real.exp (Real.log 2))^j := congrArg (fun a : ℝ => a^j) htwo
      _=Real.exp (j*Real.log 2) := (Real.exp_nat_mul _ _).symm
  constructor
  · have hc : (((n+1)/2+1:ℕ):ℝ)≤(n:ℝ)/2+2 := by
      have h : 2*((n+1)/2+1)≤n+4 := by omega
      have h' : (2:ℝ)*((n+1)/2+1:ℕ)≤n+4 := by exact_mod_cast h
      linarith
    have hb := mul_le_mul_of_nonneg_right
      (le_max_left ((1/2:ℝ)*Real.log 2) (Real.log 2-c)) (Nat.cast_nonneg n)
    have hstep := mul_le_mul_of_nonneg_right hc hl.le
    rw [hp,he]
    rw [show (4:ℝ)=Real.exp (2*Real.log 2) by
      rw [show 2*Real.log 2=Real.log 2+Real.log 2 by ring,Real.exp_add,Real.exp_log (by norm_num)]
      norm_num,
      ←Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [Counts.exponent]
    nlinarith
  · rw [hp,←Real.exp_add,he]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right
      (le_max_right ((1/2:ℝ)*Real.log 2) (Real.log 2-c)) (Nat.cast_nonneg n)
    dsimp [Counts.exponent]
    nlinarith

theorem fixed_support_exponential_nodes (p : E → PairLaw m κ)
    (hm : 0<m) (hk : 0<κ) (hn : 0<n) (units : List (Literal n))
    (hd : ∀ i, 0<(incident E i).card)
    (hp : ∀ K, 0<(product (fun e => (p e).law)).mass K → ∀ e, present (K e)) :
    expect (product (fun e => (p e).law)) (fun K => (Random.nodeCount (generate E K units):ℝ))≤
      (4+6*n)*(Counts.exponentialBase (1/2) (runtimeConstant m κ))^n ∧
      Counts.exponentialBase (1/2) (runtimeConstant m κ)<2 := by
  constructor
  · have h := fixed_support_search_expectation p hm hk hn units hd hp
    have hb := prefix_candidate_rate n (runtimeConstant m κ)
    have hh := mul_le_mul_of_nonneg_left hb.2 (show (0:ℝ)≤6*n by positivity)
    nlinarith [hb.1]
  · exact Counts.exponential_base_lt_two _ _ (by norm_num) (runtime_constant_pos hm hk)

theorem fixed_support_exponential_tail (p : E → PairLaw m κ)
    (hm : 0<m) (hk : 0<κ) (hn : 0<n) (units : List (Literal n))
    (hd : ∀ i, 0<(incident E i).card)
    (hp : ∀ K, 0<(product (fun e => (p e).law)).mass K → ∀ e, present (K e)) :
    prob (product (fun e => (p e).law)) (fun K =>
      (4+2*n)*(Counts.exponentialBase (1/2) (runtimeConstant m κ/2))^n <
        (Random.nodeCount (generate E K units):ℝ))≤
      3*Real.exp (-runtimeConstant m κ*n/2) ∧
      Counts.exponentialBase (1/2) (runtimeConstant m κ/2)<2 := by
  constructor
  · apply (prob_mono_support (product (fun e => (p e).law)) _
      (fun K => (2:ℝ)^((n+1)/2+1)+2*n*(2:ℝ)^n*Real.exp (-runtimeConstant m κ*n/2) <
        (Random.nodeCount (generate E K units):ℝ)) ?_).trans
    · exact fixed_support_search_tail p hm hk hn units hd hp
    · intro K _ hbad
      have hb := prefix_candidate_rate n (runtimeConstant m κ/2)
      have he : -(runtimeConstant m κ/2)*(n:ℝ)= -runtimeConstant m κ*n/2 := by ring
      rw [he] at hb
      have hh := mul_le_mul_of_nonneg_left hb.2 (show (0:ℝ)≤2*n by positivity)
      nlinarith [hb.1]
  · exact Counts.exponential_base_lt_two _ _ (by norm_num)
      (half_pos (runtime_constant_pos hm hk))

end
end Max2SAT.RandomInput
