import Max2SAT.IndependentPairs.MembershipParameters
import Max2SAT.IndependentPairs.ScalarEvent

/-! Substitution of the paper parameters into every scalar exceptional
probability, followed by the final union-bound arithmetic. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open RandomInput
set_option maxHeartbeats 1000000

/-- Exponential-to-polynomial conversion used by all tail bounds. -/
theorem exponential_power_bound (n k : ℕ) (x : ℝ) (hn : 0<n)
    (hx : x≤ -(k*Real.log n)) : Real.exp x≤1/(n:ℝ)^k := by
  calc
    _ ≤ Real.exp (-(k*Real.log n)) := Real.exp_le_exp.mpr hx
    _ = _ := by
      rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by exact_mod_cast hn),one_div]

/-- Any row with at least tau*n/10 independent entries has the required tail. -/
theorem row_failure_bound (n : ℕ) (B ν χ τ r : ℝ)
    (hn : 2≤n) (hB : 0<B) (hν : 0≤ν) (hχ : 1≤χ) (_hτ : 0<τ)
    (hr : τ*n/10≤r)
    (hd : (10^9:ℝ)*χ*B^2*Real.log n≤τ*n*ν) :
    Real.exp (-(1/100:ℝ)^2*r*ν/(4*B^2*χ))≤1/(n:ℝ)^3 := by
  have hlog : 0≤Real.log n := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  have hm := mul_le_mul_of_nonneg_right hr hν
  have hnon : 0≤χ*B^2*Real.log n := by positivity
  apply exponential_power_bound n 3 _ (by omega)
  apply (div_le_iff₀ (show 0<4*B^2*χ by positivity)).mpr
  norm_num
  nlinarith

/-- The mean's two tails together cost at most n^-3. -/
theorem mean_failure_bound (n : ℕ) (ν χ : ℝ)
    (hn : 100≤n) (hν : 0<ν) (hχ : 1≤χ) :
    2*Real.exp (-(Fintype.card (Edge n):ℝ)*(meanRadius n ν χ)^2/(4*(χ*ν)))≤
      1/(n:ℝ)^3 := by
  have hn100 : (100:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hl : 0≤Real.log n := Real.log_nonneg (by linarith)
  have hp := pair_count_real (n:=n) (by omega)
  have hs := mean_radius_square n ν χ (by omega) hν.le (by linarith)
  have hex : -(Fintype.card (Edge n):ℝ)*(meanRadius n ν χ)^2/(4*(χ*ν))≤
      -(4*Real.log n) := by
    apply (div_le_iff₀ (show 0<4*(χ*ν) by positivity)).mpr
    have he := congrArg (fun x : ℝ => x*(meanRadius n ν χ)^2) hp
    have hnp : 0<(n:ℝ)^2 := sq_pos_of_pos hn0
    have hlv : 0≤χ*ν*Real.log n := by positivity
    have hm := mul_le_mul_of_nonneg_right hn100 hlv
    have hs' := congrArg (fun x : ℝ => x*((n:ℝ)-1)) hs
    have he' := congrArg (fun x : ℝ => x*n) he
    nlinarith
  have htail := exponential_power_bound n 4 _ (by omega) hex
  have hlast : 2*(1/(n:ℝ)^4)≤1/(n:ℝ)^3 := by
    field_simp
    nlinarith
  exact (mul_le_mul_of_nonneg_left htail (by norm_num)).trans hlast

/-- The scalar event's full error budget needs no independence between rows. -/
theorem scalar_failure_bound (n : ℕ) (B ν χ τ : ℝ)
    (hn : 100≤n) (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ)
    (hτ : 0<τ) (hτ1 : τ<1)
    (hd : (10^9:ℝ)*χ*B^2*Real.log n≤τ*n*ν) :
    scalarFailureBound n B ν χ (meanRadius n ν χ) (lateRows n τ)≤
      ((lateRows n τ).card+3:ℝ)/(n:ℝ)^3 := by
  have hn100 : (100:ℝ)≤n := by exact_mod_cast hn
  have hp := pair_count_real (n:=n) (by omega)
  have hnp : 0≤(n:ℝ) := by positivity
  have hc : τ*n/10≤(Fintype.card (Edge n):ℝ) := by nlinarith
  have helo := row_failure_bound n B ν χ τ _ (by omega) hB hν.le hχ hτ hc hd
  have hlog : 0≤Real.log n := Real.log_nonneg (by linarith)
  have hehi : Real.exp (-(1/100:ℝ)^2*(Fintype.card (Edge n):ℝ)*χ*ν/(4*B^2))≤
      Real.exp (-(1/100:ℝ)^2*(Fintype.card (Edge n):ℝ)*ν/(4*B^2*χ)) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff₀ (by positivity : 0<4*B^2) (by positivity : 0<4*B^2*χ)).mpr
    have hm := mul_le_mul_of_nonneg_left (show 1≤χ^2 by nlinarith)
      (show 0≤(Fintype.card (Edge n):ℝ)*ν*B^2 by positivity)
    nlinarith
  have hrow : ∀ t∈lateRows n τ,
      Real.exp (-(1/100:ℝ)^2*t.val*ν/(4*B^2*χ))≤1/(n:ℝ)^3 := by
    intro t ht
    have hh := (Finset.mem_filter.mp ht).2.1
    have hhr : (⌈τ*n/10⌉₊:ℝ)≤t.val := by exact_mod_cast hh
    exact row_failure_bound n B ν χ τ _ (by omega) hB hν.le hχ hτ
      ((Nat.le_ceil _).trans hhr) hd
  have hrows := Finset.sum_le_sum hrow
  simp only [Finset.sum_const, nsmul_eq_mul] at hrows
  have hmean := mean_failure_bound n ν χ hn hν hχ
  unfold scalarFailureBound
  calc
    _ ≤ 1/(n:ℝ)^3+(1/(n:ℝ)^3+1/(n:ℝ)^3)+
        (lateRows n τ).card*(1/(n:ℝ)^3) :=
      add_le_add (add_le_add hmean (add_le_add helo (hehi.trans helo))) hrows
    _ = _ := by ring

/-- Including the one matrix event, the total failure probability is <= 1/n. -/
theorem membership_failure_bound (n : ℕ) (B ν χ τ : ℝ)
    (hn : 100≤n) (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ)
    (hτ : 0<τ) (hτ1 : τ<1)
    (hd : (10^9:ℝ)*χ*B^2*Real.log n≤τ*n*ν) :
    scalarFailureBound n B ν χ (meanRadius n ν χ) (lateRows n τ)+1/(n:ℝ)^3≤1/n := by
  have hs := scalar_failure_bound n B ν χ τ hn hB hν hχ hτ hτ1 hd
  have hc : ((lateRows n τ).card:ℝ)≤n := by
    exact_mod_cast (show (lateRows n τ).card≤n by simpa using Finset.card_le_univ (lateRows n τ))
  have hn100 : (100:ℝ)≤n := by exact_mod_cast hn
  have hnp : (0:ℝ)<n := by linarith
  have hlast : (((lateRows n τ).card+3:ℝ)/(n:ℝ)^3)+1/(n:ℝ)^3≤1/n := by
    field_simp
    nlinarith [sq_nonneg ((n:ℝ)-1)]
  exact (add_le_add hs le_rfl).trans hlast

end
end Max2SAT.IndependentPairs
