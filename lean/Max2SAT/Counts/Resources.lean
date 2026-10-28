import Max2SAT.Counts.Algorithms
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The deterministic conversion from the passing probability of each run
to the nodes actually visited across all guesses. This modular lemma
takes the analytic passing probability as input; VerifiedNodes discharges
that input from the paper's deterministic hypotheses. -/
namespace Max2SAT.Counts
noncomputable section

theorem run_nodes_of_probability (K : Assignment n → Weighted.Budget n)
    (P : Finset (Fin n)) (hK : PrefixSearch.Stable K P) (p : ℝ)
    (hp : FairCoin.probability n (fun x => (K x).Holds x)≤p) :
    (PrefixSearch.nodeCount K P : ℝ)≤(2:ℝ)^(P.card+1)+2*n*(2:ℝ)^n*p := by
  rw [FairCoin.probability_eq_count] at hp
  have hc := (div_le_iff₀ (by positivity : (0:ℝ)<2^n)).mp hp
  have hn := PrefixSearch.nodeCount_bound K P hK
  have hn' : (PrefixSearch.nodeCount K P : ℝ)≤
      (2:ℝ)^(P.card+1)+2*n*(FairCoin.eventCount n (fun x => (K x).Holds x) : ℝ) := by
    exact_mod_cast hn.trans (Nat.add_le_add_right (Nat.sub_le _ _) _)
  have hm := mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤2*n by positivity)
  nlinarith

theorem all_runs_nodes_of_probability (guesses : List ι)
    (K : ι → Assignment n → Weighted.Budget n) (P : Finset (Fin n))
    (hK : ∀ g∈guesses, PrefixSearch.Stable (K g) P) (p : ℝ)
    (hp : ∀ g∈guesses, FairCoin.probability n (fun x => (K g x).Holds x)≤p) :
    (Runs.nodeCount guesses K P : ℝ)≤guesses.length*
      ((2:ℝ)^(P.card+1)+2*n*(2:ℝ)^n*p) := by
  induction guesses with
  | nil => simp [Runs.nodeCount]
  | cons g gs ih =>
    have hh := run_nodes_of_probability (K g) P (hK g (by simp)) p (hp g (by simp))
    have ht := ih (fun h hh => hK h (by simp [hh])) (fun h hh => hp h (by simp [hh]))
    simp only [Runs.nodeCount,List.map_cons,List.sum_cons,List.length_cons,
      Nat.cast_add,Nat.cast_one] at *
    nlinarith

def exponent (τ c : ℝ) : ℝ := max (τ*Real.log 2) (Real.log 2-c)
def exponentialBase (τ c : ℝ) : ℝ := Real.exp (exponent τ c)

theorem exponential_base_lt_two (τ c : ℝ) (hτ : τ<1) (hc : 0<c) :
    exponentialBase τ c<2 := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have he : exponent τ c<Real.log 2 := by unfold exponent; exact max_lt (by nlinarith) (by linarith)
  have hh := Real.exp_lt_exp.mpr he
  exact hh.trans_eq (Real.exp_log (by norm_num : (0:ℝ)<2))

theorem all_runs_exponential (guesses : List ι)
    (K : ι → Assignment n → Weighted.Budget n) (P : Finset (Fin n))
    (hK : ∀ g∈guesses, PrefixSearch.Stable (K g) P)
    (τ c A : ℝ) (hA : 0≤A) (hsize : (P.card:ℝ)≤τ*n)
    (hp : ∀ g∈guesses,
      FairCoin.probability n (fun x => (K g x).Holds x)≤A*Real.exp (-c*n)) :
    (Runs.nodeCount guesses K P : ℝ)≤
      guesses.length*(2+2*n*A)*(exponentialBase τ c)^n := by
  have hn := all_runs_nodes_of_probability guesses K P hK _ hp
  have hn0 : (0:ℝ)≤n := Nat.cast_nonneg _
  have hl : 0≤Real.log 2 := (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have htwo : (2:ℝ)=Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
  have hpow : (2:ℝ)^n*Real.exp (-c*n)=Real.exp ((Real.log 2-c)*n) := by
    rw [htwo,←Real.exp_nat_mul,←Real.exp_add]
    simp only [Real.log_exp]
    congr 1
    ring
  have hbase : (exponentialBase τ c)^n=Real.exp (exponent τ c*n) := by
    rw [exponentialBase,←Real.exp_nat_mul]
    congr 1
    ring
  have hpre : (2:ℝ)^(P.card+1)≤2*(exponentialBase τ c)^n := by
    rw [pow_succ,htwo,←Real.exp_nat_mul]
    rw [mul_comm,←htwo,hbase]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hsize hl
    have hb := mul_le_mul_of_nonneg_right (le_max_left (τ*Real.log 2) (Real.log 2-c)) hn0
    dsimp [exponent]
    nlinarith
  have hs : (2:ℝ)^n*Real.exp (-c*n)≤(exponentialBase τ c)^n := by
    rw [hpow,hbase]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hn0)
  have hm := mul_le_mul_of_nonneg_left hs (show 0≤2*(n:ℝ)*A by positivity)
  have hinside : (2:ℝ)^(P.card+1)+2*n*(2:ℝ)^n*(A*Real.exp (-c*n))≤
      (2+2*n*A)*(exponentialBase τ c)^n := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hinside (show (0:ℝ)≤guesses.length by positivity)
  exact hn.trans (by simpa only [mul_assoc] using hh)

end
end Max2SAT.Counts
