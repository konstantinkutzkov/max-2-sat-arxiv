import Max2SAT.IndependentPairs.Profile
import Max2SAT.IndependentPairs.MatrixParameters
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Deterministic numerical implications of the membership proposition.
No probability or matrix estimate is assumed in these arithmetic lemmas. -/
namespace Max2SAT.IndependentPairs
noncomputable section
set_option maxHeartbeats 1000000

def membershipGap (τ χ : ℝ) : ℝ := τ*Real.sqrt τ/(12*Real.sqrt χ)
def meanRadius (n : ℕ) (ν χ : ℝ) : ℝ := 6*Real.sqrt (χ*ν*Real.log n)/n

theorem membership_size (n : ℕ) (χ τ : ℝ) (hχ : 1≤χ)
    (hτ : 0<τ) (hτ1 : τ<1) (hn : (10^9:ℝ)*χ^2/τ^2≤n) :
    100≤n ∧ 1000≤τ*n ∧ χ≤n := by
  have hsize : (10^9:ℝ)*χ^2≤n*τ^2 := (div_le_iff₀ (sq_pos_of_pos hτ)).mp hn
  have hnp : (0:ℝ)<n := by nlinarith [sq_nonneg χ]
  have ht2 : τ^2≤τ := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left ht2 hnp.le
  have h2 := mul_le_mul_of_nonneg_left hτ1.le hnp.le
  have h3 : (100:ℝ)≤n := by nlinarith [sq_nonneg (χ-1)]
  exact ⟨by exact_mod_cast h3,by nlinarith [sq_nonneg (χ-1)],by nlinarith [sq_nonneg (χ-1)]⟩

/-- The variance lower bound and bounded support force nu <= B^2. -/
theorem variance_le_bound {α : Type*} [Fintype α] (p : FiniteLaw.Law α)
    (X : α → ℝ) (ν B : ℝ)
    (hv : ν≤FiniteLaw.expect p (fun x => (X x)^2))
    (hb : ∀ x, 0<p.mass x → |X x|≤B) : ν≤B^2 := by
  apply hv.trans
  exact (bounded_mean p (fun x => (X x)^2) (B^2) (by
    intro x hx
    have h := abs_le.mp (hb x hx)
    exact ⟨sq_nonneg _,by nlinarith⟩)).2

/-- A positive variance budget rules out a zero or negative support bound. -/
theorem bound_positive {α : Type*} [Fintype α] (p : FiniteLaw.Law α)
    (X : α → ℝ) (ν B : ℝ) (hν : 0<ν)
    (hv : ν≤FiniteLaw.expect p (fun x => (X x)^2))
    (hb : ∀ x, 0<p.mass x → |X x|≤B) : 0<B := by
  by_contra hh
  have hB : B≤0 := le_of_not_gt hh
  have he : FiniteLaw.expect p (fun x => (X x)^2)≤0 := by
    apply le_trans (FiniteLaw.expect_mono_support p (g:=fun _ => 0) ?_) (le_of_eq (FiniteLaw.expect_const p 0))
    intro x hx
    have hz : X x=0 := abs_eq_zero.mp (le_antisymm ((hb x hx).trans hB) (abs_nonneg _))
    simp [hz]
  linarith

/-- Two usable consequences of the single density assumption. -/
theorem membership_budgets (n : ℕ) (B ν χ τ σ : ℝ)
    (hn : 2≤n) (hν : 0<ν) (hχ : 1≤χ) (hτ : 0<τ)
    (hνB : ν≤B^2)
    (hd : (10^9:ℝ)*χ/τ*(B^2*Real.log n+χ*σ^2)≤n*ν) :
    (10^9:ℝ)*χ*Real.log n≤τ*n ∧
    (10^9:ℝ)*χ^2*σ^2≤τ*n*ν ∧
    (10^9:ℝ)*χ*B^2*Real.log n≤τ*n*ν := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hl : 0≤Real.log n := Real.log_nonneg hn1
  have hd' := mul_le_mul_of_nonneg_right hd hτ.le
  have hid : ((10^9:ℝ)*χ/τ*(B^2*Real.log n+χ*σ^2))*τ=
      (10^9:ℝ)*χ*(B^2*Real.log n+χ*σ^2) := by field_simp
  rw [hid] at hd'
  have hσ : 0≤χ*σ^2 := mul_nonneg (by linarith) (sq_nonneg σ)
  have hraw : (10^9:ℝ)*χ*B^2*Real.log n≤τ*n*ν := by nlinarith
  have hsub := mul_le_mul_of_nonneg_left hνB (show 0≤(10^9:ℝ)*χ*Real.log n by positivity)
  have hlog : (10^9:ℝ)*χ*Real.log n≤τ*n := by nlinarith
  exact ⟨hlog,by nlinarith [mul_nonneg (sq_nonneg B) hl],hraw⟩

theorem mean_radius_square (n : ℕ) (ν χ : ℝ) (hn : 2≤n) (hν : 0≤ν) (hχ : 0≤χ) :
    (meanRadius n ν χ)^2*(n:ℝ)^2=36*χ*ν*Real.log n := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  unfold meanRadius
  rw [div_pow,mul_pow,Real.sq_sqrt (by positivity : 0≤χ*ν*Real.log n)]
  field_simp
  ring

/-- All conditions needed by the empirical-mean scalar and norm estimates. -/
theorem mean_radius_bounds (n : ℕ) (B ν χ τ : ℝ)
    (hn : 100≤n) (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ)
    (hτ : 0<τ) (hτ1 : τ<1)
    (hlog : (10^9:ℝ)*χ*Real.log n≤τ*n)
    (hd : (10^9:ℝ)*χ*B^2*Real.log n≤τ*n*ν) :
    0<meanRadius n ν χ ∧
    meanRadius n ν χ*B≤2*(χ*ν) ∧
    meanRadius n ν χ≤(1/1000:ℝ)*Real.sqrt ν ∧
    n*meanRadius n ν χ≤(2/1000:ℝ)*Real.sqrt (n*χ*ν) := by
  have hn100 : (100:ℝ)≤n := by exact_mod_cast hn
  have hnp : (0:ℝ)<n := by linarith
  have hl : 0<Real.log n := Real.log_pos (by linarith)
  have ha : 0<meanRadius n ν χ := by unfold meanRadius; positivity
  have hs := mean_radius_square n ν χ (by omega) hν.le (by linarith)
  have htn : τ*n≤(n:ℝ) := by nlinarith
  have hχp : 0<χ := by linarith
  have hlog' : (10^9:ℝ)*Real.log n≤n := by
    have hh := mul_le_mul_of_nonneg_right hχ hl.le
    nlinarith
  have hscale : (meanRadius n ν χ)^2*(n:ℝ)^2≤(36/10^9:ℝ)*n*ν := by
    have hh := mul_le_mul_of_nonneg_right hlog hν.le
    nlinarith
  have hshift : meanRadius n ν χ≤(1/1000:ℝ)*Real.sqrt ν := by
    apply (sq_le_sq₀ ha.le (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hν.le]
    have hh := mul_le_mul_of_nonneg_right hn100 (show 0≤(n:ℝ)*ν by positivity)
    nlinarith
  have hnorm : n*meanRadius n ν χ≤(2/1000:ℝ)*Real.sqrt (n*χ*ν) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity : 0≤(n:ℝ)*χ*ν)]
    have hh := mul_le_mul_of_nonneg_right hχ (show 0≤(n:ℝ)*ν by positivity)
    nlinarith
  have hsmall : meanRadius n ν χ*B≤2*(χ*ν) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow]
    have hh := mul_le_mul_of_nonneg_right hd hν.le
    have he := congrArg (fun x : ℝ => x*B^2) hs
    have hnν := mul_le_mul_of_nonneg_right hn100 (sq_nonneg ν)
    have hχ2 : 1≤χ^2 := by nlinarith
    have hχn := mul_le_mul_of_nonneg_right hχ2 (show 0≤(n:ℝ)^2*ν^2 by positivity)
    have hτν := mul_le_mul_of_nonneg_right htn (sq_nonneg ν)
    have hc : (meanRadius n ν χ)^2*B^2*(n:ℝ)^2≤(36/10^9:ℝ)*n*ν^2 := by nlinarith
    have hn2 : (100:ℝ)*n*ν^2≤(n:ℝ)^2*ν^2 := by
      have hh := mul_le_mul_of_nonneg_right hn100 (show 0≤(n:ℝ)*ν^2 by positivity)
      nlinarith
    have htarget : (meanRadius n ν χ)^2*B^2*(n:ℝ)^2≤4*χ^2*ν^2*(n:ℝ)^2 := by nlinarith
    exact (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hnp)).mp (by nlinarith)
  exact ⟨ha,hsmall,hshift,hnorm⟩

/-- Convert the row-profile lower bound into the parameter g used in the paper. -/
theorem profile_target (n : ℕ) (τ ν χ D : ℝ)
    (hτ : 0<τ) (hν : 0≤ν) (hχ : 1≤χ) (hD : 0≤D)
    (hcap : D≤(101/100:ℝ)*(n:ℝ)*χ*ν) :
    4*Real.sqrt 3*(membershipGap τ χ)*n*Real.sqrt D≤
      (60/100:ℝ)*(τ*n)*Real.sqrt (τ*n)*Real.sqrt ν := by
  have hχp : 0<χ := by linarith
  have hsχ := Real.sq_sqrt hχp.le
  have hsτ := Real.sq_sqrt hτ.le
  have hsN := Real.sq_sqrt (show 0≤τ*n by positivity)
  have hsν := Real.sq_sqrt hν
  have hsD := Real.sq_sqrt hD
  have hs3 := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hcap (show 0≤τ^3*(n:ℝ)^2 by positivity)
  apply (sq_le_sq₀ (by unfold membershipGap; positivity) (by positivity)).mp
  unfold membershipGap
  simp only [mul_pow,div_pow,hsχ,hsτ,hsN,hsν,hsD,hs3]
  field_simp
  nlinarith

/-- The deliberately loose square budget also covers empirical centering. -/
theorem comparison_allowance (n : ℕ) (τ ν χ D σ : ℝ)
    (hn : 100≤n) (hτ : 0<τ) (hν : 0≤ν) (hχ : 1≤χ)
    (hD : (98/100:ℝ)*((n:ℝ)-1)*ν≤D)
    (hbudget : 100000*χ*σ^2≤τ*n*ν) :
    σ≤membershipGap τ χ*Real.sqrt D/(8*τ) := by
  have hn100 : (100:ℝ)≤n := by exact_mod_cast hn
  have hχp : 0<χ := by linarith
  have hn1 : 0≤(n:ℝ)-1 := by linarith
  have hD0 : 0≤D := (by positivity : 0≤(98/100:ℝ)*((n:ℝ)-1)*ν).trans hD
  by_cases hσ : σ≤0
  · exact hσ.trans (by unfold membershipGap; positivity)
  have hσ0 : 0≤σ := le_of_lt (lt_of_not_ge hσ)
  apply (sq_le_sq₀ hσ0 (by unfold membershipGap; positivity)).mp
  unfold membershipGap
  simp only [div_pow,mul_pow,Real.sq_sqrt hτ.le,Real.sq_sqrt hχp.le,Real.sq_sqrt hD0]
  field_simp
  have hdτ := mul_le_mul_of_nonneg_left hD hτ.le
  have hnν := mul_le_mul_of_nonneg_right hn100 (show 0≤τ*ν by positivity)
  have hbτ := mul_le_mul_of_nonneg_right hbudget (sq_nonneg τ)
  have hdτ3 := mul_le_mul_of_nonneg_right hdτ (sq_nonneg τ)
  have hnτ3 := mul_le_mul_of_nonneg_right hnν (sq_nonneg τ)
  nlinarith

/-- The original size bound also implies the size bound in count accumulation. -/
theorem accumulation_size (n : ℕ) (τ χ : ℝ) (hτ : 0<τ) (hχ : 1≤χ)
    (hn : (10^9:ℝ)*χ^2/τ^2≤n) :
    256*Real.pi*τ*(9*χ)/(membershipGap τ χ)^2≤n := by
  have hχp : 0<χ := by linarith
  have hg : 0<membershipGap τ χ := by unfold membershipGap; positivity
  have hp : Real.pi≤4 := Real.pi_le_four
  have hid : 256*Real.pi*τ*(9*χ)/(membershipGap τ χ)^2=
      (331776*Real.pi)*χ^2/τ^2 := by
    unfold membershipGap
    simp only [div_pow,mul_pow,Real.sq_sqrt hτ.le,Real.sq_sqrt hχp.le]
    field_simp
    ring
  rw [hid]
  apply le_trans _ hn
  apply div_le_div_of_nonneg_right _ (sq_nonneg τ)
  have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg χ)
  nlinarith [sq_nonneg χ]

/-- Both possible comparison coefficients satisfy the same square budget.
For the empirical coefficient, triangle inequality supplies sigma<=sigma0+a. -/
theorem comparison_budget (n : ℕ) (ν χ τ σ₀ σ : ℝ)
    (hn : 100≤n) (hν : 0≤ν) (hχ : 1≤χ) (hτ : 0<τ)
    (hχn : χ≤n) (hσ₀ : 0≤σ₀) (hσ : |σ|≤σ₀+meanRadius n ν χ)
    (hlog : (10^9:ℝ)*χ*Real.log n≤τ*n)
    (hmean : (10^9:ℝ)*χ^2*σ₀^2≤τ*n*ν) :
    100000*χ*σ^2≤τ*n*ν := by
  have hn100 : (100:ℝ)≤n := by exact_mod_cast hn
  have hnp : (0:ℝ)<n := by linarith
  have ha : 0≤meanRadius n ν χ := by unfold meanRadius; positivity
  have hs := mean_radius_square n ν χ (by omega) hν (by linarith)
  have hlogν := mul_le_mul_of_nonneg_right hlog hν
  have hsc : (meanRadius n ν χ)^2*(n:ℝ)^2≤(36/10^9:ℝ)*τ*n*ν := by nlinarith
  have hχn2 : χ≤(n:ℝ)^2 := by nlinarith
  have hχa := mul_le_mul_of_nonneg_right hχn2 (sq_nonneg (meanRadius n ν χ))
  have haB : 400000*χ*(meanRadius n ν χ)^2≤τ*n*ν := by
    have hp : 0≤τ*n*ν := by positivity
    nlinarith
  have hχ2 : χ≤χ^2 := by nlinarith
  have hχσ := mul_le_mul_of_nonneg_right hχ2 (sq_nonneg σ₀)
  have hσB : 400000*χ*σ₀^2≤τ*n*ν := by nlinarith [sq_nonneg σ₀]
  have hsq : |σ|^2≤(σ₀+meanRadius n ν χ)^2 := (sq_le_sq₀ (abs_nonneg σ) (by positivity)).mpr hσ
  rw [sq_abs] at hsq
  have hab : (σ₀+meanRadius n ν χ)^2≤2*σ₀^2+2*(meanRadius n ν χ)^2 := by
    nlinarith [sq_nonneg (σ₀-meanRadius n ν χ)]
  have hmul := mul_le_mul_of_nonneg_left (hsq.trans hab) (show 0≤100000*χ by positivity)
  nlinarith

end
end Max2SAT.IndependentPairs
