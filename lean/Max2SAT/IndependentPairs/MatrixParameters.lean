import Max2SAT.IndependentPairs.MatrixExpectation

/-! Numerical substitutions for the two published matrix estimates. These
are proved arithmetic facts, not part of the external theorem interface. -/
namespace Max2SAT.IndependentPairs
noncomputable section

/-- The density condition in Proposition prop:pairmembership implies the
simpler sufficient budget used by the matrix proof. -/
theorem matrix_density_from_paper (n : ℕ) (B ν χ τ σ : ℝ)
    (hn : 2≤n) (hν : 0≤ν) (hχ : 1≤χ) (hτ : 0<τ) (hτ1 : τ<1)
    (h : (10^9:ℝ)*χ/τ*(B^2*Real.log n+χ*σ^2)≤n*ν) :
    (10^9:ℝ)*B^2*Real.log n≤n*χ*ν := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hlog : 0≤Real.log n := Real.log_nonneg hn1
  have hC : (10^9:ℝ)≤(10^9:ℝ)*χ/τ := by
    apply (le_div_iff₀ hτ).mpr
    nlinarith
  have ht : B^2*Real.log n≤B^2*Real.log n+χ*σ^2 := by
    have hh : 0≤χ*σ^2 := mul_nonneg (by linarith) (sq_nonneg σ)
    linarith
  have h1 := mul_le_mul hC ht (by positivity) (by positivity)
  have h2 : (n:ℝ)*ν≤n*χ*ν := by
    have hh := mul_le_mul_of_nonneg_right hχ (show 0≤(n:ℝ)*ν by positivity)
    nlinarith
  have h1' : (10^9:ℝ)*B^2*Real.log n≤
      (10^9:ℝ)*χ/τ*(B^2*Real.log n+χ*σ^2) := by
    simpa only [mul_assoc] using h1
  exact h1'.trans (h.trans h2)

/-- A common sufficient density budget, weaker than the paper's C0 budget. -/
theorem matrix_parameter_bounds (n : ℕ) (B v : ℝ) (hn : 2≤n) (hB : 0<B)
    (hdensity : (10^9:ℝ)*B^2*Real.log n≤v) :
    ((1+(1/100:ℝ))*(5*(2*B)*Real.sqrt (Real.log n)/
      Real.sqrt (Real.log (1+(1/100:ℝ))))≤(4/1000:ℝ)*Real.sqrt v) ∧
    ((4*n*B^2)*(n*Real.exp (-v/(80000*B^2)))≤(2/100:ℝ)*v) ∧
    Real.exp (-v/(80000*B^2))≤1/(n:ℝ)^3 := by
  have hn2 : (2:ℝ)≤n := by exact_mod_cast hn
  have hnp : (0:ℝ)<n := by linarith
  have hlog : (2/3:ℝ)≤Real.log n := by
    have h2 := Real.le_log_one_add_of_nonneg (x:=(1:ℝ)) (by norm_num)
    norm_num at h2
    exact h2.trans (Real.log_le_log (by norm_num) hn2)
  have hlog0 : 0≤Real.log n := by linarith
  have hB2 : 0<B^2 := sq_pos_of_pos hB
  have hlarge : 200*B^2≤v := by
    have hh := mul_le_mul_of_nonneg_left hlog (show 0≤(10^9:ℝ)*B^2 by positivity)
    nlinarith
  have hv : 0≤v := by linarith
  have hlow := Real.le_log_one_add_of_nonneg (x:=(1/100:ℝ)) (by norm_num)
  have hden : (199/2000:ℝ)≤Real.sqrt (Real.log (1+(1/100:ℝ))) := by
    apply Real.le_sqrt_of_sq_le
    norm_num at hlow ⊢
    linarith
  have hdenp : 0<Real.sqrt (Real.log (1+(1/100:ℝ))) := by linarith
  have hcoef : (1+(1/100:ℝ))*(5*(2*B)*Real.sqrt (Real.log n)/
      Real.sqrt (Real.log (1+(1/100:ℝ))))≤102*B*Real.sqrt (Real.log n) := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hdenp).mpr
    have hh := mul_le_mul_of_nonneg_left hden (show 0≤102*B*Real.sqrt (Real.log n) by positivity)
    nlinarith [show 0≤B*Real.sqrt (Real.log n) by positivity]
  have hnoise : 102*B*Real.sqrt (Real.log n)≤(4/1000:ℝ)*Real.sqrt v := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow,Real.sq_sqrt hlog0,Real.sq_sqrt hv]
    nlinarith [show 0≤B^2*Real.log n by positivity]
  have hexp (k : ℕ) (hk : k≤3) : Real.exp (-v/(80000*B^2))≤1/(n:ℝ)^k := by
    have hkr : (k:ℝ)≤3 := by exact_mod_cast hk
    have hh : (80000:ℝ)*k*B^2*Real.log n≤v := by
      have hm := mul_le_mul_of_nonneg_right hkr (show 0≤80000*B^2*Real.log n by positivity)
      nlinarith [show 0≤B^2*Real.log n by positivity]
    have he : -v/(80000*B^2)≤ -(k*Real.log n) := by
      apply (div_le_iff₀ (show 0<80000*B^2 by positivity)).mpr
      nlinarith
    calc
      _ ≤ Real.exp (-(k*Real.log n)) := Real.exp_le_exp.mpr he
      _ = _ := by rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log hnp,one_div]
  have he2 := hexp 2 (by omega)
  have herr := mul_le_mul_of_nonneg_left he2 (show 0≤4*(n:ℝ)^2*B^2 by positivity)
  have hid : (4*(n:ℝ)^2*B^2)*(1/(n:ℝ)^2)=4*B^2 := by field_simp
  rw [hid] at herr
  refine ⟨hcoef.trans hnoise,?_,hexp 3 (by omega)⟩
  nlinarith

end
end Max2SAT.IndependentPairs
