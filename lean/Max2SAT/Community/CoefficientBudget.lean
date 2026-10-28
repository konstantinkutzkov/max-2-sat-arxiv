import Max2SAT.Community.FullSearch

/-! Coefficient mass from Rayleigh quotients, and the original mean/size
budgets that make projection allowances small. No eigenvector accuracy
or separation of eigenvalues is required for this step. -/
namespace Max2SAT.Community
noncomputable section
open Counts
open scoped Matrix.Norms.L2Operator
variable {n r : ℕ}
set_option maxHeartbeats 1000000

theorem rayleigh_bound (J : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hv : ∑ t, (v t)^2≤1) : |∑ t, v t*(∑ w, J t w*v w)|≤‖J‖ := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (fun t => ∑ w, J t w*v w)
  have he := matrix_squared_energy J v (‖J‖^2) le_rfl
  have hsum : 0≤∑ t, (v t)^2 := Finset.sum_nonneg (fun t _ => sq_nonneg _)
  have hnorm := mul_le_mul_of_nonneg_left hv (sq_nonneg ‖J‖)
  have hmul := mul_le_mul_of_nonneg_left (he.trans hnorm) hsum
  have hlast := mul_le_mul_of_nonneg_right hv (sq_nonneg ‖J‖)
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs]
  exact hc.trans (hmul.trans (by simpa [mul_comm] using hlast))

/-- The retained diagonal entries of Q^T J Q are Rayleigh quotients of
its unit columns, even though those columns need not be eigenvectors. -/
theorem coefficient_mass_rayleigh (J : Matrix (Fin n) (Fin n) ℝ) (d : Representation n r)
    (hv : ∀ k, ∑ t, (d.direction k t:ℝ)^2≤1)
    (hcoef : ∀ k, (d.coefficient k:ℝ)=
      ∑ t, (d.direction k t:ℝ)*(∑ w, J t w*(d.direction k w:ℝ))) :
    (coefficientMass d:ℝ)≤r*‖J‖ := by
  rw [coefficient_mass_cast]
  calc
    _ ≤ ∑ _k : Fin r, ‖J‖ := Finset.sum_le_sum (fun k _ => by rw [hcoef]; exact rayleigh_bound J _ (hv k))
    _ = _ := by simp

/-- The mean-energy and size conditions imply the allowance budget. -/
theorem coefficient_budget (n r : ℕ) (Λ μ ν χ g D : ℝ)
    (hμ : 0≤μ) (hν : 0≤ν) (hχ : 0≤χ) (hg : 0≤g)
    (hD : (9/10:ℝ)*n*ν≤D)
    (hΛ : Λ≤r*(μ*n+7*Real.sqrt (n*χ*ν)))
    (hmean : (256*r*μ)^2≤g^2*n*ν)
    (hsize : 1792*r*Real.sqrt χ≤g*n) :
    Λ≤g*n*Real.sqrt D/64 := by
  have hn0 : 0≤(n:ℝ) := by positivity
  have hD0 : 0≤D := (by positivity : (0:ℝ)≤(9/10)*n*ν).trans hD
  have hm : 256*r*μ≤g*Real.sqrt (n*ν) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow,Real.sq_sqrt (by positivity : 0≤(n:ℝ)*ν)]
    nlinarith
  have hsqrt : Real.sqrt (n*ν)≤2*Real.sqrt D := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hD0,Real.sq_sqrt (by positivity : 0≤(n:ℝ)*ν)]
    nlinarith
  have hid : Real.sqrt (n*χ*ν)=Real.sqrt χ*Real.sqrt (n*ν) := by
    rw [show (n:ℝ)*χ*ν=χ*(n*ν) by ring,Real.sqrt_mul hχ]
  rw [hid] at hΛ
  have hm' := mul_le_mul_of_nonneg_right hm hn0
  have hs' := mul_le_mul_of_nonneg_right hsize (Real.sqrt_nonneg (n*ν))
  have ht := mul_le_mul_of_nonneg_left hsqrt (show 0≤g*n by positivity)
  nlinarith

/-- Translate a matrix noise estimate and the original mean bound into the
retained coefficient budget; approximation quality is not used here. -/
theorem coefficient_budget_from_matrix (J A X : Matrix (Fin n) (Fin n) ℝ)
    (d : Representation n r) (μ ν χ g D B₀ : ℝ)
    (hμ : 0≤μ) (hν : 0≤ν) (hχ : 0≤χ) (hg : 0≤g) (hB : 0≤B₀)
    (hv : ∀ k, ∑ t, (d.direction k t:ℝ)^2≤1)
    (hcoef : ∀ k, (d.coefficient k:ℝ)=
      ∑ t, (d.direction k t:ℝ)*(∑ w, J t w*(d.direction k w:ℝ)))
    (hmodel : J=A+X-Matrix.diagonal (fun i => A i i))
    (hA : ‖A‖≤μ*n) (hdiag : ∀ i, |A i i|≤B₀)
    (hnoise : ‖X‖+B₀≤7*Real.sqrt (n*χ*ν))
    (hD : (9/10:ℝ)*n*ν≤D)
    (hmean : (256*r*μ)^2≤g^2*n*ν)
    (hsize : 1792*r*Real.sqrt χ≤g*n) :
    (coefficientMass d:ℝ)≤g*n*Real.sqrt D/64 := by
  have hdiagN : ‖Matrix.diagonal (fun i => A i i)‖≤B₀ := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hB).mpr (fun i => by simpa only [Real.norm_eq_abs] using hdiag i)
  have hJ : ‖J‖≤μ*n+7*Real.sqrt (n*χ*ν) := by
    rw [hmodel]
    have h1 := norm_sub_le (A+X) (Matrix.diagonal (fun i => A i i))
    have h2 := norm_add_le A X
    linarith
  have hΛ := (coefficient_mass_rayleigh J d hv hcoef).trans
    (mul_le_mul_of_nonneg_left hJ (Nat.cast_nonneg (α:=ℝ) r))
  exact coefficient_budget n r _ μ ν χ g D hμ hν hχ hg hD hΛ hmean hsize

end
end Max2SAT.Community
