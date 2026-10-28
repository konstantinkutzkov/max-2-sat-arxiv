import Max2SAT.Community.Perturbation

/-! Explicit stability margins for the hidden-mean discovery proof.
The small Frobenius correction remains an input of these deterministic
lemmas; obtaining it from a rank bound and numerical approximation is a
separate obligation, not an external theorem assumed here. -/
namespace Max2SAT.Community
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
set_option maxHeartbeats 1000000

def matrixEnergy (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := (frobenius A)^2/n

theorem matrix_energy_sum (A : Matrix (Fin n) (Fin n) ℝ) :
    matrixEnergy A=(∑ i, ∑ j, (A i j)^2)/n := by rw [matrixEnergy,frobenius_square]

theorem remainder_identity (J A P X : Matrix (Fin n) (Fin n) ℝ)
    (hmodel : J=A+X-Matrix.diagonal (fun i => A i i)) (hx : ∀ i, X i i=0) :
    offDiagonal (J-P)=X+offDiagonal (A-P) := by
  rw [hmodel]
  ext i j
  by_cases h:i=j
  · subst j; simp [offDiagonal,hx]
  · simp [offDiagonal,h,Matrix.diagonal]
    ring

/-- A sufficiently large n converts a root-scale correction into a 1% error. -/
theorem correction_small (H : Matrix (Fin n) (Fin n) ℝ) (r L ν : ℝ)
    (hr : 0≤r) (hL : 0≤L) (hν : 0≤ν)
    (hH : frobenius H≤L*Real.sqrt (r*n*ν)) (hn : 10000*L^2*r≤n) :
    frobenius H≤(1/100:ℝ)*n*Real.sqrt ν := by
  apply hH.trans
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow,Real.sq_sqrt (by positivity : 0≤r*n*ν),Real.sq_sqrt hν]
  have hh := mul_le_mul_of_nonneg_right hn (show 0≤(n:ℝ)*ν by positivity)
  nlinarith

/-- Stability of both total-energy bounds under a computed correction. -/
theorem remainder_energy_bounds (X H : Matrix (Fin n) (Fin n) ℝ)
    (ν χ : ℝ) (hn : 100≤n) (hν : 0≤ν) (hχ : 1≤χ)
    (hraw : (99/100:ℝ)*n*((n:ℝ)-1)*ν≤(frobenius X)^2 ∧
      (frobenius X)^2≤(101/100:ℝ)*χ*n*((n:ℝ)-1)*ν)
    (hH : frobenius H≤(1/100:ℝ)*n*Real.sqrt ν) :
    (9/10:ℝ)*n*ν≤matrixEnergy (X+offDiagonal H) ∧
      matrixEnergy (X+offDiagonal H)≤(11/10:ℝ)*χ*n*ν := by
  have hn100 : (100:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hχν : 0≤χ*ν := by positivity
  have hlo : (98/100:ℝ)*n*Real.sqrt ν≤frobenius X := by
    apply (sq_le_sq₀ (by positivity) (frobenius_nonneg _)).mp
    simp only [mul_pow,Real.sq_sqrt hν]
    have hm := mul_le_mul_of_nonneg_right hn100 (show 0≤(n:ℝ)*ν by positivity)
    nlinarith [hraw.1]
  have hhi : frobenius X≤(101/100:ℝ)*n*Real.sqrt (χ*ν) := by
    apply (sq_le_sq₀ (frobenius_nonneg _) (by positivity)).mp
    simp only [mul_pow,Real.sq_sqrt hχν]
    nlinarith [hraw.2,show 0≤χ*(n:ℝ)*ν by positivity,show 0≤χ*(n:ℝ)^2*ν by positivity]
  have hroot : Real.sqrt ν≤Real.sqrt (χ*ν) := Real.sqrt_le_sqrt (by nlinarith)
  have hdiff := abs_le.mp (frobenius_perturbation X H)
  have hNlo : (97/100:ℝ)*n*Real.sqrt ν≤frobenius (X+offDiagonal H) := by linarith [hdiff.1]
  have hNhi : frobenius (X+offDiagonal H)≤(102/100:ℝ)*n*Real.sqrt (χ*ν) := by
    have hm := mul_le_mul_of_nonneg_left hroot hn0.le
    linarith [hdiff.2]
  constructor
  · apply (le_div_iff₀ hn0).mpr
    have hs := (sq_le_sq₀ (by positivity) (frobenius_nonneg _)).mpr hNlo
    simp only [mul_pow,Real.sq_sqrt hν] at hs
    nlinarith [show 0≤(n:ℝ)^2*ν by positivity]
  · apply (div_le_iff₀ hn0).mpr
    have hs := (sq_le_sq₀ (frobenius_nonneg _) (by positivity)).mpr hNhi
    simp only [mul_pow,Real.sq_sqrt hχν] at hs
    nlinarith [show 0≤χ*(n:ℝ)^2*ν by positivity]

/-- Coarse fixed-round bounds are enough: each round has at least n/5
vertices, and the total correction is at most .01 n sqrt(n nu). -/
theorem corrected_profile_lower (X H : Matrix (Fin n) (Fin n) ℝ)
    (R C : Finset (Fin n)) (ν : ℝ) (hν : 0≤ν)
    (hR : (n:ℝ)/5≤R.card) (hC : (n:ℝ)/5≤C.card)
    (hrows : ∀ i∈R, (99/100:ℝ)*C.card*ν≤∑ j∈C, (X i j)^2)
    (hH : frobenius H≤(1/100:ℝ)*n*Real.sqrt ν) :
    (7/100:ℝ)*n*Real.sqrt (n*ν)≤crossProfile (X+offDiagonal H) R C := by
  have hn0 : 0≤(n:ℝ) := by positivity
  have hbase : (44/100:ℝ)*Real.sqrt (n*ν)≤Real.sqrt ((99/100:ℝ)*C.card*ν) := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow,Real.sq_sqrt (by positivity : 0≤(n:ℝ)*ν)]
    have hh := mul_le_mul_of_nonneg_right hC hν
    nlinarith
  have hr : (44/100:ℝ)*Real.sqrt (n*ν)*R.card≤crossProfile X R C := by
    rw [cross_profile_roots]
    calc
      _ = ∑ _i∈R, (44/100:ℝ)*Real.sqrt (n*ν) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun i hi => hbase.trans (Real.sqrt_le_sqrt (hrows i hi)))
  have hRn : (R.card:ℝ)≤n := by exact_mod_cast (show R.card≤n by simpa using Finset.card_le_univ R)
  have hroot := Real.sqrt_le_sqrt hRn
  have herr : Real.sqrt R.card*frobenius H≤(1/100:ℝ)*n*Real.sqrt (n*ν) := by
    have hh := mul_le_mul hroot hH (frobenius_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.sqrt_mul hn0]
    nlinarith
  have hpre := cross_profile_perturbation X H R C
  have hnon : 0≤(n:ℝ)*Real.sqrt (n*ν) := by positivity
  have hm := mul_le_mul_of_nonneg_right hR (show 0≤(44/100:ℝ)*Real.sqrt (n*ν) by positivity)
  nlinarith

/-- The paper's g<=1/(256 sqrt chi) is comfortably below the profile margin. -/
theorem discovery_profile_target (ν χ D g : ℝ) (hν : 0≤ν) (hχ : 1≤χ)
    (hD : 0≤D) (hg : 0≤g) (hgu : g≤1/(256*Real.sqrt χ))
    (hcap : D≤(11/10:ℝ)*χ*n*ν) :
    4*Real.sqrt 3*(g*n*Real.sqrt D)≤(7/100:ℝ)*n*Real.sqrt (n*ν) := by
  have hχ0 : 0<χ := by linarith
  have hg' := (le_div_iff₀ (show 0<256*Real.sqrt χ by positivity)).mp hgu
  have hg2 := (sq_le_sq₀ (by positivity) (by norm_num : (0:ℝ)≤1)).mpr hg'
  simp only [mul_pow,Real.sq_sqrt hχ0.le,one_pow] at hg2
  have h1 := mul_le_mul_of_nonneg_left hcap (show 0≤g^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_right hg2 (show 0≤(n:ℝ)*ν by positivity)
  have h3 : 48*g^2*D≤(7/100:ℝ)^2*n*ν := by nlinarith
  have h4 := mul_le_mul_of_nonneg_right h3 (show 0≤(n:ℝ)^2 by positivity)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow,Real.sq_sqrt hD,Real.sq_sqrt (by norm_num : (0:ℝ)≤3),
    Real.sq_sqrt (by positivity : 0≤(n:ℝ)*ν)]
  nlinarith

end
end Max2SAT.Community
