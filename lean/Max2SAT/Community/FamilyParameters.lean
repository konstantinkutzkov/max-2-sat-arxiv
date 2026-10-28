import Max2SAT.Community.ComputedDiscovery

/-! Fixed class constants discharge the explicit numerical conditions from
one density assumption. They do not depend on the input or its size. -/
namespace Max2SAT.Community
noncomputable section
open Counts
set_option maxHeartbeats 1000000

def discoveryConstant (r : ℕ) (χ : ℝ) (g : ℚ) : ℝ :=
  10^9*χ+1+(256*(r:ℝ)/(g:ℝ))^2

theorem discovery_constant_bounds (r : ℕ) (χ : ℝ) (g : ℚ) (hχ : 1≤χ) :
    2≤discoveryConstant r χ g ∧ 10^9*χ≤discoveryConstant r χ g ∧
      (256*(r:ℝ)/(g:ℝ))^2≤discoveryConstant r χ g := by
  unfold discoveryConstant
  have h := sq_nonneg (256*(r:ℝ)/(g:ℝ))
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem rational_discovery_parameter (χ : ℝ) (hχ : 1≤χ) :
    ∃ g : ℚ, 0<g ∧ 1/(512*Real.sqrt χ)≤(g:ℝ) ∧ (g:ℝ)≤1/(256*Real.sqrt χ) := by
  have hs : 0<Real.sqrt χ := Real.sqrt_pos.mpr (by linarith)
  have hlt : 1/(512*Real.sqrt χ)<1/(256*Real.sqrt χ) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  obtain ⟨g,hlo,hhi⟩ := exists_rat_btwn hlt
  have hg : (0:ℝ)<g := (by positivity : (0:ℝ)<1/(512*Real.sqrt χ)).trans hlo
  exact ⟨g,by exact_mod_cast hg,hlo.le,hhi.le⟩

theorem discovery_family_threshold (r : ℕ) (χ : ℝ) (g : ℚ) (hg : 0<g) :
    ∃ N : ℕ, 100≤N ∧ r≤N ∧ 5120000*r*χ≤(N:ℝ) ∧
      1792*r*Real.sqrt χ≤(g:ℝ)*N := by
  have hgr : (0:ℝ)<g := by exact_mod_cast hg
  obtain ⟨N,hN⟩ := exists_nat_gt
    (max (max 100 (r:ℝ)) (max (5120000*r*χ) (1792*r*Real.sqrt χ/(g:ℝ))))
  have hl := (le_max_left _ _).trans hN.le
  have hr := (le_max_right _ _).trans hN.le
  have h100 : (100:ℝ)≤N := (le_max_left _ _).trans hl
  have hrN : (r:ℝ)≤N := (le_max_right _ _).trans hl
  refine ⟨N,by exact_mod_cast h100,by exact_mod_cast hrN,(le_max_left _ _).trans hr,?_⟩
  have hd := (div_le_iff₀ hgr).mp ((le_max_right _ _).trans hr)
  simpa only [mul_comm] using hd

/-- The paper's single density condition implies all scale and mean budgets. -/
theorem discovery_density_conditions (n r : ℕ) (χ B ν μ B₀ : ℝ) (g : ℚ)
    (hn : 100≤n) (hχ : 1≤χ) (hB : 1≤B) (hg : 0<g)
    (hd : discoveryConstant r χ g*(B^2*Real.log n+B₀^2+μ^2)≤n*ν) :
    (10^9:ℝ)*χ*B^2*Real.log n≤n*ν ∧
      B₀≤Real.sqrt (n*χ*ν) ∧ 1/(n:ℝ)^4≤Real.sqrt (n*χ*ν) ∧
      (256*r*μ)^2≤(g:ℝ)^2*n*ν := by
  have hn100 : (100:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hlog : (1/2:ℝ)≤Real.log n := by
    have hh := Real.one_sub_inv_le_log_of_pos hn0
    have hi : 1/(n:ℝ)≤1/2 := (div_le_iff₀ hn0).mpr (by linarith)
    rw [one_div] at hi
    linarith
  have hC := discovery_constant_bounds r χ g hχ
  have ht : 0≤B^2*Real.log n := mul_nonneg (sq_nonneg _) (by linarith)
  have hscaled : discoveryConstant r χ g*(B^2*Real.log n)≤n*ν := by
    have hh := mul_le_mul_of_nonneg_left (show B^2*Real.log n≤B^2*Real.log n+B₀^2+μ^2 by nlinarith)
      (show 0≤discoveryConstant r χ g by linarith [hC.1])
    exact hh.trans hd
  have hdiag : B₀^2≤n*ν := by
    have hh := mul_le_mul_of_nonneg_left (show B₀^2≤B^2*Real.log n+B₀^2+μ^2 by nlinarith)
      (show 0≤discoveryConstant r χ g by linarith [hC.1])
    have hprod := mul_le_mul_of_nonneg_right (show 1≤discoveryConstant r χ g by linarith [hC.1]) (sq_nonneg B₀)
    nlinarith
  have hνn : 1≤(n:ℝ)*ν := by
    have hb2 : 1≤B^2 := by nlinarith
    have ht1 := mul_le_mul hb2 hlog (by norm_num : (0:ℝ)≤1/2) (sq_nonneg B)
    have hh := mul_le_mul hC.1 ht1 (by norm_num : (0:ℝ)≤1*(1/2))
      (show 0≤discoveryConstant r χ g by linarith [hC.1])
    nlinarith
  have hscaledχ : (n:ℝ)*ν≤n*χ*ν := by nlinarith [mul_le_mul_of_nonneg_right hχ (show 0≤(n:ℝ)*ν by linarith)]
  refine ⟨?_,Real.le_sqrt_of_sq_le (hdiag.trans hscaledχ),?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hC.2.1 ht
    nlinarith
  · have hp : 1/(n:ℝ)^4≤1 := by
      apply div_le_one_of_le₀
      · exact one_le_pow₀ (by linarith : (1:ℝ)≤n)
      · positivity
    exact hp.trans (Real.le_sqrt_of_sq_le (by nlinarith))
  · have hμ := mul_le_mul_of_nonneg_left (show μ^2≤B^2*Real.log n+B₀^2+μ^2 by nlinarith)
      (show 0≤discoveryConstant r χ g by linarith [hC.1])
    have hcoef := mul_le_mul_of_nonneg_right hC.2.2 (sq_nonneg μ)
    have hh : (256*(r:ℝ)/(g:ℝ))^2*μ^2≤n*ν := hcoef.trans (hμ.trans hd)
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg (g:ℝ))
    have hg0 : (g:ℝ)≠0 := ne_of_gt (by exact_mod_cast hg)
    have he : (g:ℝ)^2*((256*(r:ℝ)/(g:ℝ))^2*μ^2)=(256*r*μ)^2 := by field_simp
    rw [he] at hh'
    simpa only [mul_assoc] using hh'

end
end Max2SAT.Community
