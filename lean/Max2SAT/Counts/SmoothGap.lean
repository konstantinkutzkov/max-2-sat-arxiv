import Max2SAT.Counts.OperatorEnergy
import Max2SAT.Counts.GapProfile

/-! A smooth upper approximation to absolute value, with explicit
first-order and squared-error bounds for the common-gap estimate. -/
namespace Max2SAT.Counts
noncomputable section

def smoothAbs (δ z : ℝ) : ℝ :=
  if z < -δ then -z else if δ < z then z else (z^2+δ^2)/(2*δ)

def smoothSlope (δ z : ℝ) : ℝ :=
  if z < -δ then -1 else if δ < z then 1 else z/δ

theorem smooth_slope_bounds (δ z : ℝ) (hδ : 0<δ) :
    -1≤smoothSlope δ z ∧ smoothSlope δ z≤1 := by
  unfold smoothSlope
  split_ifs with h₁ h₂
  · norm_num
  · norm_num
  · constructor
    · apply (le_div_iff₀ hδ).2; linarith
    · apply (div_le_iff₀ hδ).2; linarith

theorem smooth_value (δ z : ℝ) (hδ : 0<δ) :
    smoothAbs δ z=smoothSlope δ z*z+δ/2*(1-(smoothSlope δ z)^2) := by
  unfold smoothAbs smoothSlope
  split_ifs <;> field_simp <;> ring

theorem smooth_support (δ z p : ℝ) (hδ : 0<δ) (hp : -1≤p ∧ p≤1) :
    p*z+δ/2*(1-p^2)+δ/2*(p-smoothSlope δ z)^2 ≤ smoothAbs δ z := by
  have h : 0≤(smoothSlope δ z-p)*(z-δ*smoothSlope δ z) := by
    unfold smoothSlope
    split_ifs with h₁ h₂
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hp.1]) (by linarith)
    · exact mul_nonneg (by linarith [hp.2]) (by linarith)
    · have hz : z-δ*(z/δ)=0 := by field_simp; ring
      rw [hz,mul_zero]
  rw [smooth_value δ z hδ]
  nlinarith

theorem smooth_approximation (δ z : ℝ) (hδ : 0<δ) :
    |z|≤smoothAbs δ z ∧ smoothAbs δ z≤|z|+δ/2 := by
  constructor
  · have hn := smooth_support δ z (-1) hδ (by norm_num)
    have hp := smooth_support δ z 1 hδ (by norm_num)
    have hm : 0≤δ/2*(-1-smoothSlope δ z)^2 := by positivity
    have hm' : 0≤δ/2*(1-smoothSlope δ z)^2 := by positivity
    rw [abs_le]
    constructor <;> nlinarith
  · have hb := smooth_slope_bounds δ z hδ
    have hd : |smoothSlope δ z|≤1 := abs_le.mpr hb
    have he := mul_le_mul_of_nonneg_right hd (abs_nonneg z)
    rw [←abs_mul,one_mul] at he
    have hh := le_abs_self (smoothSlope δ z*z)
    rw [smooth_value δ z hδ]
    have hs : 0≤δ/2*(smoothSlope δ z)^2 := by positivity
    nlinarith

theorem smooth_taylor (δ x y : ℝ) (hδ : 0<δ) :
    0≤smoothAbs δ y-smoothAbs δ x-smoothSlope δ x*(y-x) ∧
    smoothAbs δ y-smoothAbs δ x-smoothSlope δ x*(y-x)≤(y-x)^2/(2*δ) := by
  have hx := smooth_support δ x (smoothSlope δ y) hδ (smooth_slope_bounds δ y hδ)
  have hy := smooth_support δ y (smoothSlope δ x) hδ (smooth_slope_bounds δ x hδ)
  have ex := smooth_value δ x hδ
  have ey := smooth_value δ y hδ
  constructor
  · have hs : 0≤δ/2*(smoothSlope δ x-smoothSlope δ y)^2 := by positivity
    nlinarith
  · apply (le_div_iff₀ (by positivity : 0<2*δ)).2
    have hs := sq_nonneg (δ*(smoothSlope δ y-smoothSlope δ x)-(y-x))
    nlinarith [mul_le_mul_of_nonneg_left hx (show 0≤2*δ by positivity)]

end
end Max2SAT.Counts
