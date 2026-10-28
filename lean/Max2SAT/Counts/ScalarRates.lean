import Max2SAT.Counts.ProfileParameters

namespace Max2SAT.Counts
noncomputable section
open scoped BigOperators

/-- The paper's square-root row profile has the same normalization as
the first-moment bound used by the implementation-level theorem. -/
theorem row_profile_rescale {κ : Type*} [Fintype κ] (W : κ → ℝ) (A : ℝ) (hW : ∀ t, 0≤W t)
    (h : 4*Real.sqrt 3*A≤∑ t, Real.sqrt (W t)) :
    2*A≤(∑ t, Real.sqrt (W t/3))/2 := by
  have hs : ∀ t, Real.sqrt (W t/3)=Real.sqrt (W t)/Real.sqrt 3 := by
    intro t; exact Real.sqrt_div (hW t) 3
  simp_rw [hs]
  rw [←Finset.sum_div]
  have hp : 0<Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).2
  apply (le_div_iff₀ hp).2
  nlinarith

def clipParameter (τ g K : ℝ) : ℝ := max 2 (9*τ*Real.sqrt K/(4*g))

theorem clip_parameter_ge_two (τ g K : ℝ) : 2≤clipParameter τ g K := le_max_left _ _

theorem clip_parameter_scale (T N τ g K D : ℝ)
    (hN : 0≤N) (hτ : 0≤τ) (hg : 0<g) (hK : 0≤K) (_hD : 0≤D)
    (hT : T≤τ*N) :
    2*T*Real.sqrt (K*D)≤clipParameter τ g K*(g*N*Real.sqrt D) := by
  have ha := le_max_right (2:ℝ) (9*τ*Real.sqrt K/(4*g))
  change _≤clipParameter τ g K at ha
  have hh := (div_le_iff₀ (by positivity : 0<4*g)).mp ha
  have hk : 0≤τ*Real.sqrt K := by positivity
  have hscale : 2*τ*Real.sqrt K≤clipParameter τ g K*g := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hscale (mul_nonneg hN (Real.sqrt_nonneg D))
  have ht := mul_le_mul_of_nonneg_right hT (show 0≤2*Real.sqrt (K*D) by positivity)
  rw [Real.sqrt_mul hK D] at ht ⊢
  nlinarith

/-- Cancel the variance scale and the prefix size to obtain a rate linear
in the original number of variables. -/
theorem normalized_rate (T N τ g K D C : ℝ)
    (hT : 0<T) (hN : 0<N) (hτ : 0<τ) (hK : 0<K) (hD : 0<D) (hC : 0<C)
    (hsize : T≤τ*N) :
    g^2*N/(C*τ*K)≤(g*N*Real.sqrt D)^2/(C*T*K*D) := by
  apply (div_le_div_iff₀ (by positivity : 0<C*τ*K) (by positivity : 0<C*T*K*D)).2
  rw [mul_pow,mul_pow,Real.sq_sqrt hD.le]
  have h := mul_le_mul_of_nonneg_left hsize (show 0≤C*K*D*g^2*N by positivity)
  nlinarith

end
end Max2SAT.Counts
