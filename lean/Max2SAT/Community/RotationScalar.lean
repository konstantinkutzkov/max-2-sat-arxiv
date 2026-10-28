import Max2SAT.Community.FrameGuarantees
import Mathlib.Topology.Order.IntermediateValue

/-! Rationally parameterized plane rotations and the scalar elimination
step. Real roots are used only in the proof; the algorithm searches a
finite rational grid. -/
namespace Max2SAT.Community
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
set_option maxHeartbeats 800000

def rotationC (t : K) : K := (1-t^2)/(1+t^2)
def rotationS (t : K) : K := 2*t/(1+t^2)

theorem rotation_denominator (t : K) : 0<1+t^2 := by positivity

theorem rotation_circle (t : K) : (rotationC t)^2+(rotationS t)^2=1 := by
  unfold rotationC rotationS
  field_simp [ne_of_gt (rotation_denominator t)]
  ring

theorem rotation_component_bounds (t : K) : |rotationC t|≤1 ∧ |rotationS t|≤1 := by
  have h := rotation_circle t
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (rotationS t)]
  · apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (rotationC t)]

theorem rotation_distance (t u : K) :
    (rotationC t-rotationC u)^2+(rotationS t-rotationS u)^2=
      4*(t-u)^2/((1+t^2)*(1+u^2)) := by
  unfold rotationC rotationS
  field_simp [ne_of_gt (rotation_denominator t),ne_of_gt (rotation_denominator u)]
  ring

theorem rotation_distance_bound (t u : K) :
    (rotationC t-rotationC u)^2+(rotationS t-rotationS u)^2≤4*(t-u)^2 := by
  rw [rotation_distance]
  apply div_le_self (by positivity)
  nlinarith [sq_nonneg t,sq_nonneg u,mul_nonneg (sq_nonneg t) (sq_nonneg u)]

theorem rotation_coordinate_lipschitz (t u : K) :
    |rotationC t-rotationC u|≤2*|t-u| ∧ |rotationS t-rotationS u|≤2*|t-u| := by
  have h := rotation_distance_bound t u
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    simp only [mul_pow,sq_abs]
    nlinarith [sq_nonneg (rotationS t-rotationS u)]
  · apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    simp only [mul_pow,sq_abs]
    nlinarith [sq_nonneg (rotationC t-rotationC u)]

/-- The off-diagonal entry after rotating a symmetric two-by-two block. -/
def rotatedPivot (a b d t : K) : K :=
  b*((rotationC t)^2-(rotationS t)^2)+(d-a)*rotationC t*rotationS t

theorem rotated_pivot_endpoints (a b d : K) :
    rotatedPivot a b d 0=b ∧ rotatedPivot a b d 1= -b := by
  norm_num [rotatedPivot,rotationC,rotationS]

/-- A real eliminating angle exists on a fixed bounded interval. -/
theorem eliminating_parameter (a b d : ℝ) :
    ∃ t∈Set.Icc (0:ℝ) 1, rotatedPivot a b d t=0 := by
  have hc : Continuous (fun t:ℝ => rotationC t) := by
    unfold rotationC
    exact (continuous_const.sub (continuous_id.pow 2)).div
      (continuous_const.add (continuous_id.pow 2)) (fun t => ne_of_gt (rotation_denominator t))
  have hs : Continuous (fun t:ℝ => rotationS t) := by
    unfold rotationS
    exact (continuous_const.mul continuous_id).div
      (continuous_const.add (continuous_id.pow 2)) (fun t => ne_of_gt (rotation_denominator t))
  have hf : Continuous (rotatedPivot a b d) :=
    (continuous_const.mul ((hc.pow 2).sub (hs.pow 2))).add
      ((continuous_const.mul hc).mul hs)
  have he := rotated_pivot_endpoints a b d
  have hz : (0:ℝ)∈Set.uIcc (rotatedPivot a b d 0) (rotatedPivot a b d 1) := by
    rw [he.1,he.2]
    exact Set.mem_uIcc.mpr (by
      rcases le_total b 0 with hb|hb
      · exact Or.inl ⟨hb,by linarith⟩
      · exact Or.inr ⟨by linarith,hb⟩)
  obtain ⟨t,ht,heq⟩ := intermediate_value_uIcc hf.continuousOn hz
  exact ⟨t,by simpa using ht,heq⟩

theorem bounded_product_difference (x y u v : K)
    (hx : |x|≤1) (hv : |v|≤1) : |x*y-u*v|≤|x-u|+|y-v| := by
  have he : x*y-u*v=x*(y-v)+(x-u)*v := by ring
  rw [he]
  have h := abs_add_le (x*(y-v)) ((x-u)*v)
  simp only [abs_mul] at h
  have h₁ := mul_le_mul_of_nonneg_right hx (abs_nonneg (y-v))
  have h₂ := mul_le_mul_of_nonneg_left hv (abs_nonneg (x-u))
  nlinarith

/-- A conservative Lipschitz bound for the one entry to be eliminated. -/
theorem rotated_pivot_lipschitz (a b d t u M : K)
    (ha : |a|≤M) (hb : |b|≤M) (hd : |d|≤M) :
    |rotatedPivot a b d t-rotatedPivot a b d u|≤16*M*|t-u| := by
  have ht := rotation_component_bounds t
  have hu := rotation_component_bounds u
  have hL := rotation_coordinate_lipschitz t u
  have hc : |(rotationC t)^2-(rotationC u)^2|≤4*|t-u| := by
    have h := bounded_product_difference (rotationC t) (rotationC t) (rotationC u) (rotationC u) ht.1 hu.1
    simp only [←pow_two] at h
    linarith [hL.1]
  have hs : |(rotationS t)^2-(rotationS u)^2|≤4*|t-u| := by
    have h := bounded_product_difference (rotationS t) (rotationS t) (rotationS u) (rotationS u) ht.2 hu.2
    simp only [←pow_two] at h
    linarith [hL.2]
  have hp : |rotationC t*rotationS t-rotationC u*rotationS u|≤4*|t-u| := by
    have h := bounded_product_difference (rotationC t) (rotationS t) (rotationC u) (rotationS u) ht.1 hu.2
    linarith [hL.1,hL.2]
  have he : rotatedPivot a b d t-rotatedPivot a b d u=
      b*(((rotationC t)^2-(rotationC u)^2)-((rotationS t)^2-(rotationS u)^2))+
        (d-a)*(rotationC t*rotationS t-rotationC u*rotationS u) := by unfold rotatedPivot; ring
  rw [he]
  have hsum : |((rotationC t)^2-(rotationC u)^2)-((rotationS t)^2-(rotationS u)^2)|≤8*|t-u| := by
    have h := abs_sub ((rotationC t)^2-(rotationC u)^2) ((rotationS t)^2-(rotationS u)^2)
    exact h.trans (by linarith)
  have hda : |d-a|≤2*M := (abs_sub d a).trans (by linarith)
  have hm : 0≤M := (abs_nonneg a).trans ha
  have h₁ := mul_le_mul hb hsum (abs_nonneg _) hm
  have h₂ := mul_le_mul hda hp (abs_nonneg _) (by positivity : 0≤2*M)
  have h := abs_add_le
    (b*(((rotationC t)^2-(rotationC u)^2)-((rotationS t)^2-(rotationS u)^2)))
    ((d-a)*(rotationC t*rotationS t-rotationC u*rotationS u))
  simp only [abs_mul] at h
  nlinarith

end Max2SAT.Community
