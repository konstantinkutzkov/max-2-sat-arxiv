import Max2SAT.Random.MeasureBridge
import Mathlib.MeasureTheory.Function.L2Space

/-! The moment interpolation used in Lemma `lem:random_moments`.
Two applications of Cauchy--Schwarz replace the fractional-power Holder
calculation. The integral statements cover arbitrary probability spaces. -/
namespace Max2SAT.MomentBounds
noncomputable section
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem cauchy_sq {f g : Ω → ℝ}
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ) * (∫ x, (g x)^2 ∂μ) := by
  have h : ∫ x, f x * g x ∂μ ≤
      Real.sqrt (∫ x, (f x)^2 ∂μ) * Real.sqrt (∫ x, (g x)^2 ∂μ) := by
    simpa only [ENNReal.ofReal_ofNat, Real.rpow_two, ← Real.sqrt_eq_rpow] using
      integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hf0 hg0
        (by simpa using hf) (by simpa using hg)
  have h0 : 0 ≤ ∫ x, f x * g x ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hf0, hg0] with x hx hy using mul_nonneg hx hy
  have hs := pow_le_pow_left₀ h0 h 2
  rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)),
    Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))] at hs
  exact hs

/-- For a nonnegative variable V, (E V²)³ ≤ (E V)² E V⁴.
All integrability obligations follow from its finite fourth moment. -/
theorem moment_interpolation [IsFiniteMeasure μ] (V : Ω → ℝ)
    (hV : ∀ x, 0 ≤ V x) (hm : AEStronglyMeasurable V μ)
    (h4 : Integrable (fun x => (V x)^4) μ) :
    (∫ x, (V x)^2 ∂μ)^3 ≤ (∫ x, V x ∂μ)^2 * (∫ x, (V x)^4 ∂μ) := by
  have hp : ∀ k : ℕ, k ≤ 4 → Integrable (fun x => (V x)^k) μ := by
    intro k hk
    have hn : ∀ x, ‖V x‖ = V x := fun x => Real.norm_of_nonneg (hV x)
    simpa only [hn] using integrable_norm_pow_of_le hm hk (by simpa only [hn] using h4)
  have h1 : Integrable V μ := by simpa using hp 1 (by omega)
  have hmS : AEStronglyMeasurable (fun x => Real.sqrt (V x)) μ :=
    hm.aemeasurable.sqrt.aestronglyMeasurable
  have hS : MemLp (fun x => Real.sqrt (V x)) 2 μ := by
    apply (memLp_two_iff_integrable_sq hmS).2
    simpa only [Real.sq_sqrt (hV _)] using h1
  have hVS : MemLp (fun x => V x * Real.sqrt (V x)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (hm.mul hmS)).2
    convert hp 3 (by omega) using 1
    funext x
    change (V x * Real.sqrt (V x))^2 = (V x)^3
    rw [mul_pow, Real.sq_sqrt (hV x)]
    ring
  have ha := cauchy_sq (Filter.Eventually.of_forall (fun x => Real.sqrt_nonneg (V x)))
    (Filter.Eventually.of_forall (fun x => mul_nonneg (hV x) (Real.sqrt_nonneg _))) hS hVS
  have hmul : ∀ x, Real.sqrt (V x) * (V x * Real.sqrt (V x)) = (V x)^2 := by
    intro x
    nlinarith [Real.sq_sqrt (hV x)]
  have hVSsq : ∀ x, (V x * Real.sqrt (V x))^2 = (V x)^3 := by
    intro x
    rw [mul_pow, Real.sq_sqrt (hV x)]
    ring
  simp only [hmul, hVSsq, Real.sq_sqrt (hV _)] at ha
  have h2 : MemLp V 2 μ := (memLp_two_iff_integrable_sq hm).2 (hp 2 (by omega))
  have h22 : MemLp (fun x => (V x)^2) 2 μ := by
    apply (memLp_two_iff_integrable_sq (hm.pow 2)).2
    simpa only [Pi.pow_apply, ← pow_mul] using h4
  have hb := cauchy_sq (Filter.Eventually.of_forall hV)
    (Filter.Eventually.of_forall (fun x => sq_nonneg (V x))) h2 h22
  have hmul3 : ∀ x, V x * (V x)^2 = (V x)^3 := fun x => by ring
  simp only [hmul3, ← pow_mul] at hb
  have hE2 : 0 ≤ ∫ x, (V x)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hc := pow_le_pow_left₀ (sq_nonneg (∫ x, (V x)^2 ∂μ)) ha 2
  have hd := mul_le_mul_of_nonneg_left hb (sq_nonneg (∫ x, V x ∂μ))
  by_cases hz : (∫ x, (V x)^2 ∂μ) = 0
  · rw [hz]
    norm_num only [zero_pow]
    exact mul_nonneg (sq_nonneg _) (integral_nonneg (fun x => pow_nonneg (hV x) _))
  · have hpos : 0 < ∫ x, (V x)^2 ∂μ := lt_of_le_of_ne hE2 (Ne.symm hz)
    have hcombined : (∫ x, (V x)^2 ∂μ)^4 ≤
        (∫ x, V x ∂μ)^2 * ((∫ x, (V x)^2 ∂μ) * (∫ x, (V x)^4 ∂μ)) := by
      nlinarith [hc, hd]
    nlinarith [hcombined]

/-- The second assertion of Lemma `lem:random_moments`, for any
probability space and any nonnegative variable with finite second moment. -/
theorem integral_sqrt_lower_bound [IsProbabilityMeasure μ] (U : Ω → ℝ)
    (hU : ∀ᵐ x ∂μ, 0 ≤ U x) (hm : AEStronglyMeasurable U μ)
    (h2 : Integrable (fun x => (U x)^2) μ) (hpos : 0 < ∫ x, U x ∂μ) :
    (∫ x, U x ∂μ) ^ (3 / 2 : ℝ) / (∫ x, (U x)^2 ∂μ) ^ (1 / 2 : ℝ) ≤
      ∫ x, Real.sqrt (U x) ∂μ := by
  have he2 : (fun x => (Real.sqrt (U x))^2) =ᵐ[μ] U := by
    filter_upwards [hU] with x hx using Real.sq_sqrt hx
  have he4 : (fun x => (Real.sqrt (U x))^4) =ᵐ[μ] (fun x => (U x)^2) := by
    filter_upwards [hU] with x hx
    calc
      _ = ((Real.sqrt (U x))^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hx]
  have h := moment_interpolation (fun x => Real.sqrt (U x))
    (fun _ => Real.sqrt_nonneg _) hm.aemeasurable.sqrt.aestronglyMeasurable
    (h2.congr he4.symm)
  rw [integral_congr_ae he2, integral_congr_ae he4] at h
  have hs0 : 0 ≤ ∫ x, Real.sqrt (U x) ∂μ := integral_nonneg (fun _ => Real.sqrt_nonneg _)
  have h20 : 0 ≤ ∫ x, (U x)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have h2pos : 0 < ∫ x, (U x)^2 ∂μ := by
    by_contra hn
    have hz : (∫ x, (U x)^2 ∂μ) = 0 := le_antisymm (le_of_not_gt hn) h20
    rw [hz, mul_zero] at h
    exact (not_le_of_gt (pow_pos hpos 3)) h
  have hnum : (∫ x, U x ∂μ) ^ (3 / 2 : ℝ) =
      (∫ x, U x ∂μ) * Real.sqrt (∫ x, U x ∂μ) := by
    calc
      _ = (∫ x, U x ∂μ) ^ (1 + 1 / 2 : ℝ) := by norm_num
      _ = (∫ x, U x ∂μ) ^ (1 : ℝ) * (∫ x, U x ∂μ) ^ (1 / 2 : ℝ) :=
        Real.rpow_add hpos _ _
      _ = _ := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hnum, ← Real.sqrt_eq_rpow]
  apply (div_le_iff₀ (Real.sqrt_pos.2 h2pos)).2
  have hsq := Real.sq_sqrt hpos.le
  have hsq2 := Real.sq_sqrt h20
  have htarget : ((∫ x, U x ∂μ) * Real.sqrt (∫ x, U x ∂μ))^2 ≤
      ((∫ x, Real.sqrt (U x) ∂μ) * Real.sqrt (∫ x, (U x)^2 ∂μ))^2 := by
    simpa only [mul_pow, hsq, hsq2, ← pow_succ] using h
  exact (sq_le_sq₀ (mul_nonneg hpos.le (Real.sqrt_nonneg _))
    (mul_nonneg hs0 (Real.sqrt_nonneg _))).1 htarget

end
end Max2SAT.MomentBounds
