import Max2SAT.Random.FiniteSupport
import Mathlib.Probability.Moments.Variance

/-! First moments and the ordinary measure-theoretic variance of the
original integer coefficients agree exactly with their finite encoding. -/
namespace Max2SAT.FiniteLaw
noncomputable section
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω]

theorem integer_variance (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : Ω → ℤ) (hJ : Measurable J) (K : ℕ)
    (hK : ∀ᵐ ω ∂μ, |J ω|≤(K:ℤ)) (a : ℝ)
    (hm : (∫ ω, (J ω:ℝ) ∂μ)=a) :
    expect (integerLaw μ J hJ K) (fun z => ((z:ℤ)-a)^2)=
      variance (fun ω => (J ω:ℝ)) μ := by
  rw [integer_expect μ J hJ K hK (fun z => ((z:ℝ)-a)^2)]
  have hmeas : AEMeasurable (fun ω => (J ω:ℝ)) μ :=
    ((measurable_of_countable (fun z : ℤ => (z:ℝ))).comp hJ).aemeasurable
  rw [variance_eq_integral hmeas,hm]

end
end Max2SAT.FiniteLaw
