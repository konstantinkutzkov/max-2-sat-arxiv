import Max2SAT.Random.ProductTools
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Relate the finite probability laws used by the algorithm analysis to
mathlib's probability measures. This permits reuse of general analytic
inequalities without changing the sampling model. -/
namespace Max2SAT.FiniteLaw
noncomputable section
open MeasureTheory
variable {α : Type*} [Fintype α]

def Law.toPMF (p : Law α) : PMF α := PMF.ofFintype
  (fun a => ENNReal.ofReal (p.mass a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => p.nonneg a), p.total]
    simp)

variable [MeasurableSpace α]

def Law.toMeasure (p : Law α) : Measure α := p.toPMF.toMeasure

instance (p : Law α) : IsProbabilityMeasure p.toMeasure := by
  unfold Law.toMeasure
  infer_instance

variable [MeasurableSingletonClass α]

theorem toMeasure_singleton (p : Law α) (a : α) :
    p.toMeasure {a} = ENNReal.ofReal (p.mass a) := by
  exact p.toPMF.toMeasure_apply_singleton a (measurableSet_singleton a)

theorem integral_eq_expect (p : Law α) (f : α → ℝ) :
    ∫ a, f a ∂p.toMeasure = expect p f := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [measureReal_def, toMeasure_singleton, ENNReal.toReal_ofReal (p.nonneg _),
    smul_eq_mul, expect]

end
end Max2SAT.FiniteLaw
