import Max2SAT.Random.MeasureBridge
import Mathlib.Probability.Independence.Basic

/-! Finite random variables on an arbitrary probability space. The sampling
space need not be finite: its coordinate distributions determine the law. -/
namespace Max2SAT.FiniteLaw
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω α ι : Type*} [MeasurableSpace Ω] [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

def Law.ofMeasure (μ : Measure α) [IsProbabilityMeasure μ] : Law α where
  mass a := μ.real {a}
  nonneg _ := ENNReal.toReal_nonneg
  total := by simp

theorem toMeasure_ofMeasure (μ : Measure α) [IsProbabilityMeasure μ] :
    (Law.ofMeasure μ).toMeasure = μ := by
  apply Measure.ext_of_singleton
  intro a
  rw [toMeasure_singleton]
  exact ENNReal.ofReal_toReal (measure_ne_top μ {a})

theorem prob_eq_measure (p : Law α) (P : α → Prop) :
    prob p P = p.toMeasure.real {a | P a} := by
  classical
  let s := Finset.univ.filter P
  have hs : (s : Set α) = {a | P a} := by ext a; simp [s]
  rw [← hs, ← sum_measureReal_singleton]
  simp only [measureReal_def, toMeasure_singleton,
    ENNReal.toReal_ofReal (p.nonneg _)]
  simp [s, Finset.sum_filter, prob]

theorem toMeasure_product [Fintype ι] [DecidableEq ι] (p : ι → Law α) :
    (product p).toMeasure = Measure.pi (fun i => (p i).toMeasure) := by
  apply Measure.ext_of_singleton
  intro x
  rw [toMeasure_singleton, Measure.pi_singleton]
  simp only [product, toMeasure_singleton]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => (p i).nonneg (x i))

def coordinateLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (_hY : Measurable Y) : Law α :=
  Law.ofMeasure (μ.map Y)

theorem coordinate_expect (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (hY : Measurable Y) (f : α → ℝ) :
    expect (coordinateLaw μ Y hY) f = ∫ ω, f (Y ω) ∂μ := by
  rw [← integral_eq_expect, coordinateLaw, toMeasure_ofMeasure]
  exact integral_map hY.aemeasurable (measurable_of_countable f).aestronglyMeasurable

theorem independent_event [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ι → Ω → α)
    (hY : ∀ i, Measurable (Y i)) (hi : iIndepFun Y μ) (P : (ι → α) → Prop) :
    prob (product (fun i => coordinateLaw μ (Y i) (hY i))) P =
      μ.real {ω | P (fun i => Y i ω)} := by
  rw [prob_eq_measure, toMeasure_product]
  simp only [coordinateLaw, toMeasure_ofMeasure]
  rw [← hi.map_fun_eq_pi_map (fun i => (hY i).aemeasurable)]
  simp only [measureReal_def]
  rw [Measure.map_apply (.of_eval hY) (Set.to_countable _).measurableSet]
  rfl

theorem coordinate_support (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (hY : Measurable Y) (P : α → Prop)
    (hP : ∀ᵐ ω ∂μ, P (Y ω)) (a : α)
    (ha : 0<(coordinateLaw μ Y hY).mass a) : P a := by
  by_contra h
  have hz : μ (Y ⁻¹' {a})=0 := measure_mono_null
    (by intro ω hω; change Y ω=a at hω; change ¬P (Y ω); simpa only [hω] using h)
    (ae_iff.mp hP)
  have hm : (coordinateLaw μ Y hY).mass a=0 := by
    change (μ.map Y).real {a}=0
    simp only [measureReal_def, Measure.map_apply hY (measurableSet_singleton a), hz,
      ENNReal.toReal_zero]
  linarith

end
end Max2SAT.FiniteLaw
