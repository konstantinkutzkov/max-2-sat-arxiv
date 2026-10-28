import Max2SAT.Random.AbsoluteGains
import Mathlib.Probability.Moments.SubGaussian

/-! The one-step exponential estimate in Lemma `lem:random_ranges`.
This file does not yet prove the sequential, history-dependent range
bound or its bounded-differences corollary. -/
namespace Max2SAT.FiniteLaw
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α]

theorem ae_toMeasure_iff [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : Law α) (P : α → Prop) :
    (∀ᵐ x ∂p.toMeasure, P x) ↔ ∀ x, 0 < p.mass x → P x := by
  rw [ae_iff_of_countable]
  simp only [toMeasure_singleton, ne_eq, ENNReal.ofReal_eq_zero, not_le]

/-- Hoeffding's lemma, with the sharp range-length constant 1/8.
The bounds are required only on positive-mass outcomes, so this statement
also applies directly to a conditional law on a history event. -/
theorem range_mgf (p : Law α) (X : α → ℝ) (a b t : ℝ)
    (hb : ∀ x, 0 < p.mass x → X x ∈ Set.Icc a b) :
    expect p (fun x => Real.exp (t * (X x - expect p X))) ≤
      Real.exp (t^2 * (b-a)^2 / 8) := by
  let : MeasurableSpace α := ⊤
  have hs := hasSubgaussianMGF_of_mem_Icc
    (μ := p.toMeasure) (X := X) (.of_discrete) ((ae_toMeasure_iff p _).2 hb)
  have h := hs.mgf_le t
  simp only [mgf, integral_eq_expect] at h
  have he : (((‖b-a‖₊ / 2)^2 : ℝ≥0) : ℝ) * t^2 / 2 = t^2 * (b-a)^2 / 8 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
      Real.norm_eq_abs, div_pow, sq_abs]
    ring
  rw [he] at h
  exact h

theorem centered_range_mgf (p : Law α) (X : α → ℝ) (a b t : ℝ)
    (hb : ∀ x, 0 < p.mass x → X x ∈ Set.Icc a b) (hc : expect p X = 0) :
    expect p (fun x => Real.exp (t * X x)) ≤ Real.exp (t^2 * (b-a)^2 / 8) := by
  simpa only [hc, sub_zero] using range_mgf p X a b t hb

/-- Finite exponential Markov inequality. The event may be non-strict;
the concentration statements in the paper use a strict lower tail. -/
theorem exponential_markov (p : Law α) (Z : α → ℝ) (t a : ℝ) (ht : 0 < t) :
    prob p (fun x => a ≤ Z x) ≤ Real.exp (-t*a) * expect p (fun x => Real.exp (t*Z x)) := by
  have h : Real.exp (t*a) * prob p (fun x => a ≤ Z x) ≤
      expect p (fun x => Real.exp (t*Z x)) := by
    simp only [prob, expect, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : a ≤ Z x
    · rw [ite_eq_left hx, mul_comm (Real.exp (t*a))]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx ht.le))
        (p.nonneg x)
    · rw [ite_eq_right hx, mul_zero]
      exact mul_nonneg (p.nonneg x) (Real.exp_pos _).le
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (-t*a)).le
  have he : Real.exp (-t*a) * Real.exp (t*a) = 1 := by
    rw [← Real.exp_add, show -t*a + t*a = 0 by ring, Real.exp_zero]
  simpa only [← mul_assoc, he, one_mul] using hh

theorem lower_tail_of_mgf (p : Law α) (Z : α → ℝ) (B a : ℝ)
    (hB : 0 < B) (ha : 0 < a)
    (hmgf : ∀ t : ℝ, expect p (fun x => Real.exp (-t * Z x)) ≤ Real.exp (t^2 * B/8)) :
    prob p (fun x => Z x < -a) ≤ Real.exp (-2*a^2/B) := by
  let t := 4*a/B
  have ht : 0 < t := div_pos (mul_pos (by norm_num) ha) hB
  have hevent : prob p (fun x => Z x < -a) ≤ prob p (fun x => a ≤ -Z x) := by
    unfold prob
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : Z x < -a
    · have hy : a ≤ -Z x := by linarith
      simp only [ite_eq_left hx, ite_eq_left hy, le_refl]
    · simp only [ite_eq_right hx]
      split_ifs <;> simp_all [p.nonneg]
  have hm := exponential_markov p (fun x => -Z x) t a ht
  have hm' : expect p (fun x => Real.exp (t * -Z x)) ≤ Real.exp (t^2*B/8) := by
    simpa only [mul_neg, neg_mul] using hmgf t
  have h := hevent.trans (hm.trans (mul_le_mul_of_nonneg_left hm' (Real.exp_pos _).le))
  rw [← Real.exp_add] at h
  have hexponent : -t*a + t^2*B/8 = -2*a^2/B := by
    dsimp [t]
    field_simp [ne_of_gt hB]
    ring
  rwa [hexponent] at h

end
end Max2SAT.FiniteLaw
