import Max2SAT.Random.AdaptiveRanges
import Max2SAT.Random.SignMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! The concentration mechanism for later compensation: coefficients may
depend on the past, while each sign remains fair conditional on that past. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {Ω β : Type*} [Fintype Ω] [Fintype β]

def signExposure (p : Law Ω) (k : ℕ) (H : ℕ → Ω → β)
    (a : ℕ → Ω → ℝ) (R : ℕ → Ω → Bool) (b : ℕ → β → ℝ)
    (href : ∀ i j, i ≤ j → ∀ x y, H j x = H j y → H i x = H i y)
    (hknown : ∀ j, j < k → Known (H j) (a j))
    (hsign : ∀ j, j < k → ∀ x y, H (j+1) x = H (j+1) y → R j x = R j y)
    (hfresh : ∀ j, j < k → ∀ x, 0 < p.mass x → push (fiber p (H j) (H j x)) (R j) = fair)
    (hbound : ∀ j, j < k → ∀ x, 0 < p.mass x → |a j x| ≤ b j (H j x)) :
    Exposure (β := β) p k where
  history := H
  increment j x := a j x * sign (R j x)
  lower j x := -b j x
  upper := b
  refines := href
  adapted j hj x y h := by
    dsimp only
    rw [hknown j hj x y (href j (j+1) (by omega) x y h), hsign j hj x y h]
  centered j hj x hx := by
    have he := expect_congr_support (fiber p (H j) (H j x))
      (fun y => a j y * sign (R j y)) (fun y => sign (R j y) * a j x) (by
        intro y hy
        have hh := (fiber_support p (H j) (H j x) (fiber_event_positive p (H j) x hx) y hy).1
        rw [hknown j hj y x hh, mul_comm])
    rw [he, expect_mul_const]
    have hs := congrArg (fun q => expect q sign) (hfresh j hj x hx)
    rw [expect_push, fair_sign_mean] at hs
    rw [hs, zero_mul]
  bounds j hj x hx := by
    have h := abs_le.1 (hbound j hj x hx)
    cases R j x <;> simp only [sign, Bool.false_eq_true, ↓reduceIte, mul_neg,
      mul_one, Set.mem_Icc]
    · constructor <;> linarith [h.1, h.2]
    · exact h

theorem predictable_sign_tail (p : Law Ω) (k : ℕ) (H : ℕ → Ω → β)
    (a : ℕ → Ω → ℝ) (R : ℕ → Ω → Bool) (b : ℕ → β → ℝ)
    (href : ∀ i j, i ≤ j → ∀ x y, H j x = H j y → H i x = H i y)
    (hknown : ∀ j, j < k → Known (H j) (a j))
    (hsign : ∀ j, j < k → ∀ x y, H (j+1) x = H (j+1) y → R j x = R j y)
    (hfresh : ∀ j, j < k → ∀ x, 0 < p.mass x → push (fiber p (H j) (H j x)) (R j) = fair)
    (hbound : ∀ j, j < k → ∀ x, 0 < p.mass x → |a j x| ≤ b j (H j x))
    (B c : ℝ) (hB : 0 < B) (hc : 0 < c)
    (hbudget : ∀ x, 0 < p.mass x → (∑ j ∈ Finset.range k, (2*b j (H j x))^2) ≤ B) :
    prob p (fun x => (∑ j ∈ Finset.range k, a j x * sign (R j x)) < -c) ≤
      Real.exp (-2*c^2/B) := by
  let e := signExposure p k H a R b href hknown hsign hfresh hbound
  apply e.lower_tail B c hB hc
  intro x hx
  simpa only [e, Exposure.budget, signExposure, sub_neg_eq_add, ← two_mul] using hbudget x hx

end
end Max2SAT.RandomInput

namespace Max2SAT.FiniteLaw
noncomputable section
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

theorem expect_product_separable (p : ι → Law α) (f : ι → α → ℝ) :
    expect (product p) (fun x => ∏ i, f i (x i)) = ∏ i, expect (p i) (f i) := by
  simp only [expect, product]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact (Finset.prod_mul_distrib).symm

end
end Max2SAT.FiniteLaw

namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem signed_sum_mgf (a : ι → ℝ) (t : ℝ) :
    expect (fairBits ι) (fun z => Real.exp (t*(∑ i, a i * sign (z i)))) ≤
      Real.exp (t^2*(∑ i, (a i)^2)/2) := by
  have he : ∀ z : ι → Bool, Real.exp (t*(∑ i, a i * sign (z i))) =
      ∏ i, Real.exp (t*(a i*sign (z i))) := by
    intro z
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [he]
  rw [show fairBits ι = product (fun _ : ι => fair) from rfl,
    expect_product_separable (fun _ : ι => fair) (fun i z => Real.exp (t*(a i*sign z)))]
  have hb : ∀ i, expect fair (fun z => Real.exp (t*(a i*sign z))) ≤
      Real.exp (t^2*(a i)^2/2) := by
    intro i
    have h := Real.cosh_le_exp_half_sq (t*a i)
    rw [Real.cosh_eq] at h
    have heq : (t*a i)^2/2 = t^2*(a i)^2/2 := by ring
    rw [heq] at h
    simpa [expect, fair, sign, mul_neg, mul_assoc, mul_comm, mul_left_comm, add_comm, div_eq_mul_inv,
      mul_add] using h
  calc
    _ ≤ ∏ i, Real.exp (t^2*(a i)^2/2) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact expect_nonneg _ (fun _ => (Real.exp_pos _).le)
      · intro i _; exact hb i
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [← Finset.sum_div, ← Finset.mul_sum]

end
end Max2SAT.RandomInput
