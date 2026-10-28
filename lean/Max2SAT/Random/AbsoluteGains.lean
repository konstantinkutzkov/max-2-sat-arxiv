import Max2SAT.Random.MomentBounds
import Max2SAT.Random.FourthMoment

/-! The two assertions of Lemma `lem:random_moments`, connected to the
finite sampling model used in the exposure lemma. -/
namespace Max2SAT.FiniteLaw
noncomputable section
variable {α : Type*} [Fintype α]

theorem expect_mono (p : Law α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    expect p f ≤ expect p g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x))

theorem moment_interpolation (p : Law α) (V : α → ℝ) (hV : ∀ x, 0 ≤ V x) :
    (expect p (fun x => (V x)^2))^3 ≤
      (expect p V)^2 * expect p (fun x => (V x)^4) := by
  let : MeasurableSpace α := ⊤
  have h := MomentBounds.moment_interpolation (μ := p.toMeasure) V hV
    (.of_discrete) (.of_finite)
  simpa only [integral_eq_expect] using h

theorem sqrt_lower_bound (p : Law α) (U : α → ℝ)
    (hU : ∀ x, 0 ≤ U x) (hpos : 0 < expect p U) :
    (expect p U) ^ (3 / 2 : ℝ) / (expect p (fun x => (U x)^2)) ^ (1 / 2 : ℝ) ≤
      expect p (fun x => Real.sqrt (U x)) := by
  let : MeasurableSpace α := ⊤
  have h := MomentBounds.integral_sqrt_lower_bound (μ := p.toMeasure) U
    (Filter.Eventually.of_forall hU) (.of_discrete) (.of_finite)
    (by simpa only [integral_eq_expect] using hpos)
  simpa only [integral_eq_expect] using h

end
end Max2SAT.FiniteLaw

namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem abs_four (z : ℝ) : |z|^4 = z^4 := by
  rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, sq_abs, ← pow_mul]

theorem signed_sum_absolute (a : ι → ℝ) :
    Real.sqrt ((∑ i, (a i)^2) / 3) ≤
      expect (fairBits ι) (fun z => |∑ i, sign (z i) * a i|) := by
  let Y := ∑ i, (a i)^2
  let A := expect (fairBits ι) (fun z => |∑ i, sign (z i) * a i|)
  have hY : 0 ≤ Y := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hA : 0 ≤ A := expect_nonneg _ (fun _ => abs_nonneg _)
  have h := moment_interpolation (fairBits ι)
    (fun z => |∑ i, sign (z i) * a i|) (fun _ => abs_nonneg _)
  simp only [sq_abs, abs_four, signed_sum_second] at h
  have h4 := mul_le_mul_of_nonneg_left (signed_sum_fourth_le a) (sq_nonneg A)
  have hbound : Y^3 ≤ A^2 * (3 * Y^2) := h.trans h4
  apply Real.sqrt_le_iff.2
  refine ⟨hA, ?_⟩
  by_cases hz : Y = 0
  · rw [show (∑ i, (a i)^2) = 0 from hz]
    simpa using sq_nonneg A
  · have hp : 0 < Y := lt_of_le_of_ne hY (Ne.symm hz)
    have hs : Y * Y^2 ≤ (3 * A^2) * Y^2 := by nlinarith [hbound]
    have hc := (mul_le_mul_iff_left₀ (sq_pos_of_pos hp)).1 hs
    change Y / 3 ≤ A^2
    linarith

/-- Negating every sign preserves the joint fair law, for an arbitrary
test function. This is the symmetry used after truncation. -/
theorem signed_sum_symmetric (a : ι → ℝ) (f : ℝ → ℝ) :
    expect (fairBits ι) (fun z => f (-(∑ i, sign (z i) * a i))) =
      expect (fairBits ι) (fun z => f (∑ i, sign (z i) * a i)) := by
  have h := congrArg (fun p => expect p (fun z => f (∑ i, sign (z i) * a i)))
    (fairBits_multiply (fun _ : ι => false))
  rw [expect_push] at h
  have he : ∀ z : ι → Bool,
      (∑ i, sign (multiplyBits (fun _ : ι => false) z i) * a i) =
        -(∑ i, sign (z i) * a i) := by
    intro z
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases hzi : z i <;> norm_num [multiplyBits, sign, hzi]
  simpa only [he] using h

omit [Fintype ι] [DecidableEq ι] in
theorem truncation_loss (z K : ℝ) (hK : 0 < K) :
    z - z^2 / (4*K) ≤ min z K := by
  apply le_min
  · have h : 0 ≤ z^2 / (4*K) := div_nonneg (sq_nonneg _) (by positivity)
    linarith
  · have h : (z-K) * (4*K) ≤ z^2 := by nlinarith [sq_nonneg (z-2*K)]
    have hd := (le_div_iff₀ (show 0 < 4*K by positivity)).2 h
    linarith

omit [Fintype ι] [DecidableEq ι] in
theorem shifted_truncation (b z K : ℝ) (hK : 0 ≤ K) :
    min |z| K ≤ min |b+z| K + min |b-z| K := by
  have ht : 2 * |z| ≤ |b+z| + |b-z| := by
    have h := abs_sub (b+z) (b-z)
    have he : (b+z)-(b-z) = 2*z := by ring
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    exact h
  by_cases h1 : |b+z| ≤ K
  · rw [min_eq_left h1]
    by_cases h2 : |b-z| ≤ K
    · rw [min_eq_left h2]
      exact (min_le_left _ _).trans (by linarith [abs_nonneg z])
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h2))]
      exact (min_le_right _ _).trans (le_add_of_nonneg_left (abs_nonneg _))
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h1))]
    exact (min_le_right _ _).trans (le_add_of_nonneg_right (le_min (abs_nonneg _) hK))

theorem truncated_absolute_gain (a : ι → ℝ) (b K : ℝ) (hK : 0 < K) :
    (1/2 : ℝ) * (Real.sqrt ((∑ i, (a i)^2)/3) - (∑ i, (a i)^2)/(4*K)) ≤
      expect (fairBits ι) (fun z => min |b + ∑ i, sign (z i) * a i| K) := by
  let Z : (ι → Bool) → ℝ := fun z => ∑ i, sign (z i) * a i
  have ht := expect_mono (fairBits ι) (fun z => truncation_loss |Z z| K hK)
  have he : expect (fairBits ι) (fun z => |Z z| - |Z z|^2/(4*K)) =
      expect (fairBits ι) (fun z => |Z z|) - (∑ i, (a i)^2)/(4*K) := by
    simp only [expect, mul_sub, Finset.sum_sub_distrib, ← mul_div_assoc,
      ← Finset.sum_div, sq_abs]
    rw [show (∑ z, (fairBits ι).mass z * (Z z)^2) = ∑ i, (a i)^2 from
      signed_sum_second a]
  rw [he] at ht
  have hl := signed_sum_absolute a
  have hs := expect_mono (fairBits ι) (fun z => shifted_truncation b (Z z) K hK.le)
  rw [expect_add] at hs
  have hsym : expect (fairBits ι) (fun z => min |b-Z z| K) =
      expect (fairBits ι) (fun z => min |b+Z z| K) := by
    simpa only [sub_eq_add_neg] using signed_sum_symmetric a (fun x => min |b+x| K)
  rw [hsym] at hs
  change Real.sqrt ((∑ i, (a i)^2)/3) ≤ expect (fairBits ι) (fun z => |Z z|) at hl
  change (1/2 : ℝ) * _ ≤ expect (fairBits ι) (fun z => min |b+Z z| K)
  linarith

end
end Max2SAT.RandomInput
