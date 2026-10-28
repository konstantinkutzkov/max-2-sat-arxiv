import Max2SAT.Random.Exposure
import Max2SAT.Random.AbsoluteGains

/-! Step 1 of Lemma `lem:random_requirements`: the conditional expected
requirement created by the actual residual-gain comparison. -/
namespace Max2SAT.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α]

theorem fair_nonpreferred_expectation (p : Law α) (preferred : α → Bool) (f : α → ℝ) :
    expect (tensor fair p) (fun z => if z.1 ≠ preferred z.2 then f z.2 else 0) =
      expect p f / 2 := by
  simp only [expect, tensor, Fintype.sum_prod_type, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases preferred x <;> norm_num [fair] <;> ring

end
end Max2SAT.FiniteLaw

namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {E : Finset (Edge n)}

def truncatedRequirement (K : E → Pattern m) (units : List (Literal n))
    (free : Finset (Fin n)) (i : Fin n) (cap : ℝ) (z : ExposureBit E → Bool) : ℝ :=
  let D := delta (generate E (sampled K z) units) free (assignment z) i
  if assignment z i ≠ decide (0 ≤ D) then min |D| cap else 0

theorem conditional_truncated_requirement (K : E → Pattern m) (units : List (Literal n))
    (free : Finset (Fin n)) (i : Fin n) (hi : i ∈ free) (z : ExposureBit E → Bool)
    (cap : ℝ) (hcap : 0 < cap) :
    (1/4 : ℝ) * (Real.sqrt ((∑ e : Incidence E i, (coefficient K free z i e)^2)/3) -
      (∑ e : Incidence E i, (coefficient K free z i e)^2)/(4*cap)) ≤
    expect (condition (fairBits (ExposureBit E)) (history (knownBefore E free) z)
      (fair_history_positive _ z)) (truncatedRequirement K units free i cap) := by
  let q := condition (fairBits (ExposureBit E)) (history (knownBefore E free) z)
    (fair_history_positive _ z)
  let D : (Incidence E i → Bool) → ℝ := fun r => unitBias units i +
    ∑ e, sign (r e)*coefficient K free z i e
  let f : Bool × (Incidence E i → Bool) → ℝ :=
    fun r => if r.1 ≠ decide (0 ≤ D r.2) then min |D r.2| cap else 0
  have hj := fresh_bit_and_vector (knownBefore E free) z (fair_history_positive _ z)
    (Sum.inl i) (by simp [knownBefore, hi]) (current i) (current_injective i)
    (current_fresh free i hi) (fun e => by simp [current])
  have he : expect q (truncatedRequirement K units free i cap) =
      expect (tensor fair (fairBits (Incidence E i))) f := by
    rw [← hj, expect_push]
    apply expect_congr_support
    intro w hw
    have hh := condition_support _ _ _ w hw
    have hd : delta (generate E (sampled K w) units) free (assignment w) i =
        D (fun e => w (current i e)) := by
      rw [delta_exposure E K units free w i hi]
      simp only [D, coefficient_known K free z w i hh]
    simp only [truncatedRequirement, hd, f, assignment]
  change _ ≤ expect q _
  rw [he]
  change _ ≤ expect (tensor fair (fairBits (Incidence E i)))
    (fun r => if r.1 ≠ decide (0 ≤ D r.2) then min |D r.2| cap else 0)
  rw [fair_nonpreferred_expectation (fairBits (Incidence E i))
    (fun r => decide (0 ≤ D r)) (fun r => min |D r| cap)]
  have h := truncated_absolute_gain (coefficient K free z i) (unitBias units i) cap hcap
  change _ ≤ expect (fairBits (Incidence E i)) (fun r => min |D r| cap) at h
  linarith

/-- The simple numerical bound used in the paper after truncation. -/
theorem truncated_mean_constant (Y cap : ℝ) (hY : 0 ≤ Y) (hcap : 0 < cap)
    (hlarge : Real.sqrt Y ≤ cap) :
    Real.sqrt Y / 13 ≤ (1/4 : ℝ) * (Real.sqrt (Y/3)-Y/(4*cap)) := by
  have h3 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hc : (29 : ℝ)/52 ≤ 1/Real.sqrt 3 := by
    apply (le_div_iff₀ h3).2
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hs := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg Y)
  have hr : (29 : ℝ)/52 * Real.sqrt Y ≤ Real.sqrt (Y/3) := by
    rw [Real.sqrt_div hY]
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hs
  have hloss : Y/(4*cap) ≤ Real.sqrt Y/4 := by
    apply (div_le_iff₀ (show 0 < 4*cap by positivity)).2
    have h := mul_le_mul_of_nonneg_left hlarge (Real.sqrt_nonneg Y)
    nlinarith [Real.sq_sqrt hY]
  linarith

theorem conditional_requirement_mean (K : E → Pattern m) (units : List (Literal n))
    (free : Finset (Fin n)) (i : Fin n) (hi : i ∈ free) (z : ExposureBit E → Bool)
    (cap w : ℝ) (hcap : 0 < cap) (hw : 0 ≤ w)
    (hlarge : Real.sqrt (∑ e : Incidence E i, (coefficient K free z i e)^2) ≤ cap) :
    w * Real.sqrt (∑ e : Incidence E i, (coefficient K free z i e)^2)/13 ≤
    expect (condition (fairBits (ExposureBit E)) (history (knownBefore E free) z)
      (fair_history_positive _ z)) (fun r => truncatedRequirement K units free i cap r * w) := by
  rw [expect_mul_const]
  have hY : 0 ≤ ∑ e : Incidence E i, (coefficient K free z i e)^2 :=
    Finset.sum_nonneg (fun e _ => sq_nonneg _)
  have h := (truncated_mean_constant _ cap hY hcap hlarge).trans
    (conditional_truncated_requirement K units free i hi z cap hcap)
  nlinarith [mul_le_mul_of_nonneg_right h hw]

theorem truncated_requirement_bounds (K : E → Pattern m) (units : List (Literal n))
    (free : Finset (Fin n)) (i : Fin n) (cap w : ℝ) (hcap : 0 ≤ cap) (hw : 0 ≤ w)
    (z : ExposureBit E → Bool) :
    0 ≤ truncatedRequirement K units free i cap z * w ∧
    truncatedRequirement K units free i cap z * w ≤ cap*w := by
  unfold truncatedRequirement
  dsimp only
  split_ifs
  · exact ⟨mul_nonneg (le_min (abs_nonneg _) hcap) hw,
      mul_le_mul_of_nonneg_right (min_le_right _ _) hw⟩
  · simp only [zero_mul, le_refl, true_and]
    exact mul_nonneg hcap hw

theorem truncated_requirement_le_full (K : E → Pattern m) (units : List (Literal n))
    (free : Finset (Fin n)) (i : Fin n) (cap w : ℝ) (hw : 0 ≤ w)
    (z : ExposureBit E → Bool) :
    truncatedRequirement K units free i cap z * w ≤
      let D := delta (generate E (sampled K z) units) free (assignment z) i
      if assignment z i ≠ decide (0 ≤ D) then w*(|D|+1) else 0 := by
  unfold truncatedRequirement
  dsimp only
  split_ifs
  · have h := mul_le_mul_of_nonneg_right
      (min_le_left |delta (generate E (sampled K z) units) free (assignment z) i| cap) hw
    nlinarith
  · simp

end
end Max2SAT.RandomInput
