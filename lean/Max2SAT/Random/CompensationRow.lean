import Max2SAT.Random.Exposure
import Max2SAT.Random.PredictableSigns

/-! The later contributions for one exposed variable, with coefficients
from the actual earlier residual comparisons. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {E : Finset (Edge n)}

theorem history_restrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Finset ι) (hAB : A ⊆ B) (z w : ι → Bool) (h : history B z w) : history A z w := by
  intro b
  by_cases hb : b ∈ A
  · have hh := h b
    simpa only [ite_eq_left hb] using (show w b = z b from by simpa [hAB hb] using hh)
  · simp [hb]

theorem known_before_antitone (free later : Finset (Fin n)) (h : later ⊆ free) :
    knownBefore E free ⊆ knownBefore E later := by
  intro b hb
  simp only [knownBefore, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  cases b with
  | inl j => exact fun hj => hb (h hj)
  | inr e => exact fun hj => hb (h hj)

theorem known_after_subset (free later : Finset (Fin n)) (i : Fin n)
    (h : later ⊆ free) (hi : i ∉ later) :
    knownAfterSigns E free i ⊆ knownBefore E later := by
  intro b hb
  rcases Finset.mem_union.1 hb with hb | hb
  · exact known_before_antitone free later h hb
  · rcases Finset.mem_image.1 hb with ⟨e, _, rfl⟩
    simp [knownBefore, current, incident_vertex, hi]

def comparisonMultiplier (K : E → Pattern m) (units : List (Literal n))
    (free : Finset (Fin n)) (i : Fin n) (z : ExposureBit E → Bool) : ℝ :=
  let preferred := decide (0 ≤ delta (generate E (sampled K z) units) free (assignment z) i)
  if assignment z i ≠ preferred then sign preferred else 0

theorem sign_abs (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]

theorem comparison_multiplier_bound (K : E → Pattern m) (units : List (Literal n))
    (free : Finset (Fin n)) (i : Fin n) (z : ExposureBit E → Bool) :
    |comparisonMultiplier K units free i z| ≤ 1 := by
  unfold comparisonMultiplier
  dsimp only
  split_ifs <;> simp [sign_abs]

theorem comparison_multiplier_known (K : E → Pattern m) (units : List (Literal n))
    (free later : Finset (Fin n)) (i : Fin n) (hi : i ∈ free) (hl : i ∉ later)
    (hsub : later ⊆ free) (z w : ExposureBit E → Bool)
    (h : history (knownBefore E later) z w) :
    comparisonMultiplier K units free i w = comparisonMultiplier K units free i z := by
  have hh := history_restrict _ _ (known_after_subset free later i hsub hl) z w h
  have hd := delta_known_after_signs K units free i hi z w hh
  have hx := h (Sum.inl i)
  have hx' : assignment w i = assignment z i := by simpa [knownBefore, hl, assignment] using hx
  simp only [comparisonMultiplier, hd, hx']

def laterCoefficient (K : E → Pattern m) (units : List (Literal n))
    (freeAt : Fin n → Finset (Fin n)) (weight : Fin n → ℝ)
    (i : Fin n) (e : Incidence E i) (z : ExposureBit E → Bool) : ℝ :=
  let j := partner i e.val.val
  weight j * comparisonMultiplier K units (freeAt j) j z *
    sign (z (current j (opposite e))) * eta (side j e.val.val) (K e.val)

theorem later_coefficient_known (K : E → Pattern m) (units : List (Literal n))
    (freeAt : Fin n → Finset (Fin n)) (weight : Fin n → ℝ)
    (i : Fin n) (e : Incidence E i) (later : Finset (Fin n))
    (hj : partner i e.val.val ∈ freeAt (partner i e.val.val))
    (hl : partner i e.val.val ∉ later) (hsub : later ⊆ freeAt (partner i e.val.val))
    (z w : ExposureBit E → Bool) (h : history (knownBefore E later) z w) :
    laterCoefficient K units freeAt weight i e w = laterCoefficient K units freeAt weight i e z := by
  have hm := comparison_multiplier_known K units _ later _ hj hl hsub z w h
  have hc := h (current (partner i e.val.val) (opposite e))
  have hmem : current (partner i e.val.val) (opposite e) ∈ knownBefore E later := by
    simp [knownBefore, current, incident_vertex, hl]
  have hc' : w (current (partner i e.val.val) (opposite e)) =
      z (current (partner i e.val.val) (opposite e)) := by simpa [hmem] using hc
  simp only [laterCoefficient, hm, hc']

theorem later_coefficient_bound (K : E → Pattern m) (hK : ∀ e, size (K e) ≤ m)
    (units : List (Literal n)) (freeAt : Fin n → Finset (Fin n)) (weight : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (i : Fin n) (e : Incidence E i) (z : ExposureBit E → Bool) :
    |laterCoefficient K units freeAt weight i e z| ≤ weight (partner i e.val.val) * (m:ℝ)/2 := by
  let j := partner i e.val.val
  have hm := comparison_multiplier_bound K units (freeAt j) j z
  have he := deviation_coefficient_bound K hK j (opposite e)
  simp only [laterCoefficient, abs_mul, sign_abs, mul_one, abs_of_nonneg (hw _)]
  have hm' := mul_le_mul_of_nonneg_left hm (hw j)
  have he' : |eta (side j e.val.val) (K e.val)| ≤ (m:ℝ)/2 := he
  calc
    _ ≤ weight j * ((m:ℝ)/2) := by
      apply mul_le_mul
      · simpa only [mul_one] using hm'
      · exact he'
      · exact abs_nonneg _
      · exact hw j
    _ = _ := by ring

/-- Conditional exponential estimate for the whole incoming row. The
theta signs are jointly independent, even though they share x_i. -/
theorem conditional_compensation_row_mgf (K : E → Pattern m) (units : List (Literal n))
    (freeAt : Fin n → Finset (Fin n)) (weight : Fin n → ℝ)
    (i : Fin n) (later : Finset (Fin n)) (hi : i ∈ later) (S : Finset (Incidence E i))
    (hj : ∀ e ∈ S, partner i e.val.val ∈ freeAt (partner i e.val.val))
    (hl : ∀ e ∈ S, partner i e.val.val ∉ later)
    (hsub : ∀ e ∈ S, later ⊆ freeAt (partner i e.val.val))
    (z : ExposureBit E → Bool) (t : ℝ) :
    expect (condition (fairBits (ExposureBit E)) (history (knownBefore E later) z)
      (fair_history_positive _ z))
      (fun w => Real.exp (t * ∑ e : S,
        laterCoefficient K units freeAt weight i e.val w *
          sign (theta (w (current i e.val)) (assignment w i)))) ≤
    Real.exp (t^2*(∑ e : S, (laterCoefficient K units freeAt weight i e.val z)^2)/2) := by
  let q := condition (fairBits (ExposureBit E)) (history (knownBefore E later) z)
    (fair_history_positive _ z)
  let a : S → ℝ := fun e => laterCoefficient K units freeAt weight i e.val z
  have he := expect_congr_support q
    (fun w => Real.exp (t * ∑ e : S, laterCoefficient K units freeAt weight i e.val w *
      sign (theta (w (current i e.val)) (assignment w i))))
    (fun w => Real.exp (t * ∑ e : S, a e *
      sign (theta (w (current i e.val)) (assignment w i)))) (by
        intro w hw
        have hh := condition_support _ _ _ w hw
        congr 2
        apply Finset.sum_congr rfl
        intro e _
        rw [later_coefficient_known K units freeAt weight i e.val later
          (hj e.val e.property) (hl e.val e.property) (hsub e.val e.property) z w hh])
  change expect q _ ≤ _
  rw [he]
  have hlaw := congrArg (fun p => expect p (fun r => Real.exp (t * ∑ e : S, a e * sign (r e))))
    (theta_subrow_law (E := E) later i hi z S)
  rw [expect_push] at hlaw
  change expect q _ = _ at hlaw
  rw [hlaw]
  exact signed_sum_mgf a t

end
end Max2SAT.RandomInput
