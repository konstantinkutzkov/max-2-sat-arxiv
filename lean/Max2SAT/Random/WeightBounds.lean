import Max2SAT.Random.Support
import Max2SAT.Random.AbsoluteGains

/-! The normalization inequalities used for the actual rational weights
of RandomFormula, including the squared-influence budget. -/
namespace Max2SAT.Random
noncomputable section

theorem sqrt_denominator_bounds (d : ℕ) (hd : 0 < d) :
    Real.sqrt (d : ℝ) ≤ (Nat.sqrt (d-1)+1 : ℕ) ∧
    ((Nat.sqrt (d-1)+1 : ℕ) : ℝ) ≤ 2*Real.sqrt (d : ℝ) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hceil : (d : ℝ) ≤ (((Nat.sqrt (d-1)+1 : ℕ) : ℝ))^2 := by
    exact_mod_cast (ceiling_sqrt d hd).1
  have hlow := Real.sqrt_le_iff.2 ⟨by positivity, hceil⟩
  have hs : (Nat.sqrt (d-1) : ℝ)^2 ≤ d := by
    exact_mod_cast (Nat.sqrt_le' (d-1)).trans (Nat.sub_le _ _)
  have hs' : (Nat.sqrt (d-1) : ℝ) ≤ Real.sqrt (d : ℝ) :=
    (Real.le_sqrt (by positivity) hd0).2 hs
  have hr : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := (Real.le_sqrt (by norm_num) hd0).2 (by simpa using hd1)
  refine ⟨hlow, ?_⟩
  push_cast
  linarith

theorem weight_sqrt_bounds (F : Formula n) (i : Fin n)
    (hd : 0 < (neighbors F i).card) :
    1/(2*Real.sqrt ((neighbors F i).card : ℝ)) ≤ (weight F i : ℝ) ∧
    (weight F i : ℝ) ≤ 1/Real.sqrt ((neighbors F i).card : ℝ) := by
  have hb := sqrt_denominator_bounds _ hd
  have hp : 0 < Real.sqrt ((neighbors F i).card : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hd)
  have he : (weight F i : ℝ) = 1/((Nat.sqrt ((neighbors F i).card-1)+1 : ℕ) : ℝ) := by
    simp only [weight, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  rw [he]
  constructor
  · exact one_div_le_one_div_of_le (by positivity) hb.2
  · exact one_div_le_one_div_of_le hp hb.1

theorem weight_squared_degree (F : Formula n) (i : Fin n) :
    (weight F i : ℝ)^2 * (neighbors F i).card ≤ 1 := by
  by_cases hd : 0 < (neighbors F i).card
  · have hw : 0 < (weight F i : ℝ) := by exact_mod_cast weight_positive F i
    have hp : 0 < Real.sqrt ((neighbors F i).card : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hd)
    have h := (le_div_iff₀ hp).1 (weight_sqrt_bounds F i hd).2
    have hs := pow_le_pow_left₀ (mul_nonneg hw.le hp.le) h 2
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), one_pow] using hs
  · have hz : (neighbors F i).card = 0 := by omega
    simp [hz]

end
end Max2SAT.Random
