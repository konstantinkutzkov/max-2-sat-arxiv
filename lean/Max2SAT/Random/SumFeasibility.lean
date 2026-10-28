import Max2SAT.Random.AccumulatedRequirements
import Max2SAT.Random.CompensationTail

/-! The sum of the strict score comparisons is A+Q. Combining the two
completed estimates gives the joint formula/assignment feasibility bound
used before counting candidates in the main random-input proof. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

def comparisonSum (E : Finset (Edge n)) (F : Formula n)
    (C : Finset (Fin n)) (x : Assignment n) : ℝ :=
  ∑ i∈C, let preferred := decide (0 ≤ delta F (orderedFree i.val) x i)
    if x i ≠ preferred then supportWeight E i*(sign preferred*gain F i x+1) else 0

theorem preferred_gain_absolute (D : ℝ) : sign (decide (0 ≤ D))*D = |D| := by
  by_cases h : 0 ≤ D
  · simp [h,sign,abs_of_nonneg h]
  · simp [h,sign,abs_of_neg (lt_of_not_ge h)]

theorem comparison_sum_identity (K : E → Pattern m) (units : List (Literal n))
    (C : Finset (Fin n)) (z : ExposureBit E → Bool) :
    comparisonSum E (generate E (sampled K z) units) C (assignment z) =
      requirements K units C z + compensation K units C (supportWeight E) z := by
  unfold comparisonSum requirements compensation requirementAt comparisonMultiplier
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  split_ifs with h
  · have hh := preferred_gain_absolute
      (delta (generate E (sampled K z) units) (orderedFree i.val) (assignment z) i)
    rw [← hh]
    ring
  · ring

def runtimeConstant (m : ℕ) (κ : ℝ) : ℝ := (requirementConstant m κ)^2/(10816*(m:ℝ)^2)

/-- The two scalar comparisons used after choosing a=b=c=c1*T/104. -/
theorem deviation_exponents (m c₁ T r : ℝ) (hm : 0 < m) (hc : 0 < c₁)
    (hT : 0 < T) (hr : 0 < r) (hhalf : r ≤ 2*T) :
    -2*(c₁*T/104)^2/(m^2*T) ≤ -(c₁^2/(10816*m^2))*r ∧
    -169*(c₁*T/104)^2/(m^2*r) ≤ -(c₁^2/(10816*m^2))*r := by
  have h1 : -2*(c₁*T/104)^2/(m^2*T) = -c₁^2*T/(5408*m^2) := by field_simp; ring
  have h2 : -169*(c₁*T/104)^2/(m^2*r) = -169*c₁^2*T^2/(10816*m^2*r) := by field_simp; ring
  rw [h1,h2]
  constructor
  · apply (div_le_iff₀ (show 0 < 5408*m^2 by positivity)).2
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hhalf (sq_nonneg c₁)]
  · apply (div_le_iff₀ (show 0 < 10816*m^2*r by positivity)).2
    field_simp
    have hh : r^2 ≤ 4*T^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg c₁)]

theorem sum_feasibility_tail (p : E → PairLaw m κ) (hm : 0 < m) (hk : 0 < κ)
    (units : List (Literal n)) (C : Finset (Fin n)) (hC : 0 < C.card)
    (hd : ∀ i∈C, 0 < (incident E i).card) (hhalf : n ≤ 2*C.card) :
    prob (exposureLaw p)
      (fun z => comparisonSum E (generate E (sampled z.1 z.2) units) C (assignment z.2) ≤ 0) ≤
      3*Real.exp (-runtimeConstant m κ*n) := by
  have hn : 0 < n := by
    obtain ⟨i,_⟩ := Finset.card_pos.1 hC
    exact Nat.zero_lt_of_lt i.isLt
  have hc := requirement_constant_pos hm hk
  let a : ℝ := requirementConstant m κ*C.card/104
  have ha : 0 < a := by dsimp [a]; positivity
  have hA := requirements_tail p hm hk units C hC hd a a ha ha
  have hQ := compensation_tail p hm units C hC a ha
  have h := summed_constraint_failure (exposureLaw p)
    (fun z => requirements z.1 units C z.2)
    (fun z => compensation z.1 units C (supportWeight E) z.2)
    (requirementConstant m κ*C.card/26) a a a _ _ (by convert ha using 1; dsimp [a]; ring) hA hQ
  have he := deviation_exponents (m:ℝ) (requirementConstant m κ) (C.card:ℝ) (n:ℝ)
    (by exact_mod_cast hm) hc (by exact_mod_cast hC) (by exact_mod_cast hn) (by exact_mod_cast hhalf)
  have he₁ := Real.exp_le_exp.2 he.1
  have he₂ := Real.exp_le_exp.2 he.2
  simp only [← comparison_sum_identity] at h
  apply h.trans
  dsimp only [a, runtimeConstant] at *
  nlinarith

/-- The event is about the original sampled formula and an independent
uniform assignment, not an auxiliary distribution with extra assumptions. -/
theorem sum_feasibility_input_law (p : E → PairLaw m κ) (hm : 0 < m) (hk : 0 < κ)
    (units : List (Literal n)) (C : Finset (Fin n)) (hC : 0 < C.card)
    (hd : ∀ i∈C, 0 < (incident E i).card) (hhalf : n ≤ 2*C.card) :
    prob (tensor (product (fun e => (p e).law)) (fairBits (Fin n)))
      (fun z => comparisonSum E (generate E z.1 units) C z.2 ≤ 0) ≤
      3*Real.exp (-runtimeConstant m κ*n) := by
  have h := sum_feasibility_tail p hm hk units C hC hd hhalf
  rw [← prob_push (exposureLaw p) (fun z => (sampled z.1 z.2,assignment z.2))
    (fun z => comparisonSum E (generate E z.1 units) C z.2 ≤ 0), exposure_joint_law] at h
  exact h

end
end Max2SAT.RandomInput
