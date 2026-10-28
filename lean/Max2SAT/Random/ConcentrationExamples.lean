import Max2SAT.Random.BitHistory
import Max2SAT.Random.BoundedDifferences
import Max2SAT.Random.RequirementMean
import Max2SAT.Random.PredictableSigns
import Max2SAT.Random.WeightBounds

/-! Kernel-checked regression examples for conditional concentration.
The adaptive example spends its width budget on exactly one of two steps. -/
namespace Max2SAT.RandomInput.ConcentrationExamples
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable

abbrev Bits := Fin 3 → Bool

def prefixBits (j : ℕ) : Finset (Fin 3) := Finset.univ.filter (fun i => i.val < j)
def H (j : ℕ) : Bits → Bits := observe (prefixBits j)
def nextBit (j : ℕ) (z : Bits) : Bool := z ⟨j % 3, Nat.mod_lt _ (by omega)⟩
def coeff (j : ℕ) (z : Bits) : ℝ :=
  if j = 1 then (if z 0 then 1 else 0)
  else if j = 2 then (if z 0 then 0 else 1) else 0

theorem coeff_known (j : ℕ) : Known (H j) (coeff j) := by
  intro x y h
  by_cases hj : j=1 ∨ j=2
  · have hh := congrFun h 0
    have h0 : (0 : Fin 3) ∈ prefixBits j := by simp [prefixBits]; omega
    have he : x 0 = y 0 := by simpa [H, observe, h0] using hh
    simp [coeff, he]
  · simp only [not_or] at hj
    simp [coeff, hj.1, hj.2]

/-- Revealing z_0 selects which of the two later fair signs contributes.
The sum of squared widths is always 4, although summing the worst width
at each separate later step would give 8. -/
theorem adaptive_budget_tail (a : ℝ) (ha : 0 < a) :
    prob (fairBits (Fin 3))
      (fun z => (∑ j ∈ Finset.range 3, coeff j z * sign (nextBit j z)) < -a) ≤
      Real.exp (-2*a^2/4) := by
  apply predictable_sign_tail (fairBits (Fin 3)) 3 H coeff nextBit coeff
    ?_ (fun j _ => coeff_known j) ?_ ?_ ?_ 4 a (by norm_num) ha ?_
  · intro i j hij x y h
    apply observe_refines (prefixBits i) (prefixBits j) ?_ x y h
    intro b hb
    simp only [prefixBits, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    omega
  · intro j hj x y h
    have hh := congrFun h ⟨j, hj⟩
    simpa [H, observe, prefixBits, nextBit, Nat.mod_eq_of_lt hj] using hh
  · intro j hj z _
    change push (fiber (fairBits (Fin 3)) (observe (prefixBits j))
      (observe (prefixBits j) z)) (nextBit j) = fair
    rw [fiber_fair_history]
    apply fresh_coordinate
    simp [prefixBits, Nat.mod_eq_of_lt hj]
  · intro j hj z _
    interval_cases j <;> cases hz : z 0 <;>
      norm_num [coeff, H, observe, prefixBits, hz]
  · intro z _
    cases hz : z 0 <;>
      norm_num [Finset.sum_range_succ, coeff, H, observe, prefixBits, hz]

/-- Bounded differences also covers a degenerate coordinate law. -/
example (a : ℝ) (ha : 0 < a) :
    prob (product (fun _ : Fin 1 => point true))
      (fun z => (if z 0 then (1 : ℝ) else 0) < 1-a) ≤ Real.exp (-2*a^2) := by
  let f : (Fin 1 → Bool) → ℝ := fun z => if z 0 then 1 else 0
  have hd : BoundedDifferences f (fun _ => 1) := by
    intro i z b
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    cases b <;> cases hz : z 0 <;> norm_num [f, hz]
  have he : expect (product (fun _ : Fin 1 => point true)) f = 1 := by
    rw [expect_product_cons]
    simp [expect, point, f, product]
  have h := bounded_differences_tail 1 (fun _ => point true) f (fun _ => 1) hd a ha
    (by norm_num)
  simpa [he, f] using h

example (p : Fin 2 → Law Bool) (a : ℝ) (ha : 0 < a) :
    prob (product p) (fun _ => (7 : ℝ) < 7-a) = 0 := by
  have h := zero_differences_tail 2 p (fun _ => (7 : ℝ))
    (by intro i x b; norm_num) a ha
  simpa using h

/-- For degree five the implemented rational weight is 1/3. The proof
uses this weight, not an ideal real-valued replacement 1/sqrt(5). -/
example : (1/((Nat.sqrt (5-1)+1 : ℕ) : ℝ))^2 * 5 = 5/9 := by norm_num

example (p : Law Bool) :
    expect (tensor fair p) (fun z => if z.1 ≠ z.2 then (3 : ℝ) else 0) = 3/2 := by
  simpa using fair_nonpreferred_expectation p (fun b => b) (fun _ => (3 : ℝ))

end
end Max2SAT.RandomInput.ConcentrationExamples
