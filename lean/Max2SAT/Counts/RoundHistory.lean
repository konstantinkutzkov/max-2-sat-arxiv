import Max2SAT.Counts.RoundSplit
import Max2SAT.Random.RequirementTail

/-! Conditional laws for actual rounds. The computed preference mask is
fixed by the previous rounds, while every bit of the current block remains
jointly fair. All conditional probabilities are exact finite sums. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def roundHistory (round : Fin n → ℕ) (j : ℕ) : Assignment n → Assignment n :=
  observe (roundPrefix round j)

def roundMask (H : Fin n → Affine n) (round : Fin n → ℕ) (j : ℕ)
    (x : Assignment n) : roundBlock round j → Bool := fun t => preference H round x t

theorem round_mask_known (H : Fin n → Affine n) (round : Fin n → ℕ) (j : ℕ)
    (x y : Assignment n) (h : roundHistory round j x=roundHistory round j y) :
    roundMask H round j x=roundMask H round j y := by
  funext t
  have ht : round t=j := (Finset.mem_filter.mp t.property).2
  have he : (H t).average (earlier round t) x=(H t).average (earlier round t) y := by
    apply Affine.average_agree
    intro w hw
    have hw' : w∈roundPrefix round j := by
      simpa only [roundPrefix,earlier,Finset.mem_filter,Finset.mem_univ,true_and,ht] using hw
    have hh := congrFun h w
    simpa only [roundHistory,observe,ite_eq_left hw'] using hh
  dsimp only [roundMask,preference]
  rw [he]

theorem round_fresh_law (round : Fin n → ℕ) (j : ℕ) (x : Assignment n) :
    push (fiber (fairBits (Fin n)) (roundHistory round j) (roundHistory round j x))
      (fun y (t : roundBlock round j) => y t)=fairBits (roundBlock round j) := by
  unfold roundHistory
  rw [fiber_fair_history]
  apply fresh_selection _ _ _ (fun t : roundBlock round j => t.val) Subtype.val_injective
  intro t
  have ht : round t=j := (Finset.mem_filter.mp t.property).2
  simp [roundPrefix,ht]

/-- Transfer any test function of the preferences and current block to
the product fair-bit law, with the actual earlier-round mask held fixed. -/
theorem round_conditional_expect (H : Fin n → Affine n) (round : Fin n → ℕ) (j : ℕ)
    (f : (roundBlock round j → Bool) → (roundBlock round j → Bool) → ℝ)
    (x : Assignment n) :
    expect (fiber (fairBits (Fin n)) (roundHistory round j) (roundHistory round j x))
      (fun y => f (roundMask H round j y) (fun t => y t)) =
      expect (fairBits (roundBlock round j)) (f (roundMask H round j x)) := by
  have hx : 0<(fairBits (Fin n)).mass x := by rw [fairBits_mass]; positivity
  have he := expect_congr_support
    (fiber (fairBits (Fin n)) (roundHistory round j) (roundHistory round j x))
    (fun y => f (roundMask H round j y) (fun t => y t))
    (fun y => f (roundMask H round j x) (fun t => y t)) (by
      intro y hy
      have hh := (fiber_support (fairBits (Fin n)) (roundHistory round j)
        (roundHistory round j x) (fiber_event_positive _ _ x hx) y hy).1
      rw [round_mask_known H round j y x hh])
  rw [he,←expect_push,round_fresh_law]

theorem round_conditional_probability (H : Fin n → Affine n) (round : Fin n → ℕ)
    (j : ℕ) (E : (roundBlock round j → Bool) → (roundBlock round j → Bool) → Prop)
    (x : Assignment n) :
    prob (fiber (fairBits (Fin n)) (roundHistory round j) (roundHistory round j x))
      (fun y => E (roundMask H round j y) (fun t => y t)) =
      prob (fairBits (roundBlock round j)) (E (roundMask H round j x)) := by
  have h := round_conditional_expect H round j
    (fun p z => if E p z then (1:ℝ) else 0) x
  simpa only [expect,prob,mul_ite,mul_one,mul_zero] using h

/-- Average a uniform fixed-mask bound over actual earlier-round
histories. No condition on the probability of an individual history is
needed: every assignment has positive mass under the fair product law. -/
theorem round_probability_of_fixed_masks (H : Fin n → Affine n) (round : Fin n → ℕ)
    (j : ℕ) (E : (roundBlock round j → Bool) → (roundBlock round j → Bool) → Prop)
    (q : ℝ) (hq : ∀ p, prob (fairBits (roundBlock round j)) (E p)≤q) :
    prob (fairBits (Fin n)) (fun x => E (roundMask H round j x) (fun t => x t))≤q := by
  have he : ∀ (p : Law (Assignment n)) (E : Assignment n → Prop),
      prob p E=expect p (fun x => if E x then (1:ℝ) else 0) := by
    intro p E
    simp only [prob,expect,mul_ite,mul_one,mul_zero]
  rw [he,←expect_conditional (fairBits (Fin n)) (roundHistory round j)]
  calc
    _ ≤ expect (fairBits (Fin n)) (fun _ => q) := by
      apply expect_mono
      intro x
      rw [round_conditional_expect H round j (fun p z => if E p z then (1:ℝ) else 0) x]
      have h := hq (roundMask H round j x)
      simpa only [expect,prob,mul_ite,mul_one,mul_zero] using h
    _ = q := expect_const _ _

end
end Max2SAT.Counts
