import Max2SAT.Random.Hoeffding

/-! Conditional expectations on finite histories. Zero-probability histories
receive an arbitrary law and never contribute to any expectation. -/
namespace Max2SAT.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α]

theorem prob_ge_mass (p : Law α) (P : α → Prop) (x : α) (hx : P x) :
    p.mass x ≤ prob p P := by
  unfold prob
  simpa only [ite_eq_left hx] using
    Finset.single_le_sum (f := fun y => if P y then p.mass y else 0)
      (fun y (_ : y ∈ Finset.univ) => by
      split_ifs <;> simp_all [p.nonneg]) (Finset.mem_univ x)

theorem expect_mono_support (p : Law α) {f g : α → ℝ}
    (h : ∀ x, 0 < p.mass x → f x ≤ g x) : expect p f ≤ expect p g := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : 0 < p.mass x
  · exact mul_le_mul_of_nonneg_left (h x hx) (p.nonneg x)
  · have hz : p.mass x = 0 := le_antisymm (le_of_not_gt hx) (p.nonneg x)
    simp [hz]

def fiber (p : Law α) (H : α → β) (b : β) : Law α :=
  if h : 0 < prob p (fun x => H x = b) then condition p (fun x => H x = b) h else p

theorem fiber_eq (p : Law α) (H : α → β) (b : β)
    (h : 0 < prob p (fun x => H x = b)) :
    fiber p H b = condition p (fun x => H x = b) h := by simp [fiber, h]

theorem fiber_event_positive (p : Law α) (H : α → β) (x : α) (hx : 0 < p.mass x) :
    0 < prob p (fun y => H y = H x) :=
  hx.trans_le (prob_ge_mass p _ x rfl)

theorem fiber_support (p : Law α) (H : α → β) (b : β)
    (hb : 0 < prob p (fun x => H x = b)) (y : α)
    (hy : 0 < (fiber p H b).mass y) : H y = b ∧ 0 < p.mass y := by
  rw [fiber_eq p H b hb, condition_mass] at hy
  by_cases h : H y = b
  · rw [ite_eq_left h] at hy
    exact ⟨h, (div_pos_iff_of_pos_right hb).1 hy⟩
  · simp [h] at hy

theorem fiber_mass_mul (p : Law α) (H : α → β) (b : β) (x : α) :
    prob p (fun y => H y = b) * (fiber p H b).mass x =
      if H x = b then p.mass x else 0 := by
  by_cases hb : 0 < prob p (fun y => H y = b)
  · rw [fiber_eq p H b hb, condition_mass]
    exact mul_div_cancel₀ _ (ne_of_gt hb)
  · have hz : prob p (fun y => H y = b) = 0 :=
      le_antisymm (le_of_not_gt hb) (prob_nonneg _ _)
    rw [hz, zero_mul]
    by_cases hx : H x = b
    · rw [ite_eq_left hx]
      have hm := prob_ge_mass p (fun y => H y = b) x hx
      rw [hz] at hm
      exact (le_antisymm hm (p.nonneg x)).symm
    · simp [hx]

/-- Law of total expectation, keeping the complete conditional law. -/
theorem expect_fibers [Fintype β] (p : Law α) (H : α → β) (f : α → ℝ) :
    expect (push p H) (fun b => expect (fiber p H b) f) = expect p f := by
  change (∑ b, prob p (fun x => H x = b) * (∑ x, (fiber p H b).mass x * f x)) = _
  simp_rw [Finset.mul_sum, ← mul_assoc, fiber_mass_mul]
  rw [Finset.sum_comm]
  simp [ite_mul, expect]

theorem expect_conditional [Fintype β] (p : Law α) (H : α → β) (f : α → ℝ) :
    expect p (fun x => expect (fiber p H (H x)) f) = expect p f := by
  exact (expect_push p H (fun b => expect (fiber p H b) f)).symm.trans
    (expect_fibers p H f)

/-- A quantity is known from H if it is constant on each history class. -/
def Known (H : α → β) (f : α → ℝ) : Prop := ∀ x y, H x = H y → f x = f y

def mean (p : Law α) (H : α → β) (X : α → ℝ) (x : α) : ℝ :=
  expect (fiber p H (H x)) X

theorem mean_known (p : Law α) (H : α → β) (X : α → ℝ) : Known H (mean p H X) := by
  intro x y h
  simp only [mean, h]

theorem fiber_expect_known (p : Law α) (H : α → β) (f : α → ℝ)
    (hf : Known H f) (x : α) (hx : 0 < p.mass x) :
    expect (fiber p H (H x)) f = f x := by
  calc
    _ = expect (fiber p H (H x)) (fun _ => f x) := by
      apply expect_congr_support
      intro y hy
      exact hf y x (fiber_support p H (H x) (fiber_event_positive p H x hx) y hy).1
    _ = _ := expect_const _ _

theorem centered_fiber_mean (p : Law α) (H : α → β) (X : α → ℝ)
    (x : α) (hx : 0 < p.mass x) :
    expect (fiber p H (H x)) (fun y => X y - mean p H X y) = 0 := by
  have h : expect (fiber p H (H x)) (mean p H X) = mean p H X x :=
    fiber_expect_known p H _ (mean_known p H X) x hx
  simp only [expect, mul_sub, Finset.sum_sub_distrib] at h ⊢
  rw [h]
  exact sub_self _

end
end Max2SAT.FiniteLaw
