import Max2SAT.Random.AdaptiveRanges

/-! Conditional drift and exceptional-event bookkeeping in the
accumulated-requirement proof. No independence between requirements and
compensation is used. -/
namespace Max2SAT.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α]

theorem prob_mono_support (p : Law α) (P Q : α → Prop)
    (h : ∀ x, 0 < p.mass x → P x → Q x) : prob p P ≤ prob p Q := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : 0 < p.mass x
  · by_cases hp : P x
    · simp only [ite_eq_left hp, ite_eq_left (h x hx hp), le_refl]
    · simp only [ite_eq_right hp]
      split_ifs <;> simp_all [p.nonneg]
  · have hz : p.mass x = 0 := le_antisymm (le_of_not_gt hx) (p.nonneg x)
    simp [hz]

theorem prob_union_le (p : Law α) (P Q : α → Prop) :
    prob p (fun x => P x ∨ Q x) ≤ prob p P + prob p Q := by
  simp only [prob, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq, p.nonneg]

theorem drift_lower_tail [Fintype β] (p : Law α) (k : ℕ)
    (H : ℕ → α → β) (X μ : ℕ → α → ℝ) (L U : ℕ → β → ℝ) (A : α → ℝ)
    (href : ∀ i j, i ≤ j → ∀ x y, H j x = H j y → H i x = H i y)
    (hadapt : ∀ j, j < k → Known (H (j+1)) (X j))
    (hbound : ∀ j, j < k → ∀ x, 0 < p.mass x → X j x ∈ Set.Icc (L j (H j x)) (U j (H j x)))
    (hmean : ∀ j, j < k → ∀ x, 0 < p.mass x → μ j x ≤ mean p (H j) (X j) x)
    (hA : ∀ x, 0 < p.mass x → (∑ j ∈ Finset.range k, X j x) ≤ A x)
    (B a : ℝ) (hB : 0 < B) (ha : 0 < a)
    (hbudget : ∀ x, 0 < p.mass x →
      (∑ j ∈ Finset.range k, (U j (H j x)-L j (H j x))^2) ≤ B) :
    prob p (fun x => A x < (∑ j ∈ Finset.range k, μ j x)-a) ≤ Real.exp (-2*a^2/B) := by
  apply (prob_mono_support p _ _ ?_).trans
    (conditional_ranges p k H X L U href hadapt hbound B a hB ha hbudget)
  intro x hx he
  have hm : (∑ j ∈ Finset.range k, μ j x) ≤
      ∑ j ∈ Finset.range k, mean p (H j) (X j) x := by
    apply Finset.sum_le_sum
    intro j hj
    exact hmean j (Finset.mem_range.1 hj) x hx
  rw [Finset.sum_sub_distrib]
  linarith [hA x hx]

theorem two_deviation_bound (p : Law α) (A M : α → ℝ) (C a b e₁ e₂ : ℝ)
    (h₁ : prob p (fun x => A x < M x-a) ≤ e₁)
    (h₂ : prob p (fun x => M x < C-b) ≤ e₂) :
    prob p (fun x => A x < C-a-b) ≤ e₁+e₂ := by
  have hm : prob p (fun x => A x < C-a-b) ≤
      prob p (fun x => A x < M x-a ∨ M x < C-b) := by
    apply prob_mono_support
    intro x _ hx
    by_cases h : A x < M x-a
    · exact Or.inl h
    · exact Or.inr (by linarith)
  exact hm.trans ((prob_union_le p _ _).trans (add_le_add h₁ h₂))

theorem summed_constraint_failure (p : Law α) (A Q : α → ℝ) (C a b c e₁ e₂ : ℝ)
    (hgap : 0 < C-a-b-c)
    (hA : prob p (fun x => A x < C-a-b) ≤ e₁)
    (hQ : prob p (fun x => Q x < -c) ≤ e₂) :
    prob p (fun x => A x+Q x ≤ 0) ≤ e₁+e₂ := by
  have hm : prob p (fun x => A x+Q x ≤ 0) ≤
      prob p (fun x => A x < C-a-b ∨ Q x < -c) := by
    apply prob_mono_support
    intro x _ hx
    by_cases h : A x < C-a-b
    · exact Or.inl h
    · exact Or.inr (by linarith)
  exact hm.trans ((prob_union_le p _ _).trans (add_le_add hA hQ))

end
end Max2SAT.FiniteLaw
