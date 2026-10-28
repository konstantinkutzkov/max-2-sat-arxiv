import Max2SAT.Random.AdaptiveRanges

/-! Compose conditional exponential estimates for whole exposure blocks.
This allows the independent signs at a vertex to be handled together. -/
namespace Max2SAT.FiniteLaw
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

theorem conditional_mgf_step (p : Law α) (H : α → β) (F X : α → ℝ)
    (v t : ℝ) (hF : Known H F)
    (hmgf : ∀ x, 0 < p.mass x →
      expect (fiber p H (H x)) (fun y => Real.exp (t*X y)) ≤ Real.exp (t^2*v/8)) :
    expect p (fun x => Real.exp (t*(F x+X x))) ≤
      expect p (fun x => Real.exp (t*F x)) * Real.exp (t^2*v/8) := by
  rw [← expect_mul_const, ← expect_conditional p H]
  apply expect_mono_support
  intro x hx
  have he : expect (fiber p H (H x)) (fun y => Real.exp (t*(F y+X y))) =
      expect (fiber p H (H x)) (fun y => Real.exp (t*X y)) * Real.exp (t*F x) := by
    rw [← expect_mul_const]
    apply expect_congr_support
    intro y hy
    have hh := (fiber_support p H (H x) (fiber_event_positive p H x hx) y hy).1
    rw [hF y x hh, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hmgf x hx) (Real.exp_pos (t*F x)).le

theorem conditional_mgf_sum (p : Law α) (k : ℕ) (H : ℕ → α → β)
    (X : ℕ → α → ℝ) (v : ℕ → ℝ)
    (href : ∀ i j, i ≤ j → ∀ x y, H j x = H j y → H i x = H i y)
    (hadapt : ∀ j, j < k → Known (H (j+1)) (X j))
    (hmgf : ∀ j, j < k → ∀ x, 0 < p.mass x → ∀ t : ℝ,
      expect (fiber p (H j) (H j x)) (fun y => Real.exp (t*X j y)) ≤ Real.exp (t^2*v j/8))
    (t : ℝ) :
    expect p (fun x => Real.exp (t*(∑ j ∈ Finset.range k, X j x))) ≤
      Real.exp (t^2*(∑ j ∈ Finset.range k, v j)/8) := by
  have hp : ∀ j, j ≤ k →
      expect p (fun x => Real.exp (t*(∑ i ∈ Finset.range j, X i x))) ≤
        Real.exp (t^2*(∑ i ∈ Finset.range j, v i)/8) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hknown : Known (H j) (fun x => ∑ i ∈ Finset.range j, X i x) := by
        intro x y h
        apply Finset.sum_congr rfl
        intro i hi
        have hij := Finset.mem_range.1 hi
        exact hadapt i (by omega) x y (href (i+1) j (by omega) x y h)
      have hs := conditional_mgf_step p (H j) (fun x => ∑ i ∈ Finset.range j, X i x)
        (X j) (v j) t hknown (fun x hx => hmgf j (by omega) x hx t)
      simp only [Finset.sum_range_succ]
      apply hs.trans
      apply (mul_le_mul_of_nonneg_right (ih (by omega)) (Real.exp_pos (t^2*v j/8)).le).trans_eq
      rw [← Real.exp_add]
      congr 1
      ring
  exact hp k le_rfl

theorem conditional_mgf_tail (p : Law α) (k : ℕ) (H : ℕ → α → β)
    (X : ℕ → α → ℝ) (v : ℕ → ℝ)
    (href : ∀ i j, i ≤ j → ∀ x y, H j x = H j y → H i x = H i y)
    (hadapt : ∀ j, j < k → Known (H (j+1)) (X j))
    (hmgf : ∀ j, j < k → ∀ x, 0 < p.mass x → ∀ t : ℝ,
      expect (fiber p (H j) (H j x)) (fun y => Real.exp (t*X j y)) ≤ Real.exp (t^2*v j/8))
    (B a : ℝ) (hB : 0 < B) (ha : 0 < a) (hbudget : (∑ j ∈ Finset.range k, v j) ≤ B) :
    prob p (fun x => (∑ j ∈ Finset.range k, X j x) < -a) ≤ Real.exp (-2*a^2/B) := by
  apply lower_tail_of_mgf p _ B a hB ha
  intro t
  have h := conditional_mgf_sum p k H X v href hadapt hmgf (-t)
  simp only [neg_sq] at h
  apply h.trans
  apply Real.exp_le_exp.2
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget (sq_nonneg t)) (by norm_num)

end
end Max2SAT.FiniteLaw
