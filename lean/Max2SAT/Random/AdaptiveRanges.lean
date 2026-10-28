import Max2SAT.Random.HistoryAverage

/-! Sequential Hoeffding bounds with predictable, history-dependent
intervals and a deterministic pathwise bound on their squared lengths. -/
namespace Max2SAT.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α]

theorem exponential_step [Fintype β] (p : Law α) (H : α → β) (X F G : α → ℝ)
    (L U : β → ℝ) (t : ℝ) (hF : Known H F) (hG : Known H G)
    (hcenter : ∀ x, 0 < p.mass x → expect (fiber p H (H x)) X = 0)
    (hb : ∀ x, 0 < p.mass x → X x ∈ Set.Icc (L (H x)) (U (H x))) :
    expect p (fun x => Real.exp (t*(F x + X x) -
      t^2*(G x + (U (H x)-L (H x))^2)/8)) ≤
    expect p (fun x => Real.exp (t*F x - t^2*G x/8)) := by
  rw [← expect_conditional p H]
  apply expect_mono_support
  intro x hx
  let q := fiber p H (H x)
  let c := t*F x - t^2*G x/8 - t^2*(U (H x)-L (H x))^2/8
  have hs : expect q (fun y => Real.exp (t*X y)) ≤
      Real.exp (t^2*(U (H x)-L (H x))^2/8) := by
    apply centered_range_mgf q X (L (H x)) (U (H x)) t
    · intro y hy
      have hh := fiber_support p H (H x) (fiber_event_positive p H x hx) y hy
      simpa only [hh.1] using hb y hh.2
    · exact hcenter x hx
  have he : expect q (fun y => Real.exp (t*(F y + X y) -
      t^2*(G y + (U (H y)-L (H y))^2)/8)) =
      expect q (fun y => Real.exp (t*X y)) * Real.exp c := by
    rw [← expect_mul_const]
    apply expect_congr_support
    intro y hy
    have hh := (fiber_support p H (H x) (fiber_event_positive p H x hx) y hy).1
    rw [hF y x hh, hG y x hh, hh, ← Real.exp_add]
    congr 1
    dsimp [c]
    ring
  change expect q _ ≤ _
  rw [he]
  apply (mul_le_mul_of_nonneg_right hs (Real.exp_pos c).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  dsimp [c]
  ring

/-- H j records the history before increment j. Its classes refine all
earlier histories. Increment j is known after this step, from H (j+1). -/
structure Exposure (p : Law α) (k : ℕ) where
  history : ℕ → α → β
  increment : ℕ → α → ℝ
  lower : ℕ → β → ℝ
  upper : ℕ → β → ℝ
  refines : ∀ i j, i ≤ j → ∀ x y, history j x = history j y → history i x = history i y
  adapted : ∀ j, j < k → Known (history (j+1)) (increment j)
  centered : ∀ j, j < k → ∀ x, 0 < p.mass x →
    expect (fiber p (history j) (history j x)) (increment j) = 0
  bounds : ∀ j, j < k → ∀ x, 0 < p.mass x →
    increment j x ∈ Set.Icc (lower j (history j x)) (upper j (history j x))

namespace Exposure
variable {p : Law α} {k : ℕ}

def total (e : Exposure (β := β) p k) (j : ℕ) (x : α) : ℝ :=
  ∑ i ∈ Finset.range j, e.increment i x

def budget (e : Exposure (β := β) p k) (j : ℕ) (x : α) : ℝ :=
  ∑ i ∈ Finset.range j, (e.upper i (e.history i x)-e.lower i (e.history i x))^2

theorem total_known (e : Exposure (β := β) p k) (j : ℕ) (hj : j ≤ k) :
    Known (e.history j) (e.total j) := by
  intro x y h
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i < j := Finset.mem_range.1 hi
  exact e.adapted i (lt_of_lt_of_le hij hj) x y
    (e.refines (i+1) j (by omega) x y h)

theorem budget_known (e : Exposure (β := β) p k) (j : ℕ) :
    Known (e.history j) (e.budget j) := by
  intro x y h
  apply Finset.sum_congr rfl
  intro i hi
  rw [e.refines i j (Nat.le_of_lt (Finset.mem_range.1 hi)) x y h]

/-- The compensated exponential has expectation at most one. The budget
inside the exponential is random and is not replaced by stepwise maxima. -/
theorem exponential_budget [Fintype β] (e : Exposure (β := β) p k) (t : ℝ) (j : ℕ) (hj : j ≤ k) :
    expect p (fun x => Real.exp (t*e.total j x - t^2*e.budget j x/8)) ≤ 1 := by
  induction j with
  | zero => simp [total, budget]
  | succ j ih =>
    have hstep := exponential_step p (e.history j) (e.increment j) (e.total j) (e.budget j)
      (e.lower j) (e.upper j) t (e.total_known j (by omega)) (e.budget_known j)
      (e.centered j (by omega)) (e.bounds j (by omega))
    have he : (fun x => Real.exp (t*e.total (j+1) x - t^2*e.budget (j+1) x/8)) =
        (fun x => Real.exp (t*(e.total j x + e.increment j x) -
          t^2*(e.budget j x + (e.upper j (e.history j x)-e.lower j (e.history j x))^2)/8)) := by
      funext x
      simp only [total, budget, Finset.sum_range_succ]
    rw [he]
    exact hstep.trans (ih (by omega))

theorem mgf [Fintype β] (e : Exposure (β := β) p k) (B t : ℝ)
    (hB : ∀ x, 0 < p.mass x → e.budget k x ≤ B) :
    expect p (fun x => Real.exp (t*e.total k x)) ≤ Real.exp (t^2*B/8) := by
  have hm : expect p (fun x => Real.exp (t*e.total k x)) ≤
      expect p (fun x => Real.exp (t*e.total k x-t^2*e.budget k x/8) * Real.exp (t^2*B/8)) := by
    apply expect_mono_support
    intro x hx
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hb := mul_le_mul_of_nonneg_left (hB x hx) (sq_nonneg t)
    linarith
  rw [expect_mul_const] at hm
  have hf := mul_le_mul_of_nonneg_right (e.exponential_budget t k le_rfl)
    (Real.exp_pos (t^2*B/8)).le
  exact hm.trans (by simpa using hf)

theorem lower_tail [Fintype β] (e : Exposure (β := β) p k) (B a : ℝ) (hB : 0 < B) (ha : 0 < a)
    (hbudget : ∀ x, 0 < p.mass x → e.budget k x ≤ B) :
    prob p (fun x => e.total k x < -a) ≤ Real.exp (-2*a^2/B) := by
  apply lower_tail_of_mgf p (e.total k) B a hB ha
  intro t
  simpa only [neg_sq] using e.mgf B (-t) hbudget

end Exposure

/-- Subtract the exact conditional expectation. No independence between
successive observations is assumed. -/
def centeredExposure (p : Law α) (k : ℕ) (H : ℕ → α → β) (X : ℕ → α → ℝ)
    (L U : ℕ → β → ℝ)
    (href : ∀ i j, i ≤ j → ∀ x y, H j x = H j y → H i x = H i y)
    (hadapt : ∀ j, j < k → Known (H (j+1)) (X j))
    (hbound : ∀ j, j < k → ∀ x, 0 < p.mass x → X j x ∈ Set.Icc (L j (H j x)) (U j (H j x))) :
    Exposure (β := β) p k where
  history := H
  increment j x := X j x - mean p (H j) (X j) x
  lower j b := L j b - expect (fiber p (H j) b) (X j)
  upper j b := U j b - expect (fiber p (H j) b) (X j)
  refines := href
  adapted j hj x y h := by
    dsimp only
    rw [hadapt j hj x y h, mean_known p (H j) (X j) x y (href j (j+1) (by omega) x y h)]
  centered j _ x hx := centered_fiber_mean p (H j) (X j) x hx
  bounds j hj x hx := by
    have h := hbound j hj x hx
    exact ⟨sub_le_sub_right h.1 _, sub_le_sub_right h.2 _⟩

theorem conditional_ranges [Fintype β] (p : Law α) (k : ℕ) (H : ℕ → α → β) (X : ℕ → α → ℝ)
    (L U : ℕ → β → ℝ)
    (href : ∀ i j, i ≤ j → ∀ x y, H j x = H j y → H i x = H i y)
    (hadapt : ∀ j, j < k → Known (H (j+1)) (X j))
    (hbound : ∀ j, j < k → ∀ x, 0 < p.mass x → X j x ∈ Set.Icc (L j (H j x)) (U j (H j x)))
    (B a : ℝ) (hB : 0 < B) (ha : 0 < a)
    (hbudget : ∀ x, 0 < p.mass x →
      (∑ j ∈ Finset.range k, (U j (H j x)-L j (H j x))^2) ≤ B) :
    prob p (fun x => (∑ j ∈ Finset.range k, (X j x-mean p (H j) (X j) x)) < -a) ≤
      Real.exp (-2*a^2/B) := by
  let e := centeredExposure p k H X L U href hadapt hbound
  apply e.lower_tail B a hB ha
  intro x hx
  simpa only [e, Exposure.budget, centeredExposure, sub_sub_sub_cancel_right] using hbudget x hx

end
end Max2SAT.FiniteLaw
