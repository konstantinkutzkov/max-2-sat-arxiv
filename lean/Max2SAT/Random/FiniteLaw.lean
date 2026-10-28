import Max2SAT.Basic

/-! Finite probability laws for the random-input analysis. All probabilities
are real, finite sums; conditioning is used only on positive-probability
events. A product law is the definition of independent sampling. -/
namespace Max2SAT.FiniteLaw
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

@[ext] structure Law (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]

def expect (p : Law α) (f : α → ℝ) : ℝ := ∑ a, p.mass a * f a

def prob (p : Law α) (P : α → Prop) : ℝ := by
  classical
  exact ∑ a, if P a then p.mass a else 0

theorem prob_nonneg (p : Law α) (P : α → Prop) : 0 ≤ prob p P := by
  classical
  exact Finset.sum_nonneg (fun a _ => by split_ifs <;> simp_all [p.nonneg])

theorem prob_le_one (p : Law α) (P : α → Prop) : prob p P ≤ 1 := by
  classical
  rw [← p.total]
  exact Finset.sum_le_sum (fun a _ => by split_ifs <;> simp_all [p.nonneg])

@[simp] theorem expect_const (p : Law α) (c : ℝ) : expect p (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, p.total]

theorem expect_nonneg (p : Law α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ expect p f := Finset.sum_nonneg (fun a _ => mul_nonneg (p.nonneg a) (h a))

def condition (p : Law α) (P : α → Prop) (h : 0 < prob p P) : Law α := by
  classical
  exact ⟨fun a => (if P a then p.mass a else 0) / prob p P,
    fun a => div_nonneg (by split_ifs <;> simp_all [p.nonneg]) h.le,
    by simp only [← Finset.sum_div]; exact div_self (ne_of_gt h)⟩

theorem condition_mass (p : Law α) (P : α → Prop) (h : 0 < prob p P) (a : α) :
    (condition p P h).mass a = (if P a then p.mass a else 0) / prob p P := by
  classical
  rfl

/-- Conditioning divides the expectation by the event's probability when
the quantity vanishes off that event (e.g. the squared signed count on an
empty pair). -/
theorem condition_expect (p : Law α) (P : α → Prop) (h : 0 < prob p P)
    (f : α → ℝ) (hz : ∀ a, ¬ P a → f a = 0) :
    expect (condition p P h) f = expect p f / prob p P := by
  classical
  simp only [expect, condition_mass, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P a
  · simp [ha, div_mul_eq_mul_div]
  · simp [ha, hz a ha]

def product (p : ι → Law α) : Law (ι → α) where
  mass x := ∏ i, (p i).mass (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (p i).nonneg (x i))
  total := by rw [← Fintype.prod_sum]; simp [Law.total]

theorem product_prob (p : ι → Law α) (P : ι → α → Prop) :
    prob (product p) (fun x => ∀ i, P i (x i)) = ∏ i, prob (p i) (P i) := by
  classical
  unfold prob
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [product]
  by_cases hx : ∀ i, P i (x i)
  · simp [hx]
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    simp only [hx, ↓reduceIte]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem product_event_positive (p : ι → Law α) (P : ι → α → Prop)
    (h : 0 < prob (product p) (fun x => ∀ i, P i (x i))) (i : ι) :
    0 < prob (p i) (P i) := by
  have hn : (∏ j, prob (p j) (P j)) ≠ 0 := ne_of_gt (product_prob p P ▸ h)
  exact lt_of_le_of_ne (prob_nonneg _ _) (Ne.symm
    ((Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)))

/-- The exact factorization of the conditional joint law, not merely a
pairwise-independence assertion. The positive joint event implies all
individual conditioning events have positive probability. -/
theorem condition_product (p : ι → Law α) (P : ι → α → Prop)
    (h : 0 < prob (product p) (fun x => ∀ i, P i (x i))) :
    condition (product p) (fun x => ∀ i, P i (x i)) h =
      product (fun i => condition (p i) (P i) (product_event_positive p P h i)) := by
  classical
  apply Law.ext
  funext x
  simp only [condition_mass]
  rw [product_prob]
  simp only [product, condition_mass, Finset.prod_div_distrib]
  congr 1
  by_cases hx : ∀ i, P i (x i)
  · simp [hx]
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    simp only [hx, ↓reduceIte]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

def push (p : Law α) (f : α → β) : Law β := by
  classical
  exact ⟨fun b => ∑ a, if f a = b then p.mass a else 0,
    fun b => Finset.sum_nonneg (fun a _ => by split_ifs <;> simp_all [p.nonneg]),
    by rw [Finset.sum_comm]; simpa using p.total⟩

theorem expect_push (p : Law α) (f : α → β) (g : β → ℝ) :
    expect (push p f) g = expect p (fun a => g (f a)) := by
  classical
  simp only [expect, push, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

theorem push_equiv_mass (p : Law α) (e : α ≃ β) (b : β) :
    (push p e).mass b = p.mass (e.symm b) := by
  classical
  simp [push, ← e.eq_symm_apply]

theorem push_invariant (p : Law α) (f : α → β) (e : α ≃ α) (d : β ≃ β)
    (hm : ∀ a, p.mass (e a) = p.mass a) (hf : ∀ a, f (e a) = d (f a)) (b : β) :
    (push p f).mass (d b) = (push p f).mass b := by
  classical
  unfold push
  change (∑ a, if f a = d b then p.mass a else 0) = _
  rw [← e.sum_comp (fun a => if f a = d b then p.mass a else 0)]
  simp only [hf, hm, Equiv.apply_eq_iff_eq]

/-- Invariance of the original law and event implies invariance after
conditioning. -/
theorem condition_invariant (p : Law α) (P : α → Prop) (h : 0 < prob p P)
    (e : α ≃ α) (hm : ∀ a, p.mass (e a) = p.mass a)
    (hp : ∀ a, P (e a) ↔ P a) (a : α) :
    (condition p P h).mass (e a) = (condition p P h).mass a := by
  classical
  simp only [condition_mass, hm, hp]

end
end Max2SAT.FiniteLaw
