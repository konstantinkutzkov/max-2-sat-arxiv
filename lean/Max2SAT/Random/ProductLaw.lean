import Max2SAT.Random.FiniteLaw

/-! Independent blocks of finite random data, and measure-preserving
changes of variables. These support the endpoint exposure construction. -/
namespace Max2SAT.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α β γ ι : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι] [DecidableEq ι]

def tensor (p : Law α) (q : Law β) : Law (α × β) where
  mass x := p.mass x.1 * q.mass x.2
  nonneg x := mul_nonneg (p.nonneg x.1) (q.nonneg x.2)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, p.total, q.total]

theorem expect_tensor (p : Law α) (q : Law β) (f : α × β → ℝ) :
    expect (tensor p q) f = expect p (fun a => expect q (fun b => f (a,b))) := by
  simp only [expect, tensor, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem push_tensor_fst (p : Law α) (q : Law β) : push (tensor p q) Prod.fst = p := by
  apply Law.ext
  funext a
  simp [push, tensor, Fintype.sum_prod_type, ← Finset.mul_sum, q.total]

theorem push_tensor_snd (p : Law α) (q : Law β) : push (tensor p q) Prod.snd = q := by
  apply Law.ext
  funext b
  simp [push, tensor, Fintype.sum_prod_type, ← Finset.sum_mul, p.total]

theorem tensor_prob_left (p : Law α) (q : Law β) (P : α → Prop) :
    prob (tensor p q) (fun x => P x.1) = prob p P := by
  simp [prob, tensor, Fintype.sum_prod_type, ← Finset.mul_sum, q.total]

/-- Arbitrary observations of the first block do not change the second
independent block. This handles events depending on already revealed data,
not just individual coordinate values. -/
theorem condition_tensor_left (p : Law α) (q : Law β) (P : α → Prop)
    (h : 0 < prob p P) :
    condition (tensor p q) (fun x => P x.1) (by rw [tensor_prob_left]; exact h) =
      tensor (condition p P h) q := by
  apply Law.ext
  funext x
  simp only [condition_mass, tensor_prob_left]
  change ((if P x.1 then p.mass x.1 * q.mass x.2 else 0) / prob p P) =
    ((if P x.1 then p.mass x.1 else 0) / prob p P) * q.mass x.2
  by_cases hx : P x.1 <;> simp [hx, div_mul_eq_mul_div]

/-- Changing each coordinate separately preserves independence. -/
theorem product_push (p : ι → Law α) (f : ι → α → β) :
    push (product p) (fun x i => f i (x i)) = product (fun i => push (p i) (f i)) := by
  apply Law.ext
  funext y
  simp only [push, product]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : (fun i => f i (x i)) = y
  · have hh : ∀ i, f i (x i) = y i := fun i => congrFun hx i
    simp [hh]
  · have hh : ¬ ∀ i, f i (x i) = y i := fun h => hx (funext h)
    obtain ⟨i, hi⟩ := not_forall.mp hh
    simp only [hx, ↓reduceIte]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Independently applying random symmetries of a law leaves that law
unchanged. The symmetries need not act freely on individual outcomes. -/
theorem random_symmetries (p : Law α) (q : Law β) (e : β → α ≃ α)
    (hinv : ∀ b a, p.mass (e b a) = p.mass a) :
    push (tensor p q) (fun x => e x.2 x.1) = p := by
  apply Law.ext
  funext a
  simp only [push, tensor, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have hsum : ∀ b, (∑ x, if e b x = a then p.mass x * q.mass b else 0) =
      p.mass a * q.mass b := by
    intro b
    simp only [← (e b).eq_symm_apply]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [← hinv b ((e b).symm a), Equiv.apply_symm_apply]
  simp_rw [hsum]
  rw [← Finset.mul_sum, q.total, mul_one]

end
end Max2SAT.FiniteLaw
