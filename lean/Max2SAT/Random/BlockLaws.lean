import Max2SAT.Random.ProductTools

namespace Max2SAT.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α β γ ι κ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

@[simp] theorem expect_point (a : α) (f : α → ℝ) : expect (point a) f = f a := by
  simp [expect,point]

theorem tensor_prob_both (p : Law α) (q : Law β) (P : α → Prop) (Q : β → Prop) :
    prob (tensor p q) (fun z => P z.1 ∧ Q z.2) = prob p P * prob q Q := by
  simp only [prob,tensor,Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P a <;> by_cases hb : Q b <;> simp [ha,hb]

theorem condition_tensor_both (p : Law α) (q : Law β) (P : α → Prop) (Q : β → Prop)
    (hp : 0 < prob p P) (hq : 0 < prob q Q) :
    condition (tensor p q) (fun z => P z.1 ∧ Q z.2)
      (by rw [tensor_prob_both]; exact mul_pos hp hq) =
      tensor (condition p P hp) (condition q Q hq) := by
  apply Law.ext
  funext z
  rw [condition_mass,tensor_prob_both p q P Q]
  simp only [tensor,condition_mass]
  by_cases ha : P z.1 <;> by_cases hb : Q z.2 <;> simp [ha,hb,div_mul_div_comm]

theorem push_tensor_right (p : Law α) (q : Law β) (f : β → γ) :
    push (tensor p q) (fun z => (z.1,f z.2)) = tensor p (push q f) := by
  apply Law.ext
  funext z
  rcases z with ⟨a₀,b₀⟩
  simp only [push,tensor,Fintype.sum_prod_type,Prod.mk.injEq,Finset.mul_sum]
  have he : ∀ a b, (if a=a₀ ∧ f b=b₀ then p.mass a*q.mass b else 0) =
      (if a=a₀ then p.mass a₀*(if f b=b₀ then q.mass b else 0) else 0) := by
    intro a b
    by_cases ha : a=a₀ <;> by_cases hb : f b=b₀ <;> simp [ha,hb]
  simp_rw [he]
  simp

/-- Keeping arbitrary independent data alongside the randomization still
leaves that data independent of the randomized object. -/
theorem random_symmetries_with_data (p : Law α) (q : Law β) (r : Law γ)
    (e : γ → α ≃ α) (hinv : ∀ c a, p.mass (e c a) = p.mass a) :
    push (tensor p (tensor q r)) (fun z => (e z.2.2 z.1,z.2.1)) = tensor p q := by
  apply Law.ext
  funext z
  rcases z with ⟨a,b⟩
  simp only [push,tensor,Fintype.sum_prod_type,Prod.mk.injEq]
  rw [Finset.sum_comm]
  have he : ∀ y x c, (if e c x=a ∧ y=b then p.mass x*(q.mass y*r.mass c) else 0) =
      (if y=b then (if e c x=a then p.mass x*(q.mass b*r.mass c) else 0) else 0) := by
    intro y x c
    by_cases hy : y=b <;> by_cases hx : e c x=a <;> simp [hy,hx]
  simp_rw [he]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  rw [Finset.sum_comm]
  have hx : ∀ c, (∑ x, if e c x=a then p.mass x*(q.mass b*r.mass c) else 0) =
      p.mass a*(q.mass b*r.mass c) := by
    intro c
    simp only [← (e c).eq_symm_apply,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
    rw [← hinv c ((e c).symm a),Equiv.apply_symm_apply]
  simp_rw [hx]
  simp [← mul_assoc,← Finset.mul_sum,r.total]

def bitAndVector : (Unit ⊕ κ → Bool) ≃ Bool × (κ → Bool) where
  toFun z := (z (.inl ()),fun j => z (.inr j))
  invFun z := Sum.elim (fun _ => z.1) z.2
  left_inv z := by funext b; cases b <;> rfl
  right_inv z := rfl

theorem fair_bitAndVector :
    push (fairBits (Unit ⊕ κ)) (bitAndVector (κ:=κ)) = tensor fair (fairBits κ) := by
  apply Law.ext
  funext z
  rw [push_equiv_mass,fairBits_mass]
  simp [tensor,fair,fairBits_mass,Fintype.card_sum,pow_add]

theorem fresh_bit_and_vector (known : Finset ι) (x : ι → Bool)
    (h : 0 < prob (fairBits ι) (history known x))
    (i : ι) (hi : i ∉ known) (f : κ → ι) (hf : Function.Injective f)
    (hn : ∀ j, f j ∉ known) (hne : ∀ j, f j ≠ i) :
    push (condition (fairBits ι) (history known x) h)
      (fun z => (z i,fun j => z (f j))) = tensor fair (fairBits κ) := by
  let g : Unit ⊕ κ → ι := Sum.elim (fun _ => i) f
  have hg : Function.Injective g := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => rfl
      | inr b => exact False.elim (hne b hab.symm)
    | inr a =>
      cases b with
      | inl b => exact False.elim (hne a hab)
      | inr b => exact congrArg Sum.inr (hf hab)
  have hgn : ∀ j, g j ∉ known := by intro j; cases j <;> simp_all [g]
  have hh := congrArg (fun p => push p (bitAndVector (κ:=κ)))
    (fresh_selection known x h g hg hgn)
  rw [push_comp,fair_bitAndVector] at hh
  exact hh

end
end Max2SAT.FiniteLaw
