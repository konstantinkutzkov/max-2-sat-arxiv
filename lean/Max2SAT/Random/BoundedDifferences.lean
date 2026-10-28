import Max2SAT.Random.AdaptiveRanges

/-! Sharp bounded differences for arbitrary finite independent inputs.
The proof averages the unrevealed coordinates and inducts on their number. -/
namespace Max2SAT.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α]

theorem law_nonempty (p : Law α) : Nonempty α := by
  by_contra hn
  have : IsEmpty α := not_nonempty_iff.1 hn
  have h := p.total
  simp at h

theorem expect_sub (p : Law α) (f g : α → ℝ) :
    expect p (fun x => f x-g x) = expect p f-expect p g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem abs_expect_le (p : Law α) (f : α → ℝ) :
    |expect p f| ≤ expect p (fun x => |f x|) := by
  unfold expect
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  simp only [abs_mul, abs_of_nonneg (p.nonneg _)]

theorem expect_distance (p : Law α) (f g : α → ℝ) (c : ℝ)
    (h : ∀ x, |f x-g x| ≤ c) : |expect p f-expect p g| ≤ c := by
  rw [← expect_sub]
  exact (abs_expect_le p _).trans ((expect_mono p h).trans_eq (expect_const p c))

theorem oscillation_mgf (p : Law α) (X : α → ℝ) (c t : ℝ)
    (hc : ∀ x y, |X x-X y| ≤ c) :
    expect p (fun x => Real.exp (t*(X x-expect p X))) ≤ Real.exp (t^2*c^2/8) := by
  have : Nonempty α := law_nonempty p
  obtain ⟨x₀, hmin⟩ := Finite.exists_min X
  have h := range_mgf p X (X x₀) (X x₀+c) t (by
    intro x _
    exact ⟨hmin x, by linarith [(abs_le.1 (hc x x₀)).2]⟩)
  simpa only [add_sub_cancel_left] using h

theorem expect_product_cons {n : ℕ} (p : Fin (n+1) → Law α) (f : (Fin (n+1) → α) → ℝ) :
    expect (product p) f = expect (p 0) (fun a =>
      expect (product (fun i : Fin n => p i.succ)) (fun x => f (Fin.cons a x))) := by
  unfold expect
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => α)).sum_comp]
  simp only [Fintype.sum_prod_type, product, Fin.prod_univ_succ,
    Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro x _
  change ((p 0).mass a * (∏ i : Fin n, (p i.succ).mass (x i))) * f (Fin.cons a x) =
    (p 0).mass a * ((∏ i : Fin n, (p i.succ).mass (x i)) * f (Fin.cons a x))
  exact mul_assoc _ _ _

theorem expect_product_zero (p : Fin 0 → Law α) (f : (Fin 0 → α) → ℝ) :
    expect (product p) f = f Fin.elim0 := by
  have he : f = (fun _ => f Fin.elim0) := by
    funext x
    congr 1
    funext i
    exact Fin.elim0 i
  rw [he, expect_const]

def BoundedDifferences {n : ℕ} (f : (Fin n → α) → ℝ) (c : Fin n → ℝ) : Prop :=
  ∀ i x a, |f (Function.update x i a)-f x| ≤ c i

omit [Fintype α] in
theorem update_cons_zero {n : ℕ} (x : Fin n → α) (a b : α) :
    Function.update (Fin.cons a x : Fin (n+1) → α) 0 b = Fin.cons b x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

omit [Fintype α] in
theorem update_cons_succ {n : ℕ} (x : Fin n → α) (a b : α) (i : Fin n) :
    Function.update (Fin.cons a x : Fin (n+1) → α) i.succ b = Fin.cons a (Function.update x i b) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Function.update, Ne.symm (Fin.succ_ne_zero i)]
  · by_cases h : k=i
    · subst k; simp
    · simp [h]

theorem bounded_differences_mgf (n : ℕ) (p : Fin n → Law α)
    (f : (Fin n → α) → ℝ) (c : Fin n → ℝ) (hd : BoundedDifferences f c) (t : ℝ) :
    expect (product p) (fun x => Real.exp (t*(f x-expect (product p) f))) ≤
      Real.exp (t^2*(∑ i, (c i)^2)/8) := by
  induction n with
  | zero => simp [expect_product_zero]
  | succ n ih =>
    let q := product (fun i : Fin n => p i.succ)
    let M : α → ℝ := fun a => expect q (fun x => f (Fin.cons a x))
    let V := t^2*(∑ i : Fin n, (c i.succ)^2)/8
    have htail : ∀ a, BoundedDifferences (fun x => f (Fin.cons a x)) (fun i => c i.succ) := by
      intro a i x b
      simpa only [update_cons_succ] using hd i.succ (Fin.cons a x) b
    have hM : ∀ a b, |M a-M b| ≤ c 0 := by
      intro a b
      apply expect_distance
      intro x
      simpa only [update_cons_zero] using hd 0 (Fin.cons b x) a
    have hs := oscillation_mgf (p 0) M (c 0) t hM
    have hmean : expect (product p) f = expect (p 0) M := expect_product_cons p f
    rw [expect_product_cons, hmean]
    have he : ∀ a, expect q (fun x => Real.exp (t*(f (Fin.cons a x)-expect (p 0) M))) =
        expect q (fun x => Real.exp (t*(f (Fin.cons a x)-M a))) *
          Real.exp (t*(M a-expect (p 0) M)) := by
      intro a
      rw [← expect_mul_const]
      congr 1
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    change expect (p 0) (fun a => expect q _) ≤ _
    simp_rw [he]
    calc
      _ ≤ expect (p 0) (fun a => Real.exp (t*(M a-expect (p 0) M)) * Real.exp V) := by
        apply expect_mono
        intro a
        have h := ih (fun i => p i.succ) (fun x => f (Fin.cons a x))
          (fun i => c i.succ) (htail a)
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right h
          (Real.exp_pos (t*(M a-expect (p 0) M))).le
      _ = expect (p 0) (fun a => Real.exp (t*(M a-expect (p 0) M))) * Real.exp V :=
        expect_mul_const _ _ _
      _ ≤ Real.exp (t^2*(c 0)^2/8) * Real.exp V :=
        mul_le_mul_of_nonneg_right hs (Real.exp_pos V).le
      _ = _ := by
        rw [← Real.exp_add, Fin.sum_univ_succ]
        congr 1
        dsimp [V]
        ring

theorem bounded_differences_tail (n : ℕ) (p : Fin n → Law α)
    (f : (Fin n → α) → ℝ) (c : Fin n → ℝ) (hd : BoundedDifferences f c)
    (a : ℝ) (ha : 0 < a) (hc : 0 < ∑ i, (c i)^2) :
    prob (product p) (fun x => f x < expect (product p) f-a) ≤
      Real.exp (-2*a^2/(∑ i, (c i)^2)) := by
  have h := lower_tail_of_mgf (product p) (fun x => f x-expect (product p) f)
    (∑ i, (c i)^2) a hc ha (fun t => by
      simpa only [neg_sq] using bounded_differences_mgf n p f c hd (-t))
  convert h using 2
  funext x
  apply propext
  constructor <;> intro hx <;> linarith

omit [Fintype α] in
/-- Zero coordinate allowances force the statistic to be constant. -/
theorem bounded_differences_constant (n : ℕ) (f : (Fin n → α) → ℝ)
    (hd : BoundedDifferences f (fun _ => 0)) (x y : Fin n → α) : f x = f y := by
  induction n with
  | zero => exact congrArg f (Subsingleton.elim x y)
  | succ n ih =>
    have hh : f (Fin.cons (y 0) (Fin.tail x)) = f x := by
      have h := hd 0 x (y 0)
      have he : Function.update x 0 (y 0) = Fin.cons (y 0) (Fin.tail x) := by
        conv_lhs => rw [← Fin.cons_self_tail x]
        rw [update_cons_zero]
      rw [he] at h
      exact sub_eq_zero.1 (abs_nonpos_iff.1 h)
    have ht : BoundedDifferences (fun z => f (Fin.cons (y 0) z)) (fun _ => 0) := by
      intro i z a
      simpa only [update_cons_succ] using hd i.succ (Fin.cons (y 0) z) a
    calc
      f x = f (Fin.cons (y 0) (Fin.tail x)) := hh.symm
      _ = f (Fin.cons (y 0) (Fin.tail y)) := ih _ ht _ _
      _ = f y := congrArg f (Fin.cons_self_tail y)

theorem zero_differences_tail (n : ℕ) (p : Fin n → Law α)
    (f : (Fin n → α) → ℝ) (hd : BoundedDifferences f (fun _ => 0))
    (a : ℝ) (ha : 0 < a) : prob (product p) (fun x => f x < expect (product p) f-a) = 0 := by
  have he : ∀ x, expect (product p) f = f x := by
    intro x
    have hf : f = (fun _ => f x) := funext (fun y => bounded_differences_constant n f hd y x)
    rw [hf, expect_const]
  unfold prob
  apply Finset.sum_eq_zero
  intro x _
  rw [he x]
  have hn : ¬ f x < f x-a := by linarith
  simp only [ite_eq_right hn]

end
end Max2SAT.FiniteLaw
