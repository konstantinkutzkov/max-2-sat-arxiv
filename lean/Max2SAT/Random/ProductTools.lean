import Max2SAT.Random.FreshBits

/-! Projections and moments of finite product laws. These lemmas expose
whole collections of coordinates; pairwise independence is not substituted
for joint independence. -/
namespace Max2SAT.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α β γ ι κ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem push_comp (p : Law α) (f : α → β) (g : β → γ) :
    push (push p f) g = push p (g ∘ f) := by
  apply Law.ext
  funext c
  simp only [push]
  change (∑ b, if g b = c then (∑ a, if f a = b then p.mass a else 0) else 0) = _
  have he : ∀ b, (if g b = c then (∑ a, if f a = b then p.mass a else 0) else 0) =
      ∑ a, if f a = b then (if g b = c then p.mass a else 0) else 0 := by
    intro b
    by_cases h : g b = c <;> simp [h]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem product_select (p : ι → Law α) (f : κ → ι) (hf : Function.Injective f) :
    push (product p) (fun x j => x (f j)) = product (fun j => p (f j)) := by
  apply Law.ext
  funext y
  let Q : ι → α → Prop := fun i a => ∀ j, f j = i → a = y j
  have he : (fun x : ι → α => (fun j => x (f j)) = y) = (fun x => ∀ i, Q i (x i)) := by
    funext x
    apply propext
    constructor
    · intro h i j hj
      simpa [hj] using congrFun h j
    · intro h
      exact funext (fun j => h (f j) j rfl)
  change prob (product p) (fun x => (fun j => x (f j)) = y) = _
  rw [he, product_prob]
  have hq : ∀ j, prob (p (f j)) (Q (f j)) = (p (f j)).mass (y j) := by
    intro j
    have hQ : Q (f j) = (fun a => a=y j) := by
      funext a
      apply propext
      constructor
      · intro h; exact h j rfl
      · intro h k hk
        simpa [hf hk] using h
    rw [hQ, prob_eq]
  have hout : ∀ i ∈ (Finset.univ : Finset ι), i ∉ Finset.univ.image f →
      prob (p i) (Q i) = 1 := by
    intro i _ hi
    have hQ : Q i = (fun _ => True) := by
      funext a
      apply propext
      simp only [iff_true]
      intro j hj
      exact False.elim (hi (Finset.mem_image.mpr ⟨j,Finset.mem_univ j,hj⟩))
    rw [hQ,prob_true]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image f)) hout,
    Finset.prod_image (fun i _ j _ h => hf h)]
  simp only [hq,product]

theorem push_product_apply (p : ι → Law α) (i : ι) :
    push (product p) (fun x => x i) = p i := by
  apply Law.ext
  funext a
  have he : (fun x : ι → α => x i=a) =
      (fun x => ∀ j, if j=i then x j=a else True) := by
    funext x
    simp
  change prob (product p) (fun x => x i=a) = _
  rw [he]
  rw [product_prob p (fun j b => if j=i then b=a else True)]
  have hq : ∀ j, prob (p j) (fun b => if j=i then b=a else True) =
      if j=i then (p i).mass a else 1 := by
    intro j
    by_cases h : j=i <;> simp [h]
  simp only [hq]
  simp

theorem expect_add (p : Law α) (f g : α → ℝ) :
    expect p (fun x => f x + g x) = expect p f + expect p g := by
  simp [expect,mul_add,Finset.sum_add_distrib]

theorem expect_mul_const (p : Law α) (f : α → ℝ) (c : ℝ) :
    expect p (fun x => f x * c) = expect p f * c := by
  simp [expect,mul_assoc,Finset.sum_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem expect_sum (p : Law α) (s : Finset ι) (f : ι → α → ℝ) :
    expect p (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, expect p (f i) := by
  simp only [expect,Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_congr_support (p : Law α) (f g : α → ℝ)
    (h : ∀ x, 0 < p.mass x → f x = g x) : expect p f = expect p g := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : 0 < p.mass x
  · rw [h x hx]
  · have hz : p.mass x = 0 := le_antisymm (le_of_not_gt hx) (p.nonneg x)
    simp [hz]

theorem condition_support (p : Law α) (P : α → Prop) (h : 0 < prob p P)
    (a : α) (ha : 0 < (condition p P h).mass a) : P a := by
  by_contra hn
  simp [condition_mass,hn] at ha

theorem fresh_selection (known : Finset ι) (x : ι → Bool)
    (h : 0 < prob (fairBits ι) (history known x))
    (f : κ → ι) (hf : Function.Injective f) (hn : ∀ j, f j ∉ known) :
    push (condition (fairBits ι) (history known x) h) (fun z j => z (f j)) =
      fairBits κ := by
  rw [condition_fair_history,product_select _ f hf]
  simp only [hn,↓reduceIte,fairBits]

theorem fresh_coordinate (known : Finset ι) (x : ι → Bool)
    (h : 0 < prob (fairBits ι) (history known x)) (i : ι) (hi : i ∉ known) :
    push (condition (fairBits ι) (history known x) h) (fun z => z i) = fair := by
  rw [condition_fair_history,push_product_apply]
  simp [hi]

end
end Max2SAT.FiniteLaw
