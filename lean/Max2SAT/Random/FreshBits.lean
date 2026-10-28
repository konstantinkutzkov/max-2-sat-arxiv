import Max2SAT.Random.ProductLaw

/-! Exact finite conditional laws for unrevealed independent signs. These
are exposure lemmas, not assumptions about independence of pruning cuts. -/
namespace Max2SAT.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

def point (a : α) : Law α where
  mass b := if b = a then 1 else 0
  nonneg b := by split_ifs <;> norm_num
  total := by simp

@[simp] theorem prob_true (p : Law α) : prob p (fun _ => True) = 1 := by
  simp [prob, p.total]

@[simp] theorem prob_eq (p : Law α) (a : α) : prob p (fun b => b=a) = p.mass a := by
  simp [prob]

theorem condition_true (p : Law α) (h : 0 < prob p (fun _ => True)) :
    condition p (fun _ => True) h = p := by
  apply Law.ext
  funext a
  simp [condition_mass]

theorem condition_eq (p : Law α) (a : α) (h : 0 < prob p (fun b => b=a)) :
    condition p (fun b => b=a) h = point a := by
  have hp : 0 < p.mass a := by simpa using h
  apply Law.ext
  funext b
  by_cases hb : b=a <;> simp [condition_mass, point, hb, ne_of_gt hp]

def fair : Law Bool where
  mass _ := 1/2
  nonneg _ := by norm_num
  total := by norm_num

def fairBits (ι : Type*) [Fintype ι] [DecidableEq ι] : Law (ι → Bool) :=
  product (ι := ι) (fun _ => fair)

theorem fairBits_mass (x : ι → Bool) :
    (fairBits ι).mass x = (1/2 : ℝ) ^ Fintype.card ι := by
  simp [fairBits, product, fair]

def history (known : Finset ι) (x z : ι → Bool) : Prop :=
  ∀ i, if i ∈ known then z i = x i else True

theorem fair_history_positive (known : Finset ι) (x : ι → Bool) :
    0 < prob (fairBits ι) (history known x) := by
  have he := product_prob (fun _ : ι => fair)
    (fun i b => if i ∈ known then b=x i else True)
  change 0 < prob (product (fun _ : ι => fair))
    (fun z => ∀ i, if i ∈ known then z i=x i else True)
  rw [he]
  apply Finset.prod_pos
  intro i _
  by_cases hi : i ∈ known <;> simp [hi,fair]

/-- Conditional on the exact values of any already exposed coordinates,
all other coordinates still have the independent fair-bit product law. -/
theorem condition_fair_history (known : Finset ι) (x : ι → Bool)
    (h : 0 < prob (fairBits ι) (history known x)) :
    condition (fairBits ι) (history known x) h =
      product (fun i => if i ∈ known then point (x i) else fair) := by
  have hh := condition_product (fun _ : ι => fair)
    (fun i b => if i ∈ known then b=x i else True) h
  apply hh.trans
  congr 1
  funext i
  by_cases hi : i ∈ known
  · simp only [hi, ↓reduceIte]
    exact condition_eq fair (x i) _
  · simp only [hi, ↓reduceIte]
    exact condition_true fair _

/-- Boolean multiplication of signs: equal bits represent +1. -/
def multiplyBits (mask : ι → Bool) : (ι → Bool) ≃ (ι → Bool) where
  toFun x i := !(xor (mask i) (x i))
  invFun x i := !(xor (mask i) (x i))
  left_inv x := by funext i; dsimp; cases mask i <;> cases x i <;> rfl
  right_inv x := by funext i; dsimp; cases mask i <;> cases x i <;> rfl

theorem fairBits_multiply (mask : ι → Bool) :
    push (fairBits ι) (multiplyBits mask) = fairBits ι := by
  apply Law.ext
  funext x
  rw [push_equiv_mass, fairBits_mass, fairBits_mass]

/-- A common assignment bit may multiply many endpoint signs. Their
joint distribution remains fair and independent, even conditional on all
the assignment data. The data law p is arbitrary. -/
theorem joint_multiply (p : Law α) (mask : α → ι → Bool) :
    push (tensor p (fairBits ι)) (fun z => (z.1,multiplyBits (mask z.1) z.2)) =
      tensor p (fairBits ι) := by
  apply Law.ext
  funext z
  rcases z with ⟨a,x⟩
  simp only [push,tensor,Fintype.sum_prod_type,Prod.mk.injEq]
  have he : ∀ b y,
      (if b=a ∧ multiplyBits (mask b) y=x then p.mass b * (fairBits ι).mass y else 0) =
      (if b=a then
        (if y=(multiplyBits (mask a)).symm x then p.mass a * (fairBits ι).mass x else 0)
        else 0) := by
    intro b y
    by_cases hb : b=a
    · subst b
      simp [← (multiplyBits (mask a)).eq_symm_apply, fairBits_mass]
    · simp [hb]
  simp_rw [he]
  simp

end
end Max2SAT.FiniteLaw
