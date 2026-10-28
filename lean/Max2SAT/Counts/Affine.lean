import Max2SAT.Random.WeightedEnumeration

/-! Rational sums of Boolean values used by count comparisons. The name
`Affine` is internal; evaluation is a constant plus one coefficient per bit. -/
namespace Max2SAT.Counts

def bit (b : Bool) : ℚ := if b then 1 else 0
def direction (b : Bool) : ℚ := if b then 1 else -1

@[simp] theorem bit_false : bit false = 0 := rfl
@[simp] theorem bit_true : bit true = 1 := rfl
theorem bit_nonneg (b : Bool) : 0 ≤ bit b := by cases b <;> norm_num [bit]
theorem bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> norm_num [bit]
@[simp] theorem abs_direction (b : Bool) : |direction b| = 1 := by
  cases b <;> norm_num [direction]

structure Affine (n : ℕ) where
  constant : ℚ
  coeff : Fin n → ℚ

namespace Affine
def eval (A : Affine n) (x : Assignment n) : ℚ :=
  A.constant + ∑ i, A.coeff i * bit (x i)
def zero : Affine n := ⟨0,fun _ => 0⟩
def add (A B : Affine n) : Affine n :=
  ⟨A.constant+B.constant,fun i => A.coeff i+B.coeff i⟩
def scale (q : ℚ) (A : Affine n) : Affine n :=
  ⟨q*A.constant,fun i => q*A.coeff i⟩
def shift (q : ℚ) (A : Affine n) : Affine n := ⟨A.constant+q,A.coeff⟩
def sum (S : Finset ι) (A : ι → Affine n) : Affine n :=
  ⟨∑ i∈S, (A i).constant,fun j => ∑ i∈S, (A i).coeff j⟩
def budget (A : Affine n) : Weighted.Budget n :=
  ⟨fun i b => A.coeff i*bit b,-A.constant⟩

@[simp] theorem eval_zero (x : Assignment n) : zero.eval x = 0 := by simp [eval,zero]
@[simp] theorem eval_add (A B : Affine n) (x : Assignment n) :
    (A.add B).eval x = A.eval x+B.eval x := by
  simp [eval,add,add_mul,Finset.sum_add_distrib]; ring
@[simp] theorem eval_scale (q : ℚ) (A : Affine n) (x : Assignment n) :
    (A.scale q).eval x = q*A.eval x := by
  simp [eval,scale,Finset.mul_sum,mul_add,mul_assoc]
@[simp] theorem eval_shift (q : ℚ) (A : Affine n) (x : Assignment n) :
    (A.shift q).eval x = A.eval x+q := by simp [eval,shift]; ring
@[simp] theorem eval_sum (S : Finset ι) (A : ι → Affine n) (x : Assignment n) :
    (sum S A).eval x = ∑ i∈S, (A i).eval x := by
  simp only [eval,sum,Finset.sum_mul,Finset.sum_add_distrib]
  rw [Finset.sum_comm]

@[simp] theorem budget_holds (A : Affine n) (x : Assignment n) :
    A.budget.Holds x ↔ A.eval x ≤ 0 := by
  simp only [budget,Weighted.Budget.Holds,Weighted.Budget.lhs,eval]
  constructor <;> intro h <;> linarith

theorem eval_update (A : Affine n) (x : Assignment n) (i : Fin n) (b : Bool) :
    A.eval (Function.update x i b) = A.eval x+A.coeff i*(bit b-bit (x i)) := by
  unfold eval
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have he : (∑ j∈Finset.univ.erase i, A.coeff j*bit (Function.update x i b j)) =
      ∑ j∈Finset.univ.erase i, A.coeff j*bit (x j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [(Finset.mem_erase.mp hj).1]
  simp [he]; ring

/-- Substitution of one half for unknown variables, with earlier values fixed. -/
def average (A : Affine n) (known : Finset (Fin n)) (x : Assignment n) : ℚ :=
  A.constant + ∑ i, A.coeff i*(if i∈known then bit (x i) else 1/2)

theorem average_agree (A : Affine n) (S : Finset (Fin n)) (x y : Assignment n)
    (h : ∀ i∈S, x i=y i) : A.average S x=A.average S y := by
  unfold average
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i∈S
  · simp [hi,h i hi]
  · simp [hi]

end Affine
end Max2SAT.Counts
