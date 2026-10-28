import Max2SAT.IndependentPairs.Squares

/-! Scalar properties of an independent copy difference. These are the
inputs to the random-matrix expectation estimate in the paper. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open FiniteLaw
variable {α : Type*} [Fintype α]

theorem difference_second_moment (p : Law α) (X : α → ℝ) :
    expect (tensor p p) (fun z => (X z.1-X z.2)^2)=
      2*expect p (fun x => (X x)^2)-2*(expect p X)^2 := by
  rw [expect_tensor]
  have he : ∀ a, expect p (fun b => (X a-X b)^2)=
      (X a)^2-2*X a*expect p X+expect p (fun b => (X b)^2) := by
    intro a
    simp_rw [sub_sq]
    rw [expect_add,expect_sub,expect_const,expect_const_mul]
  simp_rw [he]
  rw [expect_add,expect_sub,expect_const]
  have hh : expect p (fun a => 2*X a*expect p X)=2*(expect p X)^2 := by
    rw [expect_mul_const,expect_const_mul]; ring
  rw [hh]; ring

theorem centered_difference_moment (p : Law α) (X : α → ℝ) (hm : expect p X=0) :
    expect (tensor p p) (fun z => (X z.1-X z.2)^2)=2*expect p (fun x => (X x)^2) := by
  rw [difference_second_moment,hm]; ring

theorem difference_bound (p : Law α) (X : α → ℝ) (B : ℝ)
    (hb : ∀ x, 0<p.mass x → |X x|≤B) (z : α × α) (hz : 0<(tensor p p).mass z) :
    |X z.1-X z.2|≤2*B := by
  have h1 : 0<p.mass z.1 := pos_of_mul_pos_left hz (p.nonneg z.2)
  have h2 : 0<p.mass z.2 := pos_of_mul_pos_right hz (p.nonneg z.1)
  exact (abs_sub (X z.1) (X z.2)).trans (by linarith [hb z.1 h1,hb z.2 h2])

theorem difference_symmetric (p : Law α) (X : α → ℝ) (f : ℝ → ℝ) :
    expect (tensor p p) (fun z => f (X z.1-X z.2))=
      expect (tensor p p) (fun z => f (-(X z.1-X z.2))) := by
  simp only [expect,tensor,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [neg_sub,mul_comm (p.mass b)]

end
end Max2SAT.IndependentPairs
