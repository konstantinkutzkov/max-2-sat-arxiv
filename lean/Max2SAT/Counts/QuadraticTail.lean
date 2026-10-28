import Max2SAT.Counts.WithinRounds
import Mathlib.Analysis.Convex.Jensen

/-! A sufficient quadratic tail using random partitions and the linear
Rademacher MGF. No Hanson--Wright theorem is required. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
open scoped Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def crossForm (N : Matrix ι ι ℝ) (m x y : ι → Bool) : ℝ :=
  ∑ i, ∑ j, if m i=true ∧ m j=false then N i j*sign (x i)*sign (y j) else 0

def mixedBits (m x y : ι → Bool) : ι → Bool := fun i => if m i then x i else y i

theorem mixed_bits_law (m : ι → Bool) :
    push (tensor (fairBits ι) (fairBits ι)) (fun z => mixedBits m z.1 z.2)=fairBits ι := by
  rw [show (fun z : (ι → Bool) × (ι → Bool) => mixedBits m z.1 z.2) =
    (fun z i => if m i then (z i).1 else (z i).2) ∘ (fun z i => (z.1 i,z.2 i)) by rfl,
    ←push_comp]
  simp only [fairBits]
  rw [tensor_product_law,product_push (fun _ : ι => tensor fair fair)
    (fun i (z : Bool × Bool) => if m i then z.1 else z.2)]
  congr 1
  funext i
  cases m i <;> apply Law.ext <;> funext b <;> cases b <;>
    norm_num [push,tensor,fair,Fintype.sum_prod_type]

omit [DecidableEq ι] in
theorem cross_mixed (N : Matrix ι ι ℝ) (m x y : ι → Bool) :
    crossForm N m (mixedBits m x y) (mixedBits m x y)=crossForm N m x y := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : m i=true ∧ m j=false
  · simp [mixedBits,h]
  · simp [h]

theorem cross_mgf (N : Matrix ι ι ℝ) (m : ι → Bool) (V t : ℝ)
    (hV : 0≤V) (hN : ‖N‖^2≤V) :
    expect (fairBits ι) (fun x => Real.exp (t*crossForm N m x x)) ≤
      Real.exp (t^2*(Fintype.card ι*V)/2) := by
  rw [←mixed_bits_law m,expect_push]
  simp_rw [cross_mixed]
  rw [expect_tensor]
  apply (expect_mono _ (fun x => ?_)).trans_eq (expect_const _ _)
  let z : ι → ℝ := fun i => if m i then sign (x i) else 0
  let a : ι → ℝ := fun j => if m j then 0 else ∑ i, N i j*z i
  have he : ∀ y, crossForm N m x y=∑ j, a j*sign (y j) := by
    intro y
    unfold crossForm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    cases hj : m j
    · simp only [a,hj,Bool.false_eq_true,↓reduceIte,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      cases hi : m i <;> simp [z,hi]
    · simp [a,hj]
  simp_rw [he]
  apply (signed_sum_mgf a t).trans
  apply Real.exp_le_exp.mpr
  have ht : ‖N.transpose‖^2≤V := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (show ‖N.conjTranspose‖^2≤V by rw [Matrix.l2_opNorm_conjTranspose]; exact hN)
  have hb := matrix_squared_energy N.transpose z V ht
  have hz : (∑ i, (z i)^2)≤Fintype.card ι := by
    calc
      _ ≤ ∑ _i : ι, (1:ℝ) := Finset.sum_le_sum (fun i _ => by
        cases hm : m i <;> cases hx : x i <;> norm_num [z,hm,hx,sign])
      _ = _ := by simp
  have ha : (∑ j, (a j)^2)≤∑ j, (∑ i, N.transpose j i*z i)^2 := by
    apply Finset.sum_le_sum
    intro j _
    cases hj : m j <;> simp [a,hj,Matrix.transpose_apply,sq_nonneg]
  have h := ha.trans (hb.trans (mul_le_mul_of_nonneg_left hz hV))
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg t)
  nlinarith


theorem partition_cross_mean (N : Matrix ι ι ℝ) (hdiag : ∀ i, N i i=0)
    (x : ι → Bool) :
    expect (fairBits ι) (fun m => crossForm N m x x)=
      (∑ i, ∑ j, N i j*sign (x i)*sign (x j))/4 := by
  have he : ∀ (m : ι → Bool) i j (a : ℝ),
      (if m i=true ∧ m j=false then a else 0)=
        (1+sign (m i)-sign (m j)-sign (m i)*sign (m j))*a/4 := by
    intro m i j a
    cases m i <;> cases m j <;> norm_num [sign]
  unfold crossForm
  simp_rw [he,expect_sum]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i=j
  · subst j; simp [hdiag]
  · have hh : expect (fairBits ι)
        (fun m => 1+sign (m i)-sign (m j)-sign (m i)*sign (m j))=1 := by
      have e : ∀ (p : Law (ι → Bool)) (f g : (ι → Bool) → ℝ),
          expect p (fun z => f z-g z)=expect p f-expect p g := by
        intro p f g
        simp [expect,mul_sub,Finset.sum_sub_distrib]
      rw [e,e,expect_add,expect_const,fair_coordinate_mean,fair_coordinate_mean,
        fair_coordinate_product]
      simp [hij]
    have hh' := expect_mul_const (fairBits ι)
      (fun m => 1+sign (m i)-sign (m j)-sign (m i)*sign (m j))
      (N i j*sign (x i)*sign (x j)/4)
    simpa only [←mul_div_assoc,hh,one_mul] using hh'

theorem exp_expect_le {Ω : Type*} [Fintype Ω] (p : Law Ω) (f : Ω → ℝ) :
    Real.exp (expect p f)≤expect p (fun x => Real.exp (f x)) := by
  simpa only [expect,smul_eq_mul] using convexOn_exp.map_sum_le
    (t := Finset.univ) (w := p.mass) (p := f) (fun x _ => p.nonneg x) p.total
    (fun _ _ => Set.mem_univ _)

theorem quadratic_mgf (N : Matrix ι ι ℝ) (hdiag : ∀ i, N i i=0)
    (V t : ℝ) (hV : 0≤V) (hN : ‖N‖^2≤V) :
    expect (fairBits ι) (fun x => Real.exp (-t*quadraticTerm N x)) ≤
      Real.exp (t^2*(Fintype.card ι*V)/2) := by
  have hp : ∀ x, Real.exp (-t*quadraticTerm N x)≤
      expect (fairBits ι) (fun m => Real.exp (t*crossForm N m x x)) := by
    intro x
    have h := exp_expect_le (fairBits ι) (fun m => crossForm N m x x*t)
    rw [expect_mul_const,partition_cross_mean N hdiag x] at h
    have hsum : (∑ i, ∑ j, sign (x i)*N i j*sign (x j)) =
        ∑ i, ∑ j, N i j*sign (x i)*sign (x j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hleft : -t*quadraticTerm N x =
        (∑ i, ∑ j, N i j*sign (x i)*sign (x j))/4*t := by
      unfold quadraticTerm
      rw [hsum]
      ring
    rw [hleft]
    simpa only [mul_comm t] using h
  apply (expect_mono _ hp).trans
  have he : expect (fairBits ι) (fun x => expect (fairBits ι)
      (fun m => Real.exp (t*crossForm N m x x))) =
      expect (fairBits ι) (fun m => expect (fairBits ι)
        (fun x => Real.exp (t*crossForm N m x x))) := by
    simp only [expect,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he]
  exact (expect_mono _ (fun m => cross_mgf N m V t hV hN)).trans_eq (expect_const _ _)

/-- A norm-only quadratic estimate sufficient for the fixed-round theorem.
It holds even without symmetry. The budget B may exceed the block size
 times V, allowing one common positive budget for empty and nonempty blocks. -/
theorem quadratic_norm_tail (N : Matrix ι ι ℝ) (hdiag : ∀ i, N i i=0)
    (V B e : ℝ) (hV : 0≤V) (hB : 0<B) (he : 0<e)
    (hN : ‖N‖^2≤V) (hsize : Fintype.card ι*V≤B) :
    prob (fairBits ι) (fun x => quadraticTerm N x < -e)≤Real.exp (-e^2/(2*B)) := by
  have h := lower_tail_of_mgf (fairBits ι) (quadraticTerm N) (4*B) e
    (by positivity) he (by
      intro t
      apply (quadratic_mgf N hdiag V t hV hN).trans
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hsize (sq_nonneg t)
      nlinarith)
  convert h using 1
  congr 1
  ring

end
end Max2SAT.Counts
