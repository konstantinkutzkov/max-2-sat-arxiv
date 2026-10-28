import Max2SAT.Random.ConcentrationTools
import Max2SAT.Random.PredictableSigns
import Max2SAT.Random.RequirementTail

/-! Variance-sensitive scalar concentration used in the independent-pair
proof. The elementary estimate exp(z) <= 1+z+z^2 for |z|<=1 is sufficient
for its small relative deviations. Laws may have zero-mass outcomes. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open FiniteLaw
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

theorem expect_const_mul (p : Law α) (c : ℝ) (f : α → ℝ) :
    expect p (fun x => c*f x)=c*expect p f := by
  simpa only [mul_comm] using expect_mul_const p f c

theorem centered_small_mgf (p : Law α) (X : α → ℝ) (B v t : ℝ)
    (hm : expect p X=0) (hb : ∀ x, 0<p.mass x → |X x|≤B)
    (hv : expect p (fun x => (X x)^2)≤v) (ht : |t| *B≤1) :
    expect p (fun x => Real.exp (t*X x))≤Real.exp (t^2*v) := by
  have hp : expect p (fun x => Real.exp (t*X x))≤
      expect p (fun x => 1+t*X x+t^2*(X x)^2) := by
    apply expect_mono_support
    intro x hx
    have hsmall : |t*X x|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hb x hx) (abs_nonneg t)).trans ht
    have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hsmall)).2
    nlinarith
  have he : expect p (fun x => 1+t*X x+t^2*(X x)^2)=
      1+t^2*expect p (fun x => (X x)^2) := by
    simp [expect_add,expect_const_mul,hm]
  rw [he] at hp
  exact hp.trans ((by nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg t)] :
    1+t^2*expect p (fun x => (X x)^2)≤1+t^2*v).trans
      (by linarith [Real.add_one_le_exp (t^2*v)]))

theorem independent_small_mgf (p : ι → Law α) (X : ι → α → ℝ)
    (B : ℝ) (v : ι → ℝ) (t : ℝ)
    (hm : ∀ i, expect (p i) (X i)=0)
    (hb : ∀ i x, 0<(p i).mass x → |X i x|≤B)
    (hv : ∀ i, expect (p i) (fun x => (X i x)^2)≤v i) (ht : |t| *B≤1) :
    expect (product p) (fun x => Real.exp (t*∑ i, X i (x i)))≤
      Real.exp (t^2*∑ i, v i) := by
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [expect_product_separable p (fun i x => Real.exp (t*X i x))]
  apply Finset.prod_le_prod₀
  · intro i _; exact expect_nonneg _ (fun _ => (Real.exp_pos _).le)
  · intro i _; exact centered_small_mgf _ _ _ _ _ (hm i) (hb i) (hv i) ht

theorem upper_tail_small (p : ι → Law α) (X : ι → α → ℝ)
    (B : ℝ) (v : ι → ℝ) (V a : ℝ)
    (hm : ∀ i, expect (p i) (X i)=0)
    (hb : ∀ i x, 0<(p i).mass x → |X i x|≤B)
    (hv : ∀ i, expect (p i) (fun x => (X i x)^2)≤v i)
    (hs : (∑ i, v i)≤V) (hV : 0<V) (ha : 0<a) (hsmall : a*B≤2*V) :
    prob (product p) (fun x => a≤∑ i, X i (x i))≤Real.exp (-a^2/(4*V)) := by
  let t := a/(2*V)
  have ht : 0<t := div_pos ha (by positivity)
  have htB : |t| *B≤1 := by
    rw [abs_of_pos ht]
    dsimp [t]
    rw [div_mul_eq_mul_div]
    exact (div_le_one (by positivity : 0<2*V)).mpr hsmall
  have hmgf := independent_small_mgf p X B v t hm hb hv htB
  have hmgf' : expect (product p) (fun x => Real.exp (t*∑ i, X i (x i)))≤
      Real.exp (t^2*V) := hmgf.trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hs (sq_nonneg t)))
  have h := (exponential_markov (product p) (fun x => ∑ i, X i (x i)) t a ht).trans
    (mul_le_mul_of_nonneg_left hmgf' (Real.exp_pos _).le)
  rw [←Real.exp_add] at h
  have he : -t*a+t^2*V= -a^2/(4*V) := by
    dsimp [t]; field_simp; ring
  rwa [he] at h

theorem lower_tail_small (p : ι → Law α) (X : ι → α → ℝ)
    (B : ℝ) (v : ι → ℝ) (V a : ℝ)
    (hm : ∀ i, expect (p i) (X i)=0)
    (hb : ∀ i x, 0<(p i).mass x → |X i x|≤B)
    (hv : ∀ i, expect (p i) (fun x => (X i x)^2)≤v i)
    (hs : (∑ i, v i)≤V) (hV : 0<V) (ha : 0<a) (hsmall : a*B≤2*V) :
    prob (product p) (fun x => (∑ i, X i (x i))≤ -a)≤Real.exp (-a^2/(4*V)) := by
  have h := upper_tail_small p (fun i x => -X i x) B v V a
    (by intro i; simpa only [expect,mul_neg,Finset.sum_neg_distrib,neg_eq_zero] using hm i)
    (by simpa only [abs_neg] using hb) (by simpa only [neg_sq] using hv) hs hV ha hsmall
  simpa only [Finset.sum_neg_distrib,le_neg] using h

theorem two_sided_small (p : ι → Law α) (X : ι → α → ℝ)
    (B : ℝ) (v : ι → ℝ) (V a : ℝ)
    (hm : ∀ i, expect (p i) (X i)=0)
    (hb : ∀ i x, 0<(p i).mass x → |X i x|≤B)
    (hv : ∀ i, expect (p i) (fun x => (X i x)^2)≤v i)
    (hs : (∑ i, v i)≤V) (hV : 0<V) (ha : 0<a) (hsmall : a*B≤2*V) :
    prob (product p) (fun x => a≤|∑ i, X i (x i)|)≤2*Real.exp (-a^2/(4*V)) := by
  have he : (fun x : ι → α => a≤|∑ i, X i (x i)|)=
      (fun x => a≤(∑ i, X i (x i)) ∨ (∑ i, X i (x i))≤ -a) := by
    funext x; apply propext; simpa only [le_neg] using (le_abs (a:=a) (b:=∑ i, X i (x i)))
  rw [he]
  have h := (prob_union_le (product p) _ _).trans
    (add_le_add (upper_tail_small p X B v V a hm hb hv hs hV ha hsmall)
      (lower_tail_small p X B v V a hm hb hv hs hV ha hsmall))
  simpa only [two_mul] using h

/-- A Bernstein-form bound valid beyond the small-deviation regime. -/
theorem upper_tail (p : ι → Law α) (X : ι → α → ℝ)
    (B : ℝ) (v : ι → ℝ) (V a : ℝ) (hB : 0≤B)
    (hm : ∀ i, expect (p i) (X i)=0)
    (hb : ∀ i x, 0<(p i).mass x → |X i x|≤B)
    (hv : ∀ i, expect (p i) (fun x => (X i x)^2)≤v i)
    (hs : (∑ i, v i)≤V) (hV : 0<V) (ha : 0<a) :
    prob (product p) (fun x => a≤∑ i, X i (x i))≤
      Real.exp (-a^2/(4*V+2*B*a)) := by
  have h := upper_tail_small p X B v (V+B*a/2) a hm hb hv
    (by nlinarith) (by positivity) ha (by nlinarith)
  convert h using 2; ring

end
end Max2SAT.IndependentPairs
