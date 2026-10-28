import Max2SAT.IndependentPairs.Scalar

/-! Concentration of sums of squared entries. The variance budget is
B^2 times the expected mass, rather than the number of entries times B^4.
This distinction preserves the logarithmic-density regime in the paper. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open FiniteLaw
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

theorem bounded_mean (p : Law α) (Y : α → ℝ) (U : ℝ)
    (h : ∀ x, 0<p.mass x → Y x∈Set.Icc 0 U) :
    expect p Y∈Set.Icc 0 U := by
  constructor
  · exact (expect_const p 0).symm.trans_le (expect_mono_support p (fun x hx => (h x hx).1))
  · exact (expect_mono_support p (fun x hx => (h x hx).2)).trans_eq (expect_const p U)

theorem centered_bounded (p : Law α) (Y : α → ℝ) (U : ℝ)
    (h : ∀ x, 0<p.mass x → Y x∈Set.Icc 0 U) :
    (expect p (fun x => Y x-expect p Y)=0) ∧
    (∀ x, 0<p.mass x → |Y x-expect p Y|≤U) ∧
    expect p (fun x => (Y x-expect p Y)^2)≤U*expect p Y := by
  have hm := bounded_mean p Y U h
  have hvar : expect p (fun x => (Y x-expect p Y)^2)=
      expect p (fun x => (Y x)^2)-(expect p Y)^2 := by
    have he : (fun x => (Y x-expect p Y)^2)=
        (fun x => (Y x)^2-2*expect p Y*Y x+(expect p Y)^2) := by funext x; ring
    rw [he,expect_add,expect_sub,expect_const_mul,expect_const]
    ring
  have hsq : expect p (fun x => (Y x)^2)≤U*expect p Y := by
    calc
      _≤expect p (fun x => U*Y x) := expect_mono_support p (by
        intro x hx; rcases h x hx with ⟨h0,hU⟩; nlinarith)
      _=U*expect p Y := expect_const_mul _ _ _
  refine ⟨by simp [expect_sub],?_,?_⟩
  · intro x hx; rcases h x hx with ⟨h0,hU⟩
    exact abs_le.mpr ⟨by linarith [hm.2],by linarith [hm.1]⟩
  · rw [hvar]; nlinarith [sq_nonneg (expect p Y)]

theorem squared_entry_bounds (p : Law α) (X : α → ℝ) (B : ℝ)
    (h : ∀ x, 0<p.mass x → |X x|≤B) :
    (expect p (fun x => (X x)^2-expect p (fun y => (X y)^2))=0) ∧
    (∀ x, 0<p.mass x → |(X x)^2-expect p (fun y => (X y)^2)|≤B^2) ∧
    expect p (fun x => ((X x)^2-expect p (fun y => (X y)^2))^2)≤
      B^2*expect p (fun y => (X y)^2) := by
  apply centered_bounded
  intro x hx
  refine ⟨sq_nonneg _,?_⟩
  have hb := abs_le.mp (h x hx)
  nlinarith

theorem squares_lower_tail (p : ι → Law α) (X : ι → α → ℝ)
    (B m M η : ℝ) (hB : 0<B) (hm : 0<m) (hmM : m≤M)
    (he : 0<η) (he2 : η≤2)
    (hb : ∀ i x, 0<(p i).mass x → |X i x|≤B)
    (hmean : m≤∑ i, expect (p i) (fun x => (X i x)^2))
    (hcap : (∑ i, expect (p i) (fun x => (X i x)^2))≤M) :
    prob (product p) (fun x => (∑ i, (X i (x i))^2)≤(1-η)*m)≤
      Real.exp (-(η*m)^2/(4*B^2*M)) := by
  let μ := fun i => expect (p i) (fun x => (X i x)^2)
  let Y := fun i x => (X i x)^2-μ i
  have hc := fun i => squared_entry_bounds (p i) (X i) B (hb i)
  have h := lower_tail_small p Y (B^2) (fun i => B^2*μ i) (B^2*M) (η*m)
    (fun i => (hc i).1) (fun i => (hc i).2.1) (fun i => (hc i).2.2)
    (by rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hcap (sq_nonneg B))
    (mul_pos (sq_pos_of_pos hB) (hm.trans_le hmM)) (mul_pos he hm) (by
      have h1 : η*m≤2*M := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg B)])
  apply (prob_mono_support (product p) _ _ ?_).trans
    (by simpa only [mul_assoc] using h)
  intro x _ hx
  change (∑ i, ((X i (x i))^2-μ i))≤ -(η*m)
  rw [Finset.sum_sub_distrib]
  dsimp [μ]
  linarith [hmean]

theorem squares_upper_tail (p : ι → Law α) (X : ι → α → ℝ)
    (B M η : ℝ) (hB : 0<B) (hM : 0<M) (he : 0<η) (he2 : η≤2)
    (hb : ∀ i x, 0<(p i).mass x → |X i x|≤B)
    (hcap : (∑ i, expect (p i) (fun x => (X i x)^2))≤M) :
    prob (product p) (fun x => (1+η)*M≤∑ i, (X i (x i))^2)≤
      Real.exp (-(η*M)^2/(4*B^2*M)) := by
  let μ := fun i => expect (p i) (fun x => (X i x)^2)
  let Y := fun i x => (X i x)^2-μ i
  have hc := fun i => squared_entry_bounds (p i) (X i) B (hb i)
  have h := upper_tail_small p Y (B^2) (fun i => B^2*μ i) (B^2*M) (η*M)
    (fun i => (hc i).1) (fun i => (hc i).2.1) (fun i => (hc i).2.2)
    (by rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hcap (sq_nonneg B))
    (mul_pos (sq_pos_of_pos hB) hM) (mul_pos he hM) (by
      nlinarith [mul_le_mul_of_nonneg_right he2 (show 0≤M*B^2 by positivity)])
  apply (prob_mono_support (product p) _ _ ?_).trans
    (by simpa only [mul_assoc] using h)
  intro x _ hx
  change η*M≤∑ i, ((X i (x i))^2-μ i)
  rw [Finset.sum_sub_distrib]
  dsimp [μ]
  linarith [hcap]

end
end Max2SAT.IndependentPairs
