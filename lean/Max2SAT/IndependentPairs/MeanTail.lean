import Max2SAT.IndependentPairs.Squares
import Max2SAT.IndependentPairs.Centering

/-! The empirical common interaction is itself concentrated. The proof
uses the original independent inputs, before empirical centering. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open FiniteLaw
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem empirical_mean_tail (p : ι → Law α) (X : ι → α → ℝ)
    (B v a : ℝ) (hv : 0<v) (ha : 0<a)
    (hm : ∀ i, expect (p i) (X i)=0)
    (hb : ∀ i x, 0<(p i).mass x → |X i x|≤B)
    (hsq : ∀ i, expect (p i) (fun x => (X i x)^2)≤v)
    (hsmall : a*B≤2*v) :
    prob (product p) (fun x => a≤|empiricalMean (fun i => X i (x i))|)≤
      2*Real.exp (-(Fintype.card ι:ℝ)*a^2/(4*v)) := by
  have hc : (0:ℝ)<Fintype.card ι := by exact_mod_cast (Fintype.card_pos (α:=ι))
  have h := two_sided_small p X B (fun _ => v) ((Fintype.card ι:ℝ)*v)
    ((Fintype.card ι:ℝ)*a) hm hb hsq (by simp) (mul_pos hc hv) (mul_pos hc ha) (by
      nlinarith [mul_le_mul_of_nonneg_left hsmall hc.le])
  have he : (fun x => a≤|empiricalMean (fun i => X i (x i))|)=
      (fun x : ι → α => (Fintype.card ι:ℝ)*a≤|∑ i, X i (x i)|) := by
    funext x; apply propext
    simp only [empiricalMean,abs_div,abs_of_pos hc,le_div_iff₀ hc]
    rw [mul_comm a]
  rw [he]
  convert h using 2
  congr 1
  field_simp

/-- Fixed shifts of the original entries reduce empirical estimation error
to the mean of the centered independent variables. -/
theorem empirical_shift_tail (p : ι → Law α) (J : ι → α → ℝ)
    (μ B v a : ℝ) (hv : 0<v) (ha : 0<a)
    (hm : ∀ i, expect (p i) (J i)=μ)
    (hb : ∀ i x, 0<(p i).mass x → |J i x-μ|≤B)
    (hsq : ∀ i, expect (p i) (fun x => (J i x-μ)^2)≤v)
    (hsmall : a*B≤2*v) :
    prob (product p) (fun x => a≤|empiricalMean (fun i => J i (x i))-μ|)≤
      2*Real.exp (-(Fintype.card ι:ℝ)*a^2/(4*v)) := by
  have h := empirical_mean_tail p (fun i x => J i x-μ) B v a hv ha
    (by intro i; simp [expect_sub,hm i]) hb hsq hsmall
  simpa only [empirical_mean_shift] using h

end
end Max2SAT.IndependentPairs
