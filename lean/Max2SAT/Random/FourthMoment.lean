import Max2SAT.Random.SignMoments

/-! The fourth-moment calculation in Lemma `lem:random_moments`.
The induction averages the two values of one fresh sign; it does not
assume independence of the accumulated pruning constraints. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

private def flipCoordinate (i : ι) :=
  multiplyBits (fun j => if j = i then false else true)

omit [Fintype ι] in
private theorem flipCoordinate_apply (i j : ι) (z : ι → Bool) :
    flipCoordinate i z j = if j = i then !(z j) else z j := by
  by_cases h : j = i <;> simp [flipCoordinate, multiplyBits, h]

private theorem expect_flipCoordinate (i : ι) (f : (ι → Bool) → ℝ) :
    expect (fairBits ι) (fun z => f (flipCoordinate i z)) = expect (fairBits ι) f := by
  rw [← expect_push]
  exact congrArg (fun p => expect p f) (fairBits_multiply _)

theorem signed_subsum_second (a : ι → ℝ) (s : Finset ι) :
    expect (fairBits ι) (fun z => (∑ i ∈ s, sign (z i) * a i)^2) =
      ∑ i ∈ s, (a i)^2 := by
  have he : ∀ z : ι → Bool, (∑ i ∈ s, sign (z i) * a i)^2 =
      ∑ i ∈ s, ∑ j ∈ s, (sign (z i) * sign (z j)) * (a i * a j) := by
    intro z
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he, expect_sum, expect_mul_const, fair_coordinate_product]
  simp [ite_mul, pow_two]

theorem signed_subsum_fourth (a : ι → ℝ) (s : Finset ι) :
    expect (fairBits ι) (fun z => (∑ i ∈ s, sign (z i) * a i)^4) =
      3 * (∑ i ∈ s, (a i)^2)^2 - 2 * ∑ i ∈ s, (a i)^4 := by
  induction s using Finset.induction_on with
  | empty => simp [expect_const]
  | @insert i s hi ih =>
    let S : (ι → Bool) → ℝ := fun z => ∑ j ∈ s, sign (z j) * a j
    have hs : ∀ z, S (flipCoordinate i z) = S z := by
      intro z
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := by intro h; subst j; exact hi hj
      rw [flipCoordinate_apply, ite_eq_right hji]
    have hf := expect_flipCoordinate i (fun z => (sign (z i) * a i + S z)^4)
    have hpoint : ∀ z : ι → Bool,
        (sign (z i) * a i + S z)^4 +
          (sign (flipCoordinate i z i) * a i + S (flipCoordinate i z))^4 =
        2 * ((S z)^4 + (S z)^2 * (6 * (a i)^2) + (a i)^4) := by
      intro z
      rw [hs, flipCoordinate_apply, ite_eq_left rfl, sign_not]
      cases z i <;> norm_num [sign] <;> ring
    have havg := congrArg (expect (fairBits ι)) (funext hpoint)
    rw [expect_add, hf] at havg
    have hright : expect (fairBits ι)
        (fun z => 2 * ((S z)^4 + (S z)^2 * (6 * (a i)^2) + (a i)^4)) =
        2 * (expect (fairBits ι) (fun z => (S z)^4) +
          (∑ j ∈ s, (a j)^2) * (6 * (a i)^2) + (a i)^4) := by
      simp_rw [mul_comm (2 : ℝ)]
      rw [expect_mul_const, expect_add, expect_add, expect_mul_const, expect_const]
      rw [show expect (fairBits ι) (fun z => (S z)^2) =
        ∑ j ∈ s, (a j)^2 from signed_subsum_second a s]
    rw [hright] at havg
    change expect (fairBits ι) (fun z => (S z)^4) = _ at ih
    rw [ih] at havg
    simp only [Finset.sum_insert hi]
    change expect (fairBits ι) (fun z => (sign (z i) * a i + S z)^4) = _
    nlinarith [havg]

theorem signed_sum_fourth (a : ι → ℝ) :
    expect (fairBits ι) (fun z => (∑ i, sign (z i) * a i)^4) =
      3 * (∑ i, (a i)^2)^2 - 2 * ∑ i, (a i)^4 :=
  signed_subsum_fourth a Finset.univ

theorem signed_sum_fourth_le (a : ι → ℝ) :
    expect (fairBits ι) (fun z => (∑ i, sign (z i) * a i)^4) ≤
      3 * (∑ i, (a i)^2)^2 := by
  rw [signed_sum_fourth]
  have h : 0 ≤ ∑ i, (a i)^4 := Finset.sum_nonneg (fun i _ => by positivity)
  linarith

end
end Max2SAT.RandomInput
