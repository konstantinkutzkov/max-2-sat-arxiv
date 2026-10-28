import Max2SAT.Random.ProductTools
import Max2SAT.Random.EndpointSigns

/-! Exact first and second moments of independent signs. The variance
identity in the exposure lemma follows from these finite-sum proofs. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fair_sign_mean : expect fair sign = 0 := by norm_num [expect,fair,sign]

theorem fair_coordinate_mean (i : ι) : expect (fairBits ι) (fun z => sign (z i)) = 0 := by
  have h := congrArg (fun p => expect p sign) (push_product_apply (fun _ : ι => fair) i)
  rw [expect_push,fair_sign_mean] at h
  exact h

private theorem fair_two_signs :
    expect (fairBits Bool) (fun z => sign (z false) * sign (z true)) = 0 := by
  unfold expect
  rw [← (Equiv.boolArrowEquivProd Bool).symm.sum_comp]
  norm_num [fairBits_mass,Equiv.boolArrowEquivProd,sign,Fintype.sum_prod_type]

theorem fair_coordinate_product (i j : ι) :
    expect (fairBits ι) (fun z => sign (z i) * sign (z j)) = if i=j then 1 else 0 := by
  by_cases hij : i=j
  · subst j
    have he : (fun z : ι → Bool => sign (z i)*sign (z i)) = (fun _ => 1) := by
      funext z
      cases z i <;> norm_num [sign]
    rw [he,expect_const]
    simp
  · let f : Bool → ι := fun b => if b then j else i
    have hf : Function.Injective f := by
      intro a b h
      cases a <;> cases b <;> simp_all [f,Ne.symm hij]
    have hh := congrArg (fun p => expect p (fun z => sign (z false)*sign (z true)))
      (product_select (fun _ : ι => fair) f hf)
    rw [expect_push] at hh
    change expect (fairBits ι) (fun z => sign (z i)*sign (z j)) =
      expect (fairBits Bool) (fun z => sign (z false)*sign (z true)) at hh
    rw [hh,fair_two_signs]
    simp [hij]

theorem signed_sum_mean (a : ι → ℝ) :
    expect (fairBits ι) (fun z => ∑ i, sign (z i)*a i) = 0 := by
  rw [expect_sum]
  simp only [expect_mul_const,fair_coordinate_mean,zero_mul,Finset.sum_const_zero]

theorem signed_sum_second (a : ι → ℝ) :
    expect (fairBits ι) (fun z => (∑ i, sign (z i)*a i)^2) = ∑ i, (a i)^2 := by
  have he : ∀ z : ι → Bool, (∑ i, sign (z i)*a i)^2 =
      ∑ i, ∑ j, (sign (z i)*sign (z j))*(a i*a j) := by
    intro z
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he,expect_sum,expect_mul_const,fair_coordinate_product]
  simp [ite_mul,pow_two]

theorem signedCount_bound (left : Bool) (K : Pattern m) :
    |signedCount left K| ≤ size K := by
  unfold signedCount
  calc
    _ ≤ ∑ s, |(K s).val * sign (endpoint left s)| := Finset.abs_sum_le_sum_abs _ _
    _ = size K := by
      have hs : ∀ b, |sign b| = 1 := by intro b; cases b <;> norm_num [sign]
      simp only [abs_mul,hs,mul_one,size,Nat.cast_sum]
      simp

end
end Max2SAT.RandomInput
