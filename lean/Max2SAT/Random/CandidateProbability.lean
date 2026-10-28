import Max2SAT.Random.SumFeasibility

/-! Convert the joint feasibility probability into an expected count and
a high-probability count on a fixed support. FixedSupportNodes connects these
counts to the initialized search when every indexed vertex is active.
ActiveCandidates and SupportAveraging complete the original-label transfer
and observed-support averaging; FullRuntime gives the resulting node bounds. -/
namespace Max2SAT.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α]

theorem nonnegative_markov (p : Law α) (X : α → ℝ) (hX : ∀ x, 0 ≤ X x)
    (s : ℝ) (hs : 0 < s) : prob p (fun x => s < X x) ≤ expect p X/s := by
  apply (le_div_iff₀ hs).2
  simp only [prob,expect,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : s < X x
  · simp only [ite_eq_left h]
    exact mul_le_mul_of_nonneg_left h.le (p.nonneg x)
  · simp only [ite_eq_right h,zero_mul]
    exact mul_nonneg (p.nonneg x) (hX x)

theorem fair_assignment_count (P : (Fin n → Bool) → Prop) :
    ((Finset.univ.filter P).card : ℝ) = (2:ℝ)^n * prob (fairBits (Fin n)) P := by
  unfold prob
  simp_rw [fairBits_mass]
  rw [← Finset.sum_filter]
  simp only [Fintype.card_fin,Finset.sum_const, nsmul_eq_mul]
  have he : (2:ℝ)^n*(1/2:ℝ)^n = 1 := by rw [← mul_pow]; norm_num
  nlinarith

end
end Max2SAT.FiniteLaw

namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

def candidateCount (E : Finset (Edge n)) (F : Formula n) (C : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter (fun x => comparisonSum E F C x ≤ 0)).card

theorem fixed_support_candidate_expectation (p : E → PairLaw m κ)
    (hm : 0 < m) (hk : 0 < κ) (units : List (Literal n))
    (C : Finset (Fin n)) (hC : 0 < C.card) (hd : ∀ i∈C, 0 < (incident E i).card)
    (hhalf : n ≤ 2*C.card) :
    expect (product (fun e => (p e).law))
      (fun K => (candidateCount E (generate E K units) C : ℝ)) ≤
      3*(2:ℝ)^n*Real.exp (-runtimeConstant m κ*n) := by
  have h := sum_feasibility_input_law p hm hk units C hC hd hhalf
  rw [prob_tensor] at h
  have he : expect (product (fun e => (p e).law))
      (fun K => (candidateCount E (generate E K units) C : ℝ)) =
      (2:ℝ)^n * expect (product (fun e => (p e).law))
        (fun K => prob (fairBits (Fin n)) (fun x => comparisonSum E (generate E K units) C x ≤ 0)) := by
    unfold candidateCount
    simp_rw [fair_assignment_count]
    simp only [expect,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro K _
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left h (pow_nonneg (by norm_num : (0:ℝ)≤2) n)
  nlinarith

theorem fixed_support_candidate_tail (p : E → PairLaw m κ)
    (hm : 0 < m) (hk : 0 < κ) (units : List (Literal n))
    (C : Finset (Fin n)) (hC : 0 < C.card) (hd : ∀ i∈C, 0 < (incident E i).card)
    (hhalf : n ≤ 2*C.card) :
    prob (product (fun e => (p e).law))
      (fun K => (2:ℝ)^n*Real.exp (-runtimeConstant m κ*n/2) <
        (candidateCount E (generate E K units) C : ℝ)) ≤
      3*Real.exp (-runtimeConstant m κ*n/2) := by
  have ht := nonnegative_markov (product (fun e => (p e).law))
    (fun K => (candidateCount E (generate E K units) C : ℝ))
    (fun _ => Nat.cast_nonneg _) ((2:ℝ)^n*Real.exp (-runtimeConstant m κ*n/2)) (by positivity)
  have he := fixed_support_candidate_expectation p hm hk units C hC hd hhalf
  apply ht.trans
  apply (div_le_div_of_nonneg_right he (by positivity)).trans_eq
  have hexp : Real.exp (-runtimeConstant m κ*n) =
      Real.exp (-runtimeConstant m κ*n/2)*Real.exp (-runtimeConstant m κ*n/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  field_simp

end
end Max2SAT.RandomInput
