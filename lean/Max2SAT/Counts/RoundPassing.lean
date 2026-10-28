import Max2SAT.Counts.WithinRounds
import Max2SAT.Counts.CreatorTail

/-! Fixed-round passing probability for the implemented summed constraint.
The two unfinished concentration inputs are explicit: the common profile
probability and a uniform zero-diagonal quadratic-tail estimate. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw
open scoped Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem finite_union_bound {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (p : Law Ω) (S : Finset ι) (E : ι → Ω → Prop) :
    prob p (fun x => ∃ j∈S, E j x)≤∑ j∈S, prob p (E j) := by
  induction S using Finset.induction_on with
  | empty => simp [prob]
  | @insert j S hj ih =>
    simp only [Finset.mem_insert,exists_eq_or_imp,Finset.sum_insert hj]
    exact (prob_union_le p (E j) (fun x => ∃ i∈S, E i x)).trans (add_le_add le_rfl ih)

theorem within_sum_tail (H : Fin n → Affine n) (round : Fin n → ℕ)
    (k : ℕ) (e q : ℝ)
    (htail : ∀ j<k,
      prob (fairBits (Fin n)) (fun x => withinRound H round j x < -2*e)≤q) :
    prob (fairBits (Fin n))
      (fun x => (∑ j∈Finset.range k, withinRound H round j x)< -2*k*e)≤k*q := by
  have hsub := prob_mono_support (fairBits (Fin n))
    (fun x => (∑ j∈Finset.range k, withinRound H round j x)< -2*k*e)
    (fun x => ∃ j∈Finset.range k, withinRound H round j x < -2*e) (by
      intro x _ hx
      by_contra hn
      have h : ∀ j∈Finset.range k, -2*e≤withinRound H round j x := by
        intro j hj
        exact le_of_not_gt (fun h => hn ⟨j,hj,h⟩)
      have hs := Finset.sum_le_sum h
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
      nlinarith)
  apply hsub.trans ((finite_union_bound _ _ _).trans ?_)
  calc
    _ ≤ ∑ _j∈Finset.range k, q := Finset.sum_le_sum
      (fun j hj => htail j (Finset.mem_range.mp hj))
    _ = _ := by simp

theorem block_card_le_prefix (round : Fin n → ℕ) (j k : ℕ) (hj : j<k) :
    (roundBlock round j).card≤(roundPrefix round k).card := by
  apply Finset.card_le_card
  intro t ht
  have he := (Finset.mem_filter.mp ht).2
  simp only [roundPrefix,Finset.mem_filter,Finset.mem_univ,true_and]
  exact he ▸ hj

/-- The complete exceptional-event assembly for fixed rounds. With
a=g*n*sqrt(D_N)/8, the later threshold is a/4 and each within-round
threshold is a/(8*k), exactly as in the paper. -/
theorem round_passing_probability (H : Fin n → Affine n) (round : Fin n → ℕ)
    (k : ℕ) (hk : 0<k) (horder : OrderedRounds round) (hround : ∀ t, round t≤k)
    (hP : 0<(roundPrefix round k).card)
    (hsym : ∀ t w, (H t).coeff w=(H w).coeff t) (hdiag : ∀ t, (H t).coeff t=0)
    (s : Fin n → ℚ) (hs : ∀ t∈roundPrefix round k, 0≤s t)
    (M V a qProfile qQuad : ℝ) (hM : 0<M) (hV : 0<V) (ha : 0<a)
    (hN : ‖interactionMatrix H‖^2≤V)
    (hslack : (∑ t∈roundPrefix round k, (s t : ℝ))≤a)
    (hprofile : prob (fairBits (Fin n))
      (fun x => (∑ t∈roundPrefix round k, clippedGap H round M t x)<6*a)≤qProfile)
    (hquad : ∀ j<k, ∀ N : Matrix (roundBlock round j) (roundBlock round j) ℝ,
      (∀ t w, N t w=N w t) → (∀ t, N t t=0) → ‖N‖^2≤V →
      prob (fairBits (roundBlock round j))
        (fun z => quadraticTerm N z < -(a/(8*k)))≤qQuad) :
    prob (fairBits (Fin n))
      (fun x => (comparisonBudget H s (roundPrefix round k) round x).Holds x) ≤
      qProfile+Real.exp (-2*a^2/((roundPrefix round k).card*M^2))+
      Real.exp (-2*(a/4)^2/(k*V*(roundPrefix round k).card))+
      k*(Real.exp (-8*(a/(8*k))^2/(V*(roundPrefix round k).card))+qQuad) := by
  let P := roundPrefix round k
  let e : ℝ := a/(8*k)
  let B : ℝ := V*P.card
  have hB : 0<B := by dsimp [B]; positivity
  have he : 0<e := by dsimp [e]; positivity
  have hwithin : prob (fairBits (Fin n))
      (fun x => (∑ j∈Finset.range k, withinRound H round j x)< -2*k*e) ≤
        k*(Real.exp (-8*e^2/B)+qQuad) := by
    apply within_sum_tail
    intro j hj
    apply within_round_tail H round j hsym e
    · apply within_linear_tail H round j V B e hV.le hB he hN
      have hcard : ((roundBlock round j).card : ℝ)≤P.card := by
        exact_mod_cast block_card_le_prefix round j k hj
      simpa only [B,mul_comm] using mul_le_mul_of_nonneg_left hcard hV.le
    · exact within_quadratic_tail H round j hsym hdiag V e qQuad hV.le hN (hquad j hj)
  have hcreator := creator_gap_tail H P round horder M a hM ha hP
  have hlater := later_compensation_tail H P round horder k hk hround hP V (a/4) hV
    (by positivity) hN
  let E₁ : Assignment n → Prop := fun x => (∑ t∈P, clippedGap H round M t x)<6*a
  let E₂ : Assignment n → Prop := fun x => clippedCreators H P round M x <
    (∑ t∈P, clippedGap H round M t x)/2-a
  let E₃ : Assignment n → Prop := fun x => laterCompensation H P round x < -(a/4)
  let E₄ : Assignment n → Prop := fun x =>
    (∑ j∈Finset.range k, withinRound H round j x)< -2*k*e
  have hke : 2*k*e=a/4 := by
    dsimp [e]
    have hn : (k:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hk)
    field_simp
    ring
  have hsub := prob_mono_support (fairBits (Fin n))
    (fun x => (comparisonBudget H s P round x).Holds x)
    (fun x => ((E₁ x ∨ E₂ x) ∨ E₃ x) ∨ E₄ x) (by
      intro x _ hx
      by_cases h₁ : E₁ x
      · exact Or.inl (Or.inl (Or.inl h₁))
      by_cases h₂ : E₂ x
      · exact Or.inl (Or.inl (Or.inr h₂))
      by_cases h₃ : E₃ x
      · exact Or.inl (Or.inr h₃)
      by_cases h₄ : E₄ x
      · exact Or.inr h₄
      have hg := accumulated_gap_of_profile H P round s hs M a x
        (le_of_not_gt h₁) (le_of_not_gt h₂) hslack
      have hl := le_of_not_gt h₃
      have hw := le_of_not_gt h₄
      change -(a/4)≤laterCompensation H P round x at hl
      change -2*k*e≤(∑ j∈Finset.range k, withinRound H round j x) at hw
      have heq : -2*k*e= -(a/4) := by linarith [hke]
      rw [heq] at hw
      rw [comparisonBudget,Affine.budget_holds,comparison_sum_identity] at hx
      have hx' : (accumulatedGap H s P round x : ℝ)+(compensation H P round x : ℝ)≤0 := by
        exact_mod_cast hx
      change (accumulatedGap H s P round x : ℝ)+
        (compensation H (roundPrefix round k) round x : ℝ)≤0 at hx'
      rw [compensation_all_rounds] at hx'
      dsimp only [P] at hg hl
      exfalso
      linarith)
  have h12 := prob_union_le (fairBits (Fin n)) E₁ E₂
  have h123 := prob_union_le (fairBits (Fin n)) (fun x => E₁ x ∨ E₂ x) E₃
  have h1234 := prob_union_le (fairBits (Fin n)) (fun x => (E₁ x ∨ E₂ x) ∨ E₃ x) E₄
  change prob _ E₁≤qProfile at hprofile
  change prob _ E₂≤_ at hcreator
  change prob _ E₃≤_ at hlater
  change prob _ E₄≤_ at hwithin
  dsimp only [P,e,B] at hcreator hlater hwithin
  linarith

end
end Max2SAT.Counts
