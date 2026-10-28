import Max2SAT.Counts.CreatorTail
import Max2SAT.Counts.OperatorEnergy
import Max2SAT.Random.RequirementTail

/-! Combine the checked creator and sequential compensation bounds for
the actual summed budget. The common-gap probability remains an explicit
hypothesis until the convex concentration argument has been formalized. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw
open scoped Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem sequential_passing_probability (H : Fin n → Affine n)
    (P : Finset (Fin n)) (hP : 0<P.card) (hdiag : ∀ t, (H t).coeff t=0)
    (s : Fin n → ℚ) (hs : ∀ i∈P, 0≤s i)
    (M V a q : ℝ) (hM : 0<M) (hV : 0<V) (ha : 0<a)
    (hN : ‖sequentialMatrix H P‖^2≤V)
    (hslack : (∑ i∈P, (s i : ℝ))≤a)
    (hprofile : prob (fairBits (Fin n))
      (fun x => (∑ i∈P, clippedGap H (fun i => i.val) M i x)<6*a)≤q) :
    prob (fairBits (Fin n))
      (fun x => (comparisonBudget H s P (fun i => i.val) x).Holds x) ≤
        q+Real.exp (-2*a^2/(P.card*M^2))+Real.exp (-a^2/(2*V*P.card)) := by
  let E₁ : Assignment n → Prop := fun x =>
    (∑ i∈P, clippedGap H (fun i => i.val) M i x)<6*a
  let E₂ : Assignment n → Prop := fun x => clippedCreators H P (fun i => i.val) M x <
    (∑ i∈P, clippedGap H (fun i => i.val) M i x)/2-a
  let E₃ : Assignment n → Prop := fun x =>
    (compensation H P (fun i => i.val) x : ℝ)< -(a/2)
  have hsubset : ∀ x, (comparisonBudget H s P (fun i => i.val) x).Holds x →
      (E₁ x ∨ E₂ x) ∨ E₃ x := by
    intro x hx
    by_cases h₁ : E₁ x
    · exact Or.inl (Or.inl h₁)
    by_cases h₂ : E₂ x
    · exact Or.inl (Or.inr h₂)
    have hg := accumulated_gap_of_profile H P (fun i => i.val) s hs M a x
      (le_of_not_gt h₁) (le_of_not_gt h₂) hslack
    rw [comparisonBudget,Affine.budget_holds,comparison_sum_identity] at hx
    have hx' : (accumulatedGap H s P (fun i => i.val) x : ℝ)+
        (compensation H P (fun i => i.val) x : ℝ)≤0 := by exact_mod_cast hx
    apply Or.inr
    dsimp only [E₃]
    linarith
  have hp := prob_mono_support (fairBits (Fin n))
    (fun x => (comparisonBudget H s P (fun i => i.val) x).Holds x)
    (fun x => (E₁ x ∨ E₂ x) ∨ E₃ x) (fun x _ => hsubset x)
  have hu := prob_union_le (fairBits (Fin n)) (fun x => E₁ x ∨ E₂ x) E₃
  have hu' := prob_union_le (fairBits (Fin n)) E₁ E₂
  have hc := creator_gap_tail H P (fun i => i.val) (fun _ _ h => h) M a hM ha hP
  have hq := sequential_compensation_norm_tail H P hdiag V (a/2) hV
    (by positivity) hP hN
  have he : -2*(a/2)^2/(V*P.card) = -a^2/(2*V*P.card) := by ring
  rw [he] at hq
  change prob _ E₁≤q at hprofile
  change prob _ E₂≤_ at hc
  change prob _ E₃≤_ at hq
  linarith

end
end Max2SAT.Counts
