import Max2SAT.Counts.BitExposure
import Max2SAT.Random.ConcentrationTools

/-! The quadratic-plus-linear expansion of compensation within one round.
The expansion and linear tail are verified; Hanson--Wright is not postulated. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def changedSign (p x : Bool) : ℝ := -sign p*sign x

def conjugated (N : ι → ι → ℝ) (p : ι → Bool) (t w : ι) : ℝ :=
  sign (p t)*sign (p w)*N t w

def roundCompensation (N : ι → ι → ℝ) (p x : ι → Bool) : ℝ :=
  -(1/2 : ℝ)*(∑ t, if x t≠p t then ∑ w, sign (x t)*N t w*sign (x w) else 0)

theorem changed_sign_creator (p x : Bool) : changedSign p x=1 ↔ x≠p := by
  cases p <;> cases x <;> norm_num [changedSign,sign]

omit [Fintype ι] [DecidableEq ι] in
theorem conjugated_symmetric (N : ι → ι → ℝ) (p : ι → Bool)
    (hN : ∀ t w, N t w=N w t) :
    ∀ t w, conjugated N p t w=conjugated N p w t := by
  intro t w
  unfold conjugated
  rw [hN t w]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem conjugated_diagonal (N : ι → ι → ℝ) (p : ι → Bool)
    (hN : ∀ t, N t t=0) : ∀ t, conjugated N p t t=0 := by
  intro t
  simp [conjugated,hN]

/-- The Boolean identity behind the factor 1/4 in both terms. -/
theorem round_pair_expansion (pt pw xt xw : Bool) (a : ℝ) :
    -(1/2 : ℝ)*(if xt≠pt then sign xt*a*sign xw else 0) =
      -(1/4 : ℝ)*(changedSign pt xt*(sign pt*sign pw*a)*changedSign pw xw)
      -(1/4 : ℝ)*((sign pt*sign pw*a)*changedSign pw xw) := by
  cases pt <;> cases pw <;> cases xt <;> cases xw <;>
    norm_num [changedSign,sign] <;> ring

omit [DecidableEq ι] in
/-- For a symmetric interaction matrix, this is exactly
Q_j = -beta^T M beta/4 - <M 1,beta>/4 from the paper. -/
theorem round_compensation_expansion (N : ι → ι → ℝ) (p x : ι → Bool)
    (hN : ∀ t w, N t w=N w t) :
    roundCompensation N p x =
      -(1/4 : ℝ)*(∑ t, ∑ w, changedSign (p t) (x t)*
        conjugated N p t w*changedSign (p w) (x w))
      -(1/4 : ℝ)*(∑ t, (∑ w, conjugated N p t w)*changedSign (p t) (x t)) := by
  have he : ∀ t, (if x t≠p t then ∑ w, sign (x t)*N t w*sign (x w) else 0) =
      ∑ w, if x t≠p t then sign (x t)*N t w*sign (x w) else 0 := by
    intro t
    by_cases ht : x t≠p t <;> simp [ht]
  have hp : ∀ t w, -(1/2 : ℝ)*(if x t≠p t then sign (x t)*N t w*sign (x w) else 0) =
      -(1/4 : ℝ)*(changedSign (p t) (x t)*conjugated N p t w*changedSign (p w) (x w))
      -(1/4 : ℝ)*(conjugated N p t w*changedSign (p w) (x w)) := by
    intro t w
    exact round_pair_expansion (p t) (p w) (x t) (x w) (N t w)
  unfold roundCompensation
  simp_rw [he,Finset.mul_sum,hp,Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [conjugated_symmetric N p hN w t]


/-- Conditional on earlier rounds the preference mask is fixed; this
identity proves that the resulting beta signs are jointly independent
and fair, rather than merely pairwise independent. -/
theorem changed_sign_law (p : ι → Bool) :
    push (fairBits ι) (fun x i => decide (changedSign (p i) (x i)=1))=fairBits ι := by
  have he : (fun x i => decide (changedSign (p i) (x i)=1)) =
      multiplyBits (fun i => !(p i)) := by
    funext x i
    cases hp : p i <;> cases hx : x i <;> norm_num [changedSign,sign,multiplyBits,hp,hx]
  rw [he]
  exact fairBits_multiply _

theorem changed_sign_value (p x : Bool) :
    sign (decide (changedSign p x=1))=changedSign p x := by
  cases p <;> cases x <;> norm_num [changedSign,sign]

/-- Linear compensation for a fixed mask. The squared coefficient sum
is explicit, ready for the deterministic block norm bound. -/
theorem signed_linear_tail (a : ι → ℝ) (B e : ℝ) (hB : 0<B) (he : 0<e)
    (henergy : (∑ i, (a i)^2)≤B) :
    prob (fairBits ι) (fun x => -(1/4 : ℝ)*(∑ i, a i*sign (x i)) < -e) ≤
      Real.exp (-8*e^2/B) := by
  have h := lower_tail_of_mgf (fairBits ι)
    (fun x => -(1/4 : ℝ)*(∑ i, a i*sign (x i))) (B/4) e
    (by positivity) he (by
      intro t
      have hm := signed_sum_mgf a (t/4)
      have hexp : (t/4)^2*(∑ i, (a i)^2)/2≤t^2*(B/4)/8 := by
        have hb := mul_le_mul_of_nonneg_left henergy (sq_nonneg t)
        nlinarith
      have heq : ∀ x : ι → Bool, -t*(-(1/4 : ℝ)*(∑ i, a i*sign (x i)))=
          (t/4)*(∑ i, a i*sign (x i)) := by intro x; ring
      simp_rw [heq]
      exact hm.trans (Real.exp_le_exp.mpr hexp))
  have heq : -2*e^2/(B/4) = -8*e^2/B := by ring
  rwa [heq] at h

/-- The linear tail after the preference-dependent sign change, with
the mask held fixed as it is when conditioning on earlier rounds. -/
theorem round_linear_tail (a : ι → ℝ) (p : ι → Bool)
    (B e : ℝ) (hB : 0<B) (he : 0<e) (henergy : (∑ i, (a i)^2)≤B) :
    prob (fairBits ι) (fun x =>
      -(1/4 : ℝ)*(∑ i, a i*changedSign (p i) (x i)) < -e) ≤
      Real.exp (-8*e^2/B) := by
  let f : (ι → Bool) → (ι → Bool) := fun x i => decide (changedSign (p i) (x i)=1)
  have hlaw : push (fairBits ι) f=fairBits ι := changed_sign_law p
  have hp := congrArg (fun q => prob q
    (fun x => -(1/4 : ℝ)*(∑ i, a i*sign (x i)) < -e)) hlaw
  rw [prob_push] at hp
  simp only [f,changed_sign_value] at hp
  rw [hp]
  exact signed_linear_tail a B e hB he henergy

end
end Max2SAT.Counts
