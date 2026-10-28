import Max2SAT.Counts.RoundCompensation

/-! Decompose the compensation of the implemented rational comparison sum
into contributions from later rounds and from the creator's own round. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def roundBlock (round : Fin n → ℕ) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun t => round t=j)

def roundPrefix (round : Fin n → ℕ) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun t => round t<k)

theorem sum_round_blocks (round : Fin n → ℕ) (k : ℕ) (f : Fin n → ℝ) :
    (∑ j∈Finset.range k, ∑ t∈roundBlock round j, f t) =
      ∑ t∈roundPrefix round k, f t := by
  simp only [roundBlock,roundPrefix,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp

def laterIncoming (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (x : Assignment n) (w : Fin n) : ℝ :=
  ∑ t∈P, if round t<round w ∧ x t≠preference H round x t then
    sign (x t)*(H t).coeff w else 0

def laterCompensation (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (x : Assignment n) : ℝ :=
  ∑ w, (-laterIncoming H P round x w/2)*sign (x w)

def withinTotal (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (x : Assignment n) : ℝ :=
  ∑ t∈P, if x t≠preference H round x t then
    ∑ w, if round w=round t then -sign (x t)*(H t).coeff w*sign (x w)/2 else 0
    else 0

theorem compensation_round_split (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (x : Assignment n) :
    (compensation H P round x : ℝ)=
      laterCompensation H P round x+withinTotal H P round x := by
  unfold compensation laterCompensation laterIncoming withinTotal
  push_cast
  simp only [←Finset.sum_neg_distrib,Finset.sum_div,Finset.sum_mul]
  rw [Finset.sum_comm,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hc : x t≠preference H round x t
  · simp only [ite_eq_left hc]
    push_cast
    rw [direction_cast,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    rcases lt_trichotomy (round w) (round t) with hw|hw|hw
    · have htw : ¬round t<round w := by omega
      have he : ¬round w=round t := ne_of_lt hw
      simp [hw,htw,he]
    · simp only [hw,lt_self_iff_false,false_and,↓reduceIte,neg_zero,zero_div,zero_mul,zero_add]
      push_cast
      rw [direction_cast]
      ring
    · have hwt : ¬round w<round t := by omega
      have he : ¬round w=round t := Ne.symm (ne_of_lt hw)
      rw [ite_eq_right hwt,ite_eq_left ⟨hw,hc⟩,ite_eq_right he]
      push_cast
      rw [direction_cast]
      ring
  · simp [hc]

def blockInteractions (H : Fin n → Affine n) (round : Fin n → ℕ) (j : ℕ) :
    Matrix (roundBlock round j) (roundBlock round j) ℝ :=
  fun t w => (H t).coeff w

def withinRound (H : Fin n → Affine n) (round : Fin n → ℕ) (j : ℕ)
    (x : Assignment n) : ℝ :=
  roundCompensation (blockInteractions H round j)
    (fun t => preference H round x t) (fun t => x t)

theorem within_round_eq (H : Fin n → Affine n) (round : Fin n → ℕ)
    (j : ℕ) (x : Assignment n) :
    withinRound H round j x = withinTotal H (roundBlock round j) round x := by
  unfold withinRound roundCompensation blockInteractions withinTotal
  rw [Finset.mul_sum]
  dsimp only
  rw [Finset.sum_coe_sort (roundBlock round j)
    (fun t => -(1/2 : ℝ)*(if x t≠preference H round x t then
      ∑ w : roundBlock round j, sign (x t)*(H t).coeff w*sign (x w) else 0))]
  apply Finset.sum_congr rfl
  intro t ht
  have hr : round t=j := (Finset.mem_filter.mp ht).2
  by_cases hc : x t≠preference H round x t
  · simp only [ite_eq_left hc]
    rw [Finset.sum_coe_sort (roundBlock round j)
      (fun w => sign (x t)*(H t).coeff w*sign (x w)),Finset.mul_sum]
    rw [roundBlock,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : round w=j
    · simp only [hw,hr,↓reduceIte]
      ring
    · simp [hw,hr]
  · simp [hc]

theorem within_total_eq_sum (H : Fin n → Affine n) (round : Fin n → ℕ)
    (k : ℕ) (x : Assignment n) :
    withinTotal H (roundPrefix round k) round x =
      ∑ j∈Finset.range k, withinRound H round j x := by
  simp_rw [within_round_eq]
  exact (sum_round_blocks round k _).symm

theorem compensation_all_rounds (H : Fin n → Affine n) (round : Fin n → ℕ)
    (k : ℕ) (x : Assignment n) :
    (compensation H (roundPrefix round k) round x : ℝ) =
      laterCompensation H (roundPrefix round k) round x+
        ∑ j∈Finset.range k, withinRound H round j x := by
  rw [compensation_round_split,within_total_eq_sum]

end
end Max2SAT.Counts
