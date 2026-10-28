import Max2SAT.Counts.GapProfile
import Max2SAT.Counts.BitExposure

/-! Identify the signed-row representation in the common-gap proof with
the exact rational averages used by the implemented comparison rule. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
variable {n : ℕ}

theorem average_signed_form (A : Affine n) (S : Finset (Fin n)) (x : Assignment n) :
    A.average S x = A.constant+(∑ w, A.coeff w)/2+
      (∑ w, if w∈S then A.coeff w*direction (x w) else 0)/2 := by
  unfold Affine.average
  rw [Finset.sum_div,Finset.sum_div,add_assoc,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w∈S
  · simp only [ite_eq_left hw]
    have h := centered_bit (x w)
    rw [show bit (x w)=1/2+direction (x w)/2 by linarith]
    ring
  · simp [hw,div_eq_mul_inv]

def rowShift (A : Affine n) : ℝ := A.constant+(∑ w, (A.coeff w : ℝ))/2

def earlierRow (H : Fin n → Affine n) (round : Fin n → ℕ) (t w : Fin n) : ℝ :=
  if round w<round t then (H t).coeff w else 0

theorem average_real_signed_form (H : Fin n → Affine n) (round : Fin n → ℕ)
    (t : Fin n) (x : Assignment n) :
    ((H t).average (earlier round t) x : ℝ) =
      rowShift (H t)+(∑ w, sign (x w)*earlierRow H round t w)/2 := by
  rw [average_signed_form]
  push_cast
  unfold rowShift
  congr 2
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : round w<round t
  · simp only [earlier,Finset.mem_filter,Finset.mem_univ,true_and,hw,↓reduceIte,earlierRow]
    push_cast
    rw [direction_cast,mul_comm]
  · simp [earlier,earlierRow,hw]

theorem comparison_gap_mean (H : Fin n → Affine n) (round : Fin n → ℕ) (t : Fin n) :
    Real.sqrt ((∑ w, (earlierRow H round t w)^2)/3)/2 ≤
      expect (fairBits (Fin n)) (fun x => |((H t).average (earlier round t) x : ℝ)|) := by
  simp_rw [average_real_signed_form]
  exact row_gap_mean (earlierRow H round t) (rowShift (H t))

end
end Max2SAT.Counts
