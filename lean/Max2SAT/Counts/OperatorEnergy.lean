import Max2SAT.Counts.SequentialCompensation
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Bridge the matrix norm hypotheses in the paper to the explicit
squared-energy budgets used in the finite probability proofs. Norms here
are Euclidean operator norms, not entrywise or infinity norms. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
open scoped Matrix.Norms.L2Operator
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem matrix_squared_energy (N : Matrix κ ι ℝ) (z : ι → ℝ)
    (V : ℝ) (hN : ‖N‖^2≤V) :
    (∑ t, (∑ w, N t w*z w)^2)≤V*(∑ w, (z w)^2) := by
  let x : EuclideanSpace ℝ ι := (EuclideanSpace.equiv ι ℝ).symm z
  have h := Matrix.l2_opNorm_mulVec N x
  have hs := mul_self_le_mul_self (norm_nonneg _) h
  rw [←sq, ←sq, mul_pow, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq] at hs
  have he : (∑ t, (∑ w, N t w*z w)^2)≤‖N‖^2*(∑ w, (z w)^2) := hs
  exact he.trans (mul_le_mul_of_nonneg_right hN (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- Squared row-sum bound for the linear term inside a round. -/
theorem matrix_row_sum_energy (N : Matrix κ ι ℝ) (V : ℝ) (hN : ‖N‖^2≤V) :
    (∑ t, (∑ w, N t w)^2)≤Fintype.card ι*V := by
  simpa [mul_comm] using matrix_squared_energy N (fun _ => 1) V hN

/-- The Frobenius budget for the quadratic term, obtained by applying
the same operator bound to every coordinate vector. -/
theorem matrix_frobenius_energy (N : Matrix κ ι ℝ) (V : ℝ) (hN : ‖N‖^2≤V) :
    (∑ t, ∑ w, (N t w)^2)≤Fintype.card ι*V := by
  have hc : ∀ w : ι, (∑ t, (N t w)^2)≤V := by
    intro w
    have h := matrix_squared_energy N (fun i => if i=w then 1 else 0) V hN
    simpa using h
  rw [Finset.sum_comm]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hc w)
  simpa using h

/-- Pathwise energy for the signed rows in the common gap lemma. -/
theorem matrix_signed_energy (N : Matrix κ ι ℝ) (V : ℝ) (hN : ‖N‖^2≤V)
    (x : ι → Bool) :
    (∑ t, (∑ w, N t w*sign (x w))^2)≤Fintype.card ι*V := by
  have hs : ∀ w, (sign (x w))^2=(1:ℝ) := by
    intro w
    cases x w <;> norm_num [sign]
  have h := matrix_squared_energy N (fun w => sign (x w)) V hN
  simpa only [hs,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,mul_comm] using h

variable {n : ℕ}

/-- This is the rectangular matrix R from the sequential theorem: a row
for each prefix variable and a column for every original variable. -/
def sequentialMatrix (H : Fin n → Affine n) (P : Finset (Fin n)) : Matrix P (Fin n) ℝ :=
  fun t w => if t.val.val<w.val then (H t).coeff w else 0

theorem sequential_energy_of_norm (H : Fin n → Affine n) (P : Finset (Fin n))
    (V : ℝ) (hN : ‖sequentialMatrix H P‖^2≤V) : SequentialEnergy H P V := by
  intro z
  have hn : ‖(sequentialMatrix H P).transpose‖=‖sequentialMatrix H P‖ := by
    simpa using Matrix.l2_opNorm_conjTranspose (sequentialMatrix H P)
  have h := matrix_squared_energy (sequentialMatrix H P).transpose
    (fun t : P => z t) V (by rw [hn]; exact hN)
  simp only [Matrix.transpose_apply,sequentialMatrix,ite_mul,zero_mul] at h
  simp_rw [mul_comm (↑((H _).coeff _)) (z _)] at h
  simpa only [←Finset.sum_coe_sort P] using h

theorem sequential_compensation_norm_tail (H : Fin n → Affine n)
    (P : Finset (Fin n)) (hdiag : ∀ t, (H t).coeff t=0)
    (V b : ℝ) (hV : 0<V) (hb : 0<b) (hP : 0<P.card)
    (hN : ‖sequentialMatrix H P‖^2≤V) :
    prob (fairBits (Fin n)) (fun x =>
      (compensation H P (fun i => i.val) x : ℝ) < -b) ≤
        Real.exp (-2*b^2/(V*P.card)) :=
  sequential_compensation_tail H P hdiag V b hV hb hP
    (sequential_energy_of_norm H P V hN)

end
end Max2SAT.Counts
