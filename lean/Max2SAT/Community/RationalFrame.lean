import Max2SAT.Community.SpectralTruncation

/-! Rational data extracted from an approximate orthogonal diagonalization.
The numerical routine still has to produce Q with a small residual. These
lemmas verify the subsequent representation and its exact invariants. -/
namespace Max2SAT.Community
open scoped Matrix.Norms.L2Operator
variable {n r : ℕ}
set_option maxHeartbeats 1000000

def frameDiagonal (J Q : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) : ℚ :=
  (Q.transpose*J*Q) i i

def frameRepresentation (J Q : Matrix (Fin n) (Fin n) ℚ) (selected : Fin r ↪ Fin n) :
    Representation n r where
  coefficient k := frameDiagonal J Q (selected k)
  direction k i := Q i (selected k)
  trialSpacing := 1

noncomputable section

def realMatrix (Q : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (Q i j:ℝ)

theorem real_matrix_mul (Q R : Matrix (Fin n) (Fin n) ℚ) :
    realMatrix (Q*R)=realMatrix Q*realMatrix R := by
  ext i j
  simp [realMatrix,Matrix.mul_apply]

theorem real_matrix_transpose (Q : Matrix (Fin n) (Fin n) ℚ) :
    realMatrix Q.transpose=(realMatrix Q).transpose := rfl

theorem real_matrix_one : realMatrix (1 : Matrix (Fin n) (Fin n) ℚ)=1 := by
  ext i j
  by_cases h:i=j <;> simp [realMatrix,Matrix.one_apply,h]

def realOrthogonal (Q : Matrix (Fin n) (Fin n) ℚ) (hQ : Q.transpose*Q=1) :
    Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨realMatrix Q,Matrix.mem_unitaryGroup_iff'.mpr (by
    change (realMatrix Q).conjTranspose*realMatrix Q=1
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,←real_matrix_transpose,←real_matrix_mul,hQ]
    exact real_matrix_one)⟩

theorem frame_direction_unit (J Q : Matrix (Fin n) (Fin n) ℚ)
    (selected : Fin r ↪ Fin n) (hQ : Q.transpose*Q=1) (k : Fin r) :
    ∑ i, ((frameRepresentation J Q selected).direction k i:ℝ)^2=1 := by
  have h := congrArg (fun A => A (selected k) (selected k)) hQ
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq] at h
  have hc : ∑ i, (Q i (selected k):ℝ)*(Q i (selected k):ℝ)=1 := by exact_mod_cast h
  simpa only [frameRepresentation,pow_two] using hc

theorem frame_coefficient_rayleigh (J Q : Matrix (Fin n) (Fin n) ℚ)
    (selected : Fin r ↪ Fin n) (k : Fin r) :
    ((frameRepresentation J Q selected).coefficient k:ℝ)=
    ∑ i, ((frameRepresentation J Q selected).direction k i:ℝ)*
      (∑ j, realMatrix J i j*((frameRepresentation J Q selected).direction k j:ℝ)) := by
  simp only [frameRepresentation,frameDiagonal,Matrix.mul_apply,Matrix.transpose_apply,realMatrix]
  push_cast
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The selected rational rank-one terms are precisely the truncated
orthogonal diagonalization, not an independently chosen approximation. -/
theorem frame_matrix_eq (J Q : Matrix (Fin n) (Fin n) ℚ)
    (selected : Fin r ↪ Fin n) (hQ : Q.transpose*Q=1) :
    representationMatrix (frameRepresentation J Q selected)=
      Unitary.conjStarAlgAut ℝ _ (realOrthogonal Q hQ)
        (Matrix.diagonal (fun i => if i∈Finset.univ.map selected
          then (frameDiagonal J Q i:ℝ) else 0)) := by
  classical
  ext i j
  simp only [Unitary.conjStarAlgAut_apply,representationMatrix,frameRepresentation,
    realOrthogonal,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,star_trivial,
    Matrix.mul_apply,Matrix.diagonal_apply,realMatrix]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [ite_mul,zero_mul,Finset.sum_ite,Finset.sum_const_zero,add_zero]
  rw [show Finset.univ.filter (fun k => k∈Finset.univ.map selected)=Finset.univ.map selected by ext k; simp]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro k _
  ring

end
end Max2SAT.Community
