import Max2SAT.Community.JacobiStep

/-! A finite recursive rational diagonalization routine. The deliberately
loose additive fuel bound suffices for polynomial preprocessing. -/
namespace Max2SAT.Community
variable {n : ℕ}
set_option maxHeartbeats 1000000

def iterateFrame (D : ℕ) (ε : ℚ) : ℕ → Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ
  | 0, _ => 1
  | fuel+1, A =>
    if offEnergy A≤ε then 1
    else stepRotation D A*iterateFrame D ε fuel (jacobiUpdate D A)

theorem orthogonal_product (R P : Matrix (Fin n) (Fin n) ℚ)
    (hR : R.transpose*R=1) (hP : P.transpose*P=1) :
    (R*P).transpose*(R*P)=1 := by
  calc
    _ = P.transpose*(R.transpose*R)*P := by simp [Matrix.transpose_mul,Matrix.mul_assoc]
    _ = _ := by rw [hR]; simpa using hP

theorem conjugate_product (A R P : Matrix (Fin n) (Fin n) ℚ) :
    (R*P).transpose*A*(R*P)=P.transpose*(R.transpose*A*R)*P := by
  simp [Matrix.transpose_mul,Matrix.mul_assoc]

theorem iterate_frame_orthogonal (D : ℕ) (ε : ℚ) (fuel : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    (iterateFrame D ε fuel A).transpose*iterateFrame D ε fuel A=1 := by
  induction fuel generalizing A with
  | zero => simp [iterateFrame]
  | succ fuel ih =>
    unfold iterateFrame
    split
    · simp
    · exact orthogonal_product _ _ (step_rotation_orthogonal D A) (ih _)

/-- Exact finite termination certificate: fuel*delta bounds the initial
energy, and each active step removes at least delta. -/
theorem iterate_frame_residual (D : ℕ) (ε δ M : ℚ) (fuel : ℕ)
    (hD : 0<D) (hn : 0<n) (hM : 0≤M) (hε : 0≤ε)
    (hδ : (n:ℚ)^2*δ≤ε) (hgrid : 2*(n:ℚ)^2*(16*M/D)^2≤ε)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.IsSymm) (hsize : squareSum A≤M^2)
    (hstart : offEnergy A≤(fuel:ℚ)*δ) :
    offEnergy ((iterateFrame D ε fuel A).transpose*A*iterateFrame D ε fuel A)≤ε := by
  induction fuel generalizing A with
  | zero =>
    simp only [Nat.cast_zero,zero_mul] at hstart
    simpa [iterateFrame] using hstart.trans hε
  | succ fuel ih =>
    by_cases hstop : offEnergy A≤ε
    · simp [iterateFrame,hstop]
    · have hprog := jacobi_progress D A M ε δ hD hn hM hA hsize hε hδ hgrid (lt_of_not_ge hstop)
      have hnext : offEnergy (jacobiUpdate D A)≤(fuel:ℚ)*δ := by
        push_cast at hstart
        linarith
      have h := ih (jacobiUpdate D A) (jacobi_symmetric D A hA)
        (by rw [jacobi_square_sum]; exact hsize) hnext
      simpa only [iterateFrame,ite_eq_right hstop,conjugate_product,jacobiUpdate] using h

end Max2SAT.Community
