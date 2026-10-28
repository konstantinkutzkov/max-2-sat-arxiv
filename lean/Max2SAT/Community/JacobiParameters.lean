import Max2SAT.Community.JacobiIteration

/-! Concrete polynomial grid and iteration bounds, computed from the input
matrix using rational arithmetic and an integer ceiling. -/
namespace Max2SAT.Community
variable {n : ℕ}
set_option maxHeartbeats 1000000

def diagonalizationScale (A : Matrix (Fin n) (Fin n) ℚ) : ℕ := Nat.ceil (squareSum A)+1
def diagonalizationGrid (n M : ℕ) : ℕ := 32*n^5*M
def diagonalizationFuel (n M : ℕ) : ℕ := M*n^10
def diagonalizationAccuracy (n : ℕ) : ℚ := 1/(n:ℚ)^8
def diagonalizationDecrease (n : ℕ) : ℚ := 1/(n:ℚ)^10

def computedFrame (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  if n=0 then 1 else
    iterateFrame (diagonalizationGrid n (diagonalizationScale A)) (diagonalizationAccuracy n)
      (diagonalizationFuel n (diagonalizationScale A)) A

theorem scale_positive (A : Matrix (Fin n) (Fin n) ℚ) : 0<diagonalizationScale A := by
  unfold diagonalizationScale
  omega

theorem square_sum_le_scale (A : Matrix (Fin n) (Fin n) ℚ) :
    squareSum A≤(diagonalizationScale A:ℚ) := by
  have h := Nat.le_ceil (squareSum A)
  unfold diagonalizationScale
  push_cast
  linarith

theorem square_sum_le_scale_square (A : Matrix (Fin n) (Fin n) ℚ) :
    squareSum A≤(diagonalizationScale A:ℚ)^2 := by
  have h := square_sum_le_scale A
  have hm : (1:ℚ)≤diagonalizationScale A := by exact_mod_cast scale_positive A
  nlinarith

theorem diagonalization_parameter_bounds (n M : ℕ) (hn : 0<n) (hM : 0<M) :
    0<diagonalizationGrid n M ∧ 0≤diagonalizationAccuracy n ∧
    (n:ℚ)^2*diagonalizationDecrease n≤diagonalizationAccuracy n ∧
    2*(n:ℚ)^2*(16*(M:ℚ)/diagonalizationGrid n M)^2≤diagonalizationAccuracy n ∧
    (M:ℚ)=(diagonalizationFuel n M:ℚ)*diagonalizationDecrease n := by
  have hnq : (0:ℚ)<n := by exact_mod_cast hn
  have hMq : (0:ℚ)<M := by exact_mod_cast hM
  have hn0 : (n:ℚ)≠0 := ne_of_gt hnq
  have hM0 : (M:ℚ)≠0 := ne_of_gt hMq
  refine ⟨by unfold diagonalizationGrid; positivity,by unfold diagonalizationAccuracy; positivity,?_,?_,?_⟩
  · have he : (n:ℚ)^2*diagonalizationDecrease n=diagonalizationAccuracy n := by
      unfold diagonalizationDecrease diagonalizationAccuracy
      field_simp
    exact he.le
  · have he : 16*(M:ℚ)/(diagonalizationGrid n M:ℚ)=1/(2*(n:ℚ)^5) := by
      unfold diagonalizationGrid
      push_cast
      field_simp
      ring
    rw [he]
    have he' : 2*(n:ℚ)^2*(1/(2*(n:ℚ)^5))^2=diagonalizationAccuracy n/2 := by
      unfold diagonalizationAccuracy
      field_simp
    rw [he']
    unfold diagonalizationAccuracy
    have hp : (0:ℚ)≤1/(n:ℚ)^8 := by positivity
    linarith
  · unfold diagonalizationFuel diagonalizationDecrease
    push_cast
    field_simp

theorem computed_frame_orthogonal (A : Matrix (Fin n) (Fin n) ℚ) :
    (computedFrame A).transpose*computedFrame A=1 := by
  unfold computedFrame
  split
  · simp
  · exact iterate_frame_orthogonal _ _ _ _

/-- The total executable routine reaches the requested off-diagonal energy. -/
theorem computed_frame_energy (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.IsSymm) :
    offEnergy ((computedFrame A).transpose*A*computedFrame A)≤diagonalizationAccuracy n := by
  by_cases hn:n=0
  · subst n
    simp [offEnergy,squareSum,diagonalSquareSum,diagonalizationAccuracy]
  · have hp := diagonalization_parameter_bounds n (diagonalizationScale A) (by omega) (scale_positive A)
    unfold computedFrame
    rw [ite_eq_right hn]
    apply iterate_frame_residual _ _ (diagonalizationDecrease n) (diagonalizationScale A)
      _ hp.1 (by omega) (by positivity) hp.2.1 hp.2.2.1 hp.2.2.2.1 A hA (square_sum_le_scale_square A)
    rw [←hp.2.2.2.2]
    exact (off_energy_le_square_sum A).trans (square_sum_le_scale A)

end Max2SAT.Community
