import Max2SAT.Community.RotationScalar

/-! Explicit rational plane matrices. Their multiplication formulas are
also used to identify the scalar pivot calculation with the matrix update. -/
namespace Max2SAT.Community
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : ℕ}
set_option maxHeartbeats 800000

def plane (i j : Fin n) (c s : K) : Matrix (Fin n) (Fin n) K := fun p q =>
  if q=i then (if p=i then c else 0)+(if p=j then s else 0)
  else if q=j then (if p=i then -s else 0)+(if p=j then c else 0)
  else if p=q then 1 else 0

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem mul_plane (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) (_hij : i≠j)
    (c s : K) (p q : Fin n) :
    (A*plane i j c s) p q=
      if q=i then c*A p i+s*A p j
      else if q=j then -s*A p i+c*A p j else A p q := by
  by_cases hqi:q=i
  · subst q
    simp [plane,Matrix.mul_apply,mul_add,mul_ite,Finset.sum_add_distrib,mul_comm]
  · by_cases hqj:q=j
    · subst q
      simp [plane,Matrix.mul_apply,hqi,mul_add,mul_ite,Finset.sum_add_distrib,mul_comm]
    · simp [plane,Matrix.mul_apply,hqi,hqj,mul_ite]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem transpose_plane_mul (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) (_hij : i≠j)
    (c s : K) (p q : Fin n) :
    ((plane i j c s).transpose*A) p q=
      if p=i then c*A i q+s*A j q
      else if p=j then -s*A i q+c*A j q else A p q := by
  by_cases hpi:p=i
  · subst p
    simp [plane,Matrix.mul_apply,Matrix.transpose_apply,add_mul,ite_mul,Finset.sum_add_distrib]
  · by_cases hpj:p=j
    · subst p
      simp [plane,Matrix.mul_apply,Matrix.transpose_apply,hpi,add_mul,ite_mul,Finset.sum_add_distrib]
    · simp [plane,Matrix.mul_apply,Matrix.transpose_apply,hpi,hpj,ite_mul]

theorem plane_orthogonal (i j : Fin n) (hij : i≠j) (c s : K) (hcs : c^2+s^2=1) :
    (plane i j c s).transpose*plane i j c s=1 := by
  ext p q
  rw [transpose_plane_mul _ i j hij]
  by_cases hpi:p=i <;> by_cases hpj:p=j <;> by_cases hqi:q=i <;> by_cases hqj:q=j
  all_goals simp_all [plane,Matrix.one_apply,eq_comm]
  all_goals nlinarith

def rationalPlane (i j : Fin n) (t : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  plane i j (rotationC t) (rotationS t)

theorem rational_plane_orthogonal (i j : Fin n) (hij : i≠j) (t : ℚ) :
    (rationalPlane i j t).transpose*rationalPlane i j t=1 :=
  plane_orthogonal i j hij _ _ (rotation_circle t)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem conjugated_pivot (A : Matrix (Fin n) (Fin n) K) (i j : Fin n)
    (hij : i≠j) (hsym : A j i=A i j) (t : K) :
    ((plane i j (rotationC t) (rotationS t)).transpose*A*
      plane i j (rotationC t) (rotationS t)) i j=
      rotatedPivot (A i i) (A i j) (A j j) t := by
  rw [mul_plane _ i j hij,transpose_plane_mul _ i j hij,transpose_plane_mul _ i j hij]
  simp only [hij,Ne.symm hij,ite_false,ite_true,hsym,rotatedPivot]
  ring

end Max2SAT.Community
