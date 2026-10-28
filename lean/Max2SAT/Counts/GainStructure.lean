import Max2SAT.Counts.Adjustments

/-! Symmetry and zero diagonal of the actual formula-derived interactions,
including arbitrary supplied count and projection adjustments. -/
namespace Max2SAT.Counts
variable {n r : ℕ}

theorem coeff_eval_difference (A : Affine n) (i : Fin n) :
    A.coeff i=A.eval (Function.update (fun _ => false) i true)-A.eval (fun _ => false) := by
  rw [Affine.eval_update]
  simp

theorem gainExpr_symmetric (F : Formula n) (hF : wellFormed F) (i j : Fin n) :
    (gainExpr F i).coeff j=(gainExpr F j).coeff i := by
  by_cases hij : i=j
  · subst j; rfl
  let x : Assignment n := fun _ => false
  have hf : ∀ t, Function.update x t false=x := fun t => Function.update_eq_self t x
  rw [coeff_eval_difference,coeff_eval_difference]
  simp only [gainExpr_eval F _ _ hF,scoreGain]
  change ((score F (Function.update (Function.update x j true) i true) : ℚ)-
    score F (Function.update (Function.update x j true) i false))-
    ((score F (Function.update x i true) : ℚ)-score F (Function.update x i false)) =
    ((score F (Function.update (Function.update x i true) j true) : ℚ)-
    score F (Function.update (Function.update x i true) j false))-
    ((score F (Function.update x j true) : ℚ)-score F (Function.update x j false))
  rw [Function.update_comm (Ne.symm hij) true true x,
    Function.update_comm (Ne.symm hij) true false x,
    Function.update_comm hij true false x,hf,hf]
  ring

theorem countGain_diagonal (F : Formula n) (hF : wellFormed F)
    (beta : ℚ) (h : ℕ) (t : Fin n) : (countGain F beta h t).coeff t=0 := by
  simp [countGain,Affine.add,Affine.shift,Affine.scale,without,gainExpr_diagonal F t hF]

theorem countGain_symmetric (F : Formula n) (hF : wellFormed F)
    (beta : ℚ) (h : ℕ) (t w : Fin n) :
    (countGain F beta h t).coeff w=(countGain F beta h w).coeff t := by
  by_cases htw : t=w
  · subst w; rfl
  simp [countGain,Affine.add,Affine.shift,Affine.scale,without,htw,Ne.symm htw,
    gainExpr_symmetric F hF t w]

theorem projectionGain_diagonal (F : Formula n) (hF : wellFormed F)
    (lam : Fin r → ℚ) (v : Fin r → Fin n → ℚ) (guess : Fin r → ℚ) (t : Fin n) :
    (projectionGain F lam v guess t).coeff t=0 := by
  simp [projectionGain,Affine.add,Affine.sum,Affine.scale,Affine.shift,without,
    gainExpr_diagonal F t hF]

theorem projectionGain_symmetric (F : Formula n) (hF : wellFormed F)
    (lam : Fin r → ℚ) (v : Fin r → Fin n → ℚ) (guess : Fin r → ℚ) (t w : Fin n) :
    (projectionGain F lam v guess t).coeff w=(projectionGain F lam v guess w).coeff t := by
  by_cases htw : t=w
  · subst w; rfl
  simp only [projectionGain,Affine.add,Affine.sum,Affine.scale,Affine.shift,without,
    ite_eq_right htw,ite_eq_right (Ne.symm htw),gainExpr_symmetric F hF t w]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

end Max2SAT.Counts
