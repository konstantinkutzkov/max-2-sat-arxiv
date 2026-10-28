import Max2SAT.Counts.Affine
import Max2SAT.Preprocess

/-! Formula gains are constructed by a clause scan and identified with
the true difference between the two variable assignments. -/
namespace Max2SAT.Counts

def literalExpr (a : Literal n) : Affine n :=
  ⟨1-bit a.positive,fun i => if i=a.var then direction a.positive else 0⟩

theorem literalExpr_eval (a : Literal n) (x : Assignment n) :
    (literalExpr a).eval x = (a.value x : ℚ) := by
  simp only [literalExpr,Affine.eval,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  cases hp : a.positive <;> cases hx : x a.var <;>
    norm_num [bit,direction,Literal.value,Literal.eval,hp,hx]

def termsExpr : List (Literal n) → Affine n
  | [] => Affine.zero
  | a::as => (literalExpr a).add (termsExpr as)

theorem termsExpr_eval (as : List (Literal n)) (x : Assignment n) :
    (termsExpr as).eval x = ((as.map (fun a => a.value x)).sum : ℤ) := by
  induction as with
  | nil => simp [termsExpr]
  | cons a as ih => simp [termsExpr,literalExpr_eval,ih]

def gainExpr (F : Formula n) (i : Fin n) : Affine n :=
  let C := pruningConstraint F ⟨i,true⟩
  (termsExpr C.terms).shift (-(C.bound+1 : ℚ))

def scoreGain (F : Formula n) (i : Fin n) (x : Assignment n) : ℚ :=
  (score F (Function.update x i true) : ℚ) - score F (Function.update x i false)

theorem gainExpr_eval (F : Formula n) (i : Fin n) (x : Assignment n)
    (hF : wellFormed F) : (gainExpr F i).eval x = scoreGain F i x := by
  have h := pruning_gain_identity F ⟨i,true⟩ x hF
  have hh : ((pruningConstraint F ⟨i,true⟩).lhs x : ℚ) -
      ((pruningConstraint F ⟨i,true⟩).bound+1) = scoreGain F i x := by
    unfold scoreGain
    exact_mod_cast (by simpa [Literal.force] using h :
      (pruningConstraint F ⟨i,true⟩).lhs x -
        ((pruningConstraint F ⟨i,true⟩).bound+1) =
        score F (Function.update x i true)-score F (Function.update x i false))
  simpa [gainExpr,termsExpr_eval,Constraint.lhs,sub_eq_add_neg] using hh

theorem gainExpr_diagonal (F : Formula n) (i : Fin n) (hF : wellFormed F) :
    (gainExpr F i).coeff i=0 := by
  let x : Assignment n := fun _ => false
  have he : (gainExpr F i).eval (Function.update x i true)=(gainExpr F i).eval x := by
    simp [gainExpr_eval F i _ hF,scoreGain,x,Function.update_idem]
  rw [Affine.eval_update] at he
  simpa [x] using he

theorem oriented_score_gain (F : Formula n) (x : Assignment n) (i : Fin n)
    (p : Bool) (hi : x i≠p) :
    direction p*scoreGain F i x =
      (score F (Function.update x i p) : ℚ)-score F x := by
  cases p <;> cases hx : x i
  all_goals try exact (hi hx).elim
  · have he : Function.update x i true=x := Function.update_eq_self_iff.mpr hx.symm
    simp [direction,scoreGain,he]
  · have he : Function.update x i false=x := Function.update_eq_self_iff.mpr hx.symm
    simp [direction,scoreGain,he]

theorem optimal_oriented_gain (F : Formula n) (x : Assignment n)
    (hx : ∀ y, score F y≤score F x) (i : Fin n) (p : Bool) (hi : x i≠p) :
    direction p*scoreGain F i x≤0 := by
  rw [oriented_score_gain F x i p hi]
  exact sub_nonpos.mpr (by exact_mod_cast hx (Function.update x i p))

theorem scoreGain_preprocess (F : Formula n) (i : Fin n) (x : Assignment n) :
    scoreGain (preprocess F).1 i x=scoreGain F i x := by
  unfold scoreGain
  rw [preprocess_correct F (Function.update x i true),
    preprocess_correct F (Function.update x i false)]
  push_cast
  ring

end Max2SAT.Counts
