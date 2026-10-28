import Max2SAT.Random.Algorithm

/-! Regressions for residual preferences, observed support, weighted
cancellation, and the full formula-only procedure. -/
namespace Max2SAT.Random.Examples

def a : Literal 4 := ⟨0,true⟩
def b : Literal 4 := ⟨1,true⟩
def c : Literal 4 := ⟨2,true⟩
def d : Literal 4 := ⟨3,true⟩

def changing : Formula 4 :=
  [.pair a b, .pair b.neg c, .unit d.neg, .unit d.neg, .unit d]

example : active changing = {0,1,2} := by decide
example : weight changing 0 = 1 ∧ weight changing 1 = 1/2 ∧ weight changing 2 = 1 := by
  have h0 : (neighbors changing 0).card = 1 := by decide
  have h1 : (neighbors changing 1).card = 2 := by decide
  have h2 : (neighbors changing 2).card = 1 := by decide
  norm_num [weight,h0,h1,h2]
example : initial changing 3 = false := by decide
example : (branchLiteral changing [1,2] (fun _ => false) 1).positive = true := by decide
example : (branchLiteral changing [1,2] (fun i => i == 0) 1).positive = false := by decide

def removed : Formula 4 := [.pair a b, .pair a b.neg]
example : active removed = {0,1} := by decide
example : (preprocess (core removed)).1 = [.unit a] := by decide

def positiveCut : Constraint 1 := ⟨[⟨0,true⟩],1⟩
def negativeCut : Constraint 1 := ⟨[⟨0,false⟩],0⟩
def unequalSum : Weighted.Budget 1 := Weighted.sum [(1,positiveCut),(2,negativeCut)]

example : Weighted.minimum unequalSum [0] (fun _ => false) = 1 := by
  norm_num [Weighted.minimum,unequalSum,Weighted.sum,Weighted.ofConstraint,
    Weighted.termCost,positiveCut,negativeCut,Fin.sum_univ_succ]
example : Weighted.reject unequalSum [] (fun _ => false) = true := by
  norm_num [Weighted.reject,Weighted.minimum,unequalSum,Weighted.sum,Weighted.ofConstraint,
    Weighted.termCost,positiveCut,negativeCut,Fin.sum_univ_succ]
example : Weighted.reject unequalSum [] (fun _ => true) = false := by
  norm_num [Weighted.reject,Weighted.minimum,unequalSum,Weighted.sum,Weighted.ofConstraint,
    Weighted.termCost,positiveCut,negativeCut,Fin.sum_univ_succ]

/-- Sum enumeration deliberately permits slack in one individual cut to
compensate for violation of another. It does not solve joint feasibility. -/
example : (Weighted.sum [(1,(⟨[⟨0,true⟩],0⟩ : Constraint 1)),
    (1,(⟨[⟨0,false⟩],2⟩ : Constraint 1))]).Holds (fun _ => true) ∧
    ¬ (⟨[⟨0,true⟩],0⟩ : Constraint 1).Holds (fun _ => true) := by
  norm_num [Weighted.Budget.Holds,Weighted.Budget.lhs,Weighted.sum,Weighted.ofConstraint,
    Weighted.termCost,Fin.sum_univ_succ,Constraint.Holds,Constraint.lhs,Literal.value,Literal.eval]

def answer (F : Formula n) : Option ℤ := (randomFormula F).map Prod.fst

private theorem answer_eq (F : Formula n) (hF : wellFormed F) (k : ℤ)
    (z : Assignment n) (hz : score F z=k) (hb : ∀ x, score F x ≤ k) : answer F=some k := by
  rcases randomFormula_correct F hF with ⟨q,x,hx,hq,ho⟩
  have he : q=k := by have hh := ho z; rw [hz] at hh; rw [hq]; exact le_antisymm (hb x) (by omega)
  simp [answer,hx,he]

example : answer ([] : Formula 0) = some 0 := by
  apply answer_eq _ (by simp [wellFormed]) 0 (fun i => i.elim0) (by simp)
  intro x; simp

example : answer changing = some 4 := by
  apply answer_eq _ (by simp [changing,wellFormed,Clause.WellFormed,a,b,c,d,Literal.neg])
    4 (fun i => i != 3) (by decide)
  intro x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    norm_num [changing,score,Clause.score,Literal.value,Literal.eval,Literal.neg,a,b,c,d,h0,h1,h2,h3]

example : answer removed = some 2 := by
  apply answer_eq _ (by simp [removed,wellFormed,Clause.WellFormed,a,b,Literal.neg])
    2 (fun _ => true) (by decide)
  intro x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [removed,score,Clause.score,Literal.value,Literal.eval,Literal.neg,a,b,h0,h1]

#eval answer ([] : Formula 0)
#eval answer changing
#eval answer removed
#eval [weight changing 0,weight changing 1,weight changing 2]

end Max2SAT.Random.Examples
