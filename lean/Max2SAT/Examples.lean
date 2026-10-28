import Max2SAT.Preprocess
import Max2SAT.ConstraintCheck
import Max2SAT.Enumeration

/-! Small kernel-checked regressions. They supplement, rather than replace,
the universally quantified theorems. No native_decide is used. -/
namespace Max2SAT.Examples

def u : Literal 2 := ⟨0,true⟩
def v : Literal 2 := ⟨1,true⟩
def exampleFormula : Formula 2 := [.pair u v,.pair u v.neg,.unit u.neg]

example : wellFormed exampleFormula := by
  simp [wellFormed,exampleFormula,Clause.WellFormed,Literal.neg,u,v]
example : (preprocess exampleFormula).1=[] ∧ (preprocess exampleFormula).2=2 := by decide

/-- Neither constraint is contradictory alone. Their sum is contradictory. -/
def opposing : List (Constraint 2) := [⟨[u],0⟩,⟨[u.neg],0⟩]
example : (opposing.map Constraint.infeasible)=[false,false] := by decide
example : Constraint.infeasible (Constraint.sum opposing)=true := by decide
example : Constraint.reject Finset.univ (fun _ => false) opposing=true := by decide

example : Enumeration.enumerate [1,1,1] 1 =
    [[false,false,false],[false,false,true],[false,true,false],[true,false,false]] := by
  norm_num [Enumeration.enumerate]
example : Enumeration.nodes [1,1,1] 1=13 := by norm_num [Enumeration.nodes]
example : Enumeration.foldEnumerate (fun _ count => count+1) [1,1,1] 1 0=4 := by
  norm_num [Enumeration.foldEnumerate]
example : Enumeration.enumerate [0,2] (-1)=[] := by decide
example : Enumeration.nodes [0,2] (-1)=1 := by decide
example : Enumeration.enumerate [0,0] 0 =
    [[false,false],[false,true],[true,false],[true,true]] := by simp [Enumeration.enumerate]

#eval Constraint.reject Finset.univ (fun _ => false) opposing
#eval (Enumeration.enumerate [1,1,1] 1).length
#eval Enumeration.nodes [1,1,1] 1
end Max2SAT.Examples
