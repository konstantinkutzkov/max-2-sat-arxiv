import Max2SAT.Bias.Resources
import Max2SAT.Bias.DenseGap

/-! Kernel-checked regressions for the paper's literal-gap algorithm and exact sum enumerator. -/
namespace Max2SAT.Bias.Examples

def answer (F : Formula n) : Option ℤ := (solveBias F).map (score F)
def a : Literal 2 := ⟨0,true⟩
def b : Literal 2 := ⟨1,true⟩
def cancellation : Formula 2 := [.pair a b,.pair a b.neg,.unit a.neg]
def cutPair : Formula 2 := [.pair a b,.pair a.neg b.neg]
def repeated : Formula 2 := [.pair a b,.pair a b,.unit a.neg,.unit b.neg]

/-- Simplicity identifies clauses whose literals are written in reverse order. -/
example : ¬ Simple ([.pair a b, .pair b a] : Formula 2) := by
  simp [Simple, Clause.literalSet, Finset.pair_comm]

def producesRepeatedUnits : Formula 2 := [.pair a b, .pair a b.neg, .unit a]

example : Simple producesRepeatedUnits := by
  constructor
  · simp [wellFormed, producesRepeatedUnits, Clause.WellFormed, a, b, Literal.neg]
  · decide

example : preprocess producesRepeatedUnits = ([.unit a, .unit a], 1) := by decide
example : gap producesRepeatedUnits 0 = 4 := by decide
example : gap (preprocess producesRepeatedUnits).1 0 = 4 := by decide
example : B producesRepeatedUnits 0 = 3 ∧ B (preprocess producesRepeatedUnits).1 0 = 2 := by
  decide

private theorem answer_eq (F : Formula n) (hF : wellFormed F) (k : ℤ)
    (z : Assignment n) (hz : score F z=k) (hb : ∀ x, score F x≤k) : answer F=some k := by
  rcases solveBias_correct F hF with ⟨x,hx,ho⟩
  have he : score F x=k := by have hh := ho z; rw [hz] at hh; exact le_antisymm (hb x) hh
  simp [answer,hx,he]

example : answer ([] : Formula 0)=some 0 := by
  apply answer_eq _ (by simp [wellFormed]) 0 (fun _ => false) (by simp)
  intro x; simp
example : answer cancellation=some 2 := by
  apply answer_eq _ (by simp [wellFormed,cancellation,Clause.WellFormed,a,b,Literal.neg]) 2
    (fun _ => true) (by decide)
  intro x
  cases hx : x 0 <;> cases hy : x 1 <;>
    norm_num [score,Clause.score,Literal.value,Literal.eval,a,b,Literal.neg,hx,hy,cancellation]
example : answer cutPair=some 2 := by
  apply answer_eq _ (by simp [wellFormed,cutPair,Clause.WellFormed,a,b,Literal.neg]) 2
    (fun i => i==1) (by decide)
  intro x
  cases hx : x 0 <;> cases hy : x 1 <;>
    norm_num [score,Clause.score,Literal.value,Literal.eval,a,b,Literal.neg,hx,hy,cutPair]
example : answer repeated=some 3 := by
  apply answer_eq _ (by simp [wellFormed,repeated,Clause.WellFormed,a,b,Literal.neg]) 3
    (fun i => i==0) (by decide)
  intro x
  cases hx : x 0 <;> cases hy : x 1 <;>
    norm_num [score,Clause.score,Literal.value,Literal.eval,a,b,Literal.neg,hx,hy,repeated]

/-- Infeasible roots cost one node, even if the contradiction uses complements. -/
example : Single.nodes (⟨[a,a.neg],0⟩ : Constraint 2) [0,1] (fun _ => false)=1 := by decide
example : (Single.enumerate (⟨[a,a.neg],0⟩ : Constraint 2) [0,1] (fun _ => false)).length=0 := by decide
example : (Single.enumerate (⟨[a,b],0⟩ : Constraint 2) [0,1] (fun _ => false)).length=1 := by decide

#eval answer cancellation
#eval answer cutPair
#eval answer repeated
#eval Hybrid.nodeCount repeated (initialPreference repeated) (branchingSet repeated)
#eval (Hybrid.outputs repeated (initialPreference repeated) (branchingSet repeated)).length
end Max2SAT.Bias.Examples
