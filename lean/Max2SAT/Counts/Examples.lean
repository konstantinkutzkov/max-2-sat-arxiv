import Max2SAT.Counts.Grids
import Max2SAT.Counts.Resources
import Max2SAT.Counts.AccumulationIdentity

/-! Small kernel-checked boundary cases supplement the arbitrary-size proofs. -/
namespace Max2SAT.Counts.Examples

def cut : Formula 2 := [.pair ⟨0,true⟩ ⟨1,true⟩,.pair ⟨0,false⟩ ⟨1,false⟩]
def cutOptimum : Assignment 2 := fun i => decide (i=1)
def cutRound : Fin 2 → ℕ := fun i => i.val

private theorem cut_wellFormed : wellFormed cut := by simp [cut,wellFormed,Clause.WellFormed]
private theorem cut_plan : EarlierInPrefix ({0} : Finset (Fin 2)) cutRound := by
  intro t ht w hw
  have ht' : t=0 := by simpa using ht
  subst t
  simp [cutRound] at hw

example : countGuesses 4 0=[0] := by decide
example : (countGuesses 4 (-3)).length=5 := by decide

/-- The count is a guess used in comparisons, not a constraint on outputs. -/
example : cutOptimum∈PrefixSearch.outputs (countBudget cut 0 {0} cutRound 0) {0} ∧
    ones cutOptimum≠0 := by
  constructor
  · apply (PrefixSearch.mem_outputs _ _ _ (comparison_stable _ _ _ _ cut_plan)).mpr
    norm_num [countBudget,comparison_budget_iff,preference,Affine.average,earlier,
      countGain,gainExpr,termsExpr,literalExpr,pruningConstraint,Clause.cutPart,
      Literal.neg,Affine.add,Affine.scale,Affine.shift,Affine.zero,Affine.eval,
      without,bit,direction,cut,cutRound,cutOptimum,Fin.sum_univ_succ]
  · decide

/-- Ties at the allowance boundary are retained. -/
example : (comparisonExpr (countGain ([] : Formula 1) (-1) 1) (fun _ => 1)
    Finset.univ (fun _ => 0) (fun _ => true)).eval (fun _ => true)=0 := by
  norm_num [comparisonExpr,preference,Affine.average,earlier,countGain,gainExpr,
    termsExpr,pruningConstraint,Affine.add,Affine.scale,Affine.shift,Affine.zero,
    Affine.eval,Affine.sum,without,bit,direction,Fin.sum_univ_succ]

/-- Removing the diagonal allowance would reject this tied optimum. -/
example : ¬(comparisonBudget (countGain ([] : Formula 1) (-1) 1) (fun _ => 0)
    Finset.univ (fun _ => 0) (fun _ => true)).Holds (fun _ => true) := by
  norm_num [comparison_budget_iff,preference,Affine.average,earlier,countGain,gainExpr,
    termsExpr,pruningConstraint,Affine.add,Affine.scale,Affine.shift,Affine.zero,
    Affine.eval,without,bit,direction,Fin.sum_univ_succ]

example : coordinateGrid 1 (1/2)=[-3/2,-1,-1/2,0,1/2,1,3/2] := by
  norm_num [coordinateGrid,List.range_succ]
example : (tuples (fun _ : Fin 0 => ([] : List ℚ))).length=1 := by decide

/-- The implemented solver, including preprocessing, handles a Max-Cut pair. -/
example : ∃ x, countComparisons cut (-2) {0} cutRound=some x ∧ score cut x=2 := by
  obtain ⟨x,hx,ho⟩ := countComparisons_correct cut (-2) {0} cutRound cut_wellFormed cut_plan
  have hlo := ho cutOptimum
  have hh : score cut cutOptimum=2 := by decide
  have hu : score cut x≤2 := by
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      norm_num [cut,score,Clause.score,Literal.value,Literal.eval,h0,h1]
  exact ⟨x,hx,by omega⟩

def cancellable : Formula 2 := [.pair ⟨0,true⟩ ⟨1,true⟩,.pair ⟨0,true⟩ ⟨1,false⟩]

example : scoreGain (preprocess cancellable).1 0 cutOptimum=scoreGain cancellable 0 cutOptimum :=
  scoreGain_preprocess cancellable 0 cutOptimum

#eval (countComparisons cut (-2) {0} cutRound).map (score cut)
#eval coordinateGrid 1 (1/2)

end Max2SAT.Counts.Examples
