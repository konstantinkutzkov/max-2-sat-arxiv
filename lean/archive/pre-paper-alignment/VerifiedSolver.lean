import Max2SAT.Preprocess
import Max2SAT.Solver

namespace Max2SAT

/-- Apply score-preserving preprocessing, then stream the comparison search. -/
def solvePreprocessed (F : Formula n) : Option (Assignment n) := solve (preprocess F).1

/-- End-to-end optimality for all numbers of variables and all well-formed
unweighted formulas, including repeated clauses. There is no density assumption. -/
theorem solvePreprocessed_correct (F : Formula n) (hF : wellFormed F) :
    ∃ x, solvePreprocessed F = some x ∧ ∀ y, score F y ≤ score F x := by
  rcases solve_correct (preprocess F).1 (preprocess_finished F hF).1 with ⟨x,hx,ho⟩
  refine ⟨x,hx,?_⟩
  intro y
  rw [preprocess_correct F y,preprocess_correct F x]
  exact add_le_add (le_refl _) (ho y)

/-- Feasibility-preserving domination, available for an eager simplifier.
The side condition is necessary: an arbitrary inherited constraint need not
allow forcing the dominating literal. -/
theorem safe_domination (F : Formula n) (cs : List (Constraint n))
    (v : Literal n) (x : Assignment n) (hF : wellFormed F)
    (hu : d1 F v.neg=0) (hd : d2 F v.neg ≤ d1 F v)
    (hn : ∀ C ∈ cs, v ∉ C.terms) (hx : ∀ C ∈ cs, C.Holds x) :
    (∀ C ∈ cs, C.Holds (v.force true x)) ∧ score F x ≤ score F (v.force true x) := by
  constructor
  · intro C hC
    exact C.force_preserves v x (hn C hC) (hx C hC)
  · cases he : v.eval x
    · have h := unit_domination F v x hF hu hd
      simpa [Literal.force_eq_self v x false he] using h
    · simp [Literal.force_eq_self v x true he]
end Max2SAT
