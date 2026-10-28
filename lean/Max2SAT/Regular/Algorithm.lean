import Max2SAT.Regular.HighDegree
import Max2SAT.Regular.LowDegree
import Max2SAT.Regular.CutScore

namespace Max2SAT.Regular
variable {n : ℕ}

def inputDegree (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ :=
  if h : 0<n then G.degree ⟨0,h⟩ else 0

def independentResult (F : Formula n) (S : Finset (Fin n)) : Option (ℤ × Assignment n) :=
  (independentSolve F S).map (fun x => (score F x,x))

/-- D and N are fixed integer constants for the family. Small inputs use
exhaustive search, small degrees use a greedy independent set, and the
remaining inputs use the unchanged two-round count algorithm. -/
noncomputable def regularResult (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) (D N : ℕ) : Option (ℤ × Assignment n) :=
  if n<N then independentResult (formula G units) ∅ else
    if inputDegree G<D then independentResult (formula G units) (independentSet G)
    else countResult G units (inputDegree G)

noncomputable def regularNodes (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) (D N : ℕ) : ℕ :=
  if n<N then independentNodes (∅ : Finset (Fin n)) else
    if inputDegree G<D then independentNodes (independentSet G)
    else countNodes G units (inputDegree G)

theorem independent_result_correct (F : Formula n) (S : Finset (Fin n)) (hS : Independent F S) :
    ∃ q x, independentResult F S=some (q,x) ∧ q=score F x ∧ ∀ y, score F y≤q := by
  obtain ⟨x,hx,ho⟩ := independent_solve_correct F S hS
  exact ⟨score F x,x,by simp [independentResult,hx],rfl,ho⟩

theorem regular_result_correct (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) (D N : ℕ) :
    ∃ q x, regularResult G units D N=some (q,x) ∧ q=score (formula G units) x ∧
      ∀ y, score (formula G units) y≤q := by
  unfold regularResult
  split
  · exact independent_result_correct _ _ (by simp [Independent])
  · split
    · exact independent_result_correct _ _ (formula_independent G units)
    · exact count_result_correct _ _ _

theorem regular_result_maxcut (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D N : ℕ) :
    ∃ q x, regularResult G [] D N=some (q,x) ∧ ∀ y, cutSize G y≤cutSize G x := by
  obtain ⟨q,x,hx,hq,ho⟩ := regular_result_correct G [] D N
  exact ⟨q,x,hx,optimal_cut_of_optimal_formula G x (by simpa only [hq] using ho)⟩

theorem input_degree_regular (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (d : ℕ) (hd : G.IsRegularOfDegree d) (hn : 0<n) : inputDegree G=d := by
  simp only [inputDegree,hn,↓reduceDIte]
  exact hd _

end Max2SAT.Regular
