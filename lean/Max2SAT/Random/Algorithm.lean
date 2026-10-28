import Max2SAT.Random.Search
import Max2SAT.Random.Support
import Max2SAT.Preprocess

/-! RandomFormula receives only the formula. Its name describes the input
families in the later analysis; the algorithm itself is deterministic. -/
namespace Max2SAT.Random

def core (F : Formula n) : Formula n :=
  (Residual.restrict (active F) (initial F) F).1

def solve (F : Formula n) : Option (Assignment n) :=
  let U := Bias.ordered (active F)
  let F0 := (preprocess (core F)).1
  solveOn F0 (weight F) U ((U.length+1)/2) (initial F)

/-- Manuscript Lemma lem:exactA: optimum on every well-formed input, including
repeated clauses, arbitrary units, empty support, and zero variables. The
support, rational weights, order, and stopping depth are computed from F. -/
theorem solve_correct (F : Formula n) (hF : wellFormed F) :
    ∃ x, solve F=some x ∧ ∀ y, score F y ≤ score F x := by
  let U := Bias.ordered (active F)
  let F0 := (preprocess (core F)).1
  have hc : wellFormed (core F) := Residual.restrict_wellFormed F _ _ hF
  have hw : wellFormed F0 := (preprocess_finished (core F) hc).1
  rcases solveOn_correct F0 (weight F) U ((U.length+1)/2) (initial F) hw
    (Bias.ordered_nodup _) (fun i => (weight_positive F i).le) with ⟨x,hx,hcomp,hopt⟩
  have hxcomp : Compatible (active F) (initial F) x := by simpa [U] using hcomp
  refine ⟨x,hx,?_⟩
  intro y
  have hycomp := extend_compatible F y
  have hh := hopt (extend F y) (by simpa [U] using hycomp)
  have hys := Residual.restrict_score F (active F) (initial F) (extend F y) hycomp
  have hxs := Residual.restrict_score F (active F) (initial F) x hxcomp
  have hyp := preprocess_correct (core F) (extend F y)
  have hxp := preprocess_correct (core F) x
  have hbase := extend_score F y
  change score F0 (extend F y) ≤ score F0 x at hh
  change score (core F) (extend F y) = _ at hyp
  change score (core F) x = _ at hxp
  change score F (extend F y) = _ + score (core F) (extend F y) at hys
  change score F x = _ + score (core F) x at hxs
  dsimp [F0] at hh
  omega

def randomFormula (F : Formula n) : Option (ℤ × Assignment n) :=
  (solve F).map (fun x => (score F x,x))

theorem randomFormula_correct (F : Formula n) (hF : wellFormed F) :
    ∃ q x, randomFormula F=some (q,x) ∧ q=score F x ∧ ∀ y, score F y ≤ q := by
  rcases solve_correct F hF with ⟨x,hx,ho⟩
  exact ⟨score F x,x,by simp [randomFormula,hx],rfl,ho⟩

end Max2SAT.Random
