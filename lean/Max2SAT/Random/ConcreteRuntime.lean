import Max2SAT.Random.FullRuntime
import Max2SAT.Random.Sampling

/-! The two stated clause distributions share the paper's m0=4 and
kappa=3/4 parameters. The algorithm receives neither model nor support. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable

def oneClauseCommonModel : PairLaw 4 (3/4) where
  law := oneClause
  bounded := oneClause_bounded
  invariant := oneClause_invariant
  moment left := by rw [oneClause_moment]; norm_num

def quarterClauseModel : PairLaw 4 (3/4) where
  law := independentClauses (1/4) (by norm_num) (by norm_num)
  bounded := independentClauses_bounded _ _ _
  invariant := independentClauses_invariant _ _ _
  moment left := (quarter_moment left).ge

/-- False selects one uniform clause per pair; true selects four independent
Bernoulli(1/4) clause indicators on each pair. This flag describes the law. -/
def standardClauseModel (independent : Bool) : PairLaw 4 (3/4) :=
  if independent then quarterClauseModel else oneClauseCommonModel

theorem standard_clause_model_law (independent : Bool) :
    (standardClauseModel independent).law=
      if independent then independentClauses (1/4) (by norm_num) (by norm_num) else oneClause := by
  cases independent <;> rfl

def randomClauseConstant : ℝ := runtimeConstant 4 (3/4)

theorem random_clause_constant_bounds :
    0<randomClauseConstant ∧ randomClauseConstant<Real.log 2/2 :=
  runtime_constant_small (by decide) (by norm_num) (by norm_num)

theorem random_clauses_expected_nodes (independent : Bool) (E : Finset (Edge n))
    (units : List (Literal n)) :
    expect (product (fun _ : E => (standardClauseModel independent).law))
      (fun K => (Random.nodeCount (generate E K units):ℝ))≤
      (4+6*n)*(2:ℝ)^n*Real.exp (-randomClauseConstant*n) :=
  random_sign_expected_nodes (fun _ => standardClauseModel independent)
    (by decide) (by norm_num) (by norm_num) units

theorem random_clauses_nodes_tail (independent : Bool) (E : Finset (Edge n))
    (units : List (Literal n)) :
    prob (product (fun _ : E => (standardClauseModel independent).law)) (fun K =>
      (4+2*n)*(2:ℝ)^n*Real.exp (-randomClauseConstant*n/2)<
        (Random.nodeCount (generate E K units):ℝ))≤
      3*Real.exp (-randomClauseConstant*n/2) :=
  random_sign_nodes_tail (fun _ => standardClauseModel independent)
    (by decide) (by norm_num) (by norm_num) units

theorem generated_input_exact (E : Finset (Edge n)) (K : E → Pattern m)
    (units : List (Literal n)) :
    ∃ q x, Random.randomFormula (generate E K units)=some (q,x) ∧
      q=score (generate E K units) x ∧ ∀ y, score (generate E K units) y≤q :=
  Random.randomFormula_correct _ (generate_wellFormed E K units)

end
end Max2SAT.RandomInput
