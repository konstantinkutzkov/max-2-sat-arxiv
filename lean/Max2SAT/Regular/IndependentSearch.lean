import Max2SAT.Regular.Encoding
import Max2SAT.Regular.Greedy
import Max2SAT.Random.Algorithm

namespace Max2SAT.Regular
variable {n : ℕ}

/-- No binary clause has both endpoints among the vertices optimized last. -/
def Independent (F : Formula n) (S : Finset (Fin n)) : Prop :=
  ∀ a b, Clause.pair a b∈F → a.var∈S → b.var∈S → False

theorem formula_independent (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) : Independent (formula G units) (independentSet G) := by
  intro a b hc ha hb
  simp only [formula,List.mem_append,List.mem_map,List.mem_flatMap,Finset.mem_toList] at hc
  rcases hc with ⟨l,_,hl⟩|⟨e,he,hc⟩
  · cases hl
  · simp only [cutPair,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with h|h
    all_goals
      cases h
      exact independent_set_independent G _ _ ha hb (Finset.mem_filter.mp he).2.2

theorem independent_residual_units (F : Formula n) (S : Finset (Fin n))
    (hS : Independent F S) (x : Assignment n) (c : Clause n)
    (hc : c∈(Residual.restrict S x F).1) : ∃ a, a.var∈S ∧ c=Clause.unit a := by
  obtain ⟨e,he,hc⟩ := List.mem_flatMap.mp hc
  cases e with
  | unit a =>
    simp only [Residual.clause] at hc
    split_ifs at hc <;> simp_all
  | pair a b =>
    have hh := hS a b he
    simp only [Residual.clause] at hc
    split_ifs at hc <;> simp_all

def complete (F : Formula n) (S : Finset (Fin n)) (x : Assignment n) : Assignment n :=
  fun i => if i∈S then Random.initial (Residual.restrict S x F).1 i else x i

theorem complete_compatible (F : Formula n) (S : Finset (Fin n)) (x : Assignment n) :
    Compatible S x (complete F S x) := by
  intro i hi; simp [complete,hi]

theorem complete_optimal (F : Formula n) (S : Finset (Fin n)) (hS : Independent F S)
    (x y : Assignment n) (hy : Compatible S x y) : score F y≤score F (complete F S x) := by
  let R := (Residual.restrict S x F).1
  have hr : ∀ c∈R, ∃ a, a.var∈S ∧ c=Clause.unit a := independent_residual_units F S hS x
  have ha : Random.active R=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨c,hc,hi⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hi)
    obtain ⟨a,_,rfl⟩ := hr c hc
    simp [Random.clauseVars] at hi
  have hscore : score R (Random.initial R)=score R (complete F S x) := by
    unfold score
    congr 1
    apply List.map_congr_left
    intro c hc
    obtain ⟨a,ha,rfl⟩ := hr c hc
    simp [Clause.score,Literal.value,Literal.eval,complete,ha,R]
  have hopt := Random.extend_score R y
  have hext : Random.extend R y=Random.initial R := by funext i; simp [Random.extend,ha]
  rw [hext,hscore] at hopt
  rw [Residual.restrict_score F S x y hy,
    Residual.restrict_score F S x (complete F S x) (complete_compatible F S x)]
  exact add_le_add (le_refl _) hopt

def zeroBudget : Weighted.Budget n := ⟨fun _ _ => 0,0⟩

def independentSolve (F : Formula n) (S : Finset (Fin n)) : Option (Assignment n) :=
  Weighted.fold zeroBudget (fun best x => Bias.Hybrid.keepBest F best (complete F S x))
    (Bias.ordered Sᶜ) (fun _ => false) none

def independentNodes (S : Finset (Fin n)) : ℕ :=
  Weighted.nodes zeroBudget (Bias.ordered Sᶜ) (fun _ => false)

theorem independent_solve_correct (F : Formula n) (S : Finset (Fin n)) (hS : Independent F S) :
    ∃ z, independentSolve F S=some z ∧ ∀ y, score F y≤score F z := by
  classical
  obtain ⟨x,_,hx⟩ := Finset.exists_max_image Finset.univ (score F) Finset.univ_nonempty
  let base : Assignment n := fun i => if i∈S then false else x i
  have hbase : Compatible S base x := by intro i hi; simp [base,hi]
  have hy : base∈Weighted.enumerate zeroBudget (Bias.ordered Sᶜ) (fun _ => false) := by
    apply (Weighted.mem_enumerate _ _ _ _ (Bias.ordered_nodup _)).mpr
    constructor
    · intro i hi
      have hi' : i∈S := by simpa [Bias.ordered] using hi
      simp [base,hi']
    · simp [zeroBudget,Weighted.Budget.Holds,Weighted.Budget.lhs]
  let outputs := (Weighted.enumerate zeroBudget (Bias.ordered Sᶜ) (fun _ => false)).map (complete F S)
  have hmem : complete F S base∈outputs := List.mem_map.mpr ⟨base,hy,rfl⟩
  obtain ⟨z,hz,hbest⟩ := Bias.Hybrid.fold_best_bound F outputs none (complete F S base) (by simpa using hmem)
  refine ⟨z,?_,?_⟩
  · simpa [independentSolve,Weighted.fold_eq_foldl,outputs,List.foldl_map] using hz
  · intro y
    exact (hx y (Finset.mem_univ y)).trans ((complete_optimal F S hS base x hbase).trans hbest)

theorem zero_budget_nodes (free : List (Fin n)) (x : Assignment n) :
    Weighted.nodes zeroBudget free x=2^(free.length+1)-1 := by
  induction free generalizing x with
  | nil => simp [Weighted.nodes]
  | cons i is ih =>
    have hr : Weighted.reject (zeroBudget (n:=n)) (i::is) x=false := by
      simp [Weighted.reject,Weighted.minimum,zeroBudget]
    simp only [Weighted.nodes,hr,Bool.false_eq_true,↓reduceIte,ih,List.length_cons]
    have hp : 0<2^(is.length+1) := by positivity
    rw [pow_succ]
    omega

theorem independent_nodes_exact (S : Finset (Fin n)) :
    independentNodes S=2^(n-S.card+1)-1 := by
  simp [independentNodes,zero_budget_nodes,Bias.length_ordered,Finset.card_compl]

end Max2SAT.Regular
