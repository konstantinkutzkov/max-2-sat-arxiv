import Max2SAT.Regular.Encoding

namespace Max2SAT.Regular
variable {n : ℕ}

def cutSize (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Assignment n) : ℕ :=
  ∑ e∈edgeSet G, if x e.1≠x e.2 then 1 else 0

theorem cut_pair_score (i j : Fin n) (x : Assignment n) :
    score (cutPair i j) x=1+(if x i≠x j then (1:ℤ) else 0) := by
  cases hi : x i <;> cases hj : x j <;>
    simp [cutPair,score,Clause.score,Literal.eval,hi,hj]

theorem score_flatMap {α : Type*} (xs : List α) (f : α → Formula n) (x : Assignment n) :
    score (xs.flatMap f) x=(xs.map (fun a => score (f a) x)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [score_append,ih]

theorem formula_score (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) (x : Assignment n) :
    score (formula G units) x=score (units.map Clause.unit) x+(edgeSet G).card+cutSize G x := by
  rw [formula,score_append,score_flatMap,Finset.sum_map_toList]
  simp_rw [cut_pair_score]
  simp [Finset.sum_add_distrib,cutSize,add_assoc]

theorem optimal_cut_of_optimal_formula (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Assignment n) (hx : ∀ y, score (formula G []) y≤score (formula G []) x) :
    ∀ y, cutSize G y≤cutSize G x := by
  intro y
  have h := hx y
  simp only [formula_score,List.map_nil,score_nil,zero_add] at h
  exact_mod_cast (add_le_add_iff_left ((edgeSet G).card:ℤ)).mp h

end Max2SAT.Regular
