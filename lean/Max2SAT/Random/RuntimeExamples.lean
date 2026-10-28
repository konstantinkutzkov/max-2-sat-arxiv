import Max2SAT.Random.RuntimeRates

namespace Max2SAT.Random

def cutPair : Formula 2 := [.pair ⟨0,true⟩ ⟨1,true⟩,.pair ⟨0,false⟩ ⟨1,false⟩]
def earlyReject : Formula 4 :=
  [.unit ⟨0,true⟩,.pair ⟨0,true⟩ ⟨1,true⟩,.pair ⟨2,true⟩ ⟨3,true⟩]

#eval nodeCount cutPair
#eval (outputs cutPair).length
#eval nodeCount earlyReject
#eval (outputs earlyReject).length

-- A formula with only unit clauses has no active variables; initialization
-- selects the optimal value and the node model charges one terminal call.
example : nodeCount ([.unit ⟨0,true⟩,.unit ⟨1,false⟩] : Formula 2)=1 :=
  (nodeCount_of_active_empty _ (by decide)).1
example : (outputs ([.unit ⟨0,true⟩,.unit ⟨1,false⟩] : Formula 2)).length=1 :=
  (nodeCount_of_active_empty _ (by decide)).2
example : nodeCount ([] : Formula 0)=1 := (nodeCount_of_active_empty _ (by decide)).1

-- Rejection before any branching still contributes one visited node.
example (F : Formula n) (w : Fin n → ℚ) (suffix : List (Fin n))
    (i : Fin n) (pre : List (Fin n)) (x : Assignment n)
    (cs : List (ℚ × Constraint n))
    (h : Weighted.reject (Weighted.sum cs) (i::pre++suffix) x=true) :
    nodes F w suffix (i::pre) x cs=1 ∧ enumerate F w suffix (i::pre) x cs=[] := by
  simp only [List.cons_append] at h
  simp [nodes,enumerate,h]

end Max2SAT.Random
