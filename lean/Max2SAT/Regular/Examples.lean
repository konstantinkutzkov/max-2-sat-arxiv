import Max2SAT.Regular.Runtime

namespace Max2SAT.Regular.Examples

def pathWithUnits : Formula 3 :=
  cutPair 0 1 ++ cutPair 1 2 ++ [.unit ⟨0,false⟩,.unit ⟨2,true⟩]

-- Fixed middle vertex, independent endpoints, and a tie at the left endpoint.
example : complete pathWithUnits {0,2} (fun _ => false)=(fun i => i==2) := by decide
example : Independent pathWithUnits {0,2} := by
  intro a b hc ha hb
  simp only [pathWithUnits,cutPair,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false] at hc
  rcases hc with ((h|h)|(h|h))|(h|h)
  · cases h; norm_num at hb
  · cases h; norm_num at hb
  · cases h; norm_num at ha
  · cases h; norm_num at ha
  · cases h
  · cases h
example : independentNodes ({0,2} : Finset (Fin 3))=3 := by
  rw [independent_nodes_exact]
  decide
#eval independentSolve pathWithUnits {0,2} |>.map (fun x => score pathWithUnits x)

-- The second round need not have the same size as the first.
example : (firstRound 6).card=1 ∧ (secondRound 6).card=2 := by decide
example : (firstRound 7).card=1 ∧ (secondRound 7).card=2 := by decide

-- A clique has zero corrected row energy: density must be separated from 1.
example : rowEnergy 4 3=0 := by norm_num [rowEnergy]

-- Degree zero gives a full independent set and exponential base exactly one.
example : degreeBase 0=1 := by norm_num [degreeBase]
example : (independentSet (⊥ : SimpleGraph (Fin 5))).card=5 := by
  have h := independent_set_size (⊥ : SimpleGraph (Fin 5)) 0 (by intro v; simp)
  have h' : (independentSet (⊥ : SimpleGraph (Fin 5))).card≤5 := by
    simpa using Finset.card_le_univ (independentSet (⊥ : SimpleGraph (Fin 5)))
  omega

-- No eigenvector is required for the empty input's correctness.
example (D N : ℕ) : ∃ q x, regularResult (⊥ : SimpleGraph (Fin 0)) [] D N=some (q,x) ∧
    ∀ y, cutSize (⊥ : SimpleGraph (Fin 0)) y≤cutSize ⊥ x :=
  regular_result_maxcut _ D N

end Max2SAT.Regular.Examples
