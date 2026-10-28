import Max2SAT.Counts.TwoRounds
import Max2SAT.Counts.GridPrograms

namespace Max2SAT.Counts

-- The two-round indexing agrees with the paper on an odd input size:
-- two variables in each prefix round, and five in the suffix.
example : (List.finRange 9).map (twoRound 9)=[0,0,1,1,2,2,2,2,2] := by decide
example : (roundPrefix (twoRound 9) 2).card=4 := by rw [two_round_prefix_card]
example : (roundPrefix (twoRound 0) 2).card=0 := by rw [two_round_prefix_card]

-- The smooth approximation preserves both endpoints and raises the corner.
example : smoothAbs 2 (-2)=2 ∧ smoothAbs 2 0=1 ∧ smoothAbs 2 2=2 := by
  norm_num [smoothAbs]
example : smoothSlope 2 (-2)= -1 ∧ smoothSlope 2 0=0 ∧ smoothSlope 2 2=1 := by
  norm_num [smoothSlope]

-- The probability bridge also covers the zero-coordinate cube: it has
-- one assignment, not no assignments.
example : FiniteLaw.prob (FiniteLaw.fairBits (Fin 0)) (fun _ => True)=1 := by
  rw [fair_probability_bridge]
  simp [FairCoin.probability,FairCoin.average]

-- A norm-only quadratic bound requires a zero diagonal. A one-coordinate
-- diagonal term is constant, rather than a centered sign product.
example : quadraticTerm (fun _ _ : Fin 1 => (4:ℝ)) (fun _ => false)= -1 := by
  norm_num [quadraticTerm,RandomInput.sign]

end Max2SAT.Counts
