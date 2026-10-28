import Max2SAT.Counts.RoundPassing
import Max2SAT.Counts.GainStructure

/-! Round boundaries, skipped empty rounds, and simultaneous nonzero
later/within contributions. These supplement the general kernel proofs. -/
namespace Max2SAT.Counts.RoundExamples
noncomputable section

def H : Fin 3 → Affine 3 := fun t => ⟨0,fun w => if t=w then 0 else 1⟩
def rho : Fin 3 → ℕ := fun t => if t=2 then 1 else 0
def x : Assignment 3 := fun _ => false

example : (compensation H (roundPrefix rho 1) rho x : ℝ)= -2 := by
  norm_num [compensation,H,roundPrefix,rho,x,preference,Affine.average,
    earlier,direction,Finset.sum_filter,Fin.sum_univ_succ]

example : laterCompensation H (roundPrefix rho 1) rho x= -1 := by
  norm_num [laterCompensation,laterIncoming,H,roundPrefix,rho,x,preference,Affine.average,
    earlier,RandomInput.sign,Finset.sum_filter,Fin.sum_univ_succ]

example : withinRound H rho 0 x= -1 := by
  rw [within_round_eq]
  norm_num [withinTotal,H,roundBlock,rho,x,preference,Affine.average,
    earlier,RandomInput.sign,Finset.sum_filter,Fin.sum_univ_succ]

/-- Empty intermediate rounds have no same-round contribution. -/
example : withinRound H (fun t => 2*rho t) 1 x=0 := by
  rw [within_round_eq]
  norm_num [withinTotal,roundBlock,rho,Finset.sum_filter,Fin.sum_univ_succ]

/-- There is no later-round contribution in the first block. -/
example : laterIncoming H (roundPrefix rho 1) rho x 0=0 := by
  apply later_first_round_zero
  norm_num [rho]

end
end Max2SAT.Counts.RoundExamples
