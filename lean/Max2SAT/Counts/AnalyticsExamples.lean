import Max2SAT.Counts.GapBridge
import Max2SAT.Counts.CreatorTail
import Max2SAT.Counts.OperatorEnergy
import Max2SAT.Counts.RoundCompensation

/-! Small boundary calculations that supplement the universal proofs.
They check the sign and the two factors of 1/4 in the round expansion. -/
namespace Max2SAT.Counts.AnalyticsExamples
open FiniteLaw RandomInput
noncomputable section

def edge : Fin 2 → Fin 2 → ℝ := fun t w => if t=w then 0 else 1

example : roundCompensation edge (fun _ => true) (fun _ => false) = -1 := by
  norm_num [roundCompensation,edge,sign,Fin.sum_univ_two]

example : roundCompensation edge (fun _ => true) (fun i => i==0) = 1/2 := by
  norm_num [roundCompensation,edge,sign,Fin.sum_univ_two]

example : roundCompensation edge (fun _ => true) (fun _ => true) = 0 := by
  norm_num [roundCompensation]

/-- At a zero gap, true remains the preferred bit. -/
example : preference (fun _ : Fin 1 => Affine.zero) (fun _ => 0)
    (fun _ => false) 0 = true := by
  norm_num [preference,Affine.average,Affine.zero]

example : gapProxy (fun _ : Fin 1 => (10:ℝ)) (fun _ => 0) 2=1/2 := by
  norm_num [gapProxy]

end
end Max2SAT.Counts.AnalyticsExamples
