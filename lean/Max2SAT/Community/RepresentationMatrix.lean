import Max2SAT.Community.Computed

namespace Max2SAT.Community
noncomputable section
open Counts
variable {n r : ℕ}

def representationMatrix (d : Representation n r) : Matrix (Fin n) (Fin n) ℝ :=
  fun t w => ∑ k, (d.coefficient k:ℝ)*(d.direction k t:ℝ)*(d.direction k w:ℝ)

theorem representation_remainder (F : Formula n) (d : Representation n r) (hF : wellFormed F) :
    interactionMatrix (projectionGain F d.coefficient d.direction (fun _ => 0))=
      offDiagonal (interactionMatrix (gainExpr F)-representationMatrix d) := by
  ext t w
  by_cases ht:t=w
  · subst w
    simp [interactionMatrix,projectionGain_diagonal F hF,offDiagonal]
  · simp only [interactionMatrix,projectionGain,Affine.add,Affine.sum,Affine.scale,Affine.shift,
      without,offDiagonal,ht,Ne.symm ht,ite_false,Matrix.sub_apply,representationMatrix]
    push_cast
    rw [sub_eq_add_neg]
    congr 1
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring

end
end Max2SAT.Community
