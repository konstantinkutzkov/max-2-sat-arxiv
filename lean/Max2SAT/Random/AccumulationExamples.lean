import Max2SAT.Random.CandidateProbability
import Max2SAT.Random.ProbabilityExamples

/-! Kernel-checked regressions for the complete accumulation bounds and
for exact feasibility at the boundary of a strict comparison. -/
namespace Max2SAT.RandomInput.AccumulationExamples
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {E : Finset (Edge n)}

example (E : Finset (Edge n)) (F : Formula n) : candidateCount E F ∅ = 2^n := by
  simp [candidateCount,comparisonSum]

example (K : E → Pattern m) (units : List (Literal n)) (z : ExposureBit E → Bool) :
    requirements K units ∅ z = 0 ∧ compensation K units ∅ (supportWeight E) z = 0 := by
  simp [requirements,compensation]

/-- A pattern outside the allowed support has a bounded extension. It
never changes the statistic at any positive-probability allowed pattern. -/
example : clippedPattern (fun _ : Signs => (4 : Fin 5)) = (0 : Pattern 4) := by
  simp [clippedPattern,size]

example : requirementConstant 4 1 ≤ 1/16 := by
  have h := requirement_constant_bound (by norm_num : 0<4) (by norm_num : (0:ℝ)<1)
  norm_num at h
  exact h

open Examples in
example :
    expect (product (fun _ : support => oneClauseModel.law))
      (fun K => (candidateCount support (generate support K fixedUnits) {0,1} : ℝ)) ≤
        24*Real.exp (-runtimeConstant 4 1*3) := by
  have hd : ∀ i∈({0,1} : Finset (Fin 3)), 0 < (incident support i).card := by
    intro i _
    fin_cases i <;> decide
  have h := fixed_support_candidate_expectation (fun _ : support => oneClauseModel)
    (by norm_num) (by norm_num) fixedUnits {0,1} (by decide) hd (by decide)
  norm_num at h
  simpa only [neg_mul] using h

def onlyEdge : Edge 2 := ⟨(0,1),by decide⟩
def onlySupport : Finset (Edge 2) := {onlyEdge}
def cutPattern : onlySupport → Pattern 4 := fun _ => Examples.antipodal

def cutAssignment : ExposureBit onlySupport → Bool
  | .inl i => decide (i=1)
  | .inr _ => true

/-- On the two-edge-clause Max-Cut encoding, the assignment (0,1)
strictly improves the first variable's alternative. A+Q is exactly zero,
so the weak feasibility test must retain this boundary assignment. -/
example : comparisonSum onlySupport
    (generate onlySupport (sampled cutPattern cutAssignment) []) {0}
    (assignment cutAssignment) = 0 := by
  have he : ∀ e : onlySupport, e.val=onlyEdge := by
    intro e
    simpa [onlySupport] using e.property
  have hd := generated_delta onlySupport (sampled cutPattern cutAssignment) []
    (orderedFree 0) 0 (assignment cutAssignment) (by simp)
  have hg := generated_gain onlySupport (sampled cutPattern cutAssignment) [] 0 (assignment cutAssignment)
  norm_num [he,onlyEdge,unitBias,edgeDelta,sampled,cutPattern,rho,cutAssignment,
    signedFlip,flip,flipSigns,Examples.antipodal,signedCount,pairGain,endpoint,sign,
    Fintype.sum_prod_type,orderedFree,assignment] at hd hg
  simp only [comparisonSum,Finset.sum_singleton,Fin.val_zero]
  simp only [show (orderedFree 0 : Finset (Fin 2))=Finset.univ by simp [orderedFree], hd,hg]
  norm_num [sign,assignment,cutAssignment,onlySupport]

end
end Max2SAT.RandomInput.AccumulationExamples
