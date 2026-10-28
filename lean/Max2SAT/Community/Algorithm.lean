import Max2SAT.Community.Spacing
import Max2SAT.Counts.TwoRounds
import Max2SAT.Regular.IndependentSearch

/-! The executable search wrapper, including both exhaustive fallbacks and
the zero-coefficient case. Any total rational preprocessing routine can be
plugged in. Its approximation quality is irrelevant to exactness. -/
namespace Max2SAT.Community
open Counts
variable {n r : ℕ}

structure Representation (n r : ℕ) where
  coefficient : Fin r → ℚ
  direction : Fin r → Fin n → ℚ
  trialSpacing : ℚ

def coefficientMass (d : Representation n r) : ℚ := ∑ k, |d.coefficient k|

def remainderEnergy (F : Formula n) (d : Representation n r) : ℚ :=
  (∑ t, ∑ w, ((projectionGain F d.coefficient d.direction (fun _ => 0) t).coeff w)^2)/n

def exhaustive (F : Formula n) : Option (Assignment n) := Regular.independentSolve F ∅

def projectionPhase (F : Formula n) (d : Representation n r) : Option (Assignment n) :=
  projectionComparisons F d.coefficient d.direction (fun _ => cappedSpacing n d.trialSpacing)
    (projectionGrids d.direction (fun _ => cappedSpacing n d.trialSpacing))
    (roundPrefix (twoRound n) 2) (twoRound n)

/-- The preprocessing callback need not be correct as an approximation for
this search to be exact; approximation controls only the runtime estimate. -/
def communitySearch (F : Formula n) (prepare : Formula n → Representation n r) : Option (Assignment n) :=
  if n<4 then exhaustive F else
    let d := prepare F
    if remainderEnergy F d=0 then exhaustive F else
      if coefficientMass d=0 then countSearch F 0 (roundPrefix (twoRound n) 2) (twoRound n)
      else projectionPhase F d

def communityResult (F : Formula n) (prepare : Formula n → Representation n r) :
    Option (ℤ × Assignment n) := (communitySearch F prepare).map (fun x => (score F x,x))

def projectionNodes (F : Formula n) (d : Representation n r) : ℕ :=
  Runs.nodeCount (projectionGrids d.direction (fun _ => cappedSpacing n d.trialSpacing))
    (projectionBudget F d.coefficient d.direction (fun _ => cappedSpacing n d.trialSpacing)
      (roundPrefix (twoRound n) 2) (twoRound n)) (roundPrefix (twoRound n) 2)

def communityNodes (F : Formula n) (prepare : Formula n → Representation n r) : ℕ :=
  if n<4 then Regular.independentNodes (∅ : Finset (Fin n)) else
    let d := prepare F
    if remainderEnergy F d=0 then Regular.independentNodes (∅ : Finset (Fin n)) else
      if coefficientMass d=0 then
        Runs.nodeCount (countGuesses n 0) (countBudget F 0 (roundPrefix (twoRound n) 2) (twoRound n))
          (roundPrefix (twoRound n) 2)
      else projectionNodes F d

theorem exhaustive_correct (F : Formula n) :
    ∃ x, exhaustive F=some x ∧ ∀ y, score F y≤score F x :=
  Regular.independent_solve_correct F ∅ (by simp [Regular.Independent])

theorem projection_phase_correct (F : Formula n) (d : Representation n r)
    (hn : 0<n) (hF : wellFormed F) :
    ∃ x, projectionPhase F d=some x ∧ ∀ y, score F y≤score F x := by
  apply grid_search_correct F d.coefficient d.direction _ _ _ hF
  · exact round_prefix_closed (twoRound n) 2
  · intro k; exact capped_spacing_pos d.trialSpacing hn

/-- This covers the actual cap and all fallback branches, for every input
formula and every total rational representation-generating routine. -/
theorem community_search_correct (F : Formula n) (prepare : Formula n → Representation n r)
    (hF : wellFormed F) :
    ∃ x, communitySearch F prepare=some x ∧ ∀ y, score F y≤score F x := by
  unfold communitySearch
  split
  · exact exhaustive_correct F
  · rename_i hn
    dsimp only
    split
    · exact exhaustive_correct F
    · split
      · exact countSearch_correct F 0 _ _ hF (round_prefix_closed (twoRound n) 2)
      · exact projection_phase_correct F _ (by omega) hF

theorem community_result_correct (F : Formula n) (prepare : Formula n → Representation n r)
    (hF : wellFormed F) :
    ∃ q x, communityResult F prepare=some (q,x) ∧ q=score F x ∧ ∀ y, score F y≤q := by
  obtain ⟨x,hx,ho⟩ := community_search_correct F prepare hF
  exact ⟨score F x,x,by simp [communityResult,hx],rfl,ho⟩

theorem coefficient_mass_nonneg (d : Representation n r) : 0≤coefficientMass d :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem zero_coefficient_mass (d : Representation n r) (h : coefficientMass d=0) :
    ∀ k, d.coefficient k=0 := by
  intro k
  have hh : |d.coefficient k|≤coefficientMass d :=
    Finset.single_le_sum (fun i _ => abs_nonneg (d.coefficient i)) (Finset.mem_univ k)
  exact abs_eq_zero.mp (le_antisymm (h ▸ hh) (abs_nonneg _))

theorem zero_coefficients_gain (F : Formula n) (d : Representation n r)
    (h : coefficientMass d=0) (guess : Fin r → ℚ) (t : Fin n) :
    projectionGain F d.coefficient d.direction guess t=gainExpr F t := by
  cases he : gainExpr F t
  simp [projectionGain,zero_coefficient_mass d h,Affine.add,Affine.sum,Affine.scale,Affine.shift,he]

end Max2SAT.Community
