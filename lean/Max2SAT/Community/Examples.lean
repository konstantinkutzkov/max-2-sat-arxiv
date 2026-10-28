import Max2SAT.Community.SBMRuntime

namespace Max2SAT.Community.Examples
open Counts

-- The square-root routine uses rational/integer operations, including for
-- fractions and positive inputs whose square root is irrational.
example : rootBelow 4=2 := by norm_num [rootBelow]
example : rootBelow (1/4)=1/2 := by norm_num [rootBelow]
example : rootBelow 2=1 := by norm_num [rootBelow]
example : cappedSpacing 4 (-3)=1/16 := by norm_num [cappedSpacing]
example : cappedSpacing 4 (1/2)=1/2 := by norm_num [cappedSpacing]
example : (firstRound 11).card=2 ∧ (secondRound 11).card=3 := by decide

-- Check both exhaustive fallbacks and the zero-mass comparison branch.
def zeroRepresentation (n : ℕ) : Representation n 1 :=
  ⟨fun _ => 0, fun _ _ => 0, -1⟩
def onePair : Formula 4 := [.pair ⟨0,true⟩ ⟨1,false⟩]
#eval (computedResult ([] : Formula 0) 1 (fun _ => zeroRepresentation 0)).map Prod.fst
#eval (computedResult ([] : Formula 4) 1 (fun _ => zeroRepresentation 4)).map Prod.fst
#eval (computedResult onePair 1 (fun _ => zeroRepresentation 4)).map Prod.fst

-- A deliberately inaccurate representation still gives an exact search.
def inaccurate : Representation 4 1 := ⟨fun _ => 1, fun _ _ => 0, -1⟩
#eval (computedResult onePair 1 (fun _ => inaccurate)).map Prod.fst
example : ∃ q x, computedResult onePair 1 (fun _ => inaccurate)=some (q,x) ∧
    q=score onePair x ∧ ∀ y, score onePair y≤q :=
  computed_result_correct _ _ _ (by
    intro c hc
    simp only [onePair,List.mem_cons,List.not_mem_nil,or_false] at hc
    subst c
    decide)

-- Keep the Euclidean operator norm distinct from the entrywise function norm.
open scoped Matrix.Norms.L2Operator in
example (A : Matrix (Fin 4) (Fin 4) ℝ) :
    ‖offDiagonal A‖=‖Matrix.toEuclideanCLM (n:=Fin 4) (𝕜:=ℝ) (offDiagonal A)‖ := rfl

-- The matrix used in the search deletes the representation's diagonal.
def diagonalRepresentation : Representation 4 1 :=
  ⟨fun _ => 2, fun _ t => if t=0 then 1 else 0, 1⟩
example : representationMatrix diagonalRepresentation 0 0=2 := by
  norm_num [representationMatrix,diagonalRepresentation]
example : offDiagonal (representationMatrix diagonalRepresentation) 0 0=0 := by
  simp [offDiagonal]

-- Cross rows count distinct pairs, with no contribution from later columns.
example (z : RandomInput.Edge 4 → ℝ) :
    (∑ j∈firstRound 4, (IndependentPairs.pairMatrix z 1 j)^2)=
      (z ⟨(0,1),by decide⟩)^2 := by
  have he : firstRound 4={0} := by decide
  rw [he,Finset.sum_singleton,IndependentPairs.pair_matrix_symmetric z 1 0]
  exact congrArg (fun a : ℝ => a^2) (IndependentPairs.pair_matrix_entry z ⟨(0,1),by decide⟩)

-- Rank-zero data really selects one unadjusted run.
example : countGuesses 7 0=[0] := by simp [countGuesses]
example : coefficientMass (zeroRepresentation 4)=0 := by simp [coefficientMass,zeroRepresentation]

-- Negative coefficients, tied magnitudes, and the empty/full retained sets.
def tiedDiagonal : Fin 4 → ℚ := ![2,-5,5,0]
example : Finset.univ.map (topSelection tiedDiagonal (show 2≤4 by decide))= {1,2} := by
  norm_num [topSelection,rankedIndices,tiedDiagonal,List.finRange_succ,List.mergeSort]
  decide +kernel
example : Finset.univ.map (topSelection tiedDiagonal (show 0≤4 by decide))=∅ := by decide +kernel
example : Finset.univ.map (topSelection tiedDiagonal (show 4≤4 by decide))=Finset.univ := by
  norm_num [topSelection,rankedIndices,tiedDiagonal,List.finRange_succ,List.mergeSort]

-- A nontrivial rational orthogonal frame has exact Rayleigh coefficients.
def rationalRotation : Matrix (Fin 2) (Fin 2) ℚ := !![3/5,-4/5;4/5,3/5]
def testMatrix : Matrix (Fin 2) (Fin 2) ℚ := !![3,0;0,1]
example : rationalRotation.transpose*rationalRotation=1 := by decide +kernel
example : frameDiagonal testMatrix rationalRotation 0=43/25 := by decide +kernel
example : frameDiagonal testMatrix rationalRotation 1=57/25 := by decide +kernel
example : topSelection (frameDiagonal testMatrix rationalRotation) (show 1≤2 by decide) 0=1 := by
  norm_num [topSelection,rankedIndices,frameDiagonal,testMatrix,rationalRotation,Matrix.mul_apply,Fin.sum_univ_two,List.finRange_succ,List.mergeSort]
example : ∑ i, ((frameRepresentation testMatrix rationalRotation
    (topSelection (frameDiagonal testMatrix rationalRotation) (show 1≤2 by decide))).direction 0 i:ℝ)^2=1 :=
  frame_direction_unit _ _ _ (by decide +kernel) _

-- The new routine chooses from rational candidates, without a real root.
example : rotationC (1/2:ℚ)=3/5 ∧ rotationS (1/2:ℚ)=4/5 := by
  norm_num [rotationC,rotationS]
example : bestGridIndex 0 1 0 2=1 := by decide +kernel
example : |rotatedPivot (0:ℚ) 1 0 (gridParameter 2 (bestGridIndex 0 1 0 2))|=7/25 := by
  decide +kernel

-- A non-diagonal block is eliminated exactly by an actual grid update.
def eliminableBlock : Matrix (Fin 2) (Fin 2) ℚ := !![0,12;12,7]
example : jacobiUpdate 2 eliminableBlock=!![16,0;0,-9] := by decide +kernel
example : offEnergy (jacobiUpdate 2 eliminableBlock)=0 := by decide +kernel
example : let Q := iterateFrame 2 0 1 eliminableBlock
    offEnergy (Q.transpose*eliminableBlock*Q)=0 := by decide +kernel

-- The fully specified routine includes the empty and rank-too-large cases.
#eval (diagonalizedResult ([] : Formula 0) 0 1).map Prod.fst
#eval (diagonalizedResult ([] : Formula 4) 1 1).map Prod.fst
example : coefficientMass (discoverFormula 5 ([] : Formula 4))=0 := by decide +kernel
example : ∃ q x, diagonalizedResult onePair 5 1=some (q,x) ∧
    q=score onePair x ∧ ∀ y, score onePair y≤q :=
  diagonalized_result_correct _ _ _ (by
    intro c hc
    simp only [onePair,List.mem_cons,List.not_mem_nil,or_false] at hc
    subst c
    decide)

-- The original graph sample has one Boolean coordinate per unordered pair.
def presentEdge : RandomInput.Edge 2 → Bool := fun _ => true
def absentEdge : RandomInput.Edge 2 → Bool := fun _ => false
example : (sampledGraph presentEdge).Adj 0 1 := by simp [sampledGraph,presentEdge]
example : ¬(sampledGraph absentEdge).Adj 0 1 := by simp [sampledGraph,absentEdge]
example : interactionMatrix (gainExpr (sampledFormula presentEdge [])) 0 1= -2 := by
  rw [sampled_formula_matrix]
  norm_num [IndependentPairs.pairMatrix,IndependentPairs.cutInteraction,presentEdge]

-- A one-community model has exactly the Bernoulli variance p*(1-p).
noncomputable def halfProbability : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1/2
example : minBlockVariance (show 0<1 by decide) halfProbability=1/4 := by
  unfold minBlockVariance
  apply Finset.inf'_eq_of_forall
  intro ab _
  norm_num [halfProbability]
example : maxBlockVariance (show 0<1 by decide) halfProbability=1/4 := by
  unfold maxBlockVariance
  apply Finset.sup'_eq_of_forall
  intro ab _
  norm_num [halfProbability]

-- All vertices may occupy one group; the unused groups do not break the rank proof.
example : (blockMean (fun _ : Fin 4 => (0 : Fin 3)) (fun _ _ => (1/2:ℝ))).rank≤3 :=
  block_mean_rank _ _

-- The optimized formula still represents the ordinary maximum cut.
example : ∃ q a, diagonalizedResult (sampledFormula presentEdge []) 1 1=some (q,a) ∧
    ∀ b, Regular.cutSize (sampledGraph presentEdge) b≤Regular.cutSize (sampledGraph presentEdge) a :=
  sampled_maxcut_correct presentEdge 1 1

end Max2SAT.Community.Examples
