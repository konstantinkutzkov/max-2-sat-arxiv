import Max2SAT.Random.ObservedFormula
import Max2SAT.Random.EndpointSigns
import Max2SAT.Random.Exposure
import Max2SAT.Random.GainAverage
import Max2SAT.Random.AbsoluteGains
import Max2SAT.Random.Hoeffding

/-! Kernel-checked regression cases for the finite sampling models and
exposure transformations. No random testing is used as proof evidence. -/
namespace Max2SAT.RandomInput.Examples
noncomputable section
open FiniteLaw

example (left : Bool) : expect oneClause (fun K => (signedCount left K)^2) = 1 :=
  oneClause_moment left

example (left : Bool) : expect (independentClauses (1/4) (by norm_num) (by norm_num))
    (fun K => (signedCount left K)^2) = 3/4 := quarter_moment left

example (left : Bool) : expect (independentClauses 0 (by norm_num) (by norm_num))
    (fun K => (signedCount left K)^2) = 0 := by
  rw [independentClauses_moment]
  norm_num

example (left : Bool) : expect (independentClauses 1 (by norm_num) (by norm_num))
    (fun K => (signedCount left K)^2) = 0 := by
  rw [independentClauses_moment]
  norm_num

example : 0 < prob oneClause present := present_positive oneClauseModel (by norm_num)

/-- Shared multiplication preserves the whole joint law, even though the
same assignment bit is used for all three endpoint signs. -/
example : push (tensor fair (fairBits (Fin 3)))
    (fun z => (z.1,multiplyBits (fun _ : Fin 3 => z.1) z.2)) =
      tensor fair (fairBits (Fin 3)) := joint_multiply (ι := Fin 3) fair (fun b _ => b)

def e01 : Edge 3 := ⟨(0,1),by decide⟩
def e12 : Edge 3 := ⟨(1,2),by decide⟩
def support : Finset (Edge 3) := {e01,e12}
def draws : support → Pattern 4 := fun e => if e.val=e01 then onePattern (true,false) else 0
def fixedUnits : List (Literal 3) := [⟨2,true⟩,⟨2,true⟩]

example : wellFormed (generate support draws fixedUnits) := generate_wellFormed _ _ _

example : (1 : Fin 3) ∈ Random.neighbors (generate support draws fixedUnits) 0 := by
  have he : e01 ∈ support := by simp [support]
  apply (generated_edge_neighbors support draws fixedUnits ⟨e01,he⟩).mpr
  simp [draws,present]

example : (2 : Fin 3) ∉ Random.neighbors (generate support draws fixedUnits) 1 := by
  have he : e12 ∈ support := by simp [support]
  apply (generated_edge_neighbors support draws fixedUnits ⟨e12,he⟩).not.mpr
  have hn : e12 ≠ e01 := by decide
  simp [draws,hn,present,size]

example : pairGain true (signedFlip (false,true) (onePattern (true,false))) true -
    signedCount true (signedFlip (false,true) (onePattern (true,false))) / 2 = -1/2 := by
  rw [endpoint_deviation]
  norm_num [eta,pairGain,signedCount,onePattern,endpoint,sign,theta,Fintype.sum_prod_type]

/-- One repeated variable pair is an antipodal (Max-Cut) pair. It has
nontrivial sign symmetries, which the exposure construction allows. -/
def antipodal : Pattern 4 := fun s => if s=(true,true) ∨ s=(false,false) then 1 else 0
def mixedDraws : support → Pattern 4 :=
  fun e => if e.val=e01 then antipodal else onePattern (true,true)

def earlierEdge : Incidence support 1 :=
  ⟨⟨e01,by simp [support]⟩,by simp [incident,e01]⟩
def laterEdge : Incidence support 1 :=
  ⟨⟨e12,by simp [support]⟩,by simp [incident,e12]⟩

example : coefficient mixedDraws {1,2} (fun _ => true) 1 earlierEdge = -1 := by
  norm_num [coefficient,mixedDraws,earlierEdge,e01,partner,side,vertex,
    assignment,theta,pairGain,antipodal,endpoint,sign,Fintype.sum_prod_type]

example : coefficient mixedDraws {1,2} (fun _ => true) 1 laterEdge = 1/2 := by
  have hn : e12 ≠ e01 := by decide
  have hd : mixedDraws laterEdge.val = onePattern (true,true) := by
    change (if e12=e01 then antipodal else onePattern (true,true)) = _
    simp [hn]
  rw [coefficient,hd]
  norm_num [laterEdge,e12,partner,side,vertex,
    signedCount,onePattern,endpoint,sign,Fintype.sum_prod_type]

example (z : ExposureBit support → Bool) :
    push (condition (fairBits (ExposureBit support)) (history (knownBefore support {1,2}) z)
      (fair_history_positive _ z))
      (fun w e => theta (w (current 1 e)) (assignment w 1)) = fairBits (Incidence support 1) :=
  current_theta_law {1,2} 1 (by simp) z

/-- Two equal coefficients: E(rho_1 + rho_2)^4 = 8, not the
Gaussian upper bound 3Y² = 12. -/
example : expect (fairBits (Fin 2)) (fun z => (∑ i, sign (z i) * (1 : ℝ))^4) = 8 := by
  rw [signed_sum_fourth]
  norm_num

/-- With no random signs, the truncation bound still covers every shift. -/
example (b K : ℝ) (hK : 0 < K) :
    0 ≤ expect (fairBits (Fin 0)) (fun _ => min |b| K) := by
  simpa using truncated_absolute_gain (fun _ : Fin 0 => (0 : ℝ)) b K hK

/-- Truncation matters: shifting a single fair sign by one halves this
expectation. One cannot simply transfer the untruncated shift inequality. -/
example : expect fair (fun z => min |1 + sign z| 1) = 1/2 := by
  norm_num [expect, fair, sign]

/-- The Cauchy--Schwarz interpolation can be tight even with an atom at zero. -/
example : (expect fair (fun z => (if z then (2 : ℝ) else 0)^2))^3 =
    (expect fair (fun z => if z then (2 : ℝ) else 0))^2 *
      expect fair (fun z => (if z then (2 : ℝ) else 0)^4) := by
  norm_num [expect, fair]

/-- An interval bound is needed only on the support of a conditional law. -/
example (t : ℝ) :
    expect (point false) (fun z => Real.exp (t * (if z then (100 : ℝ) else 0))) ≤ 1 := by
  have h := centered_range_mgf (point false)
    (fun z => if z then (100 : ℝ) else 0) 0 0 t
    (by intro z hz; cases z <;> simp_all [point])
    (by simp)
  exact h.trans_eq (by simp)

end
end Max2SAT.RandomInput.Examples
