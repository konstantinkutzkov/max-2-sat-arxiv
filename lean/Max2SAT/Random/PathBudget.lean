import Max2SAT.Random.SearchNodes

namespace Max2SAT.Residual

theorem clause_congr (c : Clause n) (free : Finset (Fin n)) (x y : Assignment n)
    (hc : Compatible free x y) : clause free x c=clause free y c := by
  have he : ∀ a : Literal n, a.var∉free → a.eval x=a.eval y := by
    intro a ha
    simp [Literal.eval,hc a.var ha]
  cases c with
  | unit a =>
    by_cases ha : a.var∈free
    · simp [clause,ha]
    · simp [clause,ha,Literal.value,he a ha]
  | pair a b =>
    by_cases ha : a.var∈free <;> by_cases hb : b.var∈free
    · simp [clause,ha,hb]
    · simp [clause,ha,hb,he b hb]
    · simp [clause,ha,hb,he a ha]
    · simp [clause,ha,hb,Clause.score,he a ha,he b hb]

theorem restrict_congr (F : Formula n) (free : Finset (Fin n)) (x y : Assignment n)
    (hc : Compatible free x y) : restrict free x F=restrict free y F := by
  simp only [restrict,clause_congr _ free x y hc]

end Max2SAT.Residual

namespace Max2SAT.Random

theorem branch_literal_congr (F : Formula n) (free : List (Fin n)) (x y : Assignment n)
    (hc : Compatible free.toFinset x y) (i : Fin n) :
    branchLiteral F free x i=branchLiteral F free y i := by
  simp only [branchLiteral,Residual.restrict_congr F free.toFinset x y hc]

theorem branch_cut_congr (F : Formula n) (free : List (Fin n)) (x y : Assignment n)
    (hc : Compatible free.toFinset x y) (i : Fin n) :
    branchCut F free x i=branchCut F free y i := by
  simp only [branchCut,Residual.restrict_congr F free.toFinset x y hc,
    branch_literal_congr F free x y hc i]

/-- Construct the comparisons along a complete assignment even when the
actual search would have rejected an earlier prefix. -/
def pathExcess (F : Formula n) (w : Fin n → ℚ) (suffix : List (Fin n)) :
    List (Fin n) → Assignment n → ℚ
  | [], _ => 0
  | i::is, y =>
    let v := branchLiteral F (i::is++suffix) y i
    let C := branchCut F (i::is++suffix) y i
    (if y i≠v.positive then w i*((C.lhs y:ℚ)-C.bound) else 0)+pathExcess F w suffix is y

theorem weighted_excess_cons (w : ℚ) (C : Constraint n) (cs : List (ℚ × Constraint n))
    (y : Assignment n) :
    (Weighted.sum ((w,C)::cs)).lhs y-(Weighted.sum ((w,C)::cs)).bound =
      w*((C.lhs y:ℚ)-C.bound)+((Weighted.sum cs).lhs y-(Weighted.sum cs).bound) := by
  rw [Weighted.sum_lhs,Weighted.sum_lhs]
  simp only [List.map_cons,List.sum_cons,Weighted.sum]
  ring

/-- Only this implication is needed: early rejection may remove assignments
that satisfy the final sum, but cannot create extra outputs. -/
theorem output_path_budget (F : Formula n) (w : Fin n → ℚ)
    (suffix pre : List (Fin n)) (x y : Assignment n) (cs : List (ℚ × Constraint n))
    (hn : (pre++suffix).Nodup) (hy : y∈enumerate F w suffix pre x cs) :
    (Weighted.sum cs).lhs y-(Weighted.sum cs).bound+pathExcess F w suffix pre y≤0 := by
  induction pre generalizing x cs with
  | nil =>
    have h := ((Weighted.mem_enumerate _ suffix x y (by simpa using hn)).mp hy).2
    simpa [pathExcess,Weighted.Budget.Holds,sub_nonpos] using h
  | cons i is ih =>
    have hi := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    have hc := output_compatible F w suffix (i::is) x y cs hn hy
    have hv := branch_literal_congr F (i::is++suffix) x y hc i
    have hC := branch_cut_congr F (i::is++suffix) x y hc i
    simp only [enumerate] at hy
    split at hy
    · simp at hy
    · rcases List.mem_append.mp hy with hy | hy
      · have hb := (output_compatible F w suffix is _ y cs ht hy) i (by simpa using hi)
        have he : y i=(branchLiteral F (i::is++suffix) y i).positive := by
          rw [←hv]
          simpa [Literal.force,branchLiteral] using hb
        have h := ih _ cs ht hy
        simpa [pathExcess,he] using h
      · have hb := (output_compatible F w suffix is _ y _ ht hy) i (by simpa using hi)
        have he : y i≠(branchLiteral F (i::is++suffix) y i).positive := by
          rw [←hv]
          simp only [Literal.force,show (branchLiteral F (i::is++suffix) x i).var=i from rfl,
            Function.update_self] at hb
          cases hp : (branchLiteral F (i::is++suffix) x i).positive <;> simp_all
        have h := ih _ _ ht hy
        rw [weighted_excess_cons,hC] at h
        simpa only [pathExcess,ite_eq_left he,add_left_comm,add_assoc] using h

end Max2SAT.Random
