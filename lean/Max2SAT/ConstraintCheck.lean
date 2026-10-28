import Max2SAT.Reduction

/-! Executable cancellation and the temporary sum check. These tests only
certify infeasibility; passing a test is not a feasibility certificate. -/
namespace Max2SAT.Constraint

private theorem erase_complement (a : Literal n) (as : List (Literal n))
    (h : a.neg ∈ as) (x : Assignment n) :
    (as.map (fun v => v.value x)).sum =
      1 - a.value x + ((as.erase a.neg).map (fun v => v.value x)).sum := by
  have hp := ((List.perm_cons_erase h).map (fun v => v.value x)).sum_eq
  simpa only [List.map_cons,List.sum_cons,Literal.neg_value] using hp

/-- Cancel complementary occurrences, counting repetitions separately.
Fuel is initialized to the number of occurrences, so every recursive call
consumes at least one occurrence. -/
def cancelAux : ℕ → Constraint n → Constraint n
  | 0, C => C
  | fuel+1, C => match C.terms with
    | [] => C
    | a::as =>
      if a.neg ∈ as then cancelAux fuel ⟨as.erase a.neg,C.bound-1⟩
      else let D := cancelAux fuel ⟨as,C.bound⟩
           ⟨a::D.terms,D.bound⟩

theorem cancelAux_exact (fuel : ℕ) (C : Constraint n) (x : Assignment n) :
    (cancelAux fuel C).lhs x - (cancelAux fuel C).bound = C.lhs x-C.bound := by
  induction fuel generalizing C with
  | zero => rfl
  | succ fuel ih =>
    rcases C with ⟨terms,b⟩
    cases terms with
    | nil => rfl
    | cons a as =>
      by_cases h : a.neg ∈ as
      · simp only [cancelAux,ite_eq_left h]
        rw [ih]
        have he := erase_complement a as h x
        simp only [lhs,List.map_cons,List.sum_cons]
        omega
      · simp only [cancelAux,ite_eq_right h,lhs,List.map_cons,List.sum_cons]
        have he := ih (Constraint.mk as b)
        simp only [lhs] at he
        omega

def normalize (C : Constraint n) : Constraint n := cancelAux C.terms.length C

theorem normalize_iff (C : Constraint n) (x : Assignment n) :
    (normalize C).Holds x ↔ C.Holds x := by
  have h := cancelAux_exact C.terms.length C x
  simp only [Holds,normalize] at *
  omega

/-- Substitute the already assigned coordinates of the current Boolean cube. -/
def restrict (free : Finset (Fin n)) (x : Assignment n) (C : Constraint n) : Constraint n :=
  ⟨C.terms.filter (fun a => a.var ∈ free),
    C.bound - ((C.terms.filter (fun a => a.var ∉ free)).map (fun a => a.value x)).sum⟩

theorem restrict_exact (free : Finset (Fin n)) (x y : Assignment n)
    (h : ∀ i, i ∉ free → y i=x i) (C : Constraint n) :
    (restrict free x C).lhs y - (restrict free x C).bound = C.lhs y-C.bound := by
  have hs : ((C.terms.filter (fun a => a.var ∈ free)).map (fun a => a.value y)).sum +
      ((C.terms.filter (fun a => a.var ∉ free)).map (fun a => a.value x)).sum = C.lhs y := by
    unfold lhs
    induction C.terms with
    | nil => simp
    | cons a as ih =>
      by_cases ha : a.var ∈ free
      · simpa [List.filter_cons,ha,add_assoc,add_left_comm,add_comm] using
          congrArg (fun z : ℤ => a.value y+z) ih
      · have hv : a.value x=a.value y := by simp [Literal.value,Literal.eval,h a.var ha]
        simpa [List.filter_cons,ha,hv,add_assoc,add_left_comm,add_comm] using
          congrArg (fun z : ℤ => a.value y+z) ih
  simp only [restrict,lhs] at hs ⊢
  omega

theorem restrict_iff (free : Finset (Fin n)) (x y : Assignment n)
    (h : ∀ i, i ∉ free → y i=x i) (C : Constraint n) :
    (restrict free x C).Holds y ↔ C.Holds y := by
  have := restrict_exact free x y h C
  simp only [Holds]
  omega

def infeasible (C : Constraint n) : Bool := decide ((normalize C).bound < 0)

theorem infeasible_sound (C : Constraint n) (h : infeasible C=true) :
    ∀ x, ¬ C.Holds x := by
  have hn : (normalize C).bound < 0 := by simpa [infeasible] using h
  intro x hx
  exact negative_bound_infeasible _ hn x ((normalize_iff C x).mpr hx)

/-- Check each substituted constraint and their temporary sum. -/
def reject (free : Finset (Fin n)) (x : Assignment n) (cs : List (Constraint n)) : Bool :=
  let ds := cs.map (restrict free x)
  ds.any infeasible || infeasible (sum ds)

theorem reject_sound (free : Finset (Fin n)) (x y : Assignment n)
    (hxy : ∀ i, i ∉ free → y i=x i) (cs : List (Constraint n))
    (hr : reject free x cs=true) : ¬ ∀ C ∈ cs, C.Holds y := by
  intro hc
  have hd : ∀ D ∈ cs.map (restrict free x), D.Holds y := by
    intro D hD
    rcases List.mem_map.mp hD with ⟨C,hC,rfl⟩
    exact (restrict_iff free x y hxy C).mpr (hc C hC)
  simp only [reject,Bool.or_eq_true] at hr
  rcases hr with hi | hs
  · rcases List.any_eq_true.mp hi with ⟨D,hD,hbad⟩
    exact infeasible_sound D hbad y (hd D hD)
  · exact infeasible_sound _ hs y (holds_sum _ y hd)
end Max2SAT.Constraint
