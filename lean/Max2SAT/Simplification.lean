import Max2SAT.Reduction

namespace Max2SAT

/-- Feasibility-preserving domination, available for an eager simplifier.
The side condition is necessary: an arbitrary inherited constraint need not
allow forcing the dominating literal. -/
theorem safe_domination (F : Formula n) (cs : List (Constraint n))
    (v : Literal n) (x : Assignment n) (hF : wellFormed F)
    (hu : d1 F v.neg=0) (hd : d2 F v.neg ≤ d1 F v)
    (hn : ∀ C ∈ cs, v ∉ C.terms) (hx : ∀ C ∈ cs, C.Holds x) :
    (∀ C ∈ cs, C.Holds (v.force true x)) ∧ score F x ≤ score F (v.force true x) := by
  constructor
  · intro C hC
    exact C.force_preserves v x (hn C hC) (hx C hC)
  · cases he : v.eval x
    · have h := unit_domination F v x hF hu hd
      simpa [Literal.force_eq_self v x false he] using h
    · simp [Literal.force_eq_self v x true he]
end Max2SAT
