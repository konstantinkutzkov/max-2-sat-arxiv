import Max2SAT.Bias.Incidence
import Max2SAT.PartialAssignment

/-! Substitution in soft formulas, including exact score offsets. -/
namespace Max2SAT.Residual

def clause (free : Finset (Fin n)) (x : Assignment n) : Clause n → Formula n × ℤ
  | .unit a => if a.var ∈ free then ([.unit a],0) else ([],a.value x)
  | .pair a b =>
    if a.var ∈ free then
      if b.var ∈ free then ([.pair a b],0)
      else if b.eval x then ([],1) else ([.unit a],0)
    else if b.var ∈ free then
      if a.eval x then ([],1) else ([.unit b],0)
    else ([],Clause.score x (.pair a b))

def restrict (free : Finset (Fin n)) (x : Assignment n) (F : Formula n) : Formula n × ℤ :=
  (F.flatMap (fun c => (clause free x c).1), (F.map (fun c => (clause free x c).2)).sum)

private theorem literal_agree (a : Literal n) (free : Finset (Fin n)) (x y : Assignment n)
    (hc : Compatible free x y) (ha : a.var ∉ free) : a.eval y = a.eval x := by
  simp [Literal.eval,hc a.var ha]

theorem clause_score (c : Clause n) (free : Finset (Fin n)) (x y : Assignment n)
    (hc : Compatible free x y) :
    c.score y = (clause free x c).2 + score (clause free x c).1 y := by
  cases c with
  | unit a =>
    by_cases ha : a.var ∈ free
    · simp [clause,ha,Clause.score]
    · simp [clause,ha,Clause.score,Literal.value,literal_agree a free x y hc ha]
  | pair a b =>
    by_cases ha : a.var ∈ free <;> by_cases hb : b.var ∈ free
    · simp [clause,ha,hb]
    · have he := literal_agree b free x y hc hb
      cases h : b.eval x <;> simp [clause,ha,hb,h,Clause.score,he,Literal.value]
    · have he := literal_agree a free x y hc ha
      cases h : a.eval x <;> simp [clause,ha,hb,h,Clause.score,he,Literal.value]
    · simp [clause,ha,hb,Clause.score,literal_agree a free x y hc ha,
        literal_agree b free x y hc hb]

theorem restrict_score (F : Formula n) (free : Finset (Fin n)) (x y : Assignment n)
    (hc : Compatible free x y) :
    score F y = (restrict free x F).2 + score (restrict free x F).1 y := by
  induction F with
  | nil => simp [restrict]
  | cons c F ih =>
    have hh := clause_score c free x y hc
    simp only [restrict,List.flatMap_cons,List.map_cons,List.sum_cons,score_append,score_cons] at *
    omega

theorem restrict_wellFormed (F : Formula n) (free : Finset (Fin n)) (x : Assignment n)
    (hF : wellFormed F) : wellFormed (restrict free x F).1 := by
  intro c hc
  rcases List.mem_flatMap.mp hc with ⟨e,he,hc⟩
  have hw := hF e he
  cases e <;> simp only [clause] at hc
  all_goals split_ifs at hc <;> simp_all [Clause.WellFormed]

end Max2SAT.Residual
