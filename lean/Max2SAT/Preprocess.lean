import Max2SAT.Reduction

/-! Executable preprocessing. Search all pairs of clauses for opposite units
or two binary clauses that resolve to a unit, recording the score offset.
The original formula is a list, so multiplicities are preserved. -/
namespace Max2SAT

def reducePair (c d : Clause n) : Option (Formula n × ℤ) :=
  match c,d with
  | .unit a,.unit b => if b=a.neg then some ([],1) else none
  | .pair a b,.pair c d =>
    if a=c ∧ d=b.neg then some ([.unit a],1)
    else if a=d ∧ c=b.neg then some ([.unit a],1)
    else if b=c ∧ d=a.neg then some ([.unit b],1)
    else if b=d ∧ c=a.neg then some ([.unit b],1)
    else none
  | _,_ => none

theorem reducePair_sound (c d : Clause n) (G : Formula n) (s : ℤ)
    (h : reducePair c d=some (G,s)) : EquivalentWithOffset [c,d] G s := by
  cases c with
  | unit a =>
    cases d with
    | unit b =>
      simp only [reducePair] at h
      split at h
      · rename_i hab
        cases h; subst b
        exact unit_cancellation a []
      · simp at h
    | pair b c => simp [reducePair] at h
  | pair a b =>
    cases d with
    | unit c => simp [reducePair] at h
    | pair c d =>
      simp only [reducePair] at h
      split at h
      · rename_i hab
        rcases hab with ⟨rfl,rfl⟩
        cases h; exact pair_reduction _ _ []
      · split at h
        · rename_i hab
          rcases hab with ⟨rfl,rfl⟩
          cases h
          intro x
          simp only [score_cons,score_nil]
          simp only [Clause.pair_score]
          simp only [Clause.score,Literal.neg_value]
          ring
        · split at h
          · rename_i hab
            rcases hab with ⟨rfl,rfl⟩
            cases h
            intro x
            simp only [score_cons,score_nil]
            simp only [Clause.pair_score]
            simp only [Clause.score,Literal.neg_value]
            ring
          · split at h
            · rename_i hab
              rcases hab with ⟨rfl,rfl⟩
              cases h
              intro x
              simp only [score_cons,score_nil]
              simp only [Clause.pair_score]
              simp only [Clause.score,Literal.neg_value]
              ring
            · simp at h

/-- Try reducing the first clause against each remaining clause. -/
def reduceWith (c : Clause n) : Formula n → Option (Formula n × ℤ)
  | [] => none
  | d::ds => match reducePair c d with
    | some (G,s) => some (G++ds,s)
    | none => match reduceWith c ds with
      | none => none
      | some (G,s) => some (d::G,s)

theorem reduceWith_sound (c : Clause n) (F G : Formula n) (s : ℤ)
    (h : reduceWith c F=some (G,s)) : EquivalentWithOffset (c::F) G s := by
  induction F generalizing G s with
  | nil => simp [reduceWith] at h
  | cons d ds ih =>
    simp only [reduceWith] at h
    cases hp : reducePair c d with
    | some pair =>
      rcases pair with ⟨H,t⟩
      simp only [hp] at h
      cases h
      have hh := reducePair_sound c d H s hp
      intro x
      have hx := hh x
      simp only [score_cons,score_nil] at hx
      simp only [score_cons,score_append]
      omega
    | none =>
      simp only [hp] at h
      cases ht : reduceWith c ds with
      | none => simp [ht] at h
      | some pair =>
        rcases pair with ⟨H,t⟩
        simp only [ht] at h
        cases h
        have hh := ih H s ht
        intro x
        have hx := hh x
        simp only [score_cons] at *
        omega

/-- Find the first available rule, scanning pairs of clauses in list order. -/
def preprocessStep : Formula n → Option (Formula n × ℤ)
  | [] => none
  | c::cs => match reduceWith c cs with
    | some r => some r
    | none => match preprocessStep cs with
      | none => none
      | some (G,s) => some (c::G,s)

theorem preprocessStep_sound (F G : Formula n) (s : ℤ)
    (h : preprocessStep F=some (G,s)) : EquivalentWithOffset F G s := by
  induction F generalizing G s with
  | nil => simp [preprocessStep] at h
  | cons c cs ih =>
    simp only [preprocessStep] at h
    cases hp : reduceWith c cs with
    | some pair =>
      simp only [hp] at h
      cases h
      exact reduceWith_sound c cs G s hp
    | none =>
      simp only [hp] at h
      cases ht : preprocessStep cs with
      | none => simp [ht] at h
      | some pair =>
        rcases pair with ⟨H,t⟩
        simp only [ht] at h
        cases h
        have hh := ih H s ht
        intro x
        have hx := hh x
        simp only [score_cons] at *
        omega

def preprocessAux : ℕ → Formula n → Formula n × ℤ
  | 0,F => (F,0)
  | fuel+1,F => match preprocessStep F with
    | none => (F,0)
    | some (G,s) => let (H,t) := preprocessAux fuel G; (H,s+t)

theorem preprocessAux_sound (fuel : ℕ) (F : Formula n) :
    EquivalentWithOffset F (preprocessAux fuel F).1 (preprocessAux fuel F).2 := by
  induction fuel generalizing F with
  | zero => intro x; simp [preprocessAux]
  | succ fuel ih =>
    simp only [preprocessAux]
    cases hp : preprocessStep F with
    | none => intro x; simp
    | some pair =>
      rcases pair with ⟨G,s⟩
      exact offset_trans (preprocessStep_sound F G s hp) (ih G)

def preprocess (F : Formula n) : Formula n × ℤ := preprocessAux F.length F

theorem preprocess_correct (F : Formula n) :
    EquivalentWithOffset F (preprocess F).1 (preprocess F).2 :=
  preprocessAux_sound F.length F
private theorem reducePair_shape (c d : Clause n) (G : Formula n) (s : ℤ)
    (h : reducePair c d=some (G,s)) : wellFormed G ∧ G.length < 2 := by
  cases c <;> cases d <;> simp only [reducePair] at h
  all_goals try split_ifs at h
  all_goals cases h <;> simp [wellFormed,Clause.WellFormed]

private theorem reduceWith_shape (c : Clause n) (F G : Formula n) (s : ℤ)
    (hF : wellFormed (c::F)) (h : reduceWith c F=some (G,s)) :
    wellFormed G ∧ G.length < (c::F).length := by
  induction F generalizing G s with
  | nil => simp [reduceWith] at h
  | cons d ds ih =>
    simp only [reduceWith] at h
    cases hp : reducePair c d with
    | some pair =>
      rcases pair with ⟨H,t⟩
      simp only [hp] at h
      cases h
      rcases reducePair_shape c d H s hp with ⟨hw,hl⟩
      constructor
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hw a ha
        · exact hF a (by simp [ha])
      · simp only [List.length_append,List.length_cons]; omega
    | none =>
      simp only [hp] at h
      cases ht : reduceWith c ds with
      | none => simp [ht] at h
      | some pair =>
        rcases pair with ⟨H,t⟩
        simp only [ht] at h
        cases h
        rcases ih H s (fun a ha => hF a (by simpa only [List.mem_cons] using (List.mem_cons.mp ha).elim Or.inl (fun h => Or.inr (Or.inr h)))) ht with ⟨hw,hl⟩
        constructor
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact hF a (by simp)
          · exact hw a ha
        · simp only [List.length_cons] at *; omega

private theorem preprocessStep_shape (F G : Formula n) (s : ℤ)
    (hF : wellFormed F) (h : preprocessStep F=some (G,s)) :
    wellFormed G ∧ G.length < F.length := by
  induction F generalizing G s with
  | nil => simp [preprocessStep] at h
  | cons c cs ih =>
    simp only [preprocessStep] at h
    cases hp : reduceWith c cs with
    | some pair =>
      simp only [hp] at h
      cases h
      exact reduceWith_shape c cs G s hF hp
    | none =>
      simp only [hp] at h
      cases ht : preprocessStep cs with
      | none => simp [ht] at h
      | some pair =>
        rcases pair with ⟨H,t⟩
        simp only [ht] at h
        cases h
        rcases ih H s (fun a ha => hF a (by simp [ha])) ht with ⟨hw,hl⟩
        constructor
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact hF a (by simp)
          · exact hw a ha
        · simpa using hl

/-- The available fuel suffices to reach a fixed point of these two rules. -/
theorem preprocessAux_finished (fuel : ℕ) (F : Formula n)
    (hF : wellFormed F) (hf : F.length ≤ fuel) :
    wellFormed (preprocessAux fuel F).1 ∧
      preprocessStep (preprocessAux fuel F).1 = none := by
  induction fuel generalizing F with
  | zero =>
    have he : F=[] := List.length_eq_zero_iff.mp (by omega)
    subst F
    simp [preprocessAux,preprocessStep,wellFormed]
  | succ fuel ih =>
    simp only [preprocessAux]
    cases hp : preprocessStep F with
    | none => exact ⟨hF,hp⟩
    | some pair =>
      rcases pair with ⟨G,s⟩
      rcases preprocessStep_shape F G s hF hp with ⟨hw,hl⟩
      exact ih G hw (by omega)

theorem preprocess_finished (F : Formula n) (hF : wellFormed F) :
    wellFormed (preprocess F).1 ∧ preprocessStep (preprocess F).1=none :=
  preprocessAux_finished F.length F hF (le_refl _)

end Max2SAT
