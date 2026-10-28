import Max2SAT.Reduction

/-! Incidence identities that hold with arbitrary clause multiplicities.
The column bound is independent of the chosen preferred polarities. -/
namespace Max2SAT.Bias

def pos (i : Fin n) : Literal n := ⟨i,true⟩
def preferred (p : Fin n → Bool) (i : Fin n) : Literal n := ⟨i,p i⟩

def clauseD (i : Fin n) : Clause n → ℕ
  | .unit _ => 0
  | .pair a b => (if a.var=i then 1 else 0)+(if b.var=i then 1 else 0)
def clauseU (i : Fin n) : Clause n → ℕ
  | .unit a => if a.var=i then 1 else 0
  | .pair _ _ => 0

def D (F : Formula n) (i : Fin n) : ℕ := (F.map (clauseD i)).sum
def U (F : Formula n) (i : Fin n) : ℕ := (F.map (clauseU i)).sum
def B (F : Formula n) (i : Fin n) : ℕ := D F i+U F i

def termCount (terms : List (Literal n)) (i : Fin n) : ℕ :=
  terms.countP (fun a => a.var == i)

theorem clause_cut_length (c : Clause n) (v : Literal n) (h : c.WellFormed) :
    (c.cutPart v).1.length=clauseD v.var c := by
  rcases v with ⟨i,p⟩
  cases c with
  | unit a => simp [Clause.cutPart,clauseD]; split_ifs <;> rfl
  | pair a b =>
    rcases a with ⟨j,q⟩; rcases b with ⟨k,r⟩
    change j≠k at h
    by_cases hj : j=i
    · subst j; cases p <;> cases q <;> cases r <;>
        simp [Clause.cutPart,clauseD,Literal.neg,Literal.mk.injEq,Ne.symm h]
    · by_cases hk : k=i
      · subst k; cases p <;> cases q <;> cases r <;>
          simp [Clause.cutPart,clauseD,Literal.neg,Literal.mk.injEq,h]
      · cases p <;> cases q <;> cases r <;>
          simp [Clause.cutPart,clauseD,Literal.neg,Literal.mk.injEq,hj,hk]

theorem pruning_length (F : Formula n) (v : Literal n) (hF : wellFormed F) :
    (pruningConstraint F v).terms.length=D F v.var := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    have hc := clause_cut_length c v (hF c (by simp))
    have ht := ih (fun a ha => hF a (by simp [ha]))
    simpa [pruningConstraint,D,List.length_flatMap] using congrArg₂ (·+·) hc ht

theorem clause_cut_count (c : Clause n) (p : Fin n → Bool) (i w : Fin n)
    (h : c.WellFormed) :
    termCount (c.cutPart (preferred p i)).1 w =
      match c with
      | .unit _ => 0
      | .pair a b =>
          (if i=a.var then (if b.var=w then 1 else 0) else 0)+
          (if i=b.var then (if a.var=w then 1 else 0) else 0) := by
  cases c with
  | unit a => simp only [Clause.cutPart]; split_ifs <;> simp [termCount]
  | pair a b =>
    rcases a with ⟨j,q⟩; rcases b with ⟨k,r⟩
    change j≠k at h
    by_cases hj : j=i
    · subst j; cases hp : p i <;> cases q <;> cases r <;>
        simp [Clause.cutPart,preferred,termCount,Literal.neg,Literal.mk.injEq,h,Ne.symm h,hp]
    · by_cases hk : k=i
      · subst k; cases hp : p i <;> cases q <;> cases r <;>
          simp [Clause.cutPart,preferred,termCount,Literal.neg,Literal.mk.injEq,h,Ne.symm h,hp]
      · cases hp : p i <;> cases q <;> cases r <;>
          simp [Clause.cutPart,preferred,termCount,Literal.neg,Literal.mk.injEq,
            hj,hk,Ne.symm hj,Ne.symm hk,hp]

/-- Across one comparison per variable, a column contains exactly the original
binary occurrences of that variable. No disjoint-neighborhood hypothesis is used. -/
theorem column_count (F : Formula n) (p : Fin n → Bool) (w : Fin n)
    (hF : wellFormed F) :
    (∑ i : Fin n, termCount (pruningConstraint F (preferred p i)).terms w)=D F w := by
  induction F with
  | nil => simp [pruningConstraint,termCount,D]
  | cons c F ih =>
    have ht := ih (fun a ha => hF a (by simp [ha]))
    have hc := fun i => clause_cut_count c p i w (hF c (by simp))
    simp only [pruningConstraint,List.flatMap_cons,termCount,List.countP_append]
    rw [Finset.sum_add_distrib]
    change (∑ i : Fin n, termCount (c.cutPart (preferred p i)).1 w)+_ = _
    simp_rw [hc]
    cases c with
    | unit a => simpa [D,clauseD,termCount,pruningConstraint] using ht
    | pair a b => simpa [Finset.sum_add_distrib,D,clauseD,termCount,pruningConstraint,add_comm,add_left_comm,add_assoc] using ht

private theorem clause_degrees (c : Clause n) (i : Fin n) (h : c.WellFormed) :
    (clauseD i c : ℤ)=c.binaryCount (pos i)+c.binaryCount (pos i).neg ∧
    (clauseU i c : ℤ)=c.unitCount (pos i)+c.unitCount (pos i).neg := by
  cases c with
  | unit a =>
    rcases a with ⟨j,p⟩
    by_cases hj : j=i
    · subst j; cases p <;> simp [clauseD,clauseU,Clause.binaryCount,Clause.unitCount,pos,Literal.neg]
    · cases p <;> simp [clauseD,clauseU,Clause.binaryCount,Clause.unitCount,pos,Literal.neg,hj,Literal.mk.injEq]
  | pair a b =>
    rcases a with ⟨j,p⟩; rcases b with ⟨k,q⟩
    change j≠k at h
    by_cases hj : j=i
    · subst j; cases p <;> cases q <;>
        simp [clauseD,clauseU,Clause.binaryCount,Clause.unitCount,pos,Literal.neg,Ne.symm h,Literal.mk.injEq]
    · by_cases hk : k=i
      · subst k; cases p <;> cases q <;>
          simp [clauseD,clauseU,Clause.binaryCount,Clause.unitCount,pos,Literal.neg,h,Literal.mk.injEq]
      · cases p <;> cases q <;>
          simp [clauseD,clauseU,Clause.binaryCount,Clause.unitCount,pos,Literal.neg,hj,hk,Literal.mk.injEq]

theorem degree_counts (F : Formula n) (i : Fin n) (hF : wellFormed F) :
    (D F i : ℤ)=d2 F (pos i)+d2 F (pos i).neg ∧
    (U F i : ℤ)=d1 F (pos i)+d1 F (pos i).neg := by
  induction F with
  | nil => simp [D,U,d1,d2]
  | cons c F ih =>
    rcases clause_degrees c i (hF c (by simp)) with ⟨hD,hU⟩
    rcases ih (fun a ha => hF a (by simp [ha])) with ⟨htD,htU⟩
    simp only [D,U,d1,d2,List.map_cons,List.sum_cons,Nat.cast_add] at *
    constructor <;> omega

def gap (F : Formula n) (i : Fin n) : ℤ :=
  d2 F (pos i)-d2 F (pos i).neg+2*(d1 F (pos i)-d1 F (pos i).neg)

def initialPreference (F : Formula n) (i : Fin n) : Bool := decide (0≤gap F i)

end Max2SAT.Bias
