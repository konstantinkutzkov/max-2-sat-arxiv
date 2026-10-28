import Max2SAT.Basic

namespace Max2SAT

structure Constraint (n : ℕ) where
  terms : List (Literal n)
  bound : ℤ
  deriving Repr
namespace Constraint

def lhs (C : Constraint n) (x : Assignment n) : ℤ :=
  (C.terms.map (fun a => a.value x)).sum

def Holds (C : Constraint n) (x : Assignment n) : Prop := C.lhs x ≤ C.bound
instance (C : Constraint n) (x : Assignment n) : Decidable (C.Holds x) :=
  inferInstanceAs (Decidable (C.lhs x ≤ C.bound))

def add (C D : Constraint n) : Constraint n := ⟨C.terms ++ D.terms, C.bound+D.bound⟩
def sum (Cs : List (Constraint n)) : Constraint n := Cs.foldr add ⟨[],0⟩

@[simp] theorem lhs_nonneg (C : Constraint n) (x : Assignment n) : 0 ≤ C.lhs x := by
  exact List.sum_nonneg (fun a ha => by
    rcases List.mem_map.mp ha with ⟨v, _, rfl⟩
    exact v.value_nonneg x)

@[simp] theorem lhs_add (C D : Constraint n) (x : Assignment n) :
    (C.add D).lhs x = C.lhs x + D.lhs x := by simp [lhs, add]

theorem holds_add {C D : Constraint n} {x : Assignment n}
    (hC : C.Holds x) (hD : D.Holds x) : (C.add D).Holds x := by
  change (C.add D).lhs x ≤ C.bound + D.bound
  rw [lhs_add]
  exact add_le_add hC hD

theorem holds_sum (Cs : List (Constraint n)) (x : Assignment n)
    (h : ∀ C ∈ Cs, C.Holds x) : (sum Cs).Holds x := by
  induction Cs with
  | nil => simp [sum, Holds, lhs]
  | cons C Cs ih =>
    exact holds_add (h C (by simp)) (ih (fun D hd => h D (by simp [hd])))

theorem negative_bound_infeasible (C : Constraint n) (h : C.bound < 0) :
    ∀ x, ¬ C.Holds x := by
  intro x hx
  have hn := C.lhs_nonneg x
  simp only [Holds] at hx
  omega

theorem complementary_cancellation (v : Literal n) (terms : List (Literal n))
    (b : ℤ) (x : Assignment n) :
    (Constraint.mk (v :: v.neg :: terms) b).Holds x ↔
      (Constraint.mk terms (b-1)).Holds x := by
  simp only [Holds, lhs, List.map_cons, List.sum_cons, Literal.neg_value]
  omega

theorem sum_infeasible (Cs : List (Constraint n))
    (h : (sum Cs).bound < 0) : ¬ ∃ x, ∀ C ∈ Cs, C.Holds x := by
  rintro ⟨x,hx⟩
  exact negative_bound_infeasible _ h x (holds_sum Cs x hx)
end Constraint

/-- A scan of the formula constructs exactly the occurrence-count constraint. -/
def pruningConstraint (F : Formula n) (v : Literal n) : Constraint n :=
  ⟨F.flatMap (fun c => (c.cutPart v).1),
    (F.map (fun c => (c.cutPart v).2)).sum - 1⟩

theorem clause_gain_identity (c : Clause n) (v : Literal n) (x : Assignment n)
    (h : c.WellFormed) :
    ((c.cutPart v).1.map (fun a => a.value x)).sum - (c.cutPart v).2 =
      c.score (v.force true x) - c.score (v.force false x) := by
  rcases v with ⟨i, p⟩
  cases c with
  | unit a =>
    rcases a with ⟨j,q⟩
    by_cases hij : j = i
    · subst j
      cases p <;> cases q <;>
        simp [Clause.cutPart, Clause.score, Literal.value, Literal.eval,
          Literal.neg, Literal.force]
    · cases p <;> cases q <;>
        simp [Clause.cutPart, Clause.score, Literal.value, Literal.eval,
          Literal.neg, Literal.force, Literal.mk.injEq, hij]
  | pair a b =>
    rcases a with ⟨j,q⟩
    rcases b with ⟨k,r⟩
    change j ≠ k at h
    by_cases hj : j = i
    · subst j
      cases p <;> cases q <;> cases r <;> cases hx : x k <;>
        simp [Clause.cutPart, Clause.score, Literal.value, Literal.eval,
          Literal.neg, Literal.force, Literal.mk.injEq, Ne.symm h, hx]
    · by_cases hk : k = i
      · subst k
        cases p <;> cases q <;> cases r <;> cases hx : x j <;>
          simp [Clause.cutPart, Clause.score, Literal.value, Literal.eval,
            Literal.neg, Literal.force, Literal.mk.injEq, h, hx]
      · cases p <;> cases q <;> cases r <;>
          simp [Clause.cutPart, Clause.score, Literal.value, Literal.eval,
            Literal.neg, Literal.force, Literal.mk.injEq, hj, hk]

theorem pruning_gain_identity (F : Formula n) (v : Literal n) (x : Assignment n)
    (h : wellFormed F) :
    (pruningConstraint F v).lhs x - ((pruningConstraint F v).bound+1) =
      score F (v.force true x) - score F (v.force false x) := by
  induction F with
  | nil => simp [pruningConstraint, Constraint.lhs, score]
  | cons c F ih =>
    have hc := clause_gain_identity c v x (h c (by simp))
    have ht := ih (fun d hd => h d (by simp [hd]))
    simp only [pruningConstraint, Constraint.lhs, List.flatMap_cons,
      List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      score_cons] at *
    omega

/-- Manuscript Lemma `lem:pruning`, with the strict inequality and its -1 offset. -/
theorem pruning_iff_strict_improvement (F : Formula n) (v : Literal n)
    (x : Assignment n) (h : wellFormed F) :
    (pruningConstraint F v).Holds x ↔
      score F (v.force true x) < score F (v.force false x) := by
  have := pruning_gain_identity F v x h
  simp only [Constraint.Holds]
  omega
end Max2SAT
