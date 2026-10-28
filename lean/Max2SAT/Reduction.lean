import Max2SAT.Pruning

namespace Max2SAT
namespace Literal

theorem force_eq_self (v : Literal n) (x : Assignment n) (b : Bool)
    (h : v.eval x = b) : v.force b x = x := by
  rcases v with ⟨i,p⟩
  funext j
  by_cases hj : j=i
  · subst j
    cases p <;> cases hx : x i <;> cases b <;> simp_all [eval, force]
  · simp [force, hj]

theorem force_value_le (a v : Literal n) (x : Assignment n) (h : a ≠ v) :
    a.value (v.force true x) ≤ a.value x := by
  rcases a with ⟨i,p⟩; rcases v with ⟨j,q⟩
  by_cases hij : i=j
  · subst i
    cases p <;> cases q <;> cases hx : x j <;>
      simp_all [value, eval, force]
  · simp [value, eval, force, hij]
end Literal

namespace Clause

def unitCount (v : Literal n) : Clause n → ℤ
  | .unit a => if a=v then 1 else 0
  | .pair _ _ => 0

def binaryCount (v : Literal n) : Clause n → ℤ
  | .unit _ => 0
  | .pair a b => if a=v ∨ b=v then 1 else 0

theorem cut_bound_identity (c : Clause n) (v : Literal n) (h : c.WellFormed) :
    (c.cutPart v).2 = c.binaryCount v.neg - c.unitCount v + c.unitCount v.neg := by
  rcases v with ⟨i,p⟩
  cases c with
  | unit a =>
    rcases a with ⟨j,q⟩
    by_cases hi : j=i
    · subst j; cases p <;> cases q <;> simp [cutPart,unitCount,binaryCount,Literal.neg]
    · cases p <;> cases q <;> simp [cutPart,unitCount,binaryCount,Literal.neg,Literal.mk.injEq,hi]
  | pair a b =>
    rcases a with ⟨j,q⟩; rcases b with ⟨k,r⟩
    change j ≠ k at h
    by_cases hj : j=i
    · subst j; cases p <;> cases q <;> cases r <;>
        simp [cutPart,unitCount,binaryCount,Literal.neg,Literal.mk.injEq,Ne.symm h]
    · by_cases hk : k=i
      · subst k; cases p <;> cases q <;> cases r <;>
          simp [cutPart,unitCount,binaryCount,Literal.neg,Literal.mk.injEq,h]
      · cases p <;> cases q <;> cases r <;>
          simp [cutPart,unitCount,binaryCount,Literal.neg,Literal.mk.injEq,hj,hk]
end Clause

def d1 (F : Formula n) (v : Literal n) : ℤ := (F.map (Clause.unitCount v)).sum
def d2 (F : Formula n) (v : Literal n) : ℤ := (F.map (Clause.binaryCount v)).sum

theorem pruning_bound_counts (F : Formula n) (v : Literal n) (h : wellFormed F) :
    (pruningConstraint F v).bound = d2 F v.neg - d1 F v + d1 F v.neg - 1 := by
  induction F with
  | nil => simp [pruningConstraint,d1,d2]
  | cons c F ih =>
    have hc := c.cut_bound_identity v (h c (by simp))
    have ht := ih (fun c hc => h c (by simp [hc]))
    simp only [pruningConstraint,d1,d2,List.map_cons,List.sum_cons] at *
    omega

/-- Unit domination, including its compatibility with unit cancellation. -/
theorem unit_domination (F : Formula n) (v : Literal n) (x : Assignment n)
    (hF : wellFormed F) (hn : d1 F v.neg = 0) (hd : d2 F v.neg ≤ d1 F v) :
    score F (v.force false x) ≤ score F (v.force true x) := by
  have hg := pruning_gain_identity F v x hF
  have hb := pruning_bound_counts F v hF
  have hp := Constraint.lhs_nonneg (pruningConstraint F v) x
  omega

namespace Constraint

theorem force_preserves (C : Constraint n) (v : Literal n) (x : Assignment n)
    (hn : v ∉ C.terms) (hx : C.Holds x) : C.Holds (v.force true x) := by
  change C.lhs (v.force true x) ≤ C.bound
  apply le_trans (b := C.lhs x) ?_ hx
  have hs : ∀ terms : List (Literal n), v ∉ terms →
      (terms.map (fun a => a.value (v.force true x))).sum ≤
        (terms.map (fun a => a.value x)).sum := by
    intro terms
    induction terms with
    | nil => intro _; simp
    | cons a as ih =>
      intro hn
      simp only [List.map_cons,List.sum_cons]
      have ha : a ≠ v := by intro h; subst a; exact hn (by simp)
      have ht : v ∉ as := fun h => hn (by simp [h])
      exact add_le_add (Literal.force_value_le a v x ha) (ih ht)
  exact hs C.terms hn

theorem true_occurrences_le (terms : List (Literal n)) (v : Literal n)
    (x : Assignment n) (hv : v.eval x = true) :
    (terms.count v : ℤ) ≤ (terms.map (fun a => a.value x)).sum := by
  induction terms with
  | nil => simp
  | cons a as ih =>
    by_cases ha : a=v
    · subst a
      have hvv : v.value x = 1 := by simp [Literal.value,hv]
      simp only [List.count_cons_self, Nat.cast_add, Nat.cast_one,
        List.map_cons,List.sum_cons,hvv]
      omega
    · simp only [List.count_cons_of_ne ha,List.map_cons,List.sum_cons]
      have := a.value_nonneg x
      omega

theorem propagation (C : Constraint n) (v : Literal n) (x : Assignment n)
    (hc : C.bound < (C.terms.count v : ℤ)) (hx : C.Holds x) : v.eval x = false := by
  cases hv : v.eval x
  · rfl
  · have h := true_occurrences_le C.terms v x hv
    change C.lhs x ≤ C.bound at hx
    change (C.terms.count v : ℤ) ≤ C.lhs x at h
    omega

theorem remove_false (v : Literal n) (terms : List (Literal n)) (b : ℤ)
    (x : Assignment n) (hv : v.eval x = false) :
    (Constraint.mk (v::terms) b).Holds x ↔ (Constraint.mk terms b).Holds x := by
  simp [Holds,lhs,Literal.value,hv]

theorem remove_true (v : Literal n) (terms : List (Literal n)) (b : ℤ)
    (x : Assignment n) (hv : v.eval x = true) :
    (Constraint.mk (v::terms) b).Holds x ↔ (Constraint.mk terms (b-1)).Holds x := by
  simp only [Holds,lhs,List.map_cons,List.sum_cons,Literal.value,hv,↓reduceIte]
  omega

theorem redundant (C : Constraint n) (h : (C.terms.length : ℤ) ≤ C.bound) :
    ∀ x, C.Holds x := by
  intro x
  change C.lhs x ≤ C.bound
  apply le_trans (b := (C.terms.length : ℤ)) ?_ h
  unfold lhs
  induction C.terms with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    have := a.value_le_one x
    omega
end Constraint

/-- Finite sequences of the paper's score-preserving preprocessing rules. -/
inductive PreprocessTrace : Formula n → Formula n → ℤ → Prop
  | refl (F) : PreprocessTrace F F 0
  | units (v F) : PreprocessTrace (.unit v :: .unit v.neg :: F) F 1
  | pairs (a b F) : PreprocessTrace (.pair a b :: .pair a b.neg :: F) (.unit a :: F) 1
  | context {F G s} (h : PreprocessTrace F G s) (A B) :
      PreprocessTrace (A++F++B) (A++G++B) s
  | perm {F G} (h : F.Perm G) : PreprocessTrace F G 0
  | trans {F G H s t} (h₁ : PreprocessTrace F G s) (h₂ : PreprocessTrace G H t) :
      PreprocessTrace F H (s+t)

theorem preprocess_sound {F G : Formula n} {s : ℤ} (h : PreprocessTrace F G s) :
    EquivalentWithOffset F G s := by
  induction h with
  | refl F => intro x; simp
  | units v F => exact unit_cancellation v F
  | pairs a b F => exact pair_reduction a b F
  | context h A B ih => exact offset_context ih A B
  | perm h => intro x; simpa [score] using (h.map (Clause.score x)).sum_eq
  | trans h₁ h₂ ih₁ ih₂ => exact offset_trans ih₁ ih₂
end Max2SAT
