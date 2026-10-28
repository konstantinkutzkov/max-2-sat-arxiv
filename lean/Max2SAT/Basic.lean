import Mathlib.Tactic

/-! Clause semantics. Lists preserve clause and literal multiplicities. -/
namespace Max2SAT
abbrev Assignment (n : ℕ) := Fin n → Bool
structure Literal (n : ℕ) where
  var : Fin n
  positive : Bool
  deriving DecidableEq, Repr
namespace Literal

def neg (a : Literal n) : Literal n := ⟨a.var, !a.positive⟩
def eval (a : Literal n) (x : Assignment n) : Bool := x a.var == a.positive
def value (a : Literal n) (x : Assignment n) : ℤ := if a.eval x then 1 else 0
def force (a : Literal n) (b : Bool) (x : Assignment n) : Assignment n :=
  Function.update x a.var (b == a.positive)
@[simp] theorem neg_neg (a : Literal n) : a.neg.neg = a := by
  cases a with | mk i p => cases p <;> rfl
@[simp] theorem value_nonneg (a : Literal n) (x : Assignment n) : 0 ≤ a.value x := by
  simp only [value]; split <;> omega
@[simp] theorem value_le_one (a : Literal n) (x : Assignment n) : a.value x ≤ 1 := by
  simp only [value]; split <;> omega
@[simp] theorem neg_value (a : Literal n) (x : Assignment n) :
    a.neg.value x = 1 - a.value x := by
  rcases a with ⟨i,p⟩
  cases h : x i <;> cases p <;> simp [value, eval, neg, h]
@[simp] theorem force_self (a : Literal n) (b : Bool) (x : Assignment n) :
    a.eval (a.force b x) = b := by
  rcases a with ⟨i,p⟩
  cases b <;> cases p <;> simp [eval, force]
@[simp] theorem force_other (a v : Literal n) (b : Bool) (x : Assignment n)
    (h : a.var ≠ v.var) : a.value (v.force b x) = a.value x := by
  simp [value, eval, force, Function.update_of_ne h]
end Literal

inductive Clause (n : ℕ) where
  | unit : Literal n → Clause n
  | pair : Literal n → Literal n → Clause n
  deriving DecidableEq, Repr
namespace Clause

def WellFormed : Clause n → Prop
  | .unit _ => True
  | .pair a b => a.var ≠ b.var
instance (c : Clause n) : Decidable c.WellFormed := by
  cases c <;> simp only [WellFormed] <;> infer_instance

def score (x : Assignment n) : Clause n → ℤ
  | .unit a => a.value x
  | .pair a b => if a.eval x || b.eval x then 1 else 0
@[simp] theorem pair_score (a b : Literal n) (x : Assignment n) :
    score x (.pair a b) = a.value x + b.value x - a.value x * b.value x := by
  simp only [score, Literal.value]
  cases a.eval x <;> cases b.eval x <;> norm_num

/-- Contributions before the final strict-improvement offset of minus one. -/
def cutPart (v : Literal n) : Clause n → List (Literal n) × ℤ
  | .unit a => if a = v then ([], -1) else if a = v.neg then ([], 1) else ([], 0)
  | .pair a b =>
      if a = v then ([b.neg], 0) else if b = v then ([a.neg], 0)
      else if a = v.neg then ([b], 1) else if b = v.neg then ([a], 1)
      else ([], 0)
end Clause

abbrev Formula (n : ℕ) := List (Clause n)
def score (F : Formula n) (x : Assignment n) : ℤ := (F.map (Clause.score x)).sum
def wellFormed (F : Formula n) : Prop := ∀ c ∈ F, c.WellFormed
@[simp] theorem score_nil (x : Assignment n) : score [] x = 0 := rfl
@[simp] theorem score_cons (c : Clause n) (F : Formula n) (x : Assignment n) :
    score (c :: F) x = c.score x + score F x := by simp [score]
@[simp] theorem score_append (F G : Formula n) (x : Assignment n) :
    score (F ++ G) x = score F x + score G x := by simp [score]

theorem unit_cancellation (v : Literal n) (F : Formula n) (x : Assignment n) :
    score (.unit v :: .unit v.neg :: F) x = 1 + score F x := by
  simp [Clause.score]; ring

theorem pair_reduction (a b : Literal n) (F : Formula n) (x : Assignment n) :
    score (.pair a b :: .pair a b.neg :: F) x =
      1 + score (.unit a :: F) x := by
  simp only [score_cons]
  rw [Clause.pair_score, Clause.pair_score]
  simp only [Clause.score, Literal.neg_value]
  ring

/-- Preprocessing preserves every assignment score, not only the optimum. -/
def EquivalentWithOffset (F G : Formula n) (s : ℤ) : Prop :=
  ∀ x, score F x = s + score G x

theorem offset_trans {F G H : Formula n} {s t : ℤ}
    (h₁ : EquivalentWithOffset F G s) (h₂ : EquivalentWithOffset G H t) :
    EquivalentWithOffset F H (s+t) := by
  intro x; rw [h₁ x, h₂ x]; ring

theorem offset_context {F G : Formula n} {s : ℤ}
    (h : EquivalentWithOffset F G s) (A B : Formula n) :
    EquivalentWithOffset (A ++ F ++ B) (A ++ G ++ B) s := by
  intro x; simp only [score_append]; rw [h x]; ring
end Max2SAT
