import Max2SAT.Pruning

/-! The full decision tree is a proof object for the earliest-optimum argument
in manuscript Lemma lem:exactA. The executable search never builds this tree.
These supporting definitions reuse the earlier comparison-tree foundation;
no archived solver is imported. -/
namespace Max2SAT

inductive ComparisonTree (α C : Type) where
  | leaf : α → ComparisonTree α C
  | branch : C → ComparisonTree α C → ComparisonTree α C → ComparisonTree α C

namespace ComparisonTree

def leaves : ComparisonTree α C → List α
  | .leaf x => [x]
  | .branch _ l r => l.leaves ++ r.leaves

/-- Every excluded right-hand assignment has an at-least-as-good alternative
in the earlier child. This is the precise local obligation for a learned cut. -/
def Valid (score : α → ℤ) (holds : C → α → Prop) : ComparisonTree α C → Prop
  | .leaf _ => True
  | .branch c l r => l.Valid score holds ∧ r.Valid score holds ∧
      ∀ x ∈ r.leaves, ¬ holds c x → ∃ y ∈ l.leaves, score x ≤ score y

/-- Recursively characterize the earliest maximum in the full proof tree. -/
def winner (score : α → ℤ) : ComparisonTree α C → α
  | .leaf x => x
  | .branch _ l r =>
      if score (r.winner score) ≤ score (l.winner score)
      then l.winner score else r.winner score

theorem winner_mem (t : ComparisonTree α C) (score : α → ℤ) :
    t.winner score ∈ t.leaves := by
  induction t with
  | leaf x => simp [winner, leaves]
  | branch c l r hl hr =>
    simp only [winner, leaves, List.mem_append]
    split
    · exact Or.inl hl
    · exact Or.inr hr

theorem le_winner (t : ComparisonTree α C) (score : α → ℤ) :
    ∀ x ∈ t.leaves, score x ≤ score (t.winner score) := by
  induction t with
  | leaf y =>
    intro x hx
    have : x = y := by simpa [leaves] using hx
    subst x; simp [winner]
  | branch c l r hl hr =>
    intro x hx
    simp only [leaves, List.mem_append] at hx
    simp only [winner]
    split <;> rename_i h
    · rcases hx with hx | hx
      · exact hl x hx
      · exact le_trans (hr x hx) h
    · rcases hx with hx | hx
      · exact le_trans (hl x hx) (le_of_lt (lt_of_not_ge h))
      · exact hr x hx

end ComparisonTree
end Max2SAT
