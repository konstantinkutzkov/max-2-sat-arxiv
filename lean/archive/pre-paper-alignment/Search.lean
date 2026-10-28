import Max2SAT.Pruning

/-! Global correctness of comparison search.
The unpruned tree supplies the mathematical order used for breaking ties;
it is not an auxiliary tree that a solver needs to materialize.
The recursive `search` models learned constraints and arbitrary sound rejection.
Its theorem does not assume that a comparison's alternative satisfies older cuts. -/
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

/-- An executable choice of the earliest maximum in the full tree. -/
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

variable (holds : C → α → Prop) [DecidableRel holds]

/-- The rejection test can include sum infeasibility, individual infeasibility,
and propagation. Only sound rejection is required for correctness. -/
def RejectSound (reject : ComparisonTree α C → List C → Bool) : Prop :=
  ∀ t cs, reject t cs = true → ∀ x ∈ t.leaves, ¬ (∀ c ∈ cs, holds c x)

def search (reject : ComparisonTree α C → List C → Bool)
    (cs : List C) : ComparisonTree α C → List α
  | .leaf x => if reject (.leaf x) cs then [] else
      if ∀ c ∈ cs, holds c x then [x] else []
  | .branch c l r => if reject (.branch c l r) cs then [] else
      search reject cs l ++ search reject (c::cs) r

/-- The central invariant: the earliest full-tree optimum survives whenever
it satisfies the constraints inherited at the root of this subtree. -/
theorem winner_survives (score : α → ℤ)
    (reject : ComparisonTree α C → List C → Bool)
    (hs : RejectSound holds reject) (t : ComparisonTree α C)
    (hv : t.Valid score holds) (cs : List C)
    (hc : ∀ c ∈ cs, holds c (t.winner score)) :
    t.winner score ∈ search holds reject cs t := by
  induction t generalizing cs with
  | leaf x =>
    have hn : reject (.leaf x) cs = false := by
      cases h : reject (.leaf x) cs
      · rfl
      · exact False.elim (hs _ cs h x (by simp [leaves]) hc)
    simp_all [search, winner]
  | branch c l r hl hr =>
    have hn : reject (.branch c l r) cs = false := by
      cases h : reject (.branch c l r) cs
      · rfl
      · exact False.elim (hs _ cs h _ (winner_mem (.branch c l r) score) hc)
    rcases hv with ⟨hvl,hvr,hcut⟩
    simp only [search, hn, Bool.false_eq_true, ↓reduceIte, List.mem_append]
    by_cases h : score (r.winner score) ≤ score (l.winner score)
    · simp only [winner, ite_eq_left h] at hc ⊢
      exact Or.inl (hl hvl cs hc)
    · simp only [winner, ite_eq_right h] at hc ⊢
      have hnew : holds c (r.winner score) := by
        by_contra hbad
        rcases hcut (r.winner score) (winner_mem r score) hbad with ⟨y,hy,hxy⟩
        exact h (le_trans hxy (le_winner l score y hy))
      exact Or.inr (hr hvr (c::cs) (by simpa using And.intro hnew hc))

theorem search_subset (reject : ComparisonTree α C → List C → Bool)
    (cs : List C) (t : ComparisonTree α C) :
    ∀ x ∈ search holds reject cs t, x ∈ t.leaves := by
  induction t generalizing cs with
  | leaf y =>
    intro x hx
    simp only [search] at hx
    split at hx
    · simp at hx
    · split at hx
      · simpa [leaves] using hx
      · simp at hx
  | branch c l r hl hr =>
    intro x hx
    simp only [search] at hx
    split at hx
    · simp at hx
    · simp only [List.mem_append] at hx
      simp only [leaves, List.mem_append]
      exact hx.elim (fun h => Or.inl (hl cs x h)) (fun h => Or.inr (hr (c::cs) x h))

/-- Every output satisfies the constraints inherited at this call. -/
theorem search_holds (reject : ComparisonTree α C → List C → Bool)
    (cs : List C) (t : ComparisonTree α C) :
    ∀ x ∈ search holds reject cs t, ∀ c ∈ cs, holds c x := by
  induction t generalizing cs with
  | leaf y =>
    intro x hx
    simp only [search] at hx
    split at hx
    · simp at hx
    · split at hx
      · rename_i hy
        have he : x=y := by simpa using hx
        subst x; exact hy
      · simp at hx
  | branch c l r hl hr =>
    intro x hx d hd
    simp only [search] at hx
    split at hx
    · simp at hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hl cs x hx d hd
      · exact hr (c::cs) x hx d (by simp [hd])

/-- Global correctness: a maximum of the unpruned search is among the outputs. -/
theorem search_correct (score : α → ℤ)
    (reject : ComparisonTree α C → List C → Bool)
    (hs : RejectSound holds reject) (t : ComparisonTree α C)
    (hv : t.Valid score holds) :
    ∃ x ∈ search holds reject [] t, ∀ y ∈ t.leaves, score y ≤ score x := by
  exact ⟨t.winner score, winner_survives holds score reject hs t hv [] (by simp),
    le_winner t score⟩
end ComparisonTree
end Max2SAT
