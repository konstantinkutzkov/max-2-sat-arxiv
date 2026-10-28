import Max2SAT.Coverage
import Max2SAT.ConstraintCheck

/-! A reference implementation: no complete tree is constructed.
The list-valued specification is related to a streaming implementation below. -/
namespace Max2SAT

def checkedSearch (F : Formula n) (choose : Selector n) :
    ℕ → Finset (Fin n) → Assignment n → List (Constraint n) → List (Assignment n)
  | 0, free, x, cs =>
      if Constraint.reject free x cs then [] else
      if ∀ c ∈ cs, c.Holds x then [x] else []
  | fuel+1, free, x, cs =>
      if Constraint.reject free x cs then [] else
      if h : free.Nonempty then
        let v := (choose free h x cs).val
        let cut := pruningConstraint F v
        checkedSearch F choose fuel (free.erase v.var) (v.force true x) cs ++
          checkedSearch F choose fuel (free.erase v.var) (v.force false x) (cut::cs)
      else if ∀ c ∈ cs, c.Holds x then [x] else []

private theorem rejected_search_empty (F : Formula n) (choose : Selector n)
    (fuel : ℕ) (free : Finset (Fin n)) (x : Assignment n) (cs : List (Constraint n))
    (hf : free.card ≤ fuel) (hr : Constraint.reject free x cs=true) :
    ComparisonTree.search Constraint.Holds (fun _ _ => false) cs
      (comparisonTree F choose fuel free x cs) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro y hy
  have hl := ComparisonTree.search_subset Constraint.Holds (fun _ _ => false) cs _ y hy
  have hc := (comparisonTree_covers F choose fuel free x y cs hf).mp hl
  exact Constraint.reject_sound free x y hc cs hr
    (ComparisonTree.search_holds Constraint.Holds (fun _ _ => false) cs _ y hy)

theorem checkedSearch_eq_search (F : Formula n) (choose : Selector n)
    (fuel : ℕ) (free : Finset (Fin n)) (x : Assignment n) (cs : List (Constraint n))
    (hf : free.card ≤ fuel) :
    checkedSearch F choose fuel free x cs =
      ComparisonTree.search Constraint.Holds (fun _ _ => false) cs
        (comparisonTree F choose fuel free x cs) := by
  induction fuel generalizing free x cs with
  | zero =>
    by_cases hr : Constraint.reject free x cs=true
    · rw [rejected_search_empty F choose 0 free x cs hf hr]
      simp [checkedSearch,hr]
    · simp [checkedSearch,comparisonTree,ComparisonTree.search,hr]
  | succ fuel ih =>
    by_cases hr : Constraint.reject free x cs=true
    · rw [rejected_search_empty F choose (fuel+1) free x cs hf hr]
      simp [checkedSearch,hr]
    · by_cases h : free.Nonempty
      · let v := (choose free h x cs).val
        have hi : v.var ∈ free := (choose free h x cs).property
        have he : (free.erase v.var).card ≤ fuel := by
          rw [Finset.card_erase_of_mem hi]; omega
        simp only [checkedSearch,ite_eq_right hr,dite_eq_left h,
          comparisonTree,ComparisonTree.search,Bool.false_eq_true,↓reduceIte]
        exact congrArg₂ List.append (ih _ _ _ he) (ih _ _ _ he)
      · simp [checkedSearch,comparisonTree,ComparisonTree.search,hr,h]

/-- Fully instantiated correctness; the rejection test is proved, not assumed. -/
theorem checkedSearch_correct (F : Formula n) (choose : Selector n) (hF : wellFormed F) :
    ∃ x ∈ checkedSearch F choose n Finset.univ (fun _ => false) [],
      ∀ y, score F y ≤ score F x := by
  rw [checkedSearch_eq_search F choose n _ _ [] (by simp)]
  exact literal_gap_search_correct F choose hF (fun _ _ => false) (by
    intro t cs h; simp at h)

/-- Minimum unassigned label, always preferring the positive literal. -/
def fixedOrder : Selector n := fun free h _ _ =>
  let i := free.min' h
  let v : Literal n := ⟨i,true⟩
  ⟨v,Finset.min'_mem free h⟩

/-- Minimum unassigned label, with preference from the current comparison sum.
Twice its expectation under uniform remaining variables has the sign of
`terms.length - 2*(bound+1)`. Ties prefer the positive literal. -/
def gapOrder (F : Formula n) : Selector n := fun free h x _ =>
  let i := free.min' h
  let v : Literal n := ⟨i,true⟩
  let C := Constraint.restrict free x (pruningConstraint F v)
  let p := decide (2*(C.bound+1) ≤ (C.terms.length : ℤ))
  ⟨⟨i,p⟩,Finset.min'_mem free h⟩

/-- A fold over outputs, storing only the active recursion and the accumulator. -/
def foldSearch (F : Formula n) (choose : Selector n) (visit : σ → Assignment n → σ) :
    ℕ → Finset (Fin n) → Assignment n → List (Constraint n) → σ → σ
  | 0, free, x, cs, acc =>
      if Constraint.reject free x cs then acc else
      if ∀ c ∈ cs, c.Holds x then visit acc x else acc
  | fuel+1, free, x, cs, acc =>
      if Constraint.reject free x cs then acc else
      if h : free.Nonempty then
        let v := (choose free h x cs).val
        let cut := pruningConstraint F v
        let acc' := foldSearch F choose visit fuel (free.erase v.var) (v.force true x) cs acc
        foldSearch F choose visit fuel (free.erase v.var) (v.force false x) (cut::cs) acc'
      else if ∀ c ∈ cs, c.Holds x then visit acc x else acc

theorem foldSearch_eq_foldl (F : Formula n) (choose : Selector n)
    (visit : σ → Assignment n → σ) (fuel : ℕ) (free : Finset (Fin n))
    (x : Assignment n) (cs : List (Constraint n)) (acc : σ) :
    foldSearch F choose visit fuel free x cs acc =
      (checkedSearch F choose fuel free x cs).foldl visit acc := by
  induction fuel generalizing free x cs acc with
  | zero =>
    simp only [foldSearch,checkedSearch]
    split
    · simp
    · split <;> simp
  | succ fuel ih =>
    simp only [foldSearch,checkedSearch]
    split
    · simp
    · split
      · simp only [List.foldl_append]
        rw [ih,ih]
      · split <;> simp

/-- Keep the first maximum seen; `none` is the initial accumulator. -/
def keepBest (F : Formula n) (best : Option (Assignment n)) (x : Assignment n) :
    Option (Assignment n) := match best with
  | none => some x
  | some y => if score F x ≤ score F y then some y else some x

private theorem fold_best (F : Formula n) (xs : List (Assignment n))
    (initial : Option (Assignment n)) :
    ∀ x ∈ initial.toList ++ xs, ∃ z,
      xs.foldl (keepBest F) initial = some z ∧ score F x ≤ score F z := by
  induction xs generalizing initial with
  | nil =>
    intro x hx
    cases initial with
    | none => simp at hx
    | some y =>
      have : x=y := by simpa using hx
      subst x; exact ⟨y,rfl,le_refl _⟩
  | cons y ys ih =>
    intro x hx
    simp only [List.foldl_cons]
    by_cases ht : x ∈ ys
    · exact ih (keepBest F initial y) x (by simp [ht])
    · have hp : x ∈ initial.toList ∨ x=y := by simpa [ht] using hx
      have hk : ∃ z, keepBest F initial y=some z ∧ score F x ≤ score F z := by
        cases initial with
        | none =>
          have : x=y := by simpa using hp
          subst x; exact ⟨y,rfl,le_refl _⟩
        | some a =>
          have hp' : x=a ∨ x=y := by simpa using hp
          by_cases h : score F y ≤ score F a
          · refine ⟨a,by simp [keepBest,h],?_⟩
            rcases hp' with rfl | rfl
            · exact le_refl _
            · exact h
          · refine ⟨y,by simp [keepBest,h],?_⟩
            rcases hp' with rfl | rfl
            · exact le_of_lt (lt_of_not_ge h)
            · exact le_refl _
      rcases hk with ⟨z,hz,hxz⟩
      rcases ih (keepBest F initial y) z (by simp [hz]) with ⟨w,hw,hzw⟩
      exact ⟨w,hw,le_trans hxz hzw⟩

/-- The reference solver returns one assignment, never a list of all solutions. -/
def solve (F : Formula n) : Option (Assignment n) :=
  foldSearch F (gapOrder F) (keepBest F) n Finset.univ (fun _ => false) [] none

theorem solve_correct (F : Formula n) (hF : wellFormed F) :
    ∃ x, solve F = some x ∧ ∀ y, score F y ≤ score F x := by
  rcases checkedSearch_correct F (gapOrder F) hF with ⟨x,hx,hopt⟩
  rcases fold_best F (checkedSearch F (gapOrder F) n Finset.univ (fun _ => false) [])
    none x (by simpa using hx) with ⟨z,hz,hxz⟩
  refine ⟨z,?_,fun y => le_trans (hopt y) hxz⟩
  simpa [solve,foldSearch_eq_foldl] using hz
end Max2SAT
