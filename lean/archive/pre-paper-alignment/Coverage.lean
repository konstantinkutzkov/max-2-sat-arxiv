import Max2SAT.Reduction
import Max2SAT.Search

/-! Instantiating the abstract correctness theorem with Boolean assignments
and the actual Max 2-SAT comparison constraints. Variable selection may depend
on the current prefix and inherited constraints, but must choose an unassigned
variable. In particular, this includes moving a constraint-forced variable
before the next ordinary variable in the fixed order. -/
namespace Max2SAT

def Compatible (free : Finset (Fin n)) (x y : Assignment n) : Prop :=
  ∀ i, i ∉ free → y i = x i

abbrev Selector (n : ℕ) := (free : Finset (Fin n)) → free.Nonempty →
  Assignment n → List (Constraint n) → {v : Literal n // v.var ∈ free}

/-- A complete mathematical decision tree, including the children later rejected.
`fuel ≥ free.card` is proved at every call in the coverage theorem. -/
def comparisonTree (F : Formula n) (choose : Selector n) :
    ℕ → (free : Finset (Fin n)) → Assignment n → List (Constraint n) →
      ComparisonTree (Assignment n) (Constraint n)
  | 0, _, x, _ => .leaf x
  | fuel+1, free, x, cs =>
    if h : free.Nonempty then
      let v := (choose free h x cs).val
      let cut := pruningConstraint F v
      .branch cut
        (comparisonTree F choose fuel (free.erase v.var) (v.force true x) cs)
        (comparisonTree F choose fuel (free.erase v.var) (v.force false x) (cut::cs))
    else .leaf x

theorem compatible_empty (x y : Assignment n) : Compatible ∅ x y ↔ y=x := by
  constructor
  · intro h; funext i; exact h i (by simp)
  · intro h; subst y; intro i _; rfl

theorem compatible_erase_update (free : Finset (Fin n)) (x y : Assignment n)
    (i : Fin n) (b : Bool) (hi : i ∈ free) :
    Compatible (free.erase i) (Function.update x i b) y ↔
      y i = b ∧ Compatible free x y := by
  constructor
  · intro h
    refine ⟨by simpa using h i (by simp), ?_⟩
    intro j hj
    have hji : j ≠ i := by intro he; subst j; exact hj hi
    simpa [hji] using h j (by simp [hj])
  · rintro ⟨hy,h⟩ j hj
    by_cases hji : j=i
    · subst j; simpa using hy
    · have hj' : j ∉ free := by simpa [Finset.mem_erase,hji] using hj
      simpa [hji] using h j hj'

theorem compatible_split (free : Finset (Fin n)) (x y : Assignment n)
    (v : Literal n) (hi : v.var ∈ free) :
    (Compatible (free.erase v.var) (v.force true x) y ∨
     Compatible (free.erase v.var) (v.force false x) y) ↔ Compatible free x y := by
  simp only [Literal.force, compatible_erase_update free x y v.var _ hi]
  cases v.positive <;> cases y v.var <;> simp

theorem comparisonTree_covers (F : Formula n) (choose : Selector n) (fuel : ℕ)
    (free : Finset (Fin n)) (x y : Assignment n) (cs : List (Constraint n))
    (hf : free.card ≤ fuel) :
    y ∈ (comparisonTree F choose fuel free x cs).leaves ↔ Compatible free x y := by
  induction fuel generalizing free x cs with
  | zero =>
    have he : free = ∅ := Finset.card_eq_zero.mp (by omega)
    subst free
    simp [comparisonTree,ComparisonTree.leaves,compatible_empty]
  | succ fuel ih =>
    by_cases h : free.Nonempty
    · let v := (choose free h x cs).val
      have hi : v.var ∈ free := (choose free h x cs).property
      have he : (free.erase v.var).card ≤ fuel := by
        rw [Finset.card_erase_of_mem hi]; omega
      simp only [comparisonTree,dite_eq_left h,ComparisonTree.leaves,List.mem_append]
      change (y ∈ (comparisonTree F choose fuel (free.erase v.var) (v.force true x) cs).leaves ∨
        y ∈ (comparisonTree F choose fuel (free.erase v.var) (v.force false x)
          (pruningConstraint F v::cs)).leaves) ↔ _
      rw [ih _ _ _ he, ih _ _ _ he]
      exact compatible_split free x y v hi
    · have he : free = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst free
      simp [comparisonTree,ComparisonTree.leaves,compatible_empty]

theorem right_child_flip (free : Finset (Fin n)) (x y : Assignment n)
    (v : Literal n) (h : Compatible (free.erase v.var) (v.force false x) y) :
    v.eval y = false ∧
      Compatible (free.erase v.var) (v.force true x) (v.force true y) := by
  have hi := h v.var (by simp)
  constructor
  · unfold Literal.eval
    rw [hi]
    cases hp : v.positive <;> simp [Literal.force,hp]
  · intro j hj
    by_cases hji : j=v.var
    · subst j; simp [Literal.force]
    · simpa [Literal.force,hji] using h j hj

theorem comparisonTree_valid (F : Formula n) (choose : Selector n) (fuel : ℕ)
    (free : Finset (Fin n)) (x : Assignment n) (cs : List (Constraint n))
    (hF : wellFormed F) (hf : free.card ≤ fuel) :
    (comparisonTree F choose fuel free x cs).Valid (score F) Constraint.Holds := by
  induction fuel generalizing free x cs with
  | zero => simp [comparisonTree,ComparisonTree.Valid]
  | succ fuel ih =>
    by_cases h : free.Nonempty
    · let v := (choose free h x cs).val
      have hi : v.var ∈ free := (choose free h x cs).property
      have he : (free.erase v.var).card ≤ fuel := by
        rw [Finset.card_erase_of_mem hi]; omega
      simp only [comparisonTree,dite_eq_left h,ComparisonTree.Valid]
      refine ⟨ih _ _ _ he, ih _ _ _ he, ?_⟩
      intro y hy hbad
      have hr := (comparisonTree_covers F choose fuel (free.erase v.var)
        (v.force false x) y (pruningConstraint F v::cs) he).mp hy
      rcases right_child_flip free x y v hr with ⟨hyv,hl⟩
      refine ⟨v.force true y, ?_, ?_⟩
      · exact (comparisonTree_covers F choose fuel (free.erase v.var)
          (v.force true x) (v.force true y) cs he).mpr hl
      · have hh : ¬ score F (v.force true y) < score F (v.force false y) := by
          exact fun hlt => hbad ((pruning_iff_strict_improvement F v y hF).mpr hlt)
        simpa [Literal.force_eq_self v y false hyv] using le_of_not_gt hh
    · simp [comparisonTree,h,ComparisonTree.Valid]

/-- There is an optimal original assignment among the surviving search outputs.
No assumption that alternatives satisfy inherited constraints appears here. -/
theorem literal_gap_search_correct (F : Formula n) (choose : Selector n)
    (hF : wellFormed F)
    (reject : ComparisonTree (Assignment n) (Constraint n) → List (Constraint n) → Bool)
    (hr : ComparisonTree.RejectSound Constraint.Holds reject) :
    ∃ x ∈ ComparisonTree.search Constraint.Holds reject []
      (comparisonTree F choose n Finset.univ (fun _ => false) []),
      ∀ y : Assignment n, score F y ≤ score F x := by
  have hf : (Finset.univ : Finset (Fin n)).card ≤ n := by simp
  rcases ComparisonTree.search_correct Constraint.Holds (score F) reject hr
    (comparisonTree F choose n Finset.univ (fun _ => false) [])
    (comparisonTree_valid F choose n _ _ [] hF hf) with ⟨x,hx,hopt⟩
  refine ⟨x,hx,?_⟩
  intro y
  apply hopt y
  apply (comparisonTree_covers F choose n _ _ y [] hf).mpr
  intro i hi; simp at hi

end Max2SAT
