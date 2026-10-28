import Max2SAT.Reduction

/-! Partial assignments used by the paper's prefix/suffix enumeration. -/
namespace Max2SAT

def Compatible (free : Finset (Fin n)) (x y : Assignment n) : Prop :=
  ∀ i, i ∉ free → y i = x i

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

end Max2SAT
