import Max2SAT.Bias.Accumulation

/-! Fixed preferences provide a common tie-breaking rule. A score maximum
with the largest number of preferred bits satisfies every relevant cut. -/
namespace Max2SAT.Bias

def agreements (p : Fin n → Bool) (x : Assignment n) : ℤ :=
  ∑ i : Fin n, if x i=p i then 1 else 0

theorem agreements_bounds (p : Fin n → Bool) (x : Assignment n) :
    0≤agreements p x ∧ agreements p x≤n := by
  constructor
  · apply Finset.sum_nonneg; intro i _; split <;> norm_num
  · calc
      agreements p x ≤ ∑ _i : Fin n, (1:ℤ) := by
        apply Finset.sum_le_sum; intro i _; split <;> norm_num
      _ = n := by simp

theorem agreements_update (p : Fin n → Bool) (x : Assignment n) (i : Fin n)
    (h : x i≠p i) : agreements p (Function.update x i (p i))=agreements p x+1 := by
  unfold agreements
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i),
      ←Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have he : (∑ j∈Finset.univ.erase i, if Function.update x i (p i) j=p j then (1:ℤ) else 0)=
      ∑ j∈Finset.univ.erase i, if x j=p j then (1:ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [(Finset.mem_erase.mp hj).1]
  simp [he,h]

/-- All the fixed-preference pruning constraints can retain a common optimum. -/
theorem exists_optimal_cuts (F : Formula n) (p : Fin n → Bool) (hF : wellFormed F) :
    ∃ x, (∀ y, score F y≤score F x) ∧
      ∀ i, x i≠p i → (pruningConstraint F (preferred p i)).Holds x := by
  classical
  let objective := fun x : Assignment n => ((n:ℤ)+1)*score F x+agreements p x
  rcases Finset.exists_max_image Finset.univ objective (by exact Finset.univ_nonempty) with ⟨x,_,hx⟩
  have hm : ∀ y, objective y≤objective x := fun y => hx y (Finset.mem_univ y)
  refine ⟨x,?_,?_⟩
  · intro y
    have hy := hm y
    have h0 := (agreements_bounds p y).1
    have h1 := (agreements_bounds p x).2
    dsimp [objective] at hy
    by_contra hs
    have hd : score F x+1≤score F y := by omega
    nlinarith
  · intro i hi
    let y := Function.update x i (p i)
    have he : (preferred p i).force true x=y := by
      cases hp : p i <;> simp [preferred,Literal.force,hp,y]
    have hf := Literal.force_eq_self (preferred p i) x false (by simp [Literal.eval,preferred,hi])
    rw [pruning_iff_strict_improvement F (preferred p i) x hF,he,hf]
    have hg := agreements_update p x i hi
    have hy := hm y
    dsimp [objective,y] at hy
    rw [hg] at hy
    by_contra hs
    have hd : score F x≤score F y := by omega
    have hn : (0:ℤ)≤n+1 := by omega
    have hmul := mul_le_mul_of_nonneg_left hd hn
    dsimp [y] at hmul
    linarith

theorem exists_optimal_admissible (F : Formula n) (p : Fin n → Bool)
    (P : Finset (Fin n)) (hF : wellFormed F) :
    ∃ x, admissible F p P x ∧ ∀ y, score F y≤score F x := by
  rcases exists_optimal_cuts F p hF with ⟨x,hx,hcuts⟩
  refine ⟨x,Constraint.holds_sum _ x ?_,hx⟩
  intro C hC
  rcases List.mem_filterMap.mp hC with ⟨i,hi,he⟩
  by_cases h : x i=p i
  · simp [h] at he
  · simp only [ite_eq_right h,Option.some.injEq] at he
    subst C
    exact hcuts i h

end Max2SAT.Bias
