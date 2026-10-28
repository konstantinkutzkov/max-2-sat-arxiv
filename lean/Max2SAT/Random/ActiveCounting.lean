import Max2SAT.Random.SearchCounts

/-! Count each assignment on the active set once. Coordinates outside the
set retain their initialized values, even when the input has many isolates. -/
namespace Max2SAT.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable

def fillActive (S : Finset (Fin n)) (base : Assignment n) (y : S → Bool) : Assignment n :=
  fun i => if hi : i∈S then y ⟨i,hi⟩ else base i

theorem fill_active_compatible (S : Finset (Fin n)) (base : Assignment n) (y : S → Bool) :
    Compatible S base (fillActive S base y) := by
  intro i hi
  simp [fillActive,hi]

theorem fill_active_restrict (S : Finset (Fin n)) (base x : Assignment n)
    (hx : Compatible S base x) : fillActive S base (fun i => x i)=x := by
  funext i
  by_cases hi : i∈S
  · simp [fillActive,hi]
  · simp [fillActive,hi,hx i hi]

theorem fixed_coordinate_count (S : Finset (Fin n)) (base : Assignment n)
    (P : Assignment n → Prop)
    (hP : ∀ x y, (∀ i∈S, x i=y i) → (P x ↔ P y)) :
    ((Finset.univ.filter (fun x => Compatible S base x ∧ P x)).card:ℝ)=
      (2:ℝ)^S.card*prob (fairBits (Fin n)) P := by
  have hc : (Finset.univ.filter (fun y : S → Bool => P (fillActive S base y))).card=
      (Finset.univ.filter (fun x => Compatible S base x ∧ P x)).card := by
    apply Finset.card_bij (fun y _ => fillActive S base y)
    · intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fill_active_compatible S base y,
        (Finset.mem_filter.mp hy).2⟩
    · intro y _ z _ he
      funext i
      simpa [fillActive,i.property] using congrFun he i
    · intro x hx
      refine ⟨fun i => x i,?_,?_⟩
      · simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        rw [fill_active_restrict S base x (Finset.mem_filter.mp hx).2.1]
        exact (Finset.mem_filter.mp hx).2.2
      · exact fill_active_restrict S base x (Finset.mem_filter.mp hx).2.1
  have hl : push (fairBits (Fin n)) (fun x (i : S) => x i)=fairBits S :=
    product_select (fun _ : Fin n => fair) (fun i : S => i.val) Subtype.val_injective
  have hp : prob (fairBits S) (fun y => P (fillActive S base y))=prob (fairBits (Fin n)) P := by
    rw [←hl,prob_push]
    congr 1
    funext x
    apply propext
    exact hP _ x (fun i hi => by simp [fillActive,hi])
  rw [←hp,←hc]
  unfold prob
  simp_rw [fairBits_mass]
  rw [←Finset.sum_filter]
  simp only [Fintype.card_coe,Finset.sum_const,nsmul_eq_mul]
  have he : (2:ℝ)^S.card*(1/2:ℝ)^S.card=1 := by rw [←mul_pow]; norm_num
  nlinarith

end
end Max2SAT.FiniteLaw
