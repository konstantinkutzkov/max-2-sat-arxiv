import Max2SAT.Normalization
import Max2SAT.PartialAssignment

/-! Exact enumeration of one summed constraint. Each accepted node has a
completion, which makes the recursion output-sensitive. -/
namespace Max2SAT.Bias.Single

/-- Exact feasibility of a constraint within the current partial assignment. -/
def reject (C : Constraint n) (free : List (Fin n)) (x : Assignment n) : Bool :=
  Constraint.infeasible (Constraint.restrict free.toFinset x C)

theorem feasible_iff (C : Constraint n) (free : List (Fin n)) (x : Assignment n) :
    reject C free x=false ↔ ∃ y, Compatible free.toFinset x y ∧ C.Holds y := by
  classical
  constructor
  · intro h
    have he : ∃ z, (Constraint.restrict free.toFinset x C).Holds z := by
      by_contra hn
      have hh := (Constraint.infeasible_iff _).mpr hn
      simp [reject,hh] at h
    rcases he with ⟨z,hz⟩
    let y : Assignment n := fun i => if i∈free then z i else x i
    have hc : Compatible free.toFinset x y := by
      intro i hi
      have hn : i∉free := by simpa using hi
      simp [y,hn]
    refine ⟨y,hc,(Constraint.restrict_iff _ _ _ hc _).mp ?_⟩
    have hl : (Constraint.restrict free.toFinset x C).lhs y=
        (Constraint.restrict free.toFinset x C).lhs z := by
      unfold Constraint.lhs Constraint.restrict
      congr 1
      apply List.map_congr_left
      intro a ha
      have ha' := (List.mem_filter.mp ha).2
      simp only [decide_eq_true_eq, List.mem_toFinset] at ha'
      simp [Literal.value,Literal.eval,y,ha']
    simpa only [Constraint.Holds,hl] using hz
  · rintro ⟨y,hc,hy⟩
    have hh := (Constraint.restrict_iff _ _ _ hc _).mpr hy
    cases hr : reject C free x
    · rfl
    · exact False.elim (Constraint.infeasible_sound _ hr y hh)

def enumerate (C : Constraint n) : List (Fin n) → Assignment n → List (Assignment n)
  | [], x => if reject C [] x then [] else [x]
  | i::is, x => if reject C (i::is) x then [] else
      enumerate C is (Function.update x i false) ++ enumerate C is (Function.update x i true)

def nodes (C : Constraint n) : List (Fin n) → Assignment n → ℕ
  | [], _ => 1
  | i::is, x => if reject C (i::is) x then 1 else
      1+nodes C is (Function.update x i false)+nodes C is (Function.update x i true)

def fold (C : Constraint n) (visit : σ → Assignment n → σ) :
    List (Fin n) → Assignment n → σ → σ
  | [], x, acc => if reject C [] x then acc else visit acc x
  | i::is, x, acc => if reject C (i::is) x then acc else
      let left := fold C visit is (Function.update x i false) acc
      fold C visit is (Function.update x i true) left

theorem compatible_cons (is : List (Fin n)) (i : Fin n) (x y : Assignment n)
    (b : Bool) (hi : i∉is) :
    Compatible is.toFinset (Function.update x i b) y ↔
      y i=b ∧ Compatible (i::is).toFinset x y := by
  have he : is.toFinset=(i::is).toFinset.erase i := by simp [hi]
  rw [he]
  exact compatible_erase_update _ x y i b (by simp)

theorem mem_enumerate (C : Constraint n) (free : List (Fin n))
    (x y : Assignment n) (hn : free.Nodup) :
    y∈enumerate C free x ↔ Compatible free.toFinset x y ∧ C.Holds y := by
  induction free generalizing x with
  | nil =>
    by_cases h : reject C [] x=true
    · simp only [enumerate,h,↓reduceIte,List.not_mem_nil,false_iff]
      intro hy
      have hh := (feasible_iff C [] x).mpr ⟨y,hy⟩
      simp [h] at hh
    · have hf := (feasible_iff C [] x).mp (Bool.eq_false_iff.mpr h)
      rcases hf with ⟨z,hz,hC⟩
      have he : z=x := (compatible_empty x z).mp hz
      subst z
      simp only [enumerate,ite_eq_right h,List.mem_singleton,List.toFinset_nil,compatible_empty]
      exact ⟨fun he => ⟨he,he ▸ hC⟩,fun hh => hh.1⟩
  | cons i is ih =>
    have hi := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    by_cases h : reject C (i::is) x=true
    · simp only [enumerate,h,↓reduceIte,List.not_mem_nil,false_iff]
      intro hy
      have hh := (feasible_iff C (i::is) x).mpr ⟨y,hy⟩
      simp [h] at hh
    · simp only [enumerate,ite_eq_right h,List.mem_append,ih _ ht,compatible_cons is i _ _ _ hi]
      cases y i <;> simp

theorem enumerate_nodup (C : Constraint n) (free : List (Fin n))
    (x : Assignment n) (hn : free.Nodup) : (enumerate C free x).Nodup := by
  induction free generalizing x with
  | nil => unfold enumerate; split <;> simp
  | cons i is ih =>
    have hi := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    unfold enumerate
    split
    · simp
    · rw [List.nodup_append]
      refine ⟨ih _ ht,ih _ ht,?_⟩
      intro a ha b hb hab
      subst b
      have h0 := (mem_enumerate C is _ a ht).mp ha
      have h1 := (mem_enumerate C is _ a ht).mp hb
      have h0' := (compatible_cons is i _ a false hi).mp h0.1
      have h1' := (compatible_cons is i _ a true hi).mp h1.1
      simp [h0'.1] at h1'

theorem length_pos (C : Constraint n) (free : List (Fin n)) (x : Assignment n)
    (hn : free.Nodup) (h : reject C free x=false) : 0<(enumerate C free x).length := by
  rcases (feasible_iff C free x).mp h with ⟨y,hy⟩
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem ((mem_enumerate C free x y hn).mpr hy))

theorem nodes_bound (C : Constraint n) (free : List (Fin n)) (x : Assignment n)
    (hn : free.Nodup) :
    nodes C free x≤1+2*free.length*(enumerate C free x).length := by
  induction free generalizing x with
  | nil => simp [nodes]
  | cons i is ih =>
    have ht := (List.nodup_cons.mp hn).2
    by_cases h : reject C (i::is) x=true
    · simp [nodes,enumerate,h]
    · have hp := length_pos C (i::is) x hn (Bool.eq_false_iff.mpr h)
      have h0 := ih (Function.update x i false) ht
      have h1 := ih (Function.update x i true) ht
      simp only [nodes,enumerate,ite_eq_right h,List.length_append,List.length_cons] at *
      nlinarith

theorem fold_eq_foldl (C : Constraint n) (visit : σ → Assignment n → σ)
    (free : List (Fin n)) (x : Assignment n) (acc : σ) :
    fold C visit free x acc=(enumerate C free x).foldl visit acc := by
  induction free generalizing x acc with
  | nil => unfold fold enumerate; split <;> simp
  | cons i is ih => unfold fold enumerate; split <;> simp [ih,List.foldl_append]

end Max2SAT.Bias.Single
