import Max2SAT.Random.Weighted

/-! Streaming enumeration of exactly the completions of a rational weighted
sum. Rejection computes its exact minimum, so every live node has a completion. -/
namespace Max2SAT.Weighted

def enumerate (C : Budget n) : List (Fin n) → Assignment n → List (Assignment n)
  | [], x => if reject C [] x then [] else [x]
  | i::is, x => if reject C (i::is) x then [] else
      enumerate C is (Function.update x i false) ++ enumerate C is (Function.update x i true)

def nodes (C : Budget n) : List (Fin n) → Assignment n → ℕ
  | [], _ => 1
  | i::is, x => if reject C (i::is) x then 1 else
      1+nodes C is (Function.update x i false)+nodes C is (Function.update x i true)

def fold (C : Budget n) (visit : σ → Assignment n → σ) :
    List (Fin n) → Assignment n → σ → σ
  | [], x, acc => if reject C [] x then acc else visit acc x
  | i::is, x, acc => if reject C (i::is) x then acc else
      let left := fold C visit is (Function.update x i false) acc
      fold C visit is (Function.update x i true) left

theorem mem_enumerate (C : Budget n) (free : List (Fin n))
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
    · simp only [enumerate,ite_eq_right h,List.mem_append,ih _ ht,Bias.Single.compatible_cons is i _ _ _ hi]
      cases y i <;> simp

theorem enumerate_nodup (C : Budget n) (free : List (Fin n))
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
      have h0' := (Bias.Single.compatible_cons is i _ a false hi).mp h0.1
      have h1' := (Bias.Single.compatible_cons is i _ a true hi).mp h1.1
      simp [h0'.1] at h1'

theorem length_pos (C : Budget n) (free : List (Fin n)) (x : Assignment n)
    (hn : free.Nodup) (h : reject C free x=false) : 0<(enumerate C free x).length := by
  rcases (feasible_iff C free x).mp h with ⟨y,hy⟩
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem ((mem_enumerate C free x y hn).mpr hy))

theorem nodes_bound (C : Budget n) (free : List (Fin n)) (x : Assignment n)
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

theorem fold_eq_foldl (C : Budget n) (visit : σ → Assignment n → σ)
    (free : List (Fin n)) (x : Assignment n) (acc : σ) :
    fold C visit free x acc=(enumerate C free x).foldl visit acc := by
  induction free generalizing x acc with
  | nil => unfold fold enumerate; split <;> simp
  | cons i is ih => unfold fold enumerate; split <;> simp [ih,List.foldl_append]

end Max2SAT.Weighted
