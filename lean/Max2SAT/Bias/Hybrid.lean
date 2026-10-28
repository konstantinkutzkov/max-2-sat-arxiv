import Max2SAT.Bias.Optimal
import Max2SAT.Bias.ConstraintEnumeration

/-! The paper's literal-gap algorithm: branch on a fixed prefix set,
then enumerate completions satisfying its single summed constraint. -/
namespace Max2SAT.Bias.Hybrid

/-- Keep the first maximum seen; `none` is the initial accumulator. -/
def keepBest (F : Formula n) (best : Option (Assignment n)) (x : Assignment n) :
    Option (Assignment n) := match best with
  | none => some x
  | some y => if score F x ≤ score F y then some y else some x


/-- List specification; the executable solver below uses the streaming fold. -/
def enumerate (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (suffix : List (Fin n)) : List (Fin n) → Assignment n → List (Assignment n)
  | [], x => Single.enumerate (Constraint.sum (cuts F p (ordered P) x)) suffix x
  | i::is, x => enumerate F p P suffix is (Function.update x i false) ++
      enumerate F p P suffix is (Function.update x i true)

def nodes (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (suffix : List (Fin n)) : List (Fin n) → Assignment n → ℕ
  | [], x => Single.nodes (Constraint.sum (cuts F p (ordered P) x)) suffix x
  | i::is, x => 1+nodes F p P suffix is (Function.update x i false)+
      nodes F p P suffix is (Function.update x i true)

def fold (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (suffix : List (Fin n)) (visit : σ → Assignment n → σ) :
    List (Fin n) → Assignment n → σ → σ
  | [], x, acc => Single.fold (Constraint.sum (cuts F p (ordered P) x)) visit suffix x acc
  | i::is, x, acc =>
      let left := fold F p P suffix visit is (Function.update x i false) acc
      fold F p P suffix visit is (Function.update x i true) left

theorem mem_enumerate (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (pre suffix : List (Fin n)) (x y : Assignment n)
    (hn : (pre++suffix).Nodup) (hd : ∀ i∈suffix, i∉P) :
    y∈enumerate F p P suffix pre x ↔
      Compatible (pre++suffix).toFinset x y ∧ admissible F p P y := by
  induction pre generalizing x with
  | nil =>
    simp only [enumerate,List.nil_append] at *
    rw [Single.mem_enumerate _ suffix x y hn]
    constructor
    · rintro ⟨hc,hy⟩
      refine ⟨hc,?_⟩
      have he := cuts_agree F p (ordered P) x y (by
        intro i hi
        have hip : i∈P := by simpa using hi
        exact (hc i (by simpa using fun his => hd i his hip)).symm)
      simpa only [admissible,←he] using hy
    · rintro ⟨hc,hy⟩
      refine ⟨hc,?_⟩
      have he := cuts_agree F p (ordered P) x y (by
        intro i hi
        have hip : i∈P := by simpa using hi
        exact (hc i (by simpa using fun his => hd i his hip)).symm)
      simpa only [admissible,←he] using hy
  | cons i is ih =>
    have hi : i∉is++suffix := (List.nodup_cons.mp hn).1
    have ht : (is++suffix).Nodup := (List.nodup_cons.mp hn).2
    simp only [enumerate,List.mem_append,ih _ ht,
      Single.compatible_cons (is++suffix) i _ _ _ hi,List.cons_append]
    cases y i <;> simp

theorem enumerate_nodup (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (pre suffix : List (Fin n)) (x : Assignment n)
    (hn : (pre++suffix).Nodup) (hd : ∀ i∈suffix, i∉P) :
    (enumerate F p P suffix pre x).Nodup := by
  induction pre generalizing x with
  | nil => exact Single.enumerate_nodup _ suffix x (by simpa using hn)
  | cons i is ih =>
    have hi : i∉is++suffix := (List.nodup_cons.mp hn).1
    have ht : (is++suffix).Nodup := (List.nodup_cons.mp hn).2
    rw [enumerate,List.nodup_append]
    refine ⟨ih _ ht,ih _ ht,?_⟩
    intro a ha b hb hab
    subst b
    have h0 := (mem_enumerate F p P is suffix _ a ht hd).mp ha
    have h1 := (mem_enumerate F p P is suffix _ a ht hd).mp hb
    have h0' := (Single.compatible_cons (is++suffix) i _ a false hi).mp h0.1
    have h1' := (Single.compatible_cons (is++suffix) i _ a true hi).mp h1.1
    simp [h0'.1] at h1'

/-- Exact recursion-node accounting, including failed suffix tests. -/
theorem nodes_bound (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (pre suffix : List (Fin n)) (x : Assignment n) (hs : suffix.Nodup) :
    nodes F p P suffix pre x≤2^(pre.length+1)-1+
      2*suffix.length*(enumerate F p P suffix pre x).length := by
  induction pre generalizing x with
  | nil => simpa [nodes,enumerate] using Single.nodes_bound _ suffix x hs
  | cons i is ih =>
    have h0 := ih (Function.update x i false)
    have h1 := ih (Function.update x i true)
    have hp : 0<2^(is.length+1) := pow_pos (by omega) _
    simp only [nodes,enumerate,List.length_append,List.length_cons]
    rw [pow_succ]
    simp only [Nat.mul_add]
    omega

theorem fold_eq_foldl (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (pre suffix : List (Fin n)) (x : Assignment n) (visit : σ → Assignment n → σ)
    (acc : σ) : fold F p P suffix visit pre x acc=
      (enumerate F p P suffix pre x).foldl visit acc := by
  induction pre generalizing x acc with
  | nil => exact Single.fold_eq_foldl _ visit suffix x acc
  | cons i is ih => simp [fold,enumerate,ih,List.foldl_append]

private theorem partition_nodup (P : Finset (Fin n)) : ((ordered P)++(ordered Pᶜ)).Nodup := by
  rw [List.nodup_append]
  refine ⟨(ordered_nodup P),(ordered_nodup Pᶜ),?_⟩
  intro a ha b hb hab
  subst b
  simpa using And.intro ha hb

def outputs (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n)) : List (Assignment n) :=
  enumerate F p P (ordered Pᶜ) (ordered P) (fun _ => false)

def nodeCount (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n)) : ℕ :=
  nodes F p P (ordered Pᶜ) (ordered P) (fun _ => false)

theorem mem_outputs (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (x : Assignment n) : x∈outputs F p P ↔ admissible F p P x := by
  rw [outputs,mem_enumerate F p P _ _ _ x (partition_nodup P) (by simp)]
  simp [Compatible]

theorem outputs_nodup (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n)) :
    (outputs F p P).Nodup :=
  enumerate_nodup F p P _ _ _ (partition_nodup P) (by simp)

theorem output_count (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n)) :
    (outputs F p P).length=FairCoin.eventCount n (admissible F p P) := by
  classical
  let ys := (FairCoin.assignments n).filter (fun x => @decide (admissible F p P x) (Classical.propDecidable _))
  have hn : ys.Nodup := (FairCoin.assignments_nodup n).filter _
  have he : (outputs F p P).toFinset=ys.toFinset := by
    ext x
    simp [ys,mem_outputs,FairCoin.mem_assignments]
  have hc := congrArg Finset.card he
  rw [List.toFinset_card_of_nodup (outputs_nodup F p P),List.toFinset_card_of_nodup hn] at hc
  simpa [ys,FairCoin.eventCount,List.countP_eq_length_filter] using hc

theorem nodeCount_bound (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n)) :
    nodeCount F p P≤2^(P.card+1)-1+2*n*FairCoin.eventCount n (admissible F p P) := by
  have hh := nodes_bound F p P (ordered P) (ordered Pᶜ) (fun _ => false) (ordered_nodup Pᶜ)
  have hk : Pᶜ.card≤n := by simpa using Finset.card_le_univ Pᶜ
  change nodeCount F p P≤_ at hh
  simp only [length_ordered] at hh
  rw [←output_count]
  change nodeCount F p P≤2^(P.card+1)-1+2*n*(outputs F p P).length
  change nodeCount F p P≤2^(P.card+1)-1+2*Pᶜ.card*(outputs F p P).length at hh
  nlinarith

/-- All branch preferences and the branching set are explicit inputs. -/
def solve (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n)) : Option (Assignment n) :=
  fold F p P (ordered Pᶜ) (keepBest F) (ordered P) (fun _ => false) none

private theorem fold_best' (F : Formula n) (xs : List (Assignment n))
    (initial : Option (Assignment n)) :
    ∀ x∈initial.toList++xs, ∃ z, xs.foldl (keepBest F) initial=some z ∧ score F x≤score F z := by
  induction xs generalizing initial with
  | nil =>
    intro x hx
    cases initial with
    | none => simp at hx
    | some z =>
      have he : x=z := by simpa using hx
      subst x; exact ⟨z,rfl,le_refl _⟩
  | cons y ys ih =>
    intro x hx
    by_cases ht : x∈ys
    · exact ih (keepBest F initial y) x (by simp [ht])
    · have hp : x∈initial.toList ∨ x=y := by simpa [ht] using hx
      have hk : ∃ z, keepBest F initial y=some z ∧ score F x≤score F z := by
        cases initial with
        | none =>
          have he : x=y := by simpa using hp
          subst x; exact ⟨y,rfl,le_refl _⟩
        | some a =>
          have hh : x=a ∨ x=y := by simpa using hp
          by_cases h : score F y≤score F a
          · refine ⟨a,by simp [keepBest,h],?_⟩
            rcases hh with rfl | rfl <;> omega
          · refine ⟨y,by simp [keepBest,h],?_⟩
            rcases hh with rfl | rfl <;> omega
      rcases hk with ⟨z,hz,hxz⟩
      rcases ih (keepBest F initial y) z (by simp [hz]) with ⟨w,hw,hzw⟩
      exact ⟨w,hw,le_trans hxz hzw⟩

/-- Shared best-solution accumulator bound, also used by weighted search. -/
theorem fold_best_bound (F : Formula n) (xs : List (Assignment n))
    (initial : Option (Assignment n)) :
    ∀ x∈initial.toList++xs, ∃ z, xs.foldl (keepBest F) initial=some z ∧
      score F x≤score F z := fold_best' F xs initial

theorem solve_correct (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (hF : wellFormed F) : ∃ x, solve F p P=some x ∧ ∀ y, score F y≤score F x := by
  rcases exists_optimal_admissible F p P hF with ⟨x,hx,hm⟩
  rcases fold_best' F (outputs F p P) none x (by simpa using (mem_outputs F p P x).mpr hx) with ⟨z,hz,hxz⟩
  refine ⟨z,?_,fun y => le_trans (hm y) hxz⟩
  simpa [solve,fold_eq_foldl,outputs] using hz

end Max2SAT.Bias.Hybrid
