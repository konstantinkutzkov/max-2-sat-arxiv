import Max2SAT.Bias.Complexity

/-! Explicit recursion depth and constraint representation bounds. These are
mathematical resource bounds, not claims about a particular Lean compiler. -/
namespace Max2SAT.Bias
namespace Single

def depth (C : Constraint n) : List (Fin n) → Assignment n → ℕ
  | [], _ => 1
  | i::is, x => if reject C (i::is) x then 1 else
      1+max (depth C is (Function.update x i false)) (depth C is (Function.update x i true))

theorem depth_bound (C : Constraint n) (free : List (Fin n)) (x : Assignment n) :
    depth C free x≤free.length+1 := by
  induction free generalizing x with
  | nil => simp [depth]
  | cons i is ih =>
    simp only [depth]
    split
    · simp
    · have h0 := ih (Function.update x i false)
      have h1 := ih (Function.update x i true)
      simp only [List.length_cons]
      omega
end Single
namespace Hybrid

def depth (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (suffix : List (Fin n)) : List (Fin n) → Assignment n → ℕ
  | [], x => Single.depth (Constraint.sum (cuts F p (ordered P) x)) suffix x
  | i::is, x => 1+max (depth F p P suffix is (Function.update x i false))
      (depth F p P suffix is (Function.update x i true))

theorem depth_bound (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (pre suffix : List (Fin n)) (x : Assignment n) :
    depth F p P suffix pre x≤pre.length+suffix.length+1 := by
  induction pre generalizing x with
  | nil => simpa [depth] using Single.depth_bound _ suffix x
  | cons i is ih =>
    have h0 := ih (Function.update x i false)
    have h1 := ih (Function.update x i true)
    simp only [depth,List.length_cons]
    omega

theorem solve_depth (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n)) :
    depth F p P (ordered Pᶜ) (ordered P) (fun _ => false)≤n+1 := by
  have hh := depth_bound F p P (ordered P) (ordered Pᶜ) (fun _ => false)
  simpa [Finset.card_add_card_compl] using hh
end Hybrid

private theorem part_bounds (c : Clause n) (v : Literal n) :
    (c.cutPart v).1.length≤1 ∧ |(c.cutPart v).2|≤1 := by
  cases c <;> simp only [Clause.cutPart] <;> split_ifs <;> norm_num

theorem pruning_storage (F : Formula n) (v : Literal n) :
    (pruningConstraint F v).terms.length≤F.length ∧
      |(pruningConstraint F v).bound|≤(F.length:ℤ)+1 := by
  have hp : ∀ F : Formula n,
      (F.flatMap (fun c => (c.cutPart v).1)).length≤F.length ∧
      |(F.map (fun c => (c.cutPart v).2)).sum|≤(F.length:ℤ) := by
    intro G
    induction G with
    | nil => simp
    | cons c G ih =>
      rcases part_bounds c v with ⟨hl,hb⟩
      simp only [List.flatMap_cons,List.length_append,List.length_cons,
        List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
      constructor
      · omega
      · have ha := abs_add_le (c.cutPart v).2 (G.map (fun c => (c.cutPart v).2)).sum
        linarith [ih.2]
  refine ⟨(hp F).1,?_⟩
  have ha := abs_add_le (F.map (fun c => (c.cutPart v).2)).sum (-1)
  change |(F.map (fun c => (c.cutPart v).2)).sum-1|≤_
  norm_num [←sub_eq_add_neg] at ha
  linarith [(hp F).2]

theorem cuts_storage (F : Formula n) (p : Fin n → Bool) (is : List (Fin n))
    (x : Assignment n) :
    (Constraint.sum (cuts F p is x)).terms.length≤ is.length*F.length ∧
    |(Constraint.sum (cuts F p is x)).bound|≤(is.length:ℤ)*((F.length:ℤ)+1) := by
  induction is with
  | nil => simp [cuts,Constraint.sum]
  | cons i is ih =>
    by_cases h : x i=p i
    · simp only [cuts,List.filterMap_cons,ite_eq_left h,List.length_cons,Nat.cast_add,Nat.cast_one] at *
      constructor
      · nlinarith [ih.1]
      · nlinarith [ih.2]
    · have hp := pruning_storage F (preferred p i)
      simp only [cuts,List.filterMap_cons,ite_eq_right h,Constraint.sum,List.foldr_cons,
        Constraint.add,List.length_append,List.length_cons,Nat.cast_add,Nat.cast_one] at *
      constructor
      · nlinarith [ih.1,hp.1]
      · have ha := abs_add_le (pruningConstraint F (preferred p i)).bound
          (List.foldr Constraint.add ⟨[],0⟩ (cuts F p is x)).bound
        dsimp [cuts] at ha
        nlinarith [ih.2,hp.2]

theorem sum_storage (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (x : Assignment n) :
    (Constraint.sum (cuts F p (ordered P) x)).terms.length≤n*F.length ∧
    |(Constraint.sum (cuts F p (ordered P) x)).bound|≤(n:ℤ)*((F.length:ℤ)+1) := by
  have hh := cuts_storage F p (ordered P) x
  simp only [length_ordered] at hh
  have hc : P.card≤n := by simpa using Finset.card_le_univ P
  have hc' : (P.card:ℤ)≤n := by exact_mod_cast hc
  constructor
  · nlinarith [hh.1]
  · nlinarith [hh.2]

/-- Cancellation never increases the occurrence list and changes the bound by
at most its recursion fuel. -/
theorem cancellation_storage (fuel : ℕ) (C : Constraint n) :
    (Constraint.cancelAux fuel C).terms.length≤C.terms.length ∧
    |(Constraint.cancelAux fuel C).bound|≤|C.bound|+fuel := by
  induction fuel generalizing C with
  | zero => simp [Constraint.cancelAux]
  | succ fuel ih =>
    rcases C with ⟨terms,b⟩
    cases terms with
    | nil => simp [Constraint.cancelAux]; positivity
    | cons a terms =>
      by_cases h : a.neg∈terms
      · have ht := ih ⟨terms.erase a.neg,b-1⟩
        simp only [Constraint.cancelAux,ite_eq_left h,List.length_cons,Nat.cast_add,Nat.cast_one]
        have he := List.length_erase_le (l:=terms) (a:=a.neg)
        have hb := abs_add_le b (-1)
        norm_num [←sub_eq_add_neg] at hb
        constructor <;> dsimp at ht ⊢ <;> omega
      · have ht := ih ⟨terms,b⟩
        simp only [Constraint.cancelAux,ite_eq_right h,List.length_cons,Nat.cast_add,Nat.cast_one]
        constructor <;> dsimp at ht ⊢ <;> omega

private theorem lhs_length (terms : List (Literal n)) (x : Assignment n) :
    0≤(terms.map (fun a => a.value x)).sum ∧
      (terms.map (fun a => a.value x)).sum≤(terms.length:ℤ) := by
  induction terms with
  | nil => simp
  | cons a terms ih =>
    have h0 := a.value_nonneg x; have h1 := a.value_le_one x
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    constructor <;> omega

/-- Bound the exact checker data after substitution and complementary cancellation. -/
theorem checker_storage (C : Constraint n) (free : Finset (Fin n)) (x : Assignment n) :
    (Constraint.normalize (Constraint.restrict free x C)).terms.length≤C.terms.length ∧
    |(Constraint.normalize (Constraint.restrict free x C)).bound|≤
      |C.bound|+2*C.terms.length := by
  have hn := cancellation_storage (Constraint.restrict free x C).terms.length
    (Constraint.restrict free x C)
  change (Constraint.normalize _).terms.length≤_ ∧ |(Constraint.normalize _).bound|≤_ at hn
  have hl : (Constraint.restrict free x C).terms.length≤C.terms.length := List.length_filter_le _ _
  have hs := lhs_length (C.terms.filter (fun a => a.var∉free)) x
  have hf := List.length_filter_le (fun a : Literal n => decide (a.var∉free)) C.terms
  have hb : |(Constraint.restrict free x C).bound|≤|C.bound|+C.terms.length := by
    have ha := abs_add_le C.bound (-((C.terms.filter (fun a => a.var∉free)).map (fun a => a.value x)).sum)
    simp only [abs_neg,abs_of_nonneg hs.1] at ha
    change |C.bound-_|≤_
    simp only [sub_eq_add_neg]
    omega
  constructor <;> omega

end Max2SAT.Bias
