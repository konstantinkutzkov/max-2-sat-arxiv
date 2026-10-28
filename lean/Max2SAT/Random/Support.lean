import Max2SAT.Bias.Accumulation
import Max2SAT.PartialAssignment
import Mathlib.Data.Nat.Sqrt

/-! Formula-only initialization: observed binary support, distinct-neighbor
weights, and independent optimization of variables occurring only in units. -/
namespace Max2SAT.Random

def clauseVars : Clause n → List (Fin n)
  | .unit _ => []
  | .pair a b => [a.var,b.var]

def active (F : Formula n) : Finset (Fin n) := (F.flatMap clauseVars).toFinset

def neighbors (F : Formula n) (i : Fin n) : Finset (Fin n) :=
  (F.flatMap (fun c => match c with
    | .unit _ => []
    | .pair a b => if a.var=i then [b.var] else if b.var=i then [a.var] else [])).toFinset

theorem active_degree_positive (F : Formula n) (i : Fin n) (hi : i ∈ active F) :
    0 < (neighbors F i).card := by
  rcases List.mem_flatMap.mp (List.mem_toFinset.mp hi) with ⟨c,hc,hi⟩
  cases c with
  | unit a => simp [clauseVars] at hi
  | pair a b =>
    apply Finset.card_pos.mpr
    by_cases ha : a.var=i
    · refine ⟨b.var,List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨.pair a b,hc,?_⟩)⟩
      simp [ha]
    · have hb : b.var=i := by
        simp only [clauseVars,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with hi | hi
        · exact False.elim (ha hi.symm)
        · exact hi.symm
      refine ⟨a.var,List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨.pair a b,hc,?_⟩)⟩
      simp [ha,hb]

def weight (F : Formula n) (i : Fin n) : ℚ :=
  1 / ((Nat.sqrt ((neighbors F i).card-1) + 1 : ℕ) : ℚ)

theorem weight_positive (F : Formula n) (i : Fin n) : 0 < weight F i := by
  unfold weight
  positivity

/-- For positive degree this denominator is the least integer whose square
is at least the degree, i.e. ceil(sqrt(degree)). -/
theorem ceiling_sqrt (d : ℕ) (hd : 0 < d) :
    d ≤ (Nat.sqrt (d-1)+1)^2 ∧ ∀ k, d ≤ k^2 → Nat.sqrt (d-1)+1 ≤ k := by
  constructor
  · have hh := Nat.lt_succ_sqrt' (d-1)
    simp only [Nat.succ_eq_add_one] at hh
    omega
  · intro k hk
    have hh : d-1 < k^2 := by omega
    have hs := Nat.sqrt_lt'.mpr hh
    omega

def initial (F : Formula n) : Assignment n :=
  fun i => decide (d1 F ⟨i,false⟩ < d1 F ⟨i,true⟩)

def extend (F : Formula n) (x : Assignment n) : Assignment n :=
  fun i => if i ∈ active F then x i else initial F i

theorem extend_compatible (F : Formula n) (x : Assignment n) :
    Compatible (active F) (initial F) (extend F x) := by
  intro i hi
  simp [extend,hi]

private def pairScore (c : Clause n) (x : Assignment n) : ℤ :=
  match c with | .unit _ => 0 | .pair a b => Clause.score x (.pair a b)

private theorem clause_decomposition (c : Clause n) (x : Assignment n) :
    c.score x = pairScore c x + ∑ i, c.unitCount ⟨i,x i⟩ := by
  cases c with
  | pair a b => simp [pairScore,Clause.unitCount]
  | unit a =>
    have he : ∀ i, (Clause.unit a).unitCount ⟨i,x i⟩ =
        if i=a.var then a.value x else 0 := by
      intro i
      rcases a with ⟨j,p⟩
      by_cases hi : i=j
      · subst i
        cases hx : x j <;> cases p <;>
          simp [Clause.unitCount,Literal.value,Literal.eval,hx]
      · simp [Clause.unitCount,Literal.mk.injEq,hi,Ne.symm hi]
    simp_rw [he]
    simp [pairScore,Clause.score]

private theorem score_decomposition (F : Formula n) (x : Assignment n) :
    score F x = (F.map (fun c => pairScore c x)).sum + ∑ i, d1 F ⟨i,x i⟩ := by
  induction F with
  | nil => simp [d1]
  | cons c F ih =>
    rw [score_cons,clause_decomposition,ih]
    simp only [List.map_cons,List.sum_cons,d1]
    rw [Finset.sum_add_distrib]
    ring

private theorem pair_mem_active (F : Formula n) (a b : Literal n)
    (h : Clause.pair a b ∈ F) : a.var ∈ active F ∧ b.var ∈ active F := by
  constructor
  all_goals
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    exact ⟨.pair a b,h,by simp [clauseVars]⟩

/-- Independent unit optimization never lowers the original score and leaves
every variable occurring in a binary clause unchanged. -/
theorem extend_score (F : Formula n) (x : Assignment n) :
    score F x ≤ score F (extend F x) := by
  have hp : (F.map (fun c => pairScore c x)).sum =
      (F.map (fun c => pairScore c (extend F x))).sum := by
    congr 1
    apply List.map_congr_left
    intro c hc
    cases c with
    | unit a => rfl
    | pair a b =>
      rcases pair_mem_active F a b hc with ⟨ha,hb⟩
      simp [pairScore,Clause.score,Literal.eval,extend,ha,hb]
  have hu : (∑ i, d1 F ⟨i,x i⟩) ≤ ∑ i, d1 F ⟨i,extend F x i⟩ := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i ∈ active F
    · simp [extend,hi]
    · by_cases h : d1 F ⟨i,false⟩ < d1 F ⟨i,true⟩
      · cases x i <;> simp [extend,hi,initial,h]
        all_goals omega
      · cases x i <;> simp [extend,hi,initial,h]
        all_goals omega
  rw [score_decomposition,score_decomposition,hp]
  exact add_le_add (le_refl _) hu

end Max2SAT.Random
