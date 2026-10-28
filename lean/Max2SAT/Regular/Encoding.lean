import Max2SAT.Regular.Rows

namespace Max2SAT.Regular
open Counts
variable {n : ℕ}

def cutPair (i j : Fin n) : Formula n :=
  [.pair ⟨i,true⟩ ⟨j,true⟩,.pair ⟨i,false⟩ ⟨j,false⟩]

def edgeSet (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => e.1<e.2 ∧ G.Adj e.1 e.2)

noncomputable def formula (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) : Formula n :=
  units.map Clause.unit ++ (edgeSet G).toList.flatMap (fun e => cutPair e.1 e.2)

theorem cut_pair_wellFormed (i j : Fin n) (hij : i≠j) : wellFormed (cutPair i j) := by
  intro c hc
  simp only [cutPair,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl <;> exact hij

theorem formula_wellFormed (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) : wellFormed (formula G units) := by
  intro c hc
  simp only [formula,List.mem_append,List.mem_map,List.mem_flatMap,Finset.mem_toList] at hc
  rcases hc with ⟨a,_,rfl⟩ | ⟨e,he,hc⟩
  · trivial
  · exact cut_pair_wellFormed e.1 e.2 (ne_of_lt (Finset.mem_filter.mp he).2.1) c hc

theorem terms_append_coeff (xs ys : List (Literal n)) (w : Fin n) :
    (termsExpr (xs++ys)).coeff w=(termsExpr xs).coeff w+(termsExpr ys).coeff w := by
  induction xs with
  | nil => simp [termsExpr,Affine.zero]
  | cons a xs ih => simpa [termsExpr,Affine.add,add_assoc] using congrArg ((literalExpr a).coeff w+·) ih

theorem gain_coeff_append (F H : Formula n) (t w : Fin n) :
    (gainExpr (F++H) t).coeff w=(gainExpr F t).coeff w+(gainExpr H t).coeff w := by
  simp only [gainExpr,Affine.shift,pruningConstraint,List.flatMap_append,terms_append_coeff]

theorem gain_coeff_flatMap {α : Type*} (L : List α) (f : α → Formula n) (t w : Fin n) :
    (gainExpr (L.flatMap f) t).coeff w=(L.map (fun a => (gainExpr (f a) t).coeff w)).sum := by
  induction L with
  | nil => simp [gainExpr,pruningConstraint,termsExpr,Affine.shift,Affine.zero]
  | cons a L ih => simp [gain_coeff_append,ih]

theorem units_coeff (units : List (Literal n)) (t w : Fin n) :
    (gainExpr (units.map Clause.unit) t).coeff w=0 := by
  induction units with
  | nil => simp [gainExpr,pruningConstraint,termsExpr,Affine.shift,Affine.zero]
  | cons a units ih =>
    have h : (gainExpr [Clause.unit a] t).coeff w=0 := by
      simp only [gainExpr,pruningConstraint,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,Affine.shift,Clause.cutPart]
      split_ifs <;> rfl
    change (gainExpr ([Clause.unit a]++units.map Clause.unit) t).coeff w=0
    rw [gain_coeff_append,h,ih,add_zero]

theorem cut_pair_coeff (i j t w : Fin n) (hij : i≠j) :
    (gainExpr (cutPair i j) t).coeff w=
      if (t=i ∧ w=j) ∨ (t=j ∧ w=i) then -2 else 0 := by
  by_cases htw : t=w
  · subst w
    rw [gainExpr_diagonal _ _ (cut_pair_wellFormed i j hij)]
    split_ifs with h
    · rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> contradiction
    · rfl
  · rw [coeff_eval_difference]
    simp only [gainExpr_eval _ _ _ (cut_pair_wellFormed i j hij),scoreGain]
    by_cases hti : t=i <;> by_cases htj : t=j <;> by_cases hwi : w=i <;> by_cases hwj : w=j
    all_goals simp_all [cutPair,score,Clause.score,Literal.eval,
      (eq_comm : i=t ↔ t=i),(eq_comm : j=t ↔ t=j),
      (eq_comm : i=w ↔ w=i),(eq_comm : j=w ↔ w=j),(eq_comm : j=i ↔ i=j)]
    all_goals norm_num

theorem formula_coeff_sum (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) (t w : Fin n) :
    (gainExpr (formula G units) t).coeff w=
      ∑ e∈edgeSet G, if (t=e.1 ∧ w=e.2) ∨ (t=e.2 ∧ w=e.1) then (-2:ℚ) else 0 := by
  rw [formula,gain_coeff_append,units_coeff,zero_add,gain_coeff_flatMap]
  rw [Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro e he
  exact cut_pair_coeff e.1 e.2 t w (ne_of_lt (Finset.mem_filter.mp he).2.1)

theorem formula_coeff_ordered (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) (t w : Fin n) (htw : t<w) :
    (gainExpr (formula G units) t).coeff w= -2*G.adjMatrix ℚ t w := by
  rw [formula_coeff_sum]
  have hf : (∑ e∈edgeSet G, if (t=e.1 ∧ w=e.2) ∨ (t=e.2 ∧ w=e.1) then (-2:ℚ) else 0)=
      ∑ e∈edgeSet G, if e=(t,w) then (-2:ℚ) else 0 := by
    apply Finset.sum_congr rfl
    intro e he
    have he' := (Finset.mem_filter.mp he).2.1
    have hi : ((t=e.1 ∧ w=e.2) ∨ (t=e.2 ∧ w=e.1)) ↔ e=(t,w) := by
      constructor
      · rintro (⟨ht,hw⟩|⟨ht,hw⟩)
        · exact Prod.ext ht.symm hw.symm
        · have hh : w<t := by simpa only [←ht,←hw] using he'
          exact (lt_asymm htw hh).elim
      · rintro rfl
        simp
    simp only [hi]
  rw [hf]
  simp [edgeSet,htw,SimpleGraph.adjMatrix_apply]

theorem formula_coeff (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) (t w : Fin n) :
    (gainExpr (formula G units) t).coeff w= -2*G.adjMatrix ℚ t w := by
  rcases lt_trichotomy t w with h|rfl|h
  · exact formula_coeff_ordered G units t w h
  · rw [gainExpr_diagonal _ _ (formula_wellFormed G units)]
    simp
  · rw [gainExpr_symmetric _ (formula_wellFormed G units),formula_coeff_ordered G units w t h]
    congr 1
    exact congrFun (congrFun (G.transpose_adjMatrix (α:=ℚ)) t) w

theorem count_matrix_formula (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) (d : ℕ) :
    interactionMatrix (countGain (formula G units) (correction n d) 0)=corrected G d := by
  ext t w
  simp only [interactionMatrix,countGain,Affine.add,Affine.shift,Affine.scale,without,
    formula_coeff]
  by_cases h:t=w
  · subst w
    simp [corrected]
  · by_cases hadj : G.Adj t w <;>
      simp [corrected,h,Ne.symm h,SimpleGraph.adjMatrix_apply,hadj,sub_eq_add_neg]

end Max2SAT.Regular

