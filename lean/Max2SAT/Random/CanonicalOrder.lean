import Max2SAT.Random.ScorePaths

namespace Max2SAT.RandomInput
noncomputable section
variable {n : ℕ}

theorem canonical_of_append (pre suffix : List (Fin n))
    (h : pre++suffix=List.finRange n) : CanonicalPrefix suffix pre := by
  intro before i after he
  have hf : before++(i::after++suffix)=List.finRange n := by
    simpa only [he,List.append_assoc,List.cons_append] using h
  have hs := List.pairwise_lt_finRange n
  rw [←hf,List.pairwise_append] at hs
  have hi := List.pairwise_cons.mp hs.2.1
  ext j
  simp only [List.mem_toFinset,mem_orderedFree]
  change (j∈i::after++suffix ↔ i≤j)
  constructor
  · intro hj
    rcases List.mem_cons.mp hj with hj | hj
    · subst j; rfl
    · exact (hi.1 j hj).le
  · intro hij
    have hj : j∈before++(i::after++suffix) := by rw [hf]; exact List.mem_finRange j
    rcases List.mem_append.mp hj with hj | hj
    · have hh := hs.2.2 j hj i (by simp)
      exact False.elim ((not_lt_of_ge hij) hh)
    · exact hj

theorem canonical_take_drop (T : ℕ) :
    CanonicalPrefix ((List.finRange n).drop T) ((List.finRange n).take T) :=
  canonical_of_append _ _ (List.take_append_drop T _)

theorem ordered_univ : Bias.ordered (Finset.univ : Finset (Fin n))=List.finRange n := by
  exact Fin.sort_univ n

theorem restrict_univ (F : Formula n) (x : Assignment n) :
    (Residual.restrict Finset.univ x F).1=F := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    simp only [Residual.restrict,List.flatMap_cons] at *
    rw [ih]
    cases c <;> simp [Residual.clause]

theorem core_eq_of_active (F : Formula n) (h : Random.active F=Finset.univ) :
    Random.core F=F := by simp only [Random.core,h,restrict_univ]

end
end Max2SAT.RandomInput
