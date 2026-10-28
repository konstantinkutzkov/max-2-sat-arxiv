import Max2SAT.Random.ActiveSupport

/-! The actual order skips isolated labels. Its comparisons coincide with
the increasing-label exposure because no binary neighbor was skipped. -/
namespace Max2SAT.RandomInput
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {E : Finset (Edge n)}

theorem gain_core_compatible (F : Formula n) (x : Assignment n) (i : Fin n)
    (hi : i∈Random.active F) (hc : Compatible (Random.active F) (Random.initial F) x) :
    gain (Random.core F) i x=gain F i x := by
  have hu (b : Bool) : Compatible (Random.active F) (Random.initial F) (Function.update x i b) := by
    intro j hj
    have hji : j≠i := by intro h; subst j; exact hj hi
    simpa [Function.update_of_ne hji] using hc j hj
  have h0 := Residual.restrict_score F (Random.active F) (Random.initial F) _ (hu false)
  have h1 := Residual.restrict_score F (Random.active F) (Random.initial F) _ (hu true)
  unfold gain
  rw [h0,h1]
  simp only [Random.core]
  congr 1
  ring

theorem list_comparison_core (F : Formula n) (w : Fin n → ℚ) (suffix pre : List (Fin n))
    (x : Assignment n) (hc : Compatible (Random.active F) (Random.initial F) x)
    (hp : ∀ i∈pre, i∈Random.active F) :
    listComparison (Random.core F) w suffix pre x=listComparison F w suffix pre x := by
  induction pre with
  | nil => rfl
  | cons i is ih =>
    have hi := hp i (by simp)
    rw [listComparison,listComparison,delta_core F _ x i (by simp) hi,
      gain_core_compatible F x i hi hc,ih (fun j hj => hp j (by simp [hj]))]

def ActiveCanonical (S : Finset (Fin n)) (suffix pre : List (Fin n)) : Prop :=
  ∀ before i after, pre=before++i::after →
    (i::after++suffix).toFinset=S∩orderedFree i.val

theorem active_canonical_of_append (S : Finset (Fin n)) (pre suffix : List (Fin n))
    (h : pre++suffix=Bias.ordered S) : ActiveCanonical S suffix pre := by
  intro before i after he
  have hf : before++(i::after++suffix)=Bias.ordered S := by
    simpa only [he,List.append_assoc,List.cons_append] using h
  have hs := (Finset.sortedLT_sort S).pairwise
  change (Bias.ordered S).Pairwise (fun a b => a<b) at hs
  rw [←hf,List.pairwise_append] at hs
  have hi := List.pairwise_cons.mp hs.2.1
  have hm (j : Fin n) : j∈before++(i::after++suffix) ↔ j∈S := by
    rw [hf]; simp [Bias.ordered]
  ext j
  simp only [List.mem_toFinset,Finset.mem_inter,mem_orderedFree]
  change (j∈i::after++suffix ↔ j∈S ∧ i≤j)
  constructor
  · intro hj
    refine ⟨(hm j).mp (List.mem_append_right _ hj),?_⟩
    rcases List.mem_cons.mp hj with hj | hj
    · subst j; rfl
    · exact (hi.1 j hj).le
  · rintro ⟨hj,hij⟩
    rcases List.mem_append.mp ((hm j).mpr hj) with hj | hj
    · exact False.elim ((not_lt_of_ge hij) (hs.2.2 j hj i (by simp)))
    · exact hj

theorem active_canonical_tail (S : Finset (Fin n)) (suffix : List (Fin n))
    (i : Fin n) (is : List (Fin n)) (h : ActiveCanonical S suffix (i::is)) :
    ActiveCanonical S suffix is := by
  intro before j after he
  apply h (i::before) j after
  simp [he]

theorem delta_active_free (K : E → Pattern m) (units : List (Literal n))
    (free : Finset (Fin n)) (x : Assignment n) (i : Fin n)
    (hi : i∈activeVertices E∩free) :
    delta (generate E K units) (activeVertices E∩free) x i=
      delta (generate E K units) free x i := by
  rw [generated_delta E K units _ i x hi,generated_delta E K units free i x (Finset.mem_inter.mp hi).2]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  simp only [Finset.mem_inter,(endpoints_active e).1,(endpoints_active e).2,true_and]

theorem list_comparison_active_sum (K : E → Pattern m) (units : List (Literal n))
    (w : Fin n → ℚ) (suffix pre : List (Fin n)) (x : Assignment n)
    (hn : pre.Nodup) (ho : ActiveCanonical (activeVertices E) suffix pre)
    (hw : ∀ i∈pre, (w i:ℝ)=supportWeight E i) :
    listComparison (generate E K units) w suffix pre x=
      comparisonSum E (generate E K units) pre.toFinset x := by
  induction pre with
  | nil => simp [listComparison,comparisonSum]
  | cons i is ih =>
    have hi := (List.nodup_cons.mp hn).1
    have hf := ho [] i is (by simp)
    have hmem : i∈activeVertices E∩orderedFree i.val := by rw [←hf]; simp
    rw [listComparison,hf,delta_active_free K units _ x i hmem,hw i (by simp),
      ih (List.nodup_cons.mp hn).2 (active_canonical_tail _ _ _ _ ho)
        (fun j hj => hw j (by simp [hj]))]
    simp [comparisonSum,hi]

theorem comparison_sum_active_agree (K : E → Pattern m) (units : List (Literal n))
    (C : Finset (Fin n)) (hC : C⊆activeVertices E) (x y : Assignment n)
    (hxy : ∀ i∈activeVertices E, x i=y i) :
    comparisonSum E (generate E K units) C x=comparisonSum E (generate E K units) C y := by
  unfold comparisonSum
  apply Finset.sum_congr rfl
  intro i hi
  have hg : gain (generate E K units) i x=gain (generate E K units) i y := by
    rw [generated_gain,generated_gain]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    rw [hxy _ (endpoints_active e).1,hxy _ (endpoints_active e).2]
  have hd : delta (generate E K units) (orderedFree i.val) x i=
      delta (generate E K units) (orderedFree i.val) y i := by
    rw [generated_delta _ _ _ _ _ _ (by simp),generated_delta _ _ _ _ _ _ (by simp)]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    rw [hxy _ (endpoints_active e).1,hxy _ (endpoints_active e).2]
  rw [hg,hd,hxy i (hC hi)]

end
end Max2SAT.RandomInput
