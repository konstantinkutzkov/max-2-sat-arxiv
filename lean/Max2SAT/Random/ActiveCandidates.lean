import Max2SAT.Random.ActivePaths
import Max2SAT.Random.ActiveCounting
import Max2SAT.Random.ActiveConcentration

namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {E : Finset (Edge n)}

def supportPrefix (E : Finset (Edge n)) : Finset (Fin n) :=
  ((Bias.ordered (activeVertices E)).take (((activeVertices E).card+1)/2)).toFinset

theorem support_prefix_card : (supportPrefix E).card=((activeVertices E).card+1)/2 := by
  rw [supportPrefix,List.toFinset_card_of_nodup ((Bias.ordered_nodup _).take)]
  simp only [List.length_take,Bias.length_ordered]
  have h : ((activeVertices E).card+1)/2≤(activeVertices E).card := by omega
  exact min_eq_left h

theorem support_prefix_subset : supportPrefix E⊆activeVertices E := by
  intro i hi
  have h := (List.take_sublist _ (Bias.ordered (activeVertices E))).subset
    (List.mem_toFinset.mp hi)
  simpa [Bias.ordered] using h

theorem list_comparison_equivalent (F G : Formula n) (s : ℤ)
    (hF : wellFormed F) (hG : wellFormed G) (he : EquivalentWithOffset F G s)
    (w : Fin n → ℚ) (suffix pre : List (Fin n)) (x : Assignment n) :
    listComparison F w suffix pre x=listComparison G w suffix pre x := by
  have hg (i : Fin n) : gain F i x=gain G i x := by
    unfold gain
    rw [he,he]
    congr 1
    ring
  induction pre with
  | nil => rfl
  | cons i is ih =>
    simp only [listComparison,delta_equivalent F G s he hF hG,hg,ih]

/-- The formula may be presented in any score-equivalent clause order.
Only its observed support and weights are needed to identify the count. -/
theorem initialized_candidate_probability (F : Formula n) (hF : wellFormed F)
    (K : E → Pattern m) (units : List (Literal n)) (s : ℤ)
    (he : EquivalentWithOffset F (generate E K units) s)
    (ha : Random.active F=activeVertices E)
    (hw : ∀ i, (Random.weight F i:ℝ)=supportWeight E i) :
    (Random.candidateCount F:ℝ)=(2:ℝ)^(activeVertices E).card*
      prob (fairBits (Fin n)) (fun x => comparisonSum E (generate E K units) (supportPrefix E) x≤0) := by
  let U := Bias.ordered (activeVertices E)
  let T := ((activeVertices E).card+1)/2
  have hpre : ∀ i∈U.take T, i∈Random.active F := by
    intro i hi
    rw [ha]
    exact support_prefix_subset (List.mem_toFinset.mpr hi)
  have hid (x : Assignment n) (hc : Compatible (activeVertices E) (Random.initial F) x) :
      (Random.pathExcess (preprocess (Random.core F)).1 (Random.weight F) (U.drop T) (U.take T) x:ℝ)=
        comparisonSum E (generate E K units) (supportPrefix E) x := by
    have hcore : wellFormed (Random.core F) :=
      Residual.restrict_wellFormed F (Random.active F) (Random.initial F) hF
    rw [path_excess_score (preprocess (Random.core F)).1
        (preprocess_finished (Random.core F) hcore).1 (Random.weight F) (U.drop T) (U.take T) x,
      list_comparison_preprocess (Random.core F) hcore,
      list_comparison_core F _ _ _ x (by simpa only [ha] using hc) hpre,
      list_comparison_equivalent F (generate E K units) s hF (generate_wellFormed E K units) he,
      list_comparison_active_sum K units _ _ _ x ((Bias.ordered_nodup _).take)
        (active_canonical_of_append _ _ _ (List.take_append_drop T U)) (fun i _ => hw i)]
    rfl
  have hs : Random.pathCandidates (preprocess (Random.core F)).1 (Random.weight F)
      (U.drop T) (U.take T) (Random.initial F)=
      Finset.univ.filter (fun x => Compatible (activeVertices E) (Random.initial F) x ∧
        comparisonSum E (generate E K units) (supportPrefix E) x≤0) := by
    ext x
    simp only [Random.pathCandidates,Finset.mem_filter,Finset.mem_univ,true_and,
      List.take_append_drop,U,Bias.ordered,Finset.sort_toFinset]
    apply and_congr_right
    intro hc
    rw [←hid x hc]
    exact_mod_cast (Iff.rfl : Random.pathExcess (preprocess (Random.core F)).1 (Random.weight F)
      (U.drop T) (U.take T) x≤0 ↔ _)
  unfold Random.candidateCount
  simp only [ha,Bias.length_ordered]
  change ((Random.pathCandidates _ _ (U.drop T) (U.take T) _).card:ℝ)=_
  rw [hs]
  exact fixed_coordinate_count _ _ _ (fun x y hxy => by
    rw [comparison_sum_active_agree K units _ support_prefix_subset x y hxy])

theorem generated_candidate_probability (K : E → Pattern m) (hp : ∀ e, present (K e))
    (units : List (Literal n)) :
    (Random.candidateCount (generate E K units):ℝ)=(2:ℝ)^(activeVertices E).card*
      prob (fairBits (Fin n)) (fun x => comparisonSum E (generate E K units) (supportPrefix E) x≤0) :=
  initialized_candidate_probability _ (generate_wellFormed E K units) K units 0
    (fun _ => by simp) (generated_active K hp units) (fun i => (support_weight_eq K hp units i).symm)

end
end Max2SAT.RandomInput
