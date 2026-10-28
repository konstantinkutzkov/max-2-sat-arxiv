import Max2SAT.Random.SearchCounts
import Max2SAT.Random.CanonicalOrder

/-! The probability/count estimate now bounds the actual initialized
RandomFormula search when the fixed support has no isolated labels. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

def halfPrefix (n : ℕ) : Finset (Fin n) :=
  ((List.finRange n).take ((n+1)/2)).toFinset

theorem half_prefix_card : (halfPrefix n).card=(n+1)/2 := by
  rw [halfPrefix,List.toFinset_card_of_nodup ((List.nodup_finRange n).take)]
  simp only [List.length_take,List.length_finRange]
  have h : (n+1)/2≤n := by omega
  exact min_eq_left h

theorem neighbors_imply_active (F : Formula n) (i j : Fin n)
    (hj : j∈Random.neighbors F i) : i∈Random.active F := by
  obtain ⟨c,hc,hj⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hj)
  cases c with
  | unit a => simp at hj
  | pair a b =>
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    refine ⟨.pair a b,hc,?_⟩
    by_cases ha : a.var=i
    · simp [Random.clauseVars,ha]
    · by_cases hb : b.var=i
      · simp [Random.clauseVars,hb]
      · simp [ha,hb] at hj

theorem generated_all_active (K : E → Pattern m) (hp : ∀ e, present (K e))
    (units : List (Literal n)) (hd : ∀ i, 0<(incident E i).card) :
    Random.active (generate E K units)=Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  have h := hd i
  rw [←observed_degree E K hp units i] at h
  obtain ⟨j,hj⟩ := Finset.card_pos.mp h
  exact neighbors_imply_active _ i j hj

theorem initialized_candidate_identity (F : Formula n) (hF : wellFormed F)
    (ha : Random.active F=Finset.univ) (E : Finset (Edge n))
    (hw : ∀ i, (Random.weight F i:ℝ)=supportWeight E i) :
    Random.candidateCount F=candidateCount E F (halfPrefix n) := by
  unfold Random.candidateCount
  simp only [ha,ordered_univ,List.length_finRange,core_eq_of_active F ha]
  apply congrArg Finset.card
  ext y
  simp only [Random.pathCandidates,Finset.mem_filter,Finset.mem_univ,true_and,
    List.take_append_drop,List.toFinset_finRange,Compatible]
  have he := path_excess_score (preprocess F).1 (preprocess_finished F hF).1 (Random.weight F)
    ((List.finRange n).drop ((n+1)/2)) ((List.finRange n).take ((n+1)/2)) y
  rw [list_comparison_preprocess F hF] at he
  rw [list_comparison_sum E F _ _ _ y ((List.nodup_finRange n).take)
    (canonical_take_drop _) (fun i _ => hw i)] at he
  simp only [not_true_eq_false,false_implies,implies_true,true_and]
  unfold halfPrefix
  rw [←he]
  exact_mod_cast (Iff.rfl :
    Random.pathExcess (preprocess F).1 (Random.weight F)
      ((List.finRange n).drop ((n+1)/2)) ((List.finRange n).take ((n+1)/2)) y≤0 ↔ _)

theorem fixed_support_search_expectation (p : E → PairLaw m κ)
    (hm : 0<m) (hk : 0<κ) (hn : 0<n) (units : List (Literal n))
    (hd : ∀ i, 0<(incident E i).card)
    (hp : ∀ K, 0<(product (fun e => (p e).law)).mass K → ∀ e, present (K e)) :
    expect (product (fun e => (p e).law)) (fun K => (Random.nodeCount (generate E K units):ℝ))≤
      (2:ℝ)^((n+1)/2+1)+6*n*(2:ℝ)^n*Real.exp (-runtimeConstant m κ*n) := by
  have hc : 0<(halfPrefix n).card := by rw [half_prefix_card]; omega
  have hh : n≤2*(halfPrefix n).card := by rw [half_prefix_card]; omega
  have he := fixed_support_candidate_expectation p hm hk units (halfPrefix n) hc (fun i _ => hd i) hh
  have hi : expect (product (fun e => (p e).law))
      (fun K => (Random.candidateCount (generate E K units):ℝ)) =
      expect (product (fun e => (p e).law)) (fun K => (candidateCount E (generate E K units) (halfPrefix n):ℝ)) := by
    apply expect_congr_support
    intro K hK
    rw [initialized_candidate_identity _ (generate_wellFormed E K units)
      (generated_all_active K (hp K hK) units hd) E (fun i => (support_weight_eq K (hp K hK) units i).symm)]
  have h := Random.expected_nodes_of_candidates (product (fun e => (p e).law))
    (fun K => generate E K units) n
    (fun K => by simpa using Finset.card_le_univ (Random.active (generate E K units)))
    (3*(2:ℝ)^n*Real.exp (-runtimeConstant m κ*n)) (by rw [hi]; exact he)
  convert h using 1
  ring


theorem fixed_support_search_tail (p : E → PairLaw m κ)
    (hm : 0<m) (hk : 0<κ) (hn : 0<n) (units : List (Literal n))
    (hd : ∀ i, 0<(incident E i).card)
    (hp : ∀ K, 0<(product (fun e => (p e).law)).mass K → ∀ e, present (K e)) :
    prob (product (fun e => (p e).law)) (fun K =>
      (2:ℝ)^((n+1)/2+1)+2*n*(2:ℝ)^n*Real.exp (-runtimeConstant m κ*n/2) <
        (Random.nodeCount (generate E K units):ℝ))≤
      3*Real.exp (-runtimeConstant m κ*n/2) := by
  have hc : 0<(halfPrefix n).card := by rw [half_prefix_card]; omega
  have hh : n≤2*(halfPrefix n).card := by rw [half_prefix_card]; omega
  apply (prob_mono_support (product (fun e => (p e).law)) _
    (fun K => (2:ℝ)^n*Real.exp (-runtimeConstant m κ*n/2) <
      (candidateCount E (generate E K units) (halfPrefix n):ℝ)) ?_).trans
  · exact fixed_support_candidate_tail p hm hk units (halfPrefix n) hc (fun i _ => hd i) hh
  · intro K hK hbad
    have ha := generated_all_active K (hp K hK) units hd
    have hb := Random.nodes_le_candidates (generate E K units)
    rw [ha,Finset.card_univ,Fintype.card_fin,
      initialized_candidate_identity _ (generate_wellFormed E K units) ha E
        (fun i => (support_weight_eq K (hp K hK) units i).symm)] at hb
    have hb' : (Random.nodeCount (generate E K units):ℝ)≤
        (2:ℝ)^((n+1)/2+1)+2*n*(candidateCount E (generate E K units) (halfPrefix n):ℝ) := by
      exact_mod_cast hb.trans (Nat.add_le_add_right (Nat.sub_le _ _) _)
    by_contra hh
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hh) (show (0:ℝ)≤2*n by positivity)
    nlinarith

/-- This is exactly the retained-pair model after conditioning on the
observed support. Nonemptiness is derived from the conditioning law. -/
theorem retained_support_search_expectation (p : E → PairLaw m κ)
    (hret : ∀ e, 0<prob (p e).law present)
    (hm : 0<m) (hk : 0<κ) (hn : 0<n) (units : List (Literal n))
    (hd : ∀ i, 0<(incident E i).card) :
    expect (product (fun e => (retained (p e) (hret e)).law))
      (fun K => (Random.nodeCount (generate E K units):ℝ))≤
      (2:ℝ)^((n+1)/2+1)+6*n*(2:ℝ)^n*Real.exp (-runtimeConstant m κ*n) :=
  fixed_support_search_expectation (fun e => retained (p e) (hret e)) hm hk hn units hd
    (fun K hK => retained_base_present p hret K hK)

theorem retained_support_search_tail (p : E → PairLaw m κ)
    (hret : ∀ e, 0<prob (p e).law present)
    (hm : 0<m) (hk : 0<κ) (hn : 0<n) (units : List (Literal n))
    (hd : ∀ i, 0<(incident E i).card) :
    prob (product (fun e => (retained (p e) (hret e)).law)) (fun K =>
      (2:ℝ)^((n+1)/2+1)+2*n*(2:ℝ)^n*Real.exp (-runtimeConstant m κ*n/2) <
        (Random.nodeCount (generate E K units):ℝ))≤
      3*Real.exp (-runtimeConstant m κ*n/2) :=
  fixed_support_search_tail (fun e => retained (p e) (hret e)) hm hk hn units hd
    (fun K hK => retained_base_present p hret K hK)

end
end Max2SAT.RandomInput
