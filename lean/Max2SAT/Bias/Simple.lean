import Max2SAT.Bias.Incidence

/-! Simplicity concerns logical clauses: reversing the order of a binary
clause does not create a different clause. Preprocessed formulas need not
remain simple, since reductions may produce repeated unit clauses. -/
namespace Max2SAT

def Clause.literalSet : Clause n → Finset (Literal n)
  | .unit a => {a}
  | .pair a b => {a,b}

def Simple (F : Formula n) : Prop :=
  wellFormed F ∧ (F.map Clause.literalSet).Nodup

namespace Bias

private def incidentKeys (i : Fin n) : Finset (Finset (Literal n)) :=
  (Finset.univ.image (fun p : Bool => ({⟨i,p⟩} : Finset (Literal n)))) ∪
  (((Finset.univ.erase i).product
    ((Finset.univ : Finset Bool).product Finset.univ)).image
      (fun t => ({⟨i,t.2.1⟩,⟨t.1,t.2.2⟩} : Finset (Literal n))))

private theorem incidentKeys_card (i : Fin n) :
    (incidentKeys i).card ≤ 4 * (n-1) + 2 := by
  unfold incidentKeys
  apply le_trans (Finset.card_union_le _ _)
  apply le_trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
  simp [Finset.card_product, Finset.card_erase_of_mem]
  omega

private theorem incidentKey_mem (c : Clause n) (i : Fin n)
    (hc : clauseD i c + clauseU i c = 1) : c.literalSet ∈ incidentKeys i := by
  cases c with
  | unit a =>
    have hi : a.var = i := by
      simpa [clauseD, clauseU] using hc
    rcases a with ⟨j,p⟩
    change j = i at hi
    subst j
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
  | pair a b =>
    rcases a with ⟨j,p⟩
    rcases b with ⟨k,q⟩
    change (if j=i then 1 else 0) + (if k=i then 1 else 0) + 0 = 1 at hc
    by_cases hj : j=i
    · subst j
      have hk : k ≠ i := by intro he; subst k; simp at hc
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(k,(p,q)), ?_, rfl⟩
      simp [hk]
    · have hk : k=i := by by_contra hk; simp [hj,hk] at hc
      subst k
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(j,(q,p)), ?_, ?_⟩
      · simp [hj]
      · simp [Clause.literalSet, Finset.pair_comm]

private theorem occurrence_filter (F : Formula n) (i : Fin n) (hF : wellFormed F) :
    B F i = (F.filter (fun c => decide (clauseD i c + clauseU i c = 1))).length := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    have hc := hF c (by simp)
    have ht := ih (fun e he => hF e (by simp [he]))
    have hb : clauseD i c + clauseU i c ≤ 1 := by
      cases c with
      | unit a => simp [clauseD,clauseU]; split_ifs <;> omega
      | pair a b =>
        change a.var ≠ b.var at hc
        simp only [clauseD,clauseU]
        split_ifs <;> omega
    simp only [B,D,U,List.map_cons,List.sum_cons] at *
    simp only [List.filter_cons]
    split <;> simp_all <;> omega

/-- At most four sign patterns per other variable, and two unit clauses.
No orientation convention on the input clause lists is assumed. -/
theorem simple_occurrences (F : Formula n) (hF : Simple F) (i : Fin n) :
    B F i ≤ 4 * (n-1) + 2 := by
  let L := F.filter (fun c => decide (clauseD i c + clauseU i c = 1))
  have hsub : (L.map Clause.literalSet).Sublist (F.map Clause.literalSet) :=
    (List.filter_sublist).map Clause.literalSet
  have hnd : (L.map Clause.literalSet).Nodup := hF.2.sublist hsub
  have hcard : (L.map Clause.literalSet).toFinset.card = L.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  have hmem : (L.map Clause.literalSet).toFinset ⊆ incidentKeys i := by
    intro k hk
    rcases List.mem_map.mp (List.mem_toFinset.mp hk) with ⟨c,hc,rfl⟩
    have hci : clauseD i c + clauseU i c = 1 := by
      simpa [L] using (List.mem_filter.mp hc).2
    exact incidentKey_mem c i hci
  rw [occurrence_filter F i hF.1]
  change L.length ≤ _
  rw [←hcard]
  exact le_trans (Finset.card_le_card hmem) (incidentKeys_card i)

theorem simple_occurrences_linear (F : Formula n) (hF : Simple F) (i : Fin n) :
    B F i ≤ 4*n := by
  have hh := simple_occurrences F hF i
  have hn : 0 < n := i.pos
  omega

end Bias
end Max2SAT
