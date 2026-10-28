import Max2SAT.Community.Computed
import Mathlib.Data.List.Sort

/-! Deterministic rational selection of the largest absolute diagonal
entries. Sorting keeps indices distinct, including ties and zero entries. -/
namespace Max2SAT.Community
variable {n r : ℕ}

def rankedIndices (d : Fin n → ℚ) : List (Fin n) :=
  (List.finRange n).mergeSort (fun i j => |d j|≤|d i|)

theorem ranked_length (d : Fin n → ℚ) : (rankedIndices d).length=n := by
  simp [rankedIndices]

theorem ranked_nodup (d : Fin n → ℚ) : (rankedIndices d).Nodup := by
  exact (List.mergeSort_perm (List.finRange n) _).nodup_iff.mpr (List.nodup_finRange n)

theorem ranked_mem (d : Fin n → ℚ) (i : Fin n) : i∈rankedIndices d := by
  simp [rankedIndices]

theorem ranked_pairwise (d : Fin n → ℚ) :
    (rankedIndices d).Pairwise (fun i j => |d j|≤|d i|) := by
  simpa [rankedIndices] using List.pairwise_mergeSort
    (le:=fun i j : Fin n => decide (|d j|≤|d i|))
    (fun a b c h₁ h₂ => by simp only [decide_eq_true_eq] at *; exact h₂.trans h₁)
    (fun a b => by simpa only [Bool.or_eq_true,decide_eq_true_eq] using (le_total |d b| |d a|)) (List.finRange n)

def topSelection (d : Fin n → ℚ) (h : r≤n) : Fin r ↪ Fin n where
  toFun k := (rankedIndices d).get ⟨k.val,by rw [ranked_length]; exact k.isLt.trans_le h⟩
  inj' := by
    intro i j he
    have hi := (ranked_nodup d).injective_get he
    exact Fin.ext (congrArg (fun k : Fin (rankedIndices d).length => k.val) hi)

theorem top_selection_largest (d : Fin n → ℚ) (h : r≤n) :
    ∀ i∈Finset.univ.map (topSelection d h), ∀ j∉Finset.univ.map (topSelection d h),
      |d j|≤|d i| := by
  intro i hi j hj
  obtain ⟨k,_,rfl⟩ := Finset.mem_map.mp hi
  obtain ⟨q,hq⟩ := List.mem_iff_get.mp (ranked_mem d j)
  have hqbig : r≤q.val := by
    by_contra hsmall
    have hqr : q.val<r := by omega
    apply hj
    apply Finset.mem_map.mpr
    refine ⟨⟨q.val,hqr⟩,Finset.mem_univ _,?_⟩
    exact hq
  have hh := (ranked_pairwise d).rel_get_of_lt
    (a:=⟨k.val,by rw [ranked_length]; exact k.isLt.trans_le h⟩) (b:=q)
    (by change k.val<q.val; omega)
  rw [hq] at hh
  exact hh

end Max2SAT.Community
