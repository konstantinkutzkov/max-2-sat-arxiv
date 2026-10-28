import Max2SAT.Community.Perturbation
import Max2SAT.Counts.TwoRounds

/-! Connect the concrete two prefix rounds to the cross-row matrix profile.
This makes the rounding and the algorithm's earlier-row notation explicit. -/
namespace Max2SAT.Community
noncomputable section
open Counts
variable {n : ℕ}

def firstRound (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val<n/4)
def secondRound (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => n / 4 ≤ i.val ∧ i.val < n / 2)

theorem first_round_card : (firstRound n).card=n/4 := by
  rw [firstRound,Fin.card_filter_val_lt,min_eq_right (Nat.div_le_self n 4)]

theorem rounds_disjoint : Disjoint (firstRound n) (secondRound n) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [firstRound,secondRound,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
  omega

theorem prefix_round_union : roundPrefix (twoRound n) 2=firstRound n∪secondRound n := by
  ext i
  simp only [roundPrefix,firstRound,secondRound,Finset.mem_filter,Finset.mem_univ,
    true_and,Finset.mem_union]
  dsimp [twoRound]
  split_ifs <;> omega

theorem second_round_card : (secondRound n).card=n/2-n/4 := by
  have hc := Finset.card_union_of_disjoint (rounds_disjoint (n:=n))
  rw [←prefix_round_union,two_round_prefix_card,first_round_card] at hc
  omega

theorem round_sizes (hn : 20≤n) :
    (n:ℝ)/5≤(firstRound n).card ∧ (n:ℝ)/5≤(secondRound n).card := by
  rw [first_round_card,second_round_card]
  have ha : n≤5*(n/4) := by omega
  have hb : n≤5*(n/2-n/4) := by omega
  have ha' : (n:ℝ)≤5*((n/4:ℕ):ℝ) := by exact_mod_cast ha
  have hb' : (n:ℝ)≤5*((n/2-n/4:ℕ):ℝ) := by exact_mod_cast hb
  constructor <;> linarith

theorem two_round_first (i : Fin n) (hi : i∈firstRound n) : twoRound n i=0 := by
  simp only [firstRound,Finset.mem_filter,Finset.mem_univ,true_and] at hi
  simp [twoRound,hi]

theorem two_round_second (i : Fin n) (hi : i∈secondRound n) : twoRound n i=1 := by
  simp only [secondRound,Finset.mem_filter,Finset.mem_univ,true_and] at hi
  simp [twoRound,not_lt.mpr hi.1,hi.2]

theorem earlier_second_row (H : Fin n → Affine n) (t : Fin n) (ht : t∈secondRound n) (w : Fin n) :
    earlierRow H (twoRound n) t w=if w∈firstRound n then (interactionMatrix H) t w else 0 := by
  rw [earlierRow,two_round_second t ht]
  have he : twoRound n w<1 ↔ w∈firstRound n := by
    simp only [firstRound,Finset.mem_filter,Finset.mem_univ,true_and]
    dsimp [twoRound]
    split_ifs <;> omega
  simp only [he,interactionMatrix]

/-- The actual algorithm profile is exactly the second-round cross profile. -/
theorem two_round_profile (H : Fin n → Affine n) :
    (∑ t : roundPrefix (twoRound n) 2,
      Real.sqrt (∑ w, (earlierRow H (twoRound n) t w)^2))=
      crossProfile (interactionMatrix H) (secondRound n) (firstRound n) := by
  rw [Finset.sum_coe_sort (roundPrefix (twoRound n) 2)
    (fun t : Fin n => Real.sqrt (∑ w, (earlierRow H (twoRound n) t w)^2)),
    prefix_round_union,Finset.sum_union rounds_disjoint,cross_profile_roots]
  have hz : (∑ t∈firstRound n, Real.sqrt (∑ w, (earlierRow H (twoRound n) t w)^2))=0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp [earlierRow,two_round_first t ht]
  rw [hz,zero_add]
  apply Finset.sum_congr rfl
  intro t ht
  simp_rw [earlier_second_row H t ht]
  simp

end
end Max2SAT.Community
