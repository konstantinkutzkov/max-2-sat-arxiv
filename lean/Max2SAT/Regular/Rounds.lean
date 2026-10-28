import Max2SAT.Regular.Mixing
import Max2SAT.Regular.Profile

namespace Max2SAT.Regular
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {n d : ℕ}

def firstRound (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val<n/4)
def secondRound (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => n / 4 ≤ i.val ∧ i.val < n / 2)

theorem first_round_card : (firstRound n).card=n/4 := by
  rw [firstRound,Fin.card_filter_val_lt,min_eq_right (Nat.div_le_self n 4)]

theorem rounds_disjoint : Disjoint (firstRound n) (secondRound n) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [firstRound,secondRound,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
  omega

theorem prefix_rounds : Counts.roundPrefix (Counts.twoRound n) 2=firstRound n∪secondRound n := by
  ext i
  simp only [Counts.roundPrefix,firstRound,secondRound,Finset.mem_filter,Finset.mem_univ,
    true_and,Finset.mem_union]
  dsimp [Counts.twoRound]
  split_ifs <;> omega

theorem round_cards : (firstRound n).card+(secondRound n).card=n/2 := by
  rw [←Finset.card_union_of_disjoint rounds_disjoint,←prefix_rounds,Counts.two_round_prefix_card]

theorem round_card_bounds :
    (n:ℝ)/4-1≤(firstRound n).card ∧ (n:ℝ)/4-1≤(secondRound n).card ∧
    ((firstRound n).card:ℝ)+(secondRound n).card≤(n:ℝ)/2 := by
  have h1 : n≤4*(firstRound n).card+4 := by rw [first_round_card]; omega
  have h2 : n≤4*(secondRound n).card+4 := by
    have h := round_cards (n:=n)
    rw [first_round_card] at h
    omega
  have h3 : 2*((firstRound n).card+(secondRound n).card)≤n := by rw [round_cards]; omega
  have h1' : (n:ℝ)≤4*(firstRound n).card+4 := by exact_mod_cast h1
  have h2' : (n:ℝ)≤4*(secondRound n).card+4 := by exact_mod_cast h2
  have h3' : (2:ℝ)*((firstRound n).card+(secondRound n).card)≤n := by exact_mod_cast h3
  exact ⟨by linarith,by linarith,by linarith⟩

theorem first_round_value (t : Fin n) (ht : t∈firstRound n) : Counts.twoRound n t=0 := by
  have h := (Finset.mem_filter.mp ht).2
  simp [Counts.twoRound,h]

theorem second_round_value (t : Fin n) (ht : t∈secondRound n) : Counts.twoRound n t=1 := by
  have h := (Finset.mem_filter.mp ht).2
  simp [Counts.twoRound,not_lt.mpr h.1,h.2]

theorem earlier_second (t w : Fin n) (ht : t∈secondRound n) :
    Counts.twoRound n w<Counts.twoRound n t ↔ w∈firstRound n := by
  rw [second_round_value t ht]
  simp only [firstRound,Finset.mem_filter,Finset.mem_univ,true_and]
  dsimp [Counts.twoRound]
  split_ifs <;> omega

theorem actual_round_profile (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Fin n → Counts.Affine n)
    (hcoeff : ∀ t w, ((H t).coeff w:ℝ)=corrected G d t w) :
    (∑ t : Counts.roundPrefix (Counts.twoRound n) 2,
      Real.sqrt (∑ w, (Counts.earlierRow H (Counts.twoRound n) t w)^2))=
      ∑ t∈secondRound n, Real.sqrt (roundRow G d (firstRound n) t) := by
  rw [Finset.sum_coe_sort (Counts.roundPrefix (Counts.twoRound n) 2)
    (fun t => Real.sqrt (∑ w, (Counts.earlierRow H (Counts.twoRound n) t w)^2))]
  rw [prefix_rounds,Finset.sum_union rounds_disjoint]
  have hfirst : (∑ t∈firstRound n,
      Real.sqrt (∑ w, (Counts.earlierRow H (Counts.twoRound n) t w)^2))=0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp [Counts.earlierRow,first_round_value t ht]
  rw [hfirst,zero_add]
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  simp only [Counts.earlierRow,earlier_second t _ ht,hcoeff,ite_pow,zero_pow (by omega : 2≠0)]
  simp [roundRow,firstRound,Finset.sum_filter]

theorem cross_edges_swap (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X Y : Finset (Fin n)) : crossEdges G X Y=∑ t∈Y, crossDegree G X t := by
  unfold crossEdges crossDegree
  apply Finset.sum_comm.trans
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro w _
  exact congrFun (congrFun (G.transpose_adjMatrix (α:=ℝ)) t) w

theorem actual_round_edge_lower (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 80≤n) (L : ℝ) (hL : 0≤L) (hLd : L≤(d:ℝ)/8)
    (hcenter : ‖centered G d‖≤L) :
    (d:ℝ)*n/40≤∑ t∈secondRound n, crossDegree G (firstRound n) t := by
  rw [←cross_edges_swap]
  have hb := round_card_bounds (n:=n)
  exact round_edge_lower n (firstRound n).card (secondRound n).card d L _
    (by exact_mod_cast hn) (by positivity) (by positivity) hb.1 hb.2.1 hb.2.2
    (by positivity) hL hLd (expander_mixing G _ _ L hcenter)

end
end Max2SAT.Regular
