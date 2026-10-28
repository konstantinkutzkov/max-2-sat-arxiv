import Max2SAT.Counts.ProgramBounds

/-! The two fixed prefix rounds used in the main-text count lemma. -/
namespace Max2SAT.Counts
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

def twoRound (n : ℕ) (i : Fin n) : ℕ :=
  if i.val<n/4 then 0 else if i.val<n/2 then 1 else 2

theorem two_round_order : OrderedRounds (twoRound n) := by
  intro w t h
  dsimp [twoRound] at h
  split_ifs at h <;> omega

theorem two_round_range (i : Fin n) : twoRound n i≤2 := by
  unfold twoRound
  split_ifs <;> omega

theorem two_round_prefix_card : (roundPrefix (twoRound n) 2).card=n/2 := by
  have he : roundPrefix (twoRound n) 2=Finset.univ.filter (fun i : Fin n => i.val<n/2) := by
    ext i
    change (i∈Finset.univ.filter (fun t : Fin n => twoRound n t<2)) ↔ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    dsimp [twoRound]
    have hn : n/4≤n/2 := by omega
    split_ifs <;> omega
  rw [he,Fin.card_filter_val_lt,min_eq_right (Nat.div_le_self n 2)]

theorem two_round_size : ((roundPrefix (twoRound n) 2).card:ℝ)≤(1/2:ℝ)*n := by
  rw [two_round_prefix_card]
  have h : 2*(n/2)≤n := by omega
  have hc : (2:ℝ)*(n/2:ℕ)≤n := by exact_mod_cast h
  linarith

theorem first_round_row_zero (H : Fin n → Affine n) (t w : Fin n)
    (ht : twoRound n t=0) : earlierRow H (twoRound n) t w=0 := by
  simp [earlierRow,ht]

/-- The two-round accumulation lemma with its exact prefix size and number
of count guesses. The row profile can equivalently omit the first round,
whose rows are identically zero. -/
theorem count_two_round_nodes (F : Formula n) (hF : wellFormed F) (β : ℚ)
    (hn : 2≤n) (g K D : ℝ) (hg : 0<g) (hK : 0<K) (hD : 0<D)
    (hN : ‖interactionMatrix (countGain F β 0)‖^2≤K*D)
    (hprofile : 4*Real.sqrt 3*(g*n*Real.sqrt D)≤
      ∑ t : roundPrefix (twoRound n) 2,
        Real.sqrt (∑ w, (earlierRow (countGain F β 0) (twoRound n) t w)^2))
    (hslack : (n/2:ℕ)*|(β:ℝ)|≤g*n*Real.sqrt D/8) :
    (Runs.nodeCount (countGuesses n β)
      (countBudget (preprocess F).1 β (roundPrefix (twoRound n) 2) (twoRound n))
      (roundPrefix (twoRound n) 2) : ℝ)≤
      (n+1)*(2+14*n)*(exponentialBase (1/2) (roundRate 2 (1/2) g K))^n ∧
      exponentialBase (1/2) (roundRate 2 (1/2) g K)<2 := by
  have hp : 0<(roundPrefix (twoRound n) 2).card := by rw [two_round_prefix_card]; omega
  have h := count_round_nodes F hF β (twoRound n) 2 (by omega) two_round_order
    two_round_range hp (1/2) g K D (by norm_num) (by norm_num) hg hK hD
    two_round_size hN hprofile (by simpa only [two_round_prefix_card] using hslack)
  convert h using 1
  norm_num
  ring

end
end Max2SAT.Counts
