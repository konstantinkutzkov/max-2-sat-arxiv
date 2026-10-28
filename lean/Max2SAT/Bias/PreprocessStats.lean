import Max2SAT.Bias.Moments
import Max2SAT.Preprocess

/-! The dense-gap corollary needs statistics of the original input, although
the search runs on the preprocessed formula. -/
namespace Max2SAT.Bias

@[simp] theorem B_nil (i : Fin n) : B [] i = 0 := rfl
@[simp] theorem B_cons (c : Clause n) (F : Formula n) (i : Fin n) :
    B (c :: F) i = clauseD i c + clauseU i c + B F i := by
  simp [B, D, U]; omega
@[simp] theorem B_append (F G : Formula n) (i : Fin n) :
    B (F ++ G) i = B F i + B G i := by
  simp [B, D, U]; omega

private theorem reducePair_occurrences (c e : Clause n) (G : Formula n)
    (s : ℤ) (h : reducePair c e = some (G,s)) (i : Fin n) :
    B G i ≤ B [c,e] i := by
  cases c <;> cases e <;> simp only [reducePair] at h
  all_goals try split_ifs at h
  all_goals cases h
  all_goals simp only [B, D, U, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, clauseD, clauseU]
  all_goals split_ifs <;> omega

private theorem reduceWith_occurrences (c : Clause n) (F G : Formula n)
    (s : ℤ) (h : reduceWith c F = some (G,s)) (i : Fin n) :
    B G i ≤ B (c :: F) i := by
  induction F generalizing G s with
  | nil => simp [reduceWith] at h
  | cons e es ih =>
    simp only [reduceWith] at h
    cases hp : reducePair c e with
    | some pair =>
      rcases pair with ⟨H,t⟩
      simp only [hp] at h
      cases h
      have hh := reducePair_occurrences c e H s hp i
      simp only [B_append, B_cons, B_nil] at *
      omega
    | none =>
      simp only [hp] at h
      cases ht : reduceWith c es with
      | none => simp [ht] at h
      | some pair =>
        rcases pair with ⟨H,t⟩
        simp only [ht] at h
        cases h
        have hh := ih H s ht
        simp only [B_cons] at *
        omega

private theorem preprocessStep_occurrences (F G : Formula n) (s : ℤ)
    (h : preprocessStep F = some (G,s)) (i : Fin n) : B G i ≤ B F i := by
  induction F generalizing G s with
  | nil => simp [preprocessStep] at h
  | cons c cs ih =>
    simp only [preprocessStep] at h
    cases hp : reduceWith c cs with
    | some pair =>
      simp only [hp] at h
      cases h
      exact reduceWith_occurrences c cs G s hp i
    | none =>
      simp only [hp] at h
      cases ht : preprocessStep cs with
      | none => simp [ht] at h
      | some pair =>
        rcases pair with ⟨H,t⟩
        simp only [ht] at h
        cases h
        have hh := ih H s ht
        simp only [B_cons]
        omega

theorem preprocessAux_occurrences (fuel : ℕ) (F : Formula n) (i : Fin n) :
    B (preprocessAux fuel F).1 i ≤ B F i := by
  induction fuel generalizing F with
  | zero => exact le_refl _
  | succ fuel ih =>
    simp only [preprocessAux]
    cases hp : preprocessStep F with
    | none => exact le_refl _
    | some pair =>
      rcases pair with ⟨G,s⟩
      exact le_trans (ih G) (preprocessStep_occurrences F G s hp i)

theorem preprocess_occurrences (F : Formula n) (i : Fin n) :
    B (preprocess F).1 i ≤ B F i := preprocessAux_occurrences F.length F i

noncomputable section
open FairCoin

/-- The signed effective gap is determined by the score function up to an
additive constant. This avoids repeating a gap calculation for each rule. -/
theorem mean_positive_benefit (F : Formula n) (i : Fin n) (hF : wellFormed F) :
    average n (benefit F (fun _ => true) i) = (gap F i : ℝ) / 4 := by
  rw [mean_benefit F _ i hF, pruning_bound_counts F _ hF]
  have hD : (D F i : ℝ) = (d2 F (pos i) : ℝ) + (d2 F (pos i).neg : ℝ) := by
    exact_mod_cast (degree_counts F i hF).1
  change ((D F i : ℝ) / 2 -
    ((d2 F (pos i).neg - d1 F (pos i) + d1 F (pos i).neg - 1) + 1 : ℤ)) / 2 = _
  simp only [gap, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  linarith

theorem equivalent_gap (F G : Formula n) (s : ℤ)
    (hF : wellFormed F) (hG : wellFormed G) (h : EquivalentWithOffset F G s)
    (i : Fin n) : gap F i = gap G i := by
  have hb : benefit F (fun _ => true) i = benefit G (fun _ => true) i := by
    funext x
    unfold benefit
    rw [h _, h x]
    congr 1
    ring
  have hm := congrArg (average n) hb
  rw [mean_positive_benefit F i hF, mean_positive_benefit G i hG] at hm
  have he : (gap F i : ℝ) = (gap G i : ℝ) := by linarith
  exact_mod_cast he

theorem preprocess_gap (F : Formula n) (hF : wellFormed F) (i : Fin n) :
    gap (preprocess F).1 i = gap F i :=
  (equivalent_gap F (preprocess F).1 (preprocess F).2 hF
    (preprocess_finished F hF).1 (preprocess_correct F) i).symm

end
end Max2SAT.Bias
