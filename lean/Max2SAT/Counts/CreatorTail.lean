import Max2SAT.Counts.BitExposure

/-! The creator-indicator estimate in the proof of `res:counts`, for the
actual preferences computed by the count/projection algorithm. The input
formula is fixed; only the completed Boolean assignment is random. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def clippedGap (H : Fin n → Affine n) (round : Fin n → ℕ)
    (M : ℝ) (i : Fin n) (x : Assignment n) : ℝ :=
  min |((H i).average (earlier round i) x : ℝ)| M

def clippedCreators (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (M : ℝ) (x : Assignment n) : ℝ :=
  ∑ i∈P, if x i≠preference H round x i then clippedGap H round M i x else 0

theorem creator_centering (x p : Bool) (w : ℝ) :
    (if x≠p then w else 0)-w/2 = (-sign p*w/2)*sign x := by
  cases x <;> cases p <;> norm_num [sign] <;> ring

/-- Preferences need not be independent of previous creator decisions.
They only need the earlier-round information used by the algorithm. -/
theorem creator_gap_tail (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (horder : OrderedRounds round)
    (M a : ℝ) (hM : 0<M) (ha : 0<a) (hP : 0<P.card) :
    prob (fairBits (Fin n)) (fun x => clippedCreators H P round M x <
      (∑ i∈P, clippedGap H round M i x)/2-a) ≤
        Real.exp (-2*a^2/(P.card*M^2)) := by
  let A : Fin n → Assignment n → ℝ := fun i x =>
    if i∈P then -sign (preference H round x i)*clippedGap H round M i x/2 else 0
  have hk : ∀ i, Known (bitHistory n i.val) (A i) := by
    intro i x y h
    simp only [A, clippedGap, preference_known H round horder i x y h,
      average_known H round horder i x y h]
  have he : ∀ x, (∑ i, 4*(A i x)^2)≤P.card*M^2 := by
    intro x
    have hp : ∀ i, 4*(A i x)^2 ≤ if i∈P then M^2 else 0 := by
      intro i
      by_cases hi : i∈P
      · have hw : 0≤clippedGap H round M i x := le_min (abs_nonneg _) hM.le
        have hu : clippedGap H round M i x≤M := min_le_right _ _
        have hs : (sign (preference H round x i))^2=1 := by
          cases preference H round x i <;> norm_num [sign]
        simp only [A, ite_eq_left hi, div_pow, mul_pow, neg_sq, hs, one_mul]
        nlinarith [sq_nonneg (M-clippedGap H round M i x)]
      · simp [A,hi]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
    simpa using hh
  have ht := assignment_sign_tail A hk (P.card*M^2) a
    (mul_pos (by exact_mod_cast hP) (sq_pos_of_pos hM)) ha he
  have hid : ∀ x, (∑ i, A i x*sign (x i)) =
      clippedCreators H P round M x-(∑ i∈P, clippedGap H round M i x)/2 := by
    intro x
    unfold clippedCreators
    rw [Finset.sum_div, ←Finset.sum_sub_distrib]
    simp only [A, ite_mul, zero_mul, ←creator_centering]
    simp
  simpa only [hid, sub_lt_iff_lt_add, neg_add_eq_sub] using ht

/-- Subtracting all allowances, including those at noncreators, only
weakens the lower bound on the actual accumulated gap. -/
theorem accumulated_gap_lower (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (s : Fin n → ℚ) (hs : ∀ i∈P, 0≤s i)
    (M : ℝ) (x : Assignment n) :
    clippedCreators H P round M x-(∑ i∈P, (s i : ℝ)) ≤
      (accumulatedGap H s P round x : ℝ) := by
  unfold clippedCreators accumulatedGap
  push_cast
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  split_ifs with hc
  · push_cast
    exact sub_le_sub_right (min_le_left _ _) _
  · have hsi : (0:ℝ)≤s i := by exact_mod_cast hs i hi
    norm_num only [Rat.cast_zero]
    linarith

/-- Outside the profile and creator exceptional events, the numerical
constants used in the paper give the required accumulated gap. The
parameter a represents g*n*sqrt(D_N)/8. -/
theorem accumulated_gap_of_profile (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (s : Fin n → ℚ) (hs : ∀ i∈P, 0≤s i)
    (M a : ℝ) (x : Assignment n)
    (hprofile : 6*a≤∑ i∈P, clippedGap H round M i x)
    (hcreator : (∑ i∈P, clippedGap H round M i x)/2-a≤clippedCreators H P round M x)
    (hslack : (∑ i∈P, (s i : ℝ))≤a) :
    a≤(accumulatedGap H s P round x : ℝ) := by
  have h := accumulated_gap_lower H P round s hs M x
  linarith

end
end Max2SAT.Counts
