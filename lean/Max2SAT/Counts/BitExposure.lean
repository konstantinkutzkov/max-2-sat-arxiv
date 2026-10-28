import Max2SAT.Random.PredictableSigns
import Max2SAT.Random.BitHistory
import Max2SAT.Counts.AccumulationIdentity

/-! Exposure of the actual assignment bits in their fixed order. Coefficients
may depend on every earlier bit, with one pathwise squared-energy bound. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def past (n j : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val<j)

def bitHistory (n j : ℕ) (x : Assignment n) : Assignment n := observe (past n j) x

theorem bit_history_agree (j : ℕ) (x y : Assignment n)
    (h : bitHistory n j x=bitHistory n j y) (i : Fin n) (hi : i.val<j) : x i=y i := by
  have he := congrFun h i
  simpa [bitHistory, observe, past, hi] using he

theorem bit_history_refines (i j : ℕ) (hij : i≤j) (x y : Assignment n)
    (h : bitHistory n j x=bitHistory n j y) : bitHistory n i x=bitHistory n i y := by
  apply observe_refines (past n i) (past n j) _ x y h
  intro w hw
  simp only [past, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  exact hw.trans_le hij

theorem bit_history_fresh (i : Fin n) (x : Assignment n) :
    push (fiber (fairBits (Fin n)) (bitHistory n i.val) (bitHistory n i.val x))
      (fun y => y i)=fair := by
  unfold bitHistory
  rw [fiber_fair_history]
  exact fresh_coordinate _ _ _ i (by simp [past])

/-- The finite-index version of the already verified martingale bound,
with all history and fresh-bit hypotheses discharged for assignments. -/
theorem assignment_sign_tail (a : Fin n → Assignment n → ℝ)
    (ha : ∀ i, Known (bitHistory n i.val) (a i))
    (B b : ℝ) (hB : 0<B) (hb : 0<b)
    (henergy : ∀ x, (∑ i, 4*(a i x)^2)≤B) :
    prob (fairBits (Fin n)) (fun x => (∑ i, a i x*sign (x i)) < -b) ≤
      Real.exp (-2*b^2/B) := by
  let A : ℕ → Assignment n → ℝ := fun j x => if h : j<n then a ⟨j,h⟩ x else 0
  let R : ℕ → Assignment n → Bool := fun j x => if h : j<n then x ⟨j,h⟩ else false
  let U : ℕ → Assignment n → ℝ := fun j x => |A j x|
  have hk : ∀ j, j<n → Known (bitHistory n j) (A j) := by
    intro j hj
    simpa only [A, dite_eq_left hj] using ha ⟨j,hj⟩
  have hobs : ∀ j x, bitHistory n j (bitHistory n j x)=bitHistory n j x := by
    intro j x
    funext i
    simp [bitHistory, observe]
  have hA : ∀ j, j<n → ∀ x, A j (bitHistory n j x)=A j x := by
    intro j hj x
    exact hk j hj _ _ (hobs j x)
  have h := predictable_sign_tail (fairBits (Fin n)) n (bitHistory n) A R U
    bit_history_refines hk
    (by
      intro j hj x y hxy
      simpa only [R, dite_eq_left hj] using bit_history_agree (j+1) x y hxy ⟨j,hj⟩ (Nat.lt_succ_self j))
    (by
      intro j hj x _
      simpa only [R, dite_eq_left hj] using bit_history_fresh ⟨j,hj⟩ x)
    (by intro j hj x _; simp only [U, hA j hj x, le_refl])
    B b hB hb (by
      intro x _
      rw [←Fin.sum_univ_eq_sum_range]
      have he : ∀ i : Fin n, (2*U i.val (bitHistory n i.val x))^2=4*(a i x)^2 := by
        intro i
        simp only [U, hA i.val i.isLt x, A, dite_eq_left i.isLt, mul_pow, sq_abs]
        norm_num
      simp_rw [he]
      exact henergy x)
  have he : ∀ x, (∑ j∈Finset.range n, A j x*sign (R j x))=∑ i, a i x*sign (x i) := by
    intro x
    rw [←Fin.sum_univ_eq_sum_range]
    simp [A,R]
  simpa only [he] using h

def OrderedRounds (round : Fin n → ℕ) : Prop :=
  ∀ t w, round w<round t → w.val<t.val

theorem average_known (H : Fin n → Affine n) (round : Fin n → ℕ)
    (horder : OrderedRounds round) (i : Fin n) (x y : Assignment n)
    (h : bitHistory n i.val x=bitHistory n i.val y) :
    (H i).average (earlier round i) x=(H i).average (earlier round i) y := by
  apply Affine.average_agree
  intro w hw
  exact bit_history_agree i.val x y h w (horder i w (Finset.mem_filter.mp hw).2)

theorem preference_known (H : Fin n → Affine n) (round : Fin n → ℕ)
    (horder : OrderedRounds round) (i : Fin n) (x y : Assignment n)
    (h : bitHistory n i.val x=bitHistory n i.val y) :
    preference H round x i=preference H round y i := by
  unfold preference
  rw [average_known H round horder i x y h]

theorem direction_cast (b : Bool) : (direction b : ℝ)=sign b := by
  cases b <;> norm_num [direction,sign]

end
end Max2SAT.Counts
