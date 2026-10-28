import Max2SAT.Counts.BitExposure
import Mathlib.Analysis.Calculus.MeanValue

/-! Finite-cube logarithmic Sobolev estimates. All expectations are finite
sums; the proof starts with the elementary inequality log t <= t-1. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable

abbrev cubeMean (n : ℕ) (f : Assignment n → ℝ) : ℝ := expect (fairBits (Fin n)) f

def cubeFlip {n : ℕ} (i : Fin n) (x : Assignment n) : Assignment n :=
  Function.update x i (!(x i))

def cubeEntropy (n : ℕ) (f : Assignment n → ℝ) : ℝ :=
  cubeMean n (fun x => f x*Real.log (f x)) - cubeMean n f*Real.log (cubeMean n f)

theorem cube_mean_succ (n : ℕ) (f : Assignment (n+1) → ℝ) :
    cubeMean (n+1) f = cubeMean n (fun x => (f (Fin.cons false x)+f (Fin.cons true x))/2) := by
  simp only [cubeMean,expect,fairBits_mass,Fintype.card_fin]
  rw [←(Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,pow_succ]
  change (∑ x, ((1/2:ℝ)^n*(1/2))*f (Fin.cons true x))+
      (∑ x, ((1/2:ℝ)^n*(1/2))*f (Fin.cons false x)) =
      ∑ x, (1/2:ℝ)^n*((f (Fin.cons false x)+f (Fin.cons true x))/2)
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem two_point_entropy (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (a^2*Real.log (a^2)+b^2*Real.log (b^2))/2 -
      ((a^2+b^2)/2)*Real.log ((a^2+b^2)/2) ≤ (a-b)^2 := by
  let m := (a^2+b^2)/2
  have hm : 0<m := by dsimp [m]; positivity
  have hla := Real.log_le_sub_one_of_pos (div_pos (sq_pos_of_pos ha) hm)
  have hlb := Real.log_le_sub_one_of_pos (div_pos (sq_pos_of_pos hb) hm)
  rw [Real.log_div (ne_of_gt (sq_pos_of_pos ha)) hm.ne'] at hla
  rw [Real.log_div (ne_of_gt (sq_pos_of_pos hb)) hm.ne'] at hlb
  have h1 := mul_le_mul_of_nonneg_left hla (show 0≤a^2*m by positivity)
  have h2 := mul_le_mul_of_nonneg_left hlb (show 0≤b^2*m by positivity)
  have e1 : a^2*m*(a^2/m-1)=a^4-a^2*m := by field_simp
  have e2 : b^2*m*(b^2/m-1)=b^4-b^2*m := by field_simp
  rw [e1] at h1
  rw [e2] at h2
  have em : 2*m=a^2+b^2 := by dsimp [m]; ring
  have he : m*(a-b)^2-(a^2-b^2)^2/4=(a-b)^4/4 := by rw [show m=(a^2+b^2)/2 by rfl]; ring
  have hs : 0≤(a-b)^4/4 := by positivity
  change _-m*Real.log m≤_
  dsimp [m] at h1 h2 ⊢
  nlinarith [sq_nonneg ((a-b)^2)]

/-- Reverse triangle inequality for the two-coordinate Euclidean norm,
written without a norm coercion so it can be used inside the induction. -/
theorem rms_difference_sq (a b c d : ℝ) :
    (Real.sqrt ((a^2+b^2)/2)-Real.sqrt ((c^2+d^2)/2))^2 ≤
      ((a-c)^2+(b-d)^2)/2 := by
  have hp : 0≤(a^2+b^2)/2 := by positivity
  have hq : 0≤(c^2+d^2)/2 := by positivity
  have hs := Real.sq_sqrt hp
  have ht := Real.sq_sqrt hq
  have hprod : a*c+b*d ≤ 2*Real.sqrt ((a^2+b^2)/2)*Real.sqrt ((c^2+d^2)/2) := by
    by_cases h : a*c+b*d≤0
    · exact h.trans (by positivity)
    · have hc : (a*c+b*d)^2≤(a^2+b^2)*(c^2+d^2) := by nlinarith [sq_nonneg (a*d-b*c)]
      have hr : 0≤Real.sqrt ((a^2+b^2)/2)*Real.sqrt ((c^2+d^2)/2) := by positivity
      have he : (Real.sqrt ((a^2+b^2)/2)*Real.sqrt ((c^2+d^2)/2))^2=
          ((a^2+b^2)/2)*((c^2+d^2)/2) := by rw [mul_pow,hs,ht]
      nlinarith
  nlinarith


theorem cube_flip_cons_zero {n : ℕ} (b : Bool) (x : Assignment n) :
    cubeFlip 0 (Fin.cons b x)=Fin.cons (!b) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [cubeFlip]

theorem cube_flip_cons_succ {n : ℕ} (b : Bool) (x : Assignment n) (i : Fin n) :
    cubeFlip i.succ (Fin.cons b x)=Fin.cons b (cubeFlip i x) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · have hi : (0 : Fin (n+1))≠i.succ := Ne.symm (Fin.succ_ne_zero i)
    simp [cubeFlip,Function.update,hi]
  · by_cases h : j=i <;> simp [cubeFlip,Function.update,h]

/-- A deliberately conservative finite-cube logarithmic Sobolev bound.
The factor is obtained from log t <= t-1, followed by tensorization using
the reverse triangle inequality for the two-coordinate Euclidean norm. -/
theorem cube_log_sobolev (n : ℕ) (g : Assignment n → ℝ) (hg : ∀ x, 0<g x) :
    cubeEntropy n (fun x => (g x)^2) ≤
      cubeMean n (fun x => ∑ i, (g x-g (cubeFlip i x))^2) := by
  induction n with
  | zero => simp [cubeEntropy,cubeMean,expect,fairBits_mass]
  | succ n ih =>
    let g0 : Assignment n → ℝ := fun x => g (Fin.cons false x)
    let g1 : Assignment n → ℝ := fun x => g (Fin.cons true x)
    let h : Assignment n → ℝ := fun x => Real.sqrt (((g0 x)^2+(g1 x)^2)/2)
    have hh : ∀ x, 0<h x := by
      intro x
      have hp : 0<(g0 x)^2 := sq_pos_of_pos (hg _)
      dsimp [h]
      exact Real.sqrt_pos.mpr (by positivity)
    have hs : ∀ x, (h x)^2=((g0 x)^2+(g1 x)^2)/2 := by
      intro x; exact Real.sq_sqrt (by positivity)
    let e : Assignment n → ℝ := fun x =>
      ((g0 x)^2*Real.log ((g0 x)^2)+(g1 x)^2*Real.log ((g1 x)^2))/2 -
      (((g0 x)^2+(g1 x)^2)/2)*Real.log (((g0 x)^2+(g1 x)^2)/2)
    have he : cubeEntropy (n+1) (fun x => (g x)^2) =
        cubeEntropy n (fun x => (h x)^2)+cubeMean n e := by
      unfold cubeEntropy
      rw [cube_mean_succ,cube_mean_succ]
      simp_rw [hs]
      dsimp [e,g0,g1,cubeMean]
      simp only [expect,mul_sub,Finset.sum_sub_distrib]
      ring
    have he2 : cubeMean n e≤cubeMean n (fun x => (g0 x-g1 x)^2) :=
      expect_mono _ (fun x => two_point_entropy _ _ (hg _) (hg _))
    have hd : cubeMean n (fun x => ∑ i, (h x-h (cubeFlip i x))^2) ≤
        cubeMean n (fun x => ∑ i,
          ((g0 x-g0 (cubeFlip i x))^2+(g1 x-g1 (cubeFlip i x))^2)/2) := by
      apply expect_mono
      intro x
      apply Finset.sum_le_sum
      intro i _
      exact rms_difference_sq _ _ _ _
    have hbudget : cubeMean n (fun x => ∑ i,
        ((g0 x-g0 (cubeFlip i x))^2+(g1 x-g1 (cubeFlip i x))^2)/2)+
        cubeMean n (fun x => (g0 x-g1 x)^2) =
        cubeMean (n+1) (fun x => ∑ i, (g x-g (cubeFlip i x))^2) := by
      rw [cube_mean_succ,←expect_add]
      congr 1
      funext x
      simp only [Fin.sum_univ_succ,cube_flip_cons_zero,cube_flip_cons_succ,
        Bool.not_false,Bool.not_true]
      rw [←Finset.sum_div,Finset.sum_add_distrib]
      dsimp [g0,g1]
      ring
    rw [he]
    exact (add_le_add ((ih h hh).trans hd) he2).trans_eq hbudget

end
end Max2SAT.Counts
