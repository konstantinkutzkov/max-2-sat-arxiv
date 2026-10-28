import Max2SAT.IndependentPairs.RowTails
import Mathlib.Algebra.Order.Floor.Ring

/-! A discrete row-profile estimate, with explicit rounding. Indices are
zero-based: row j has j earlier neighbors. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open RandomInput
set_option maxHeartbeats 800000

/-- The elementary increment bound behind the discrete integral estimate. -/
theorem root_increment (x : ℝ) (hx : 0≤x) :
    (x+1)*Real.sqrt (x+1)-x*Real.sqrt x≤(3/2:ℝ)*Real.sqrt (x+1) := by
  have ha := Real.sqrt_nonneg x
  have hb := Real.sqrt_nonneg (x+1)
  have hab := Real.sqrt_le_sqrt (show x≤x+1 by linarith)
  have ha2 := Real.sq_sqrt hx
  have hb2 := Real.sq_sqrt (show 0≤x+1 by linarith)
  have h := mul_nonneg (sq_nonneg (Real.sqrt (x+1)-Real.sqrt x))
    (show 0≤Real.sqrt (x+1)+2*Real.sqrt x by positivity)
  nlinarith

/-- A lower Riemann sum, proved by telescoping rather than integration. -/
theorem root_sum_lower (T : ℕ) :
    (2/3:ℝ)*T*Real.sqrt T-Real.sqrt T≤
      ∑ j∈Finset.range T, Real.sqrt (j:ℝ) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have h := root_increment (T:ℝ) (by positivity)
    push_cast
    nlinarith

theorem root_sum_upper (a : ℕ) :
    (∑ j∈Finset.range a, Real.sqrt (j:ℝ))≤a*Real.sqrt a := by
  calc
    _ ≤ ∑ _j∈Finset.range a, Real.sqrt (a:ℝ) := Finset.sum_le_sum (by
      intro j hj
      exact Real.sqrt_le_sqrt (by exact_mod_cast (Finset.mem_range.mp hj).le))
    _ = _ := by simp

/-- Only rows between ceil(N/10) and floor(N) are needed. The conservative
bound 0.62 leaves room for all integer rounding when N >= 1000. -/
theorem root_interval_lower (N : ℝ) (hN : 1000≤N) :
    (62/100:ℝ)*N*Real.sqrt N≤
      ∑ j∈Finset.Ico ⌈N/10⌉₊ ⌊N⌋₊, Real.sqrt (j:ℝ) := by
  let a := ⌈N/10⌉₊
  let T := ⌊N⌋₊
  have hN0 : 0≤N := by linarith
  have hTlo : N-1≤(T:ℝ) := by
    have h := Nat.lt_floor_add_one N
    dsimp [T]; linarith
  have hThi : (T:ℝ)≤N := Nat.floor_le hN0
  have halo : N/10≤(a:ℝ) := Nat.le_ceil _
  have hahi : (a:ℝ)≤N/10+1 := by
    have h := Nat.ceil_lt_add_one (show 0≤N/10 by positivity)
    dsimp [a]; linarith
  have haT : a≤T := by exact_mod_cast (show (a:ℝ)≤T by linarith)
  have hTsmall : (99/100:ℝ)*N≤T := by linarith
  have hasmall : (a:ℝ)≤(101/1000:ℝ)*N := by linarith
  have hsT : (994/1000:ℝ)*Real.sqrt N≤Real.sqrt T := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow,Real.sq_sqrt hN0]
    nlinarith
  have hsa : Real.sqrt a≤(318/1000:ℝ)*Real.sqrt N := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [mul_pow,Real.sq_sqrt hN0]
    nlinarith
  have hsThi : Real.sqrt T≤Real.sqrt N := Real.sqrt_le_sqrt hThi
  have hmain := mul_le_mul hTsmall hsT (by positivity) (by positivity)
  have hcut := mul_le_mul hasmall hsa (by positivity) (by positivity)
  have hlo := root_sum_lower T
  have hhi := root_sum_upper a
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => Real.sqrt (j:ℝ)) haT
  have hlarge := mul_le_mul_of_nonneg_right hN (Real.sqrt_nonneg N)
  dsimp [a,T] at hsplit
  dsimp [a,T] at hlo hhi hmain hcut hsThi
  nlinarith

def lateRows (n : ℕ) (τ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun t => ⌈τ*n/10⌉₊≤t.val ∧ t.val<⌊τ*n⌋₊)

def rowProfile {n : ℕ} (z : Edge n → ℝ) (T : ℕ) : ℝ :=
  ∑ t∈Finset.univ.filter (fun t : Fin n => t.val<T), Real.sqrt (earlierEnergy z t)

theorem late_rows_positive {n : ℕ} (τ : ℝ) (hN : 1000≤τ*n) :
    ∀ t∈lateRows n τ, 0<t.val := by
  intro t ht
  have h := (Finset.mem_filter.mp ht).2.1
  have hc := Nat.le_ceil (τ*n/10)
  have ht' : (⌈τ*n/10⌉₊:ℝ)≤t.val := by exact_mod_cast h
  have hp : (0:ℝ)<t.val := by linarith
  exact_mod_cast hp

/-- Pointwise row lower bounds imply the required total profile. -/
theorem row_profile_lower {n : ℕ} (z : Edge n → ℝ) (τ ν : ℝ)
    (hτ : 0<τ) (hτ1 : τ<1) (hN : 1000≤τ*n) (_hν : 0≤ν)
    (hrows : ∀ t∈lateRows n τ, (993/1000:ℝ)*Real.sqrt (t.val*ν)≤
      Real.sqrt (earlierEnergy z t)) :
    (61/100:ℝ)*(τ*n)*Real.sqrt (τ*n)*Real.sqrt ν≤rowProfile z ⌊τ*n⌋₊ := by
  have hn0 : (0:ℝ)<n := by nlinarith
  have hTn : ⌊τ*n⌋₊≤n := by
    apply Nat.floor_le_of_le
    nlinarith
  have he : (∑ j∈Finset.Ico ⌈τ*n/10⌉₊ ⌊τ*n⌋₊, Real.sqrt (j:ℝ))=
      ∑ t∈lateRows n τ, Real.sqrt (t.val:ℝ) := by
    symm
    apply Finset.sum_bij (fun t _ => t.val)
    · intro t ht; simpa [lateRows] using ht
    · intro a _ b _ h; exact Fin.ext h
    · intro j hj
      have h := Finset.mem_Ico.mp hj
      exact ⟨⟨j,h.2.trans_le hTn⟩,by simpa [lateRows] using hj,rfl⟩
    · intro t _; rfl
  have hr := root_interval_lower (τ*n) hN
  rw [he] at hr
  have hm := mul_le_mul_of_nonneg_right hr (show 0≤(993/1000:ℝ)*Real.sqrt ν by positivity)
  have hsum : (∑ t∈lateRows n τ, Real.sqrt (t.val:ℝ))*((993/1000:ℝ)*Real.sqrt ν)≤
      ∑ t∈lateRows n τ, Real.sqrt (earlierEnergy z t) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro t ht
    have h := hrows t ht
    rw [Real.sqrt_mul (Nat.cast_nonneg t.val)] at h
    nlinarith
  have hsub : (∑ t∈lateRows n τ, Real.sqrt (earlierEnergy z t))≤rowProfile z ⌊τ*n⌋₊ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro t ht; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ht).2.2⟩
    · intro t _ _; positivity
  have hp : 0≤(τ*n)*Real.sqrt (τ*n)*Real.sqrt ν := by positivity
  nlinarith

end
end Max2SAT.IndependentPairs
