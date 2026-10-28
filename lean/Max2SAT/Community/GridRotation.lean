import Max2SAT.Community.RotationScalar
import Mathlib.Data.List.MinMax

/-! A finite rational search replaces approximation of a real root. -/
namespace Max2SAT.Community
set_option maxHeartbeats 800000

def gridParameter (D j : ℕ) : ℚ := (j:ℚ)/D

def bestGridIndex (a b d : ℚ) (D : ℕ) : ℕ :=
  ((List.range (D+1)).argmin (fun j => |rotatedPivot a b d (gridParameter D j)|)).getD 0

theorem best_grid_le (a b d : ℚ) (D j : ℕ) (hj : j≤D) :
    |rotatedPivot a b d (gridParameter D (bestGridIndex a b d D))|≤
      |rotatedPivot a b d (gridParameter D j)| := by
  unfold bestGridIndex
  generalize he : List.argmin (fun j => |rotatedPivot a b d (gridParameter D j)|) (List.range (D+1))=o
  cases o with
  | none =>
    have hh := List.argmin_eq_none.mp he
    simp at hh
  | some k =>
    simp only [Option.getD_some]
    exact List.le_of_mem_argmin (f:=fun q => |rotatedPivot a b d (gridParameter D q)|)
      (a:=j) (m:=k) (l:=List.range (D+1)) (List.mem_range.mpr (by omega)) (by rw [he]; simp)

theorem best_grid_index_bound (a b d : ℚ) (D : ℕ) : bestGridIndex a b d D≤D := by
  unfold bestGridIndex
  generalize he : List.argmin (fun j => |rotatedPivot a b d (gridParameter D j)|) (List.range (D+1))=o
  cases o with
  | none => simp
  | some k =>
    have hh : k∈List.range (D+1) := List.argmin_mem (by rw [he]; simp)
    simpa using Nat.le_of_lt_succ (List.mem_range.mp hh)

theorem grid_covers_interval (D : ℕ) (hD : 0<D) (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    ∃ j≤D, |(gridParameter D j:ℝ)-t|≤1/(D:ℝ) := by
  have hDr : (0:ℝ)<D := by exact_mod_cast hD
  let j := Nat.floor ((D:ℝ)*t)
  have hj : j≤D := Nat.floor_le_of_le (by nlinarith [ht.2])
  refine ⟨j,hj,?_⟩
  have hlo : (j:ℝ)≤D*t := Nat.floor_le (by nlinarith [ht.1])
  have hhi : (D:ℝ)*t<(j:ℝ)+1 := Nat.lt_floor_add_one _
  have hleft : (j:ℝ)/D≤t := (div_le_iff₀ hDr).mpr (by nlinarith)
  have hright : t-(j:ℝ)/D≤1/D := by
    apply (le_div_iff₀ hDr).mpr
    have he : ((j:ℝ)/D)*(D:ℝ)=j := div_mul_cancel₀ _ (ne_of_gt hDr)
    nlinarith
  simpa [gridParameter,abs_of_nonpos (sub_nonpos.mpr hleft)] using hright

theorem rotated_pivot_cast (a b d t : ℚ) :
    ((rotatedPivot a b d t:ℚ):ℝ)=rotatedPivot (a:ℝ) (b:ℝ) (d:ℝ) (t:ℝ) := by
  simp [rotatedPivot,rotationC,rotationS]

/-- The implemented rational minimizer achieves a small residual pivot. -/
theorem best_grid_pivot_bound (a b d : ℚ) (D : ℕ) (hD : 0<D) (M : ℝ)
    (ha : |(a:ℝ)|≤M) (hb : |(b:ℝ)|≤M) (hd : |(d:ℝ)|≤M) :
    |((rotatedPivot a b d (gridParameter D (bestGridIndex a b d D)):ℚ):ℝ)|≤16*M/D := by
  obtain ⟨t,ht,he⟩ := eliminating_parameter (a:ℝ) (b:ℝ) (d:ℝ)
  obtain ⟨j,hj,hclose⟩ := grid_covers_interval D hD t ht
  have hL := rotated_pivot_lipschitz (a:ℝ) (b:ℝ) (d:ℝ) (gridParameter D j:ℝ) t M ha hb hd
  rw [he,sub_zero,←rotated_pivot_cast] at hL
  have hm : 0≤M := (abs_nonneg (a:ℝ)).trans ha
  have hbound := hL.trans (mul_le_mul_of_nonneg_left hclose (show 0≤16*M by positivity))
  have hbest : |((rotatedPivot a b d (gridParameter D (bestGridIndex a b d D)):ℚ):ℝ)|≤
      |((rotatedPivot a b d (gridParameter D j):ℚ):ℝ)| := by
    exact_mod_cast best_grid_le a b d D j hj
  exact hbest.trans (by simpa [div_eq_mul_inv,mul_assoc] using hbound)

end Max2SAT.Community
