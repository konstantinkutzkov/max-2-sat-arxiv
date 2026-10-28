import Max2SAT.Counts.Algorithms
import Mathlib.Data.List.Pi

/-! Finite projection grids. Coverage is proved for the grid actually
constructed; no enumeration of Boolean assignments is used to build it. -/
namespace Max2SAT.Counts

def radius (v : Fin n → ℚ) : ℚ := ∑ i, |v i|

theorem projection_abs_le (v : Fin n → ℚ) (x : Assignment n) :
    |projection v x|≤radius v := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul,abs_of_nonneg (bit_nonneg _)]
  exact mul_le_of_le_one_right (abs_nonneg _) (bit_le_one _)

def coordinateGrid (A δ : ℚ) : List ℚ :=
  let q := ⌊A/δ⌋₊
  (List.range (2*q+3)).map (fun j : ℕ => δ*((j:ℚ)-(q+1)))

theorem coordinate_grid_length (A δ : ℚ) :
    (coordinateGrid A δ).length=2*⌊A/δ⌋₊+3 := by simp [coordinateGrid]

theorem coordinate_grid_length_bound (A δ : ℚ) (hA : 0≤A) (hδ : 0<δ) :
    ((coordinateGrid A δ).length : ℚ)≤2*A/δ+3 := by
  rw [coordinate_grid_length]
  have hq := Nat.floor_le (div_nonneg hA hδ.le)
  push_cast
  simpa only [mul_div_assoc,add_comm] using
    add_le_add_right (mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℚ)≤2)) 3

theorem coordinate_grid_cover (A δ y : ℚ) (hδ : 0<δ)
    (hy : |y|≤A) : ∃ g∈coordinateGrid A δ, |y-g|≤δ := by
  let q := ⌊A/δ⌋₊
  let z := ⌊y/δ⌋
  have hq : A/δ<(q:ℚ)+1 := Nat.lt_floor_add_one _
  have hzlo : (z:ℚ)≤y/δ := Int.floor_le _
  have hzhi : y/δ<(z:ℚ)+1 := Int.lt_floor_add_one _
  have hylo : -A/δ≤y/δ := div_le_div_of_nonneg_right (abs_le.mp hy).1 hδ.le
  rw [neg_div] at hylo
  have hyhi : y/δ≤A/δ := div_le_div_of_nonneg_right (abs_le.mp hy).2 hδ.le
  have hzlo' : -(q:ℤ)-1≤z := by
    have hh : -(q:ℚ)-2<(z:ℚ) := by linarith
    have hh' : -(q:ℤ)-2<z := by exact_mod_cast hh
    omega
  have hzhi' : z≤(q:ℤ) := by
    have hh : (z:ℚ)<(q:ℚ)+1 := by linarith
    have hh' : z<(q:ℤ)+1 := by exact_mod_cast hh
    omega
  let j := (z+(q:ℤ)+1).toNat
  have hjcast : (j:ℤ)=z+(q:ℤ)+1 := Int.toNat_of_nonneg (by omega)
  have hj : j<2*q+3 := by omega
  have he : (j:ℚ)-(q+1)=(z:ℚ) := by exact_mod_cast (by omega : (j:ℤ)-((q:ℤ)+1)=z)
  refine ⟨δ*((j:ℚ)-(q+1)),?_,?_⟩
  · simp only [coordinateGrid]
    change δ*((j:ℚ)-(q+1)) ∈
      (List.range (2*q+3)).map (fun h : ℕ => δ*((h:ℚ)-(q+1)))
    exact List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩
  · rw [he]
    have hl : δ*(z:ℚ)≤y := by nlinarith [(le_div_iff₀ hδ).mp hzlo]
    have hu : y<δ*((z:ℚ)+1) := by nlinarith [(div_lt_iff₀ hδ).mp hzhi]
    exact abs_le.mpr ⟨by linarith,by linarith⟩

def tuples (grids : Fin r → List ℚ) : List (Fin r → ℚ) :=
  (List.pi (List.finRange r) grids).map (fun f i => f i (List.mem_finRange i))

theorem mem_tuples (grids : Fin r → List ℚ) (g : Fin r → ℚ) :
    g∈tuples grids ↔ ∀ k, g k∈grids k := by
  constructor
  · intro h
    obtain ⟨f,hf,he⟩ := List.mem_map.mp h
    have hh := (List.mem_pi grids f).mp hf
    intro k
    rw [←he]
    exact hh k (List.mem_finRange k)
  · intro h
    apply List.mem_map.mpr
    refine ⟨fun i _ => g i,(List.mem_pi _ _).mpr (fun i _ => h i),rfl⟩

theorem pi_length (l : List ι) [DecidableEq ι] (grids : ι → List ℚ) :
    (List.pi l grids).length=(l.map (fun i => (grids i).length)).prod := by
  induction l with
  | nil => simp [List.pi]
  | cons i l ih => simp [List.pi,List.length_flatMap,ih]

theorem tuples_length (grids : Fin r → List ℚ) :
    (tuples grids).length=((List.finRange r).map (fun i => (grids i).length)).prod := by
  simp [tuples,pi_length]

theorem tuples_length_le (grids : Fin r → List ℚ) (B : ℕ)
    (hB : ∀ i, (grids i).length≤B) : (tuples grids).length≤B^r := by
  rw [tuples_length]
  have hl : ∀ l : List (Fin r), (l.map (fun i => (grids i).length)).prod≤B^l.length := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ]
      nlinarith [Nat.mul_le_mul (hB i) ih]
  simpa using hl (List.finRange r)

def projectionGrids (v : Fin r → Fin n → ℚ) (δ : Fin r → ℚ) : List (Fin r → ℚ) :=
  tuples (fun k => coordinateGrid (radius (v k)) (δ k))

theorem projection_grids_cover (v : Fin r → Fin n → ℚ) (δ : Fin r → ℚ)
    (hδ : ∀ k, 0<δ k) : Covers (projectionGrids v δ) v δ := by
  intro x
  have hh : ∀ k, ∃ g∈coordinateGrid (radius (v k)) (δ k),
      |projection (v k) x-g|≤δ k := by
    intro k
    exact coordinate_grid_cover _ _ _ (hδ k) (projection_abs_le (v k) x)
  choose g hg he using hh
  exact ⟨g,(mem_tuples _ g).mpr hg,he⟩

theorem grid_search_correct (F : Formula n) (lam : Fin r → ℚ)
    (v : Fin r → Fin n → ℚ) (δ : Fin r → ℚ) (P : Finset (Fin n))
    (round : Fin n → ℕ) (hF : wellFormed F) (hr : EarlierInPrefix P round)
    (hδ : ∀ k, 0<δ k) :
    ∃ x, projectionComparisons F lam v δ (projectionGrids v δ) P round=some x ∧
      ∀ y, score F y≤score F x :=
  projectionComparisons_correct F lam v δ _ P round hF hr (projection_grids_cover v δ hδ)

end Max2SAT.Counts
