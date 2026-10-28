import Max2SAT.Counts.SmoothGap
import Max2SAT.Counts.CubeEntropy

namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
open scoped Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

def rowValue (H : κ → ℝ) (L : Matrix κ (Fin n) ℝ) (x : Assignment n) (t : κ) : ℝ :=
  H t+(∑ i, L t i*sign (x i))/2

def smoothProxy (H : κ → ℝ) (L : Matrix κ (Fin n) ℝ) (M δ : ℝ)
    (x : Assignment n) : ℝ :=
  ∑ t, if |H t|≤M/2 then smoothAbs δ (rowValue H L x t) else M/4

def proxySlope (H : κ → ℝ) (L : Matrix κ (Fin n) ℝ) (M δ : ℝ)
    (x : Assignment n) (t : κ) : ℝ :=
  if |H t|≤M/2 then smoothSlope δ (rowValue H L x t) else 0

def columnEnergy (L : Matrix κ (Fin n) ℝ) (i : Fin n) : ℝ := ∑ t, (L t i)^2

omit [Fintype κ] [DecidableEq κ] in
theorem row_value_flip (H : κ → ℝ) (L : Matrix κ (Fin n) ℝ)
    (x : Assignment n) (i : Fin n) (t : κ) :
    rowValue H L (cubeFlip i x) t=rowValue H L x t-L t i*sign (x i) := by
  have he : ∀ j, L t j*sign (cubeFlip i x j) =
      L t j*sign (x j)-(if j=i then 2*L t i*sign (x i) else 0) := by
    intro j
    by_cases h : j=i
    · subst j; cases hx : x i <;> simp [cubeFlip,hx,sign] <;> ring
    · simp [cubeFlip,Function.update,h]
  simp only [rowValue,he,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  ring

omit [DecidableEq κ] in
theorem proxy_slope_sq (H : κ → ℝ) (L : Matrix κ (Fin n) ℝ) (M δ : ℝ)
    (hδ : 0<δ) (x : Assignment n) :
    (∑ t, (proxySlope H L M δ x t)^2)≤Fintype.card κ := by
  calc
    _ ≤ ∑ _t : κ, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro t _
      unfold proxySlope
      split_ifs
      · have h := smooth_slope_bounds δ (rowValue H L x t) hδ
        nlinarith [sq_nonneg (smoothSlope δ (rowValue H L x t)+1),
          mul_nonneg (by linarith : 0≤1-smoothSlope δ (rowValue H L x t))
            (by linarith : 0≤1+smoothSlope δ (rowValue H L x t))]
      · norm_num
    _ = _ := by simp

omit [DecidableEq κ] in
theorem smooth_proxy_flip_error (H : κ → ℝ) (L : Matrix κ (Fin n) ℝ) (M δ : ℝ)
    (hδ : 0<δ) (x : Assignment n) (i : Fin n) :
    0≤smoothProxy H L M δ (cubeFlip i x)-smoothProxy H L M δ x+
      sign (x i)*(∑ t, L t i*proxySlope H L M δ x t) ∧
    smoothProxy H L M δ (cubeFlip i x)-smoothProxy H L M δ x+
      sign (x i)*(∑ t, L t i*proxySlope H L M δ x t)≤columnEnergy L i/(2*δ) := by
  let E : κ → ℝ := fun t =>
    (if |H t|≤M/2 then smoothAbs δ (rowValue H L (cubeFlip i x) t) else M/4)-
    (if |H t|≤M/2 then smoothAbs δ (rowValue H L x t) else M/4)+
      sign (x i)*L t i*proxySlope H L M δ x t
  have he : ∀ t, 0≤E t ∧ E t≤(L t i)^2/(2*δ) := by
    intro t
    by_cases ht : |H t|≤M/2
    · have h := smooth_taylor δ (rowValue H L x t) (rowValue H L (cubeFlip i x) t) hδ
      rw [row_value_flip] at h
      dsimp [E,proxySlope]
      simp only [ite_eq_left ht]
      have hs : (sign (x i))^2=(1:ℝ) := by cases x i <;> norm_num [sign]
      rw [row_value_flip]
      have hr : (rowValue H L x t-L t i*sign (x i)-rowValue H L x t)^2/(2*δ)=
          (L t i)^2/(2*δ) := by
        rw [show rowValue H L x t-L t i*sign (x i)-rowValue H L x t =
          -(L t i*sign (x i)) by ring,neg_sq,mul_pow,hs,mul_one]
      rw [hr] at h
      constructor <;> nlinarith [h.1,h.2]
    · dsimp [E,proxySlope]
      simp only [ite_eq_right ht,mul_zero,sub_self,add_zero]
      exact ⟨le_refl _,div_nonneg (sq_nonneg _) (by positivity)⟩
  have hsum : (∑ t, E t)=smoothProxy H L M δ (cubeFlip i x)-smoothProxy H L M δ x+
      sign (x i)*(∑ t, L t i*proxySlope H L M δ x t) := by
    simp only [E,smoothProxy,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]
  constructor
  · rw [←hsum]; exact Finset.sum_nonneg (fun t _ => (he t).1)
  · rw [←hsum]
    have h := Finset.sum_le_sum (s := Finset.univ) (fun t _ => (he t).2)
    simpa only [columnEnergy,Finset.sum_div] using h


theorem error_square_bound (D G R : ℝ) (h : 0≤D+G ∧ D+G≤R) :
    D^2≤2*G^2+2*R^2 := by
  have he : (D+G)^2≤R^2 := by nlinarith
  nlinarith [sq_nonneg (D+2*G)]

theorem column_energy_budgets (L : Matrix κ (Fin n) ℝ) (V : ℝ)
    (hV : 0≤V) (hN : ‖L‖^2≤V) :
    (∀ i, 0≤columnEnergy L i ∧ columnEnergy L i≤V) ∧
    (∑ i, (columnEnergy L i)^2)≤Fintype.card κ*V^2 := by
  have hcol : ∀ i, 0≤columnEnergy L i ∧ columnEnergy L i≤V := by
    intro i
    constructor
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    · have h := matrix_squared_energy L (fun j => if j=i then 1 else 0) V hN
      simpa [columnEnergy] using h
  have hn : ‖L.transpose‖^2≤V := by
    simpa using (show ‖L.conjTranspose‖^2≤V by rw [Matrix.l2_opNorm_conjTranspose]; exact hN)
  have hsum := matrix_frobenius_energy L.transpose V hn
  change (∑ i, columnEnergy L i)≤Fintype.card κ*V at hsum
  refine ⟨hcol,?_⟩
  calc
    _ ≤ ∑ i, V*columnEnergy L i := Finset.sum_le_sum (fun i _ => by nlinarith [(hcol i).1,(hcol i).2])
    _ = V*∑ i, columnEnergy L i := (Finset.mul_sum _ _ _).symm
    _ ≤ V*(Fintype.card κ*V) := mul_le_mul_of_nonneg_left hsum hV
    _ = _ := by ring

theorem smooth_proxy_energy (H : κ → ℝ) (L : Matrix κ (Fin n) ℝ) (M δ V : ℝ)
    (hδ : 0<δ) (hV : 0≤V) (hN : ‖L‖^2≤V) (x : Assignment n) :
    (∑ i, (smoothProxy H L M δ x-smoothProxy H L M δ (cubeFlip i x))^2)≤
      2*Fintype.card κ*V+Fintype.card κ*V^2/(2*δ^2) := by
  let G : Fin n → ℝ := fun i => ∑ t, L t i*proxySlope H L M δ x t
  have hp : ∀ i, (smoothProxy H L M δ x-smoothProxy H L M δ (cubeFlip i x))^2≤
      2*(G i)^2+(columnEnergy L i)^2/(2*δ^2) := by
    intro i
    have h := error_square_bound _ _ _ (smooth_proxy_flip_error H L M δ hδ x i)
    have hs : (sign (x i))^2=(1:ℝ) := by cases x i <;> norm_num [sign]
    have he : (sign (x i)*G i)^2=(G i)^2 := by rw [mul_pow,hs,one_mul]
    change _≤2*(sign (x i)*G i)^2+2*(columnEnergy L i/(2*δ))^2 at h
    rw [he] at h
    convert h using 1 <;> ring
  have ht : ‖L.transpose‖^2≤V := by
    simpa using (show ‖L.conjTranspose‖^2≤V by rw [Matrix.l2_opNorm_conjTranspose]; exact hN)
  have hg := (matrix_squared_energy L.transpose (proxySlope H L M δ x) V ht).trans
    (mul_le_mul_of_nonneg_left (proxy_slope_sq H L M δ hδ x) hV)
  change (∑ i, (G i)^2)≤V*Fintype.card κ at hg
  have hc := (column_energy_budgets L V hV hN).2
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_div] at hs
  have hd := div_le_div_of_nonneg_right hc (show 0≤2*δ^2 by positivity)
  nlinarith


end
end Max2SAT.Counts
