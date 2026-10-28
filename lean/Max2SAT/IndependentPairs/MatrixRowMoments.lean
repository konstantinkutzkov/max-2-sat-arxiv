import Max2SAT.IndependentPairs.MatrixExpectation
import Max2SAT.Counts.RoundPassing

/-! Scalar bounds on the row and column maxima of the independent-copy
matrix. Both are bounded by the incident squared mass at the same vertex;
this slightly coarser common bound suffices for the constant 2.89. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open FiniteLaw RandomInput
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 800000
variable {n : ℕ} {α : Type*} [Fintype α]

def incidentEdge (i : Fin n) (j : {j : Fin n // j≠i}) : Edge n :=
  if h : i < j.val then ⟨(i,j.val),h⟩
  else ⟨(j.val,i),lt_of_le_of_ne (le_of_not_gt h) j.property⟩

theorem incident_edge_value (i : Fin n) (j : {j : Fin n // j≠i}) (z : Edge n → ℝ) :
    pairMatrix z i j.val=z (incidentEdge i j) := by
  by_cases h : i < j.val
  · simp [pairMatrix,incidentEdge,h]
  · have hj : j.val < i := lt_of_le_of_ne (le_of_not_gt h) j.property
    simp [pairMatrix,incidentEdge,h,hj]

theorem incident_edge_injective (i : Fin n) : Function.Injective (incidentEdge i) := by
  have back : ∀ j : {j : Fin n // j≠i},
      (if (incidentEdge i j).val.1=i then (incidentEdge i j).val.2
       else (incidentEdge i j).val.1)=j.val := by
    intro j
    by_cases h : i < j.val
    · simp [incidentEdge,h]
    · simp [incidentEdge,h,j.property]
  intro j k h
  apply Subtype.ext
  rw [←back j,←back k,h]

def incidentEnergy (z : Edge n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, (pairMatrix z i j)^2

theorem incident_energy_sum (z : Edge n → ℝ) (i : Fin n) :
    incidentEnergy z i=∑ j : {j : Fin n // j≠i}, (z (incidentEdge i j))^2 := by
  simp_rw [←incident_edge_value]
  rw [←Finset.sum_subtype (Finset.univ.filter (fun j : Fin n => j≠i))
    (by intro j; simp) (fun j => (pairMatrix z i j)^2),Finset.sum_filter]
  unfold incidentEnergy
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j=i
  · subst j; simp [pair_matrix_diagonal]
  · simp [h]

theorem upper_entry_le_pair_square (T : ℕ) (z : Edge n → ℝ) (i j : Fin n) :
    (upperMatrix T z i j)^2≤(pairMatrix z i j)^2 := by
  dsimp [upperMatrix]
  split_ifs with h hT
  · simp [pairMatrix,h]
  · simpa using sq_nonneg (pairMatrix z i j)
  · simpa using sq_nonneg (pairMatrix z i j)

theorem row_size_le_of_incident (T : ℕ) (z : Edge n → ℝ) (a : ℝ)
    (h : ∀ i, incidentEnergy z i≤a) :
    rowSize (upperMatrix T z)≤Real.sqrt a ∧
      rowSize (upperMatrix T z).transpose≤Real.sqrt a := by
  constructor
  · apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg a)).mpr
    intro i
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs,sq_abs]
    apply Real.sqrt_le_sqrt
    exact (Finset.sum_le_sum (fun j _ => upper_entry_le_pair_square T z i j)).trans (h i)
  · apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg a)).mpr
    intro i
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs,sq_abs,Matrix.transpose_apply]
    apply Real.sqrt_le_sqrt
    have he := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => upper_entry_le_pair_square T z j i)
    simp_rw [pair_matrix_symmetric z _ i] at he
    exact he.trans (h i)

theorem incident_energy_bound (z : Edge n → ℝ) (b : ℝ)
    (hz : ∀ e, |z e|≤b) (i : Fin n) : incidentEnergy z i≤n*b^2 := by
  have he : ∀ j, (pairMatrix z i j)^2≤b^2 := by
    intro j
    by_cases hij : j=i
    · subst j; simp [pair_matrix_diagonal,sq_nonneg]
    · rw [incident_edge_value i ⟨j,hij⟩ z]
      have hh := abs_le.mp (hz (incidentEdge i ⟨j,hij⟩))
      nlinarith
  simpa [incidentEnergy] using Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => he j)

/-- Concentration for all incident coordinates; each is independently
sampled once, although the symmetric matrix uses it in two orientations. -/
theorem copy_incident_tail (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (i : Fin n) (B ν χ : ℝ) (hB : 0<B) (hν : 0<ν) (hχ : 0<χ)
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, expect (p e) (fun x => (X e x)^2)≤χ*ν) :
    prob (copyLaw p) (fun x => (202/100:ℝ)*n*χ*ν≤ incidentEnergy (copyDifference X x) i)≤
      Real.exp (-(1/100:ℝ)^2*n*χ*ν/(8*B^2)) := by
  let q := fun e => tensor (p e) (p e)
  let Y := fun (j : {j : Fin n // j≠i}) (a : α × α) =>
    X (incidentEdge i j) a.1-X (incidentEdge i j) a.2
  have hn : (0:ℝ)<n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hcard : (Fintype.card {j : Fin n // j≠i}:ℝ)≤n := by
    exact_mod_cast (show Fintype.card {j : Fin n // j≠i}≤n from
      (Fintype.card_le_of_injective (fun j : {j : Fin n // j≠i} => j.val) Subtype.val_injective).trans_eq
        (Fintype.card_fin n))
  have hcap : (∑ j, expect (q (incidentEdge i j)) (fun a => (Y j a)^2))≤2*n*χ*ν := by
    have hh : ∀ j, expect (q (incidentEdge i j)) (fun a => (Y j a)^2)≤2*(χ*ν) := by
      intro j
      dsimp [q,Y]
      rw [centered_difference_moment _ _ (hm _)]
      exact mul_le_mul_of_nonneg_left (hv _) (by norm_num)
    calc
      _ ≤ ∑ _j : {j : Fin n // j≠i}, 2*(χ*ν) := Finset.sum_le_sum (fun j _ => hh j)
      _ ≤ _ := by simpa [mul_assoc,mul_comm,mul_left_comm] using
        mul_le_mul_of_nonneg_right hcard (show 0≤2*χ*ν by positivity)
  have h := squares_upper_tail (fun j => q (incidentEdge i j)) Y (2*B) (2*n*χ*ν)
    (1/100) (by positivity) (by positivity) (by norm_num) (by norm_num)
    (fun j a ha => difference_bound _ _ B (hb _) a ha) hcap
  have hlaw := product_select q (incidentEdge i) (incident_edge_injective i)
  have hp := prob_push (copyLaw p) (fun x j => x (incidentEdge i j))
    (fun y => (1+(1/100:ℝ))*(2*n*χ*ν)≤∑ j, (Y j (y j))^2)
  change prob (push (product q) _) _=_ at hp
  rw [hlaw] at hp
  rw [hp] at h
  have hexp : -((1/100:ℝ)*(2*n*χ*ν))^2/(4*(2*B)^2*(2*n*χ*ν))=
      -(1/100:ℝ)^2*n*χ*ν/(8*B^2) := by field_simp; ring
  rw [hexp] at h
  simpa only [copyLaw,incident_energy_sum,copyDifference,Y,show
    (1+(1/100:ℝ))*(2*n*χ*ν)=(202/100:ℝ)*n*χ*ν by ring] using h

/-- Split a bounded random quantity into its ordinary and exceptional cases. -/
theorem expect_bound_with_exception {β : Type*} [Fintype β] (p : Law β)
    (f : β → ℝ) (bad : β → Prop) (a b : ℝ) (ha : 0≤a)
    (hcap : ∀ x, 0<p.mass x → f x≤b)
    (hgood : ∀ x, 0<p.mass x → ¬bad x → f x≤a) :
    expect p f≤a+b*prob p bad := by
  classical
  have he : expect p (fun x => if bad x then b else 0)=b*prob p bad := by
    simp only [expect,prob,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  calc
    _ ≤ expect p (fun x => a+(if bad x then b else 0)) := expect_mono_support p (by
      intro x hx
      by_cases hh : bad x
      · simp only [hh,↓reduceIte]; linarith [hcap x hx]
      · simpa only [hh,↓reduceIte,add_zero] using hgood x hx hh)
    _ = _ := by rw [expect_add,expect_const,he]

/-- The two moments required by the norm expectation proof, derived from
scalar concentration. The displayed small-error budget is subsequently
checked from the paper's large-density constants. -/
theorem copy_row_moment_bounds (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (T : ℕ) (B ν χ : ℝ) (hB : 0<B) (hν : 0<ν) (hχ : 0<χ)
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, expect (p e) (fun x => (X e x)^2)≤χ*ν)
    (herr : (4*n*B^2)*(n*Real.exp (-(1/100:ℝ)^2*n*χ*ν/(8*B^2)))≤
      (2/100:ℝ)*n*χ*ν) :
    (expect (copyLaw p) (fun x => (rowSize (upperMatrix T (copyDifference X x)))^2)≤(204/100:ℝ)*n*χ*ν) ∧
    (expect (copyLaw p) (fun x => (rowSize (upperMatrix T (copyDifference X x)).transpose)^2)≤(204/100:ℝ)*n*χ*ν) := by
  let bad := fun x => ∃ i : Fin n, (202/100:ℝ)*n*χ*ν< incidentEnergy (copyDifference X x) i
  have hbad : prob (copyLaw p) bad≤n*Real.exp (-(1/100:ℝ)^2*n*χ*ν/(8*B^2)) := by
    have hu := Counts.finite_union_bound (copyLaw p) Finset.univ
      (fun i x => (202/100:ℝ)*n*χ*ν< incidentEnergy (copyDifference X x) i)
    simp only [Finset.mem_univ,true_and] at hu
    apply hu.trans
    have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
      (prob_mono_support (copyLaw p)
        (fun x => (202/100:ℝ)*n*χ*ν < incidentEnergy (copyDifference X x) i)
        (fun x => (202/100:ℝ)*n*χ*ν ≤ incidentEnergy (copyDifference X x) i)
        (fun x _ hx => hx.le)).trans
        (copy_incident_tail p X i B ν χ hB hν hχ hm hb hv))
    simpa using hh
  have hcap : ∀ x, 0<(copyLaw p).mass x →
      (rowSize (upperMatrix T (copyDifference X x)))^2≤4*n*B^2 ∧
      (rowSize (upperMatrix T (copyDifference X x)).transpose)^2≤4*n*B^2 := by
    intro x hx
    have hh := row_size_le_of_incident T (copyDifference X x) (n*(2*B)^2)
      (fun i => incident_energy_bound _ (2*B) (fun e =>
        difference_bound (p e) (X e) B (hb e) (x e)
          (product_coordinate_positive (fun e => tensor (p e) (p e)) x hx e)) i)
    have hs := Real.sq_sqrt (x:=(n:ℝ)*(2*B)^2) (by positivity)
    constructor
    · have h := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hh.1
      rw [hs] at h
      dsimp only [rowSize]
      convert h using 1; ring
    · have h := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hh.2
      rw [hs] at h
      dsimp only [rowSize]
      convert h using 1; ring
  have hgood : ∀ x, ¬bad x →
      (rowSize (upperMatrix T (copyDifference X x)))^2≤(202/100:ℝ)*n*χ*ν ∧
      (rowSize (upperMatrix T (copyDifference X x)).transpose)^2≤(202/100:ℝ)*n*χ*ν := by
    intro x hx
    have hh := row_size_le_of_incident T (copyDifference X x) ((202/100:ℝ)*n*χ*ν)
      (fun i => le_of_not_gt (fun hi => hx ⟨i,hi⟩))
    have hs := Real.sq_sqrt (x:=(202/100:ℝ)*n*χ*ν) (by positivity)
    constructor
    · have h := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hh.1
      rwa [hs] at h
    · have h := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hh.2
      rwa [hs] at h
  have herror := mul_le_mul_of_nonneg_left hbad (show 0≤4*(n:ℝ)*B^2 by positivity)
  have hr := expect_bound_with_exception (copyLaw p)
    (fun x => (rowSize (upperMatrix T (copyDifference X x)))^2) bad
    ((202/100:ℝ)*n*χ*ν) (4*n*B^2) (by positivity)
    (fun x hx => (hcap x hx).1) (fun x _ hx => (hgood x hx).1)
  have hc := expect_bound_with_exception (copyLaw p)
    (fun x => (rowSize (upperMatrix T (copyDifference X x)).transpose)^2) bad
    ((202/100:ℝ)*n*χ*ν) (4*n*B^2) (by positivity)
    (fun x hx => (hcap x hx).2) (fun x _ hx => (hgood x hx).2)
  constructor <;> linarith

end
end Max2SAT.IndependentPairs
