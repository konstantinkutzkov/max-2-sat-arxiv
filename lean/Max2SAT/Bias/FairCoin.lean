import Max2SAT.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! Finite uniform Boolean probability, defined by repeated averaging.
No measure-theoretic conditional expectations are needed for this model. -/
namespace Max2SAT.FairCoin
noncomputable section

/-- Uniform expectation over all assignments to n independent fair bits. -/
def average : (n : ℕ) → (Assignment n → ℝ) → ℝ
  | 0, f => f Fin.elim0
  | n+1, f => (average n (fun x => f (Fin.cons false x)) +
      average n (fun x => f (Fin.cons true x))) / 2

@[simp] theorem average_const (n : ℕ) (a : ℝ) : average n (fun _ => a)=a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [average,ih]

theorem average_add (n : ℕ) (f g : Assignment n → ℝ) :
    average n (fun x => f x+g x)=average n f+average n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [average,ih]; ring

theorem average_sub (n : ℕ) (f g : Assignment n → ℝ) :
    average n (fun x => f x-g x)=average n f-average n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [average,ih]; ring

theorem average_mul (n : ℕ) (a : ℝ) (f : Assignment n → ℝ) :
    average n (fun x => a*f x)=a*average n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [average,ih]; ring

theorem average_mono (n : ℕ) {f g : Assignment n → ℝ} (h : ∀ x, f x≤g x) :
    average n f ≤ average n g := by
  induction n with
  | zero => exact h _
  | succ n ih =>
    exact div_le_div_of_nonneg_right
      (add_le_add (ih (fun x => h (Fin.cons false x)))
        (ih (fun x => h (Fin.cons true x)))) (by norm_num)

theorem average_nonneg (n : ℕ) {f : Assignment n → ℝ} (h : ∀ x, 0≤f x) :
    0≤average n f := by
  simpa using average_mono n h

theorem abs_average_le (n : ℕ) (f : Assignment n → ℝ) :
    |average n f| ≤ average n (fun x => |f x|) := by
  rw [abs_le]
  constructor
  · have hh := average_mono n (fun x => neg_abs_le (f x))
    have he : average n (fun x => -|f x|) = -average n (fun x => |f x|) := by
      simpa using average_mul n (-1) (fun x => |f x|)
    simpa [he] using hh
  · exact average_mono n (fun x => le_abs_self (f x))

/-- A Boolean event's probability, represented as the mean of its indicator. -/
def probability (n : ℕ) (P : Assignment n → Prop) : ℝ := by
  classical
  exact average n (fun x => if P x then 1 else 0)

/-- Changing one coordinate changes the statistic by at most its allowance. -/
def BoundedDifferences (f : Assignment n → ℝ) (c : Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (x : Assignment n) (b : Bool), |f (Function.update x i b)-f x| ≤ c i

theorem update_cons_zero (x : Assignment n) (a b : Bool) :
    Function.update (Fin.cons a x : Assignment (n+1)) 0 b =
      (Fin.cons b x : Assignment (n+1)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

theorem update_cons_succ (x : Assignment n) (a b : Bool) (i : Fin n) :
    Function.update (Fin.cons a x : Assignment (n+1)) i.succ b =
      (Fin.cons a (Function.update x i b) : Assignment (n+1)) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Function.update,Ne.symm (Fin.succ_ne_zero i)]
  · by_cases h : k=i
    · subst k; simp
    · simp [h]

theorem bounded_tail {f : Assignment (n+1) → ℝ} {c : Fin (n+1) → ℝ}
    (h : BoundedDifferences f c) (a : Bool) :
    BoundedDifferences (fun x => f (Fin.cons a x)) (fun i => c i.succ) := by
  intro i x b
  simpa only [update_cons_succ] using h i.succ (Fin.cons a x) b

theorem mean_children_distance {f : Assignment (n+1) → ℝ} {c : Fin (n+1) → ℝ}
    (h : BoundedDifferences f c) :
    |average n (fun x => f (Fin.cons false x))-
      average n (fun x => f (Fin.cons true x))| ≤ c 0 := by
  rw [← average_sub]
  apply le_trans (abs_average_le _ _) ?_
  rw [← average_const n (c 0)]
  apply average_mono
  intro x
  simpa only [update_cons_zero] using h 0 (Fin.cons true x) false

/-- The elementary fair-coin exponential estimate used in the concentration proof. -/
theorem exp_pair_le (u v t c : ℝ) (_hc : 0≤c) (hd : |u-v|≤c) :
    (Real.exp (t*(u-(u+v)/2))+Real.exp (t*(v-(u+v)/2)))/2 ≤
      Real.exp (t^2*c^2/2) := by
  let z := t*(u-v)/2
  have h0 : t*(u-(u+v)/2)=z := by dsimp [z]; ring
  have h1 : t*(v-(u+v)/2)= -z := by dsimp [z]; ring
  rw [h0,h1,←Real.cosh_eq]
  apply le_trans (Real.cosh_le_exp_half_sq z)
  apply Real.exp_le_exp.mpr
  have hs : (u-v)^2 ≤ c^2 := by
    have hp := mul_nonneg (sub_nonneg.mpr (abs_le.mp hd).2)
      (show 0≤c+(u-v) by linarith [(abs_le.mp hd).1])
    nlinarith
  dsimp [z]
  nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hs),sq_nonneg (t*(u-v))]

/-- A deliberately conservative bounded-differences exponential-moment bound. -/
theorem mgf_bound (n : ℕ) (f : Assignment n → ℝ) (c : Fin n → ℝ)
    (hc : ∀ i, 0≤c i) (hd : BoundedDifferences f c) (t : ℝ) :
    average n (fun x => Real.exp (t*(f x-average n f))) ≤
      Real.exp (t^2*(∑ i, (c i)^2)/2) := by
  induction n with
  | zero => simp [average]
  | succ n ih =>
    let f0 := fun x => f (Fin.cons false x)
    let f1 := fun x => f (Fin.cons true x)
    let m0 := average n f0
    let m1 := average n f1
    let v := t^2*(∑ i : Fin n, (c i.succ)^2)/2
    have h0 := ih f0 (fun i => c i.succ) (fun i => hc i.succ) (bounded_tail hd false)
    have h1 := ih f1 (fun i => c i.succ) (fun i => hc i.succ) (bounded_tail hd true)
    have e0 : average n (fun x => Real.exp (t*(f0 x-(m0+m1)/2))) =
        Real.exp (t*(m0-(m0+m1)/2))*average n (fun x => Real.exp (t*(f0 x-m0))) := by
      rw [← average_mul]
      congr 1; funext x
      rw [←Real.exp_add]; congr 1; ring
    have e1 : average n (fun x => Real.exp (t*(f1 x-(m0+m1)/2))) =
        Real.exp (t*(m1-(m0+m1)/2))*average n (fun x => Real.exp (t*(f1 x-m1))) := by
      rw [← average_mul]
      congr 1; funext x
      rw [←Real.exp_add]; congr 1; ring
    change (average n (fun x => Real.exp (t*(f0 x-(m0+m1)/2)))+
      average n (fun x => Real.exp (t*(f1 x-(m0+m1)/2))))/2 ≤ _
    rw [e0,e1]
    have hm := exp_pair_le m0 m1 t (c 0) (hc 0) (mean_children_distance hd)
    calc
      _ ≤ ((Real.exp (t*(m0-(m0+m1)/2))+Real.exp (t*(m1-(m0+m1)/2)))/2)*Real.exp v := by
        have h0' := mul_le_mul_of_nonneg_left h0 (Real.exp_pos (t*(m0-(m0+m1)/2))).le
        have h1' := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (t*(m1-(m0+m1)/2))).le
        dsimp [v,m0,m1] at *
        nlinarith
      _ ≤ Real.exp (t^2*(c 0)^2/2)*Real.exp v :=
        mul_le_mul_of_nonneg_right hm (Real.exp_pos v).le
      _ = _ := by
        rw [←Real.exp_add,Fin.sum_univ_succ]
        congr 1; dsimp [v]; ring

/-- Chernoff's argument on the finite Boolean cube. -/
theorem lower_tail (n : ℕ) (f : Assignment n → ℝ) (c : Fin n → ℝ)
    (hc : ∀ i, 0≤c i) (hd : BoundedDifferences f c) (a : ℝ) (ha : 0≤a)
    (hv : 0 < ∑ i, (c i)^2) :
    probability n (fun x => f x ≤ average n f-a) ≤
      Real.exp (-a^2/(2*(∑ i, (c i)^2))) := by
  classical
  let V := ∑ i, (c i)^2
  let t := a/V
  have ht : 0≤t := div_nonneg ha hv.le
  have hm := mgf_bound n f c hc hd (-t)
  have hp : probability n (fun x => f x≤average n f-a) * Real.exp (t*a) ≤
      average n (fun x => Real.exp (-t*(f x-average n f))) := by
    unfold probability
    rw [mul_comm,←average_mul]
    apply average_mono
    intro x
    split
    · rename_i hx
      simp only [mul_one]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg ht (show 0≤average n f-a-f x by linarith)]
    · simp [Real.exp_nonneg]
  have hres := le_trans hp hm
  have hres' := (le_div_iff₀ (Real.exp_pos (t*a))).mpr hres
  convert hres' using 1
  rw [←Real.exp_sub]
  congr 1
  dsimp [t,V]
  field_simp
  ring

/-- Enumerate the finite probability space, for exact cardinality statements. -/
def assignments : (n : ℕ) → List (Assignment n)
  | 0 => [Fin.elim0]
  | n+1 => (assignments n).map (Fin.cons false) ++ (assignments n).map (Fin.cons true)

@[simp] theorem assignments_length (n : ℕ) : (assignments n).length=2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [assignments,ih,pow_succ]; omega

theorem mem_assignments (n : ℕ) (x : Assignment n) : x∈assignments n := by
  induction n with
  | zero =>
    have hx : x=Fin.elim0 := by funext i; exact i.elim0
    simp [assignments,hx]
  | succ n ih =>
    have hx : x=Fin.cons (x 0) (fun i => x i.succ) := by
      funext i; exact Fin.cases (by simp) (fun j => by simp) i
    rw [hx]
    cases h : x 0 <;> simp [assignments,ih]

theorem assignments_nodup (n : ℕ) : (assignments n).Nodup := by
  induction n with
  | zero => simp [assignments]
  | succ n ih =>
    rw [assignments,List.nodup_append]
    have hinj (b : Bool) : Function.Injective (fun x : Assignment n => (Fin.cons b x : Assignment (n+1))) := by
      intro x y h
      funext i
      simpa using congrFun h i.succ
    refine ⟨ih.map (hinj false),ih.map (hinj true),?_⟩
    intro x hx y hy hxy
    rcases List.mem_map.mp hx with ⟨a,ha,rfl⟩
    rcases List.mem_map.mp hy with ⟨b,hb,rfl⟩
    have h := congrFun hxy 0
    simp at h

theorem average_eq_sum (n : ℕ) (f : Assignment n → ℝ) :
    average n f = ((assignments n).map f).sum / 2^n := by
  induction n with
  | zero => simp [average,assignments]
  | succ n ih =>
    simp only [average,assignments,List.map_append,List.sum_append,List.map_map,Function.comp_def,ih,pow_succ]
    ring

def eventCount (n : ℕ) (P : Assignment n → Prop) : ℕ := by
  classical
  exact (assignments n).countP (fun x => decide (P x))

/-- The random-path probability is exactly the surviving fraction of assignments. -/
theorem probability_eq_count (n : ℕ) (P : Assignment n → Prop) :
    probability n P = (eventCount n P : ℝ)/2^n := by
  classical
  rw [probability,average_eq_sum,eventCount]
  congr 1
  induction assignments n with
  | nil => simp
  | cons x xs ih =>
    by_cases h : P x <;> simp [h,ih,add_comm]

end
end Max2SAT.FairCoin
