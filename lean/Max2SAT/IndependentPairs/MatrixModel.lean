import Max2SAT.Random.Encoding
import Max2SAT.IndependentPairs.Centering
import Mathlib.Algebra.BigOperators.Intervals

/-! One independent coordinate per unordered pair, and its symmetric
zero-diagonal matrix. No independence of the two matrix orientations is
assumed. The Frobenius normalization counts each pair twice. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open RandomInput
variable {n : ℕ}

def pairMatrix (z : Edge n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if h:i < j then z ⟨(i,j),h⟩ else if h:j < i then z ⟨(j,i),h⟩ else 0

theorem pair_matrix_diagonal (z : Edge n → ℝ) (i : Fin n) : pairMatrix z i i=0 := by
  simp [pairMatrix]

theorem pair_matrix_symmetric (z : Edge n → ℝ) (i j : Fin n) :
    pairMatrix z i j=pairMatrix z j i := by
  rcases lt_trichotomy i j with h|rfl|h
  · simp [pairMatrix,h,not_lt.mpr h.le]
  · rfl
  · simp [pairMatrix,h,not_lt.mpr h.le]

theorem pair_matrix_entry (z : Edge n → ℝ) (e : Edge n) :
    pairMatrix z e.val.1 e.val.2=z e := by simp [pairMatrix,e.property]

theorem sum_on_pairs (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ e : Edge n, A e.val.1 e.val.2)=∑ i, ∑ j, if i < j then A i j else 0 := by
  rw [←Finset.sum_subtype (Finset.univ.filter (fun e : Fin n × Fin n => e.1<e.2))
    (by intro e; simp) (fun e => A e.1 e.2),Finset.sum_filter,Fintype.sum_prod_type]

theorem symmetric_matrix_sum (A : Matrix (Fin n) (Fin n) ℝ)
    (hs : ∀ i j, A i j=A j i) (hd : ∀ i, A i i=0) :
    (∑ i, ∑ j, A i j)=2*∑ e : Edge n, A e.val.1 e.val.2 := by
  rw [sum_on_pairs,two_mul]
  have he : ∀ i j, A i j=(if i < j then A i j else 0)+(if j < i then A i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h|rfl|h
    · simp [h,not_lt.mpr h.le]
    · simp [hd]
    · simp [h,not_lt.mpr h.le]
  have hsum : (∑ i, ∑ j, A i j)=
      (∑ i, ∑ j, if i < j then A i j else 0)+(∑ i, ∑ j, if j < i then A i j else 0) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => he i j)
  rw [hsum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs j i]

theorem pair_matrix_energy (z : Edge n → ℝ) :
    (∑ i, ∑ j, (pairMatrix z i j)^2)=2*∑ e, (z e)^2 := by
  rw [symmetric_matrix_sum (fun i j => (pairMatrix z i j)^2)
    (by intro i j; rw [pair_matrix_symmetric z i j])
    (by intro i; simp [pair_matrix_diagonal])]
  simp_rw [pair_matrix_entry]

def pairEnergy (z : Edge n → ℝ) : ℝ := (∑ i, ∑ j, (pairMatrix z i j)^2)/(n:ℝ)

theorem pair_energy_formula (z : Edge n → ℝ) :
    pairEnergy z=2*(∑ e, (z e)^2)/(n:ℝ) := by rw [pairEnergy,pair_matrix_energy]

/-- Rows use one copy of each pair, indexed by the earlier endpoint. -/
def earlierEdge (t : Fin n) (j : Fin t.val) : Edge n :=
  ⟨(⟨j.val,j.isLt.trans t.isLt⟩,t),j.isLt⟩

theorem earlier_edge_injective (t : Fin n) : Function.Injective (earlierEdge t) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun e : Edge n => e.val.1.val) h

def edgeEquiv : Edge n ≃ Σ t : Fin n, Fin t.val where
  toFun e := ⟨e.val.2,⟨e.val.1.val,e.property⟩⟩
  invFun e := earlierEdge e.1 e.2
  left_inv e := by apply Subtype.ext; apply Prod.ext <;> rfl
  right_inv e := by cases e; rfl

theorem pair_count : Fintype.card (Edge n)*2=n*(n-1) := by
  rw [Fintype.card_congr edgeEquiv,Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n]
  exact Finset.sum_range_id_mul_two n

theorem pair_count_real (hn : 1≤n) :
    2*(Fintype.card (Edge n):ℝ)=(n:ℝ)*((n:ℝ)-1) := by
  have h := pair_count (n:=n)
  have he : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by simp [Nat.cast_sub hn]
  have hc : (Fintype.card (Edge n):ℝ)*2=(n:ℝ)*((n-1:ℕ):ℝ) := by exact_mod_cast h
  rw [he] at hc
  linarith

theorem empirical_pair_energy [Nonempty (Edge n)] (z : Edge n → ℝ) (hn : 1≤n) :
    pairEnergy (fun e => z e-empiricalMean z)=
      pairEnergy z-((n:ℝ)-1)*(empiricalMean z)^2 := by
  rw [pair_energy_formula,pair_energy_formula,empirical_energy]
  have h := pair_count_real hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  field_simp
  nlinarith [congrArg (fun u : ℝ => u*(empiricalMean z)^2) h]

end
end Max2SAT.IndependentPairs
