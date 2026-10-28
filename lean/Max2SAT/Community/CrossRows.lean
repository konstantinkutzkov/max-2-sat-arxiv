import Max2SAT.Community.Rounds
import Max2SAT.IndependentPairs.EnergyTails

/-! Cross-round row concentration under the original independent pair law.
Each unordered pair appears only once in a row. No independence between
rows, or between the scalar and matrix events, is used. -/
namespace Max2SAT.Community
noncomputable section
open FiniteLaw RandomInput IndependentPairs
variable {n : ℕ} {α : Type*} [Fintype α]

def crossEdge (t : Fin n) (C : Finset (Fin n)) (hC : ∀ j∈C, j<t) (j : C) : Edge n :=
  ⟨(j.val,t),hC j.val j.property⟩

theorem cross_edge_injective (t : Fin n) (C : Finset (Fin n)) (hC : ∀ j∈C, j<t) :
    Function.Injective (crossEdge t C hC) := by
  intro i j h
  apply Subtype.ext
  exact congrArg (fun e : Edge n => e.val.1) h

theorem cross_row_energy (z : Edge n → ℝ) (t : Fin n) (C : Finset (Fin n))
    (hC : ∀ j∈C, j<t) :
    (∑ j : C, (z (crossEdge t C hC j))^2)=∑ j∈C, (pairMatrix z t j)^2 := by
  rw [←Finset.sum_coe_sort C (fun j : Fin n => (pairMatrix z t j)^2)]
  apply Finset.sum_congr rfl
  intro j _
  rw [pair_matrix_symmetric z t j.val]
  exact congrArg (fun a : ℝ => a^2) (pair_matrix_entry z (crossEdge t C hC j)).symm

/-- A rectangular row has the same scalar tail as an earlier-neighbor row. -/
theorem cross_row_tail (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (t : Fin n) (C : Finset (Fin n)) (hC : ∀ j∈C, j<t) (hc : 0<C.card)
    (B ν χ η : ℝ) (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ) (hη : 0<η) (hη2 : η≤2)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧
      expect (p e) (fun x => (X e x)^2)≤χ*ν) :
    prob (product p) (fun x => (∑ j∈C, (pairMatrix (fun e => X e (x e)) t j)^2)≤(1-η)*C.card*ν)≤
      Real.exp (-η^2*C.card*ν/(4*B^2*χ)) := by
  let e := crossEdge t C hC
  have hc' : (0:ℝ)<C.card := by exact_mod_cast hc
  have hlo : C.card*ν≤∑ j : C, expect (p (e j)) (fun x => (X (e j) x)^2) := by
    simpa using Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => (hv (e j)).1)
  have hhi : (∑ j : C, expect (p (e j)) (fun x => (X (e j) x)^2))≤C.card*χ*ν := by
    simpa [mul_assoc] using Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => (hv (e j)).2)
  have h := squares_lower_tail (fun j => p (e j)) (fun j => X (e j))
    B (C.card*ν) (C.card*χ*ν) η hB (mul_pos hc' hν)
    (by nlinarith [mul_nonneg (mul_nonneg hc'.le hν.le) (sub_nonneg.mpr hχ)]) hη hη2
    (fun j => hb (e j)) hlo hhi
  have hlaw := prob_push (product p) (fun x j => x (e j))
    (fun y => (∑ j : C, (X (e j) (y j))^2)≤(1-η)*(C.card*ν))
  rw [product_select p e (cross_edge_injective t C hC)] at hlaw
  have hr : -(η*(C.card*ν))^2/(4*B^2*(C.card*χ*ν))= -η^2*C.card*ν/(4*B^2*χ) := by
    have hχ0 : χ≠0 := by linarith
    field_simp
  rw [hlaw,hr] at h
  simp_rw [←cross_row_energy _ t C hC]
  simpa only [e,mul_assoc] using h

theorem first_before_second (t : Fin n) (ht : t∈secondRound n) :
    ∀ j∈firstRound n, j<t := by
  intro j hj
  simp only [firstRound,secondRound,Finset.mem_filter,Finset.mem_univ,true_and] at hj ht
  change j.val<t.val
  omega

theorem two_round_row_tail (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (t : Fin n) (ht : t∈secondRound n) (hn : 4≤n)
    (B ν χ : ℝ) (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧
      expect (p e) (fun x => (X e x)^2)≤χ*ν) :
    prob (product p) (fun x => (∑ j∈firstRound n, (pairMatrix (fun e => X e (x e)) t j)^2)≤
      (99/100:ℝ)*(firstRound n).card*ν)≤
      Real.exp (-(1/100:ℝ)^2*(firstRound n).card*ν/(4*B^2*χ)) := by
  have hc : 0<(firstRound n).card := by rw [first_round_card]; omega
  simpa only [show (1:ℝ)-1/100=99/100 by norm_num] using
    cross_row_tail p X t (firstRound n) (first_before_second t ht) hc B ν χ (1/100)
      hB hν hχ (by norm_num) (by norm_num) hb hv

end
end Max2SAT.Community
