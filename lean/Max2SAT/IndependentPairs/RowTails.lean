import Max2SAT.IndependentPairs.MeanTail
import Max2SAT.IndependentPairs.MatrixModel

/-! The original independent-pair law induces the product law on every
row's earlier neighbors. Concentration is applied before empirical centering. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open FiniteLaw RandomInput
variable {n : ℕ} {α : Type*} [Fintype α]

def earlierEnergy (z : Edge n → ℝ) (t : Fin n) : ℝ :=
  ∑ j : Fin t.val, (z (earlierEdge t j))^2

theorem earlier_pair_value (z : Edge n → ℝ) (t : Fin n) (j : Fin t.val) :
    pairMatrix z t ⟨j.val,j.isLt.trans t.isLt⟩=z (earlierEdge t j) := by
  rw [pair_matrix_symmetric]
  exact pair_matrix_entry z (earlierEdge t j)

theorem earlier_energy_matrix (z : Edge n → ℝ) (t : Fin n) :
    earlierEnergy z t=
      ∑ j : Fin t.val, (pairMatrix z t ⟨j.val,j.isLt.trans t.isLt⟩)^2 := by
  simp only [earlier_pair_value,earlierEnergy]

theorem earlier_product_law (p : Edge n → Law α) (t : Fin n) :
    push (product p) (fun x j => x (earlierEdge t j))=
      product (fun j => p (earlierEdge t j)) :=
  product_select p (earlierEdge t) (earlier_edge_injective t)

theorem earlier_energy_tail (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (t : Fin n) (ht : 0<t.val) (B ν χ η : ℝ)
    (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ) (hη : 0<η) (hη2 : η≤2)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧
      expect (p e) (fun x => (X e x)^2)≤χ*ν) :
    prob (product p) (fun x => earlierEnergy (fun e => X e (x e)) t≤(1-η)*t.val*ν)≤
      Real.exp (-η^2*t.val*ν/(4*B^2*χ)) := by
  have ht' : (0:ℝ)<t.val := by exact_mod_cast ht
  have hlo : (t.val:ℝ)*ν≤∑ j : Fin t.val, expect (p (earlierEdge t j))
      (fun x => (X (earlierEdge t j) x)^2) := by
    simpa using Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => (hv (earlierEdge t j)).1)
  have hhi : (∑ j : Fin t.val, expect (p (earlierEdge t j))
      (fun x => (X (earlierEdge t j) x)^2))≤(t.val:ℝ)*χ*ν := by
    simpa [mul_assoc] using Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => (hv (earlierEdge t j)).2)
  have h := squares_lower_tail (fun j => p (earlierEdge t j)) (fun j => X (earlierEdge t j))
    B (t.val*ν) (t.val*χ*ν) η hB (mul_pos ht' hν)
    (by nlinarith [mul_nonneg (mul_nonneg ht'.le hν.le) (sub_nonneg.mpr hχ)]) hη hη2
    (fun j => hb (earlierEdge t j)) hlo hhi
  have hlaw := prob_push (product p) (fun x j => x (earlierEdge t j))
    (fun y => (∑ j : Fin t.val, (X (earlierEdge t j) (y j))^2)≤(1-η)*(t.val*ν))
  rw [earlier_product_law] at hlaw
  have hr : -(η*(t.val*ν))^2/(4*B^2*(t.val*χ*ν))= -η^2*t.val*ν/(4*B^2*χ) := by
    have hχ0 : χ≠0 := by linarith
    field_simp
  rw [hlaw,hr] at h
  simpa only [earlierEnergy,mul_assoc] using h

/-- A bound on the empirical shift gives a row bound simultaneously for
all such shifts. This uses no independence after centering. -/
theorem earlier_shift_lower (z : Edge n → ℝ) (t : Fin n) (δ ν : ℝ)
    (hν : 0≤ν) (hmass : (99/100:ℝ)*t.val*ν≤earlierEnergy z t)
    (hδ : |δ|≤(1/1000:ℝ)*Real.sqrt ν) :
    (993/1000:ℝ)*Real.sqrt (t.val*ν)≤
      Real.sqrt (earlierEnergy (fun e => z e-δ) t) := by
  simpa only [Fintype.card_fin,earlierEnergy] using
    centered_row_lower (fun j : Fin t.val => z (earlierEdge t j)) δ ν hν
      (by simpa only [Fintype.card_fin,earlierEnergy] using hmass) hδ

end
end Max2SAT.IndependentPairs
