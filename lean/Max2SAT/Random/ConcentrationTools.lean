import Max2SAT.Random.BoundedDifferences
import Max2SAT.Random.BlockLaws

/-! Finite-product identities used when applying concentration to the
actual independent edge inputs. -/
namespace Max2SAT.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]

theorem prob_tensor (p : Law α) (q : Law β) (P : α × β → Prop) :
    prob (tensor p q) P = expect p (fun a => prob q (fun b => P (a,b))) := by
  simp only [prob, expect, tensor, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

theorem prob_le_support (p : Law α) (P : α → Prop) (c : ℝ)
    (h : ∀ x, 0 < p.mass x → (if P x then (1:ℝ) else 0) ≤ c) : prob p P ≤ c := by
  have he : prob p P = expect p (fun x => if P x then (1:ℝ) else 0) := by
    simp [prob,expect,mul_ite]
  rw [he]
  exact (expect_mono_support p h).trans_eq (expect_const p c)

theorem prob_push (p : Law α) (f : α → β) (P : β → Prop) :
    prob (push p f) P = prob p (fun x => P (f x)) := by
  have h := expect_push p f (fun y => if P y then (1:ℝ) else 0)
  simpa [expect, prob, mul_ite] using h

theorem tensor_product_law (p : ι → Law α) (q : ι → Law β) :
    push (tensor (product p) (product q)) (fun z i => (z.1 i,z.2 i)) =
      product (fun i => tensor (p i) (q i)) := by
  let e : ((ι → α) × (ι → β)) ≃ (ι → α × β) :=
    { toFun := fun z i => (z.1 i,z.2 i)
      invFun := fun z => (fun i => (z i).1, fun i => (z i).2)
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  apply Law.ext
  funext z
  change (push _ e).mass z = _
  rw [push_equiv_mass]
  simp [e, tensor, product, Finset.prod_mul_distrib]

theorem bounded_differences_finite (p : ι → Law α) (f : (ι → α) → ℝ)
    (c : ι → ℝ) (hd : ∀ i x a, |f (Function.update x i a)-f x| ≤ c i)
    (a : ℝ) (ha : 0 < a) (hc : 0 < ∑ i, (c i)^2) :
    prob (product p) (fun x => f x < expect (product p) f-a) ≤
      Real.exp (-2*a^2/(∑ i, (c i)^2)) := by
  let e := Fintype.equivFin ι
  let back : (Fin (Fintype.card ι) → α) → (ι → α) := fun x i => x (e i)
  have hlaw : push (product (fun j => p (e.symm j))) back = product p := by
    have h := product_select (fun j => p (e.symm j)) e e.injective
    simpa [back] using h
  have hd' : BoundedDifferences (fun x => f (back x)) (fun j => c (e.symm j)) := by
    intro j x b
    have he : back (Function.update x j b) = Function.update (back x) (e.symm j) b := by
      funext i
      simp [back, Function.update, ← e.eq_symm_apply]
    dsimp only
    rw [he]
    exact hd _ _ _
  have hs : (∑ j, (c (e.symm j))^2) = ∑ i, (c i)^2 :=
    Equiv.sum_comp e.symm (fun i => (c i)^2)
  have hmean : expect (product (fun j => p (e.symm j))) (fun x => f (back x)) =
      expect (product p) f := by rw [← expect_push, hlaw]
  have hprob : prob (product (fun j => p (e.symm j)))
      (fun x => f (back x) < expect (product p) f-a) =
      prob (product p) (fun x => f x < expect (product p) f-a) := by
    rw [← prob_push (product (fun j => p (e.symm j))) back
      (fun x => f x < expect (product p) f-a), hlaw]
  have h := bounded_differences_tail (Fintype.card ι) (fun j => p (e.symm j))
    (fun x => f (back x)) (fun j => c (e.symm j)) hd' a ha (by rw [hs]; exact hc)
  rw [hs, hmean, hprob] at h
  exact h

end
end Max2SAT.FiniteLaw
