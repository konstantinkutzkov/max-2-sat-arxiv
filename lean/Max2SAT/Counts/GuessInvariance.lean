import Max2SAT.Counts.GainStructure
import Max2SAT.Counts.ProfileParameters

namespace Max2SAT.Counts
variable {n r : ℕ}

theorem count_coeff_independent (F : Formula n) (β : ℚ) (a b : ℕ) (t w : Fin n) :
    (countGain F β a t).coeff w=(countGain F β b t).coeff w := rfl

theorem projection_coeff_independent (F : Formula n) (lam : Fin r → ℚ)
    (v : Fin r → Fin n → ℚ) (a b : Fin r → ℚ) (t w : Fin n) :
    (projectionGain F lam v a t).coeff w=(projectionGain F lam v b t).coeff w := rfl

theorem gain_coeff_preprocess (F : Formula n) (hF : wellFormed F) (t w : Fin n) :
    (gainExpr (preprocess F).1 t).coeff w=(gainExpr F t).coeff w := by
  rw [coeff_eval_difference,coeff_eval_difference]
  simp only [gainExpr_eval _ _ _ (preprocess_finished F hF).1,
    gainExpr_eval _ _ _ hF,scoreGain_preprocess]

theorem count_coeff_preprocess (F : Formula n) (hF : wellFormed F) (β : ℚ)
    (a b : ℕ) (t w : Fin n) :
    (countGain (preprocess F).1 β a t).coeff w=(countGain F β b t).coeff w := by
  simp only [countGain,Affine.add,Affine.shift,Affine.scale,gain_coeff_preprocess F hF]

theorem prefix_rows_of_coeff_eq (H G : Fin n → Affine n)
    (h : ∀ t w, (H t).coeff w=(G t).coeff w) (P : Finset (Fin n)) (round : Fin n → ℕ) :
    prefixRows H P round=prefixRows G P round := by
  funext t w
  simp only [prefixRows,earlierRow,h]

theorem sequential_matrix_of_coeff_eq (H G : Fin n → Affine n)
    (h : ∀ t w, (H t).coeff w=(G t).coeff w) (P : Finset (Fin n)) :
    sequentialMatrix H P=sequentialMatrix G P := by
  funext t w
  simp only [sequentialMatrix,h]

theorem earlier_rows_of_coeff_eq (H G : Fin n → Affine n)
    (h : ∀ t w, (H t).coeff w=(G t).coeff w) (round : Fin n → ℕ) (t w : Fin n) :
    earlierRow H round t w=earlierRow G round t w := by
  simp only [earlierRow,h]

end Max2SAT.Counts
