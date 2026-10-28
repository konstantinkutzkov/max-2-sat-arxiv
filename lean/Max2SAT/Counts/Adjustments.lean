import Max2SAT.Counts.FormulaGains

/-! Exact count and approximate projection adjustments. The diagonal
correction is retained: even the correct guess generally needs slack. -/
namespace Max2SAT.Counts

def projection (v : Fin n → ℚ) (x : Assignment n) : ℚ := ∑ i, v i*bit (x i)
def without (v : Fin n → ℚ) (t : Fin n) : Affine n :=
  ⟨0,fun w => if w=t then 0 else v w⟩

theorem without_eval (v : Fin n → ℚ) (t : Fin n) (x : Assignment n) :
    (without v t).eval x=projection v x-v t*bit (x t) := by
  have hsum := Finset.sum_erase_add Finset.univ (fun w => v w*bit (x w)) (Finset.mem_univ t)
  have he : (without v t).eval x = ∑ w∈Finset.univ.erase t, v w*bit (x w) := by
    unfold Affine.eval without
    simp only [zero_add]
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ t)]
    simp only [ite_true,zero_mul,add_zero]
    apply Finset.sum_congr rfl
    intro w hw
    simp only [ite_eq_right (Finset.mem_erase.mp hw).1]
  rw [he]
  exact eq_sub_iff_add_eq.mpr hsum

def ones (x : Assignment n) : ℕ := ∑ i, if x i then 1 else 0

theorem ones_le (x : Assignment n) : ones x≤n := by
  calc
    ones x ≤ ∑ _i : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro i _
      split <;> omega
    _ = n := by simp

theorem ones_cast (x : Assignment n) : (ones x : ℚ)=projection (fun _ => 1) x := by
  simp [ones,projection,bit]

def countGain (F : Formula n) (β : ℚ) (h : ℕ) (t : Fin n) : Affine n :=
  (gainExpr F t).add (((without (fun _ => 1) t).scale (-β)).shift (β*h))

theorem countGain_eval (F : Formula n) (β : ℚ) (h : ℕ) (t : Fin n)
    (x : Assignment n) (hF : wellFormed F) :
    (countGain F β h t).eval x =
      scoreGain F t x+β*((h:ℚ)-(ones x : ℚ)+bit (x t)) := by
  simp only [countGain,Affine.eval_add,Affine.eval_shift,Affine.eval_scale,
    gainExpr_eval F t x hF,without_eval,←ones_cast]
  ring

theorem correct_count_error (F : Formula n) (β : ℚ) (x : Assignment n)
    (t : Fin n) (hF : wellFormed F) :
    |scoreGain F t x-(countGain F β (ones x) t).eval x|≤|β| := by
  rw [countGain_eval F β (ones x) t x hF]
  cases x t <;> simp

theorem zero_count_error (F : Formula n) (x : Assignment n)
    (t : Fin n) (hF : wellFormed F) :
    |scoreGain F t x-(countGain F 0 0 t).eval x|≤|0| := by
  simp [countGain_eval F 0 0 t x hF]

def countGuesses (n : ℕ) (β : ℚ) : List ℕ :=
  if β=0 then [0] else List.range (n+1)

theorem count_guesses_length (β : ℚ) : (countGuesses n β).length≤n+1 := by
  unfold countGuesses
  split <;> simp

theorem exists_count_guess (F : Formula n) (β : ℚ) (x : Assignment n)
    (hF : wellFormed F) : ∃ h∈countGuesses n β,
      ∀ t, |scoreGain F t x-(countGain F β h t).eval x|≤|β| := by
  by_cases hb : β=0
  · subst β
    exact ⟨0,by simp [countGuesses],fun t => zero_count_error F x t hF⟩
  · have hn := ones_le x
    exact ⟨ones x,by simp [countGuesses,hb,List.mem_range]; omega,
      fun t => correct_count_error F β x t hF⟩

def projectionGain (F : Formula n) (lam : Fin r → ℚ) (v : Fin r → Fin n → ℚ)
    (guess : Fin r → ℚ) (t : Fin n) : Affine n :=
  (gainExpr F t).add (Affine.sum Finset.univ (fun k =>
    ((without (v k) t).scale (-1)).shift (guess k) |>.scale (lam k*v k t)))

def allowance (lam : Fin r → ℚ) (v : Fin r → Fin n → ℚ)
    (δ : Fin r → ℚ) (t : Fin n) : ℚ :=
  ∑ k, |lam k| * |v k t| * (δ k+|v k t|)

theorem projection_gain_error_identity (F : Formula n) (lam : Fin r → ℚ)
    (v : Fin r → Fin n → ℚ) (guess : Fin r → ℚ) (x : Assignment n)
    (t : Fin n) (hF : wellFormed F) :
    scoreGain F t x-(projectionGain F lam v guess t).eval x =
      ∑ k, lam k*v k t*(projection (v k) x-guess k-v k t*bit (x t)) := by
  simp only [projectionGain,Affine.eval_add,Affine.eval_sum,Affine.eval_scale,
    Affine.eval_shift,gainExpr_eval F t x hF,without_eval]
  rw [show scoreGain F t x-(scoreGain F t x+∑ k,
      lam k*v k t*(-1*(projection (v k) x-v k t*bit (x t))+guess k)) =
      -(∑ k, lam k*v k t*(-1*(projection (v k) x-v k t*bit (x t))+guess k)) by ring,
    ←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem projection_gain_error_bound (F : Formula n) (lam : Fin r → ℚ)
    (v : Fin r → Fin n → ℚ) (guess δ : Fin r → ℚ) (x : Assignment n)
    (t : Fin n) (hF : wellFormed F)
    (hguess : ∀ k, |projection (v k) x-guess k|≤δ k) :
    |scoreGain F t x-(projectionGain F lam v guess t).eval x|≤allowance lam v δ t := by
  rw [projection_gain_error_identity F lam v guess x t hF]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc
    |projection (v k) x-guess k-v k t*bit (x t)| ≤
        |projection (v k) x-guess k|+|v k t*bit (x t)| := abs_sub _ _
    _ ≤ δ k+|v k t| := by
      apply add_le_add (hguess k)
      rw [abs_mul,abs_of_nonneg (bit_nonneg _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (bit_le_one _)

end Max2SAT.Counts
