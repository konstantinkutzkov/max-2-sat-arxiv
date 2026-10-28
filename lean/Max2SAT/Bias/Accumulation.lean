import Max2SAT.Bias.Influence

/-! A prefix selects comparisons using only its assigned bits. The resulting
sum is a single ordinary occurrence-count constraint on the remaining bits. -/
namespace Max2SAT.Bias
open FairCoin
/-- Increasing variable labels, computed without a choice operation. -/
def ordered (P : Finset (Fin n)) : List (Fin n) := P.sort (·≤·)
@[simp] theorem mem_ordered (P : Finset (Fin n)) (i : Fin n) : i∈ordered P ↔ i∈P := by simp [ordered]
@[simp] theorem length_ordered (P : Finset (Fin n)) : (ordered P).length=P.card := by simp [ordered]
@[simp] theorem ordered_toFinset (P : Finset (Fin n)) : (ordered P).toFinset=P := by simp [ordered]
theorem ordered_nodup (P : Finset (Fin n)) : (ordered P).Nodup := by simp [ordered]
noncomputable section

/-- Keep the constraint exactly when the chosen value is nonpreferred. -/
def cuts (F : Formula n) (p : Fin n → Bool) (order : List (Fin n))
    (x : Assignment n) : List (Constraint n) :=
  order.filterMap (fun i => if x i=p i then none else some (pruningConstraint F (preferred p i)))

theorem cuts_agree (F : Formula n) (p : Fin n → Bool) (order : List (Fin n))
    (x y : Assignment n) (h : ∀ i∈order, x i=y i) : cuts F p order x=cuts F p order y := by
  unfold cuts
  apply List.filterMap_congr
  intro i hi
  rw [h i hi]

theorem sum_surplus (cs : List (Constraint n)) (x : Assignment n) :
    ((Constraint.sum cs).lhs x-(Constraint.sum cs).bound : ℤ)=
      (cs.map (fun C => C.lhs x-C.bound)).sum := by
  induction cs with
  | nil => simp [Constraint.sum,Constraint.lhs]
  | cons c cs ih =>
    change (c.add (Constraint.sum cs)).lhs x-(c.bound+(Constraint.sum cs).bound) =
      (c.lhs x-c.bound)+(cs.map (fun C => C.lhs x-C.bound)).sum
    rw [Constraint.lhs_add]
    omega

/-- Each strict cut contributes one additional unit beyond the comparison gain. -/
theorem cuts_surplus (F : Formula n) (p : Fin n → Bool) (order : List (Fin n))
    (x : Assignment n) (hF : wellFormed F) :
    (((Constraint.sum (cuts F p order x)).lhs x-
        (Constraint.sum (cuts F p order x)).bound : ℤ) : ℝ)=
      (order.map (fun i => benefit F p i x)).sum+(cuts F p order x).length := by
  rw [sum_surplus]
  induction order with
  | nil => simp [cuts]
  | cons i order ih =>
    by_cases h : x i=p i
    · simpa [cuts,h,benefit_same F p i x h] using ih
    · have hb := benefit_other F p i x h hF
      simp only [cuts,List.filterMap_cons,ite_eq_right h,List.map_cons,List.sum_cons,
        List.length_cons,Int.cast_add,Nat.cast_add,Nat.cast_one] at *
      push_cast at hb ih ⊢
      linarith

/-- A full assignment admitted by the summed prefix constraint. -/
def admissible (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (x : Assignment n) : Prop := (Constraint.sum (cuts F p (ordered P) x)).Holds x
instance (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n)) (x : Assignment n) :
    Decidable (admissible F p P x) := inferInstanceAs (Decidable (Constraint.Holds _ _))

theorem admissible_statistic (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (x : Assignment n) (hF : wellFormed F) (ha : admissible F p P x) :
    statistic F p P x≤0 := by
  have hh := cuts_surplus F p (ordered P) x hF
  have hs : (((Constraint.sum (cuts F p (ordered P) x)).lhs x-
      (Constraint.sum (cuts F p (ordered P) x)).bound : ℤ) : ℝ)≤0 := by
    exact_mod_cast (sub_nonpos.mpr ha)
  have hl : (0:ℝ)≤(cuts F p (ordered P) x).length := by positivity
  have he : ((ordered P).map (fun i => benefit F p i x)).sum=statistic F p P x := by
    have hp := ((Finset.sort_perm_toList P (·≤·)).map (fun i => benefit F p i x)).sum_eq
    simpa [statistic,ordered] using hp
  rw [he] at hh
  linarith

/-- The probability bound refers to the actual summed pruning constraints,
not to an independently postulated event. -/
theorem admissible_probability (F : Formula n) (P : Finset (Fin n))
    (hF : wellFormed F) (hV : 0<∑ i : Fin n, (2*(B F i : ℝ))^2) :
    probability n (admissible F (initialPreference F) P) ≤
      Real.exp (-((∑ i∈P, |(gap F i : ℝ)|)/4)^2 /
        (2*(∑ i : Fin n, (2*(B F i : ℝ))^2))) := by
  let f := statistic F (initialPreference F) P
  have hm := mean_statistic F P hF
  have hm0 : 0≤average n f := by rw [hm]; positivity
  have ht := lower_tail n f (fun i => 2*(B F i : ℝ)) (fun i => by positivity)
    (statistic_bounded F _ P hF) (average n f) hm0 hV
  rw [hm] at ht
  apply le_trans ?_ ht
  unfold probability
  apply average_mono
  intro x
  by_cases ha : admissible F (initialPreference F) P x
  · have hx := admissible_statistic F _ P x hF ha
    simp [ha,sub_self,f,hx]
  · simp [ha]; positivity

end
end Max2SAT.Bias
