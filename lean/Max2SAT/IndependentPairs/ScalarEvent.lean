import Max2SAT.IndependentPairs.EnergyTails
import Max2SAT.Counts.RoundPassing

/-! Simultaneous scalar estimates, using a union bound on the original
pair inputs. Overlap between rows and the sampled common shift is allowed.
The separate random-matrix operator estimate is not a hypothesis here and
is not a conclusion of these scalar estimates. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open FiniteLaw RandomInput
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {α : Type*} [Fintype α]

def scalarGood (z : Edge n → ℝ) (ν χ a : ℝ) (S : Finset (Fin n)) : Prop :=
  |empiricalMean z|≤a ∧
  ((98/100:ℝ)*((n:ℝ)-1)*ν≤pairEnergy (fun e => z e-empiricalMean z) ∧
    pairEnergy (fun e => z e-empiricalMean z)≤(101/100:ℝ)*((n:ℝ)-1)*χ*ν) ∧
  ∀ t∈S, (993/1000:ℝ)*Real.sqrt (t.val*ν)≤
    Real.sqrt (earlierEnergy (fun e => z e-empiricalMean z) t)

theorem scalar_good_of_raw (z : Edge n → ℝ) (hn : 2≤n)
    (ν χ a : ℝ) (S : Finset (Fin n)) (hν : 0≤ν)
    (ha : a≤(1/1000:ℝ)*Real.sqrt ν)
    (hmean : |empiricalMean z|≤a)
    (hraw : (99/100:ℝ)*((n:ℝ)-1)*ν≤pairEnergy z ∧
      pairEnergy z≤(101/100:ℝ)*((n:ℝ)-1)*χ*ν)
    (hrows : ∀ t∈S, (99/100:ℝ)*t.val*ν≤earlierEnergy z t) :
    scalarGood z ν χ a S := by
  have hδ := hmean.trans ha
  exact ⟨hmean,empirical_energy_bounds z hn ν χ hν hraw hδ,
    fun t ht => earlier_shift_lower z t _ ν hν (hrows t ht) hδ⟩

def scalarFailureBound (n : ℕ) (B ν χ a : ℝ) (S : Finset (Fin n)) : ℝ :=
  2*Real.exp (-(Fintype.card (Edge n):ℝ)*a^2/(4*(χ*ν)))+
    (Real.exp (-(1/100:ℝ)^2*(Fintype.card (Edge n):ℝ)*ν/(4*B^2*χ))+
     Real.exp (-(1/100:ℝ)^2*(Fintype.card (Edge n):ℝ)*χ*ν/(4*B^2)))+
    ∑ t∈S, Real.exp (-(1/100:ℝ)^2*t.val*ν/(4*B^2*χ))

/-- Fully proved simultaneous scalar event. All probability bounds are
derived from independence, bounded entries and their second moments. -/
theorem scalar_event_probability (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (hn : 2≤n) (B ν χ a : ℝ) (S : Finset (Fin n))
    (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ) (ha : 0<a)
    (haSmall : a*B≤2*(χ*ν)) (haShift : a≤(1/1000:ℝ)*Real.sqrt ν)
    (hS : ∀ t∈S, 0<t.val)
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧
      expect (p e) (fun x => (X e x)^2)≤χ*ν) :
    prob (product p) (fun x => ¬scalarGood (fun e => X e (x e)) ν χ a S)≤
      scalarFailureBound n B ν χ a S := by
  have : Nonempty (Edge n) := Fintype.card_pos_iff.mp (pair_count_positive hn)
  let z := fun (x : Edge n → α) e => X e (x e)
  let meanBad := fun x => a≤|empiricalMean (z x)|
  let energyBad := fun x => pairEnergy (z x)<(99/100:ℝ)*((n:ℝ)-1)*ν ∨
    (101/100:ℝ)*((n:ℝ)-1)*χ*ν<pairEnergy (z x)
  let rowBad := fun t x => earlierEnergy (z x) t≤(99/100:ℝ)*t.val*ν
  have hmean := empirical_mean_tail p X B (χ*ν) a (by positivity) ha hm hb
    (fun e => (hv e).2) haSmall
  have henergy := raw_energy_tails p X hn B ν χ (1/100) hB hν hχ
    (by norm_num) (by norm_num) hb hv
  have hrow : ∀ t∈S, prob (product p) (rowBad t)≤
      Real.exp (-(1/100:ℝ)^2*t.val*ν/(4*B^2*χ)) := by
    intro t ht
    simpa only [rowBad,z,show (1:ℝ)-1/100=99/100 by norm_num] using
      earlier_energy_tail p X t (hS t ht) B ν χ (1/100) hB hν hχ
        (by norm_num) (by norm_num) hb hv
  have hrows := (Counts.finite_union_bound (product p) S rowBad).trans
    (Finset.sum_le_sum hrow)
  have hsub := prob_mono_support (product p)
    (fun x => ¬scalarGood (z x) ν χ a S)
    (fun x => (meanBad x ∨ energyBad x) ∨ ∃ t∈S, rowBad t x) (by
      intro x _ hbad
      by_contra h
      have hmean' : |empiricalMean (z x)|≤a := by
        by_contra hm'; exact h (Or.inl (Or.inl (le_of_lt (lt_of_not_ge hm'))))
      have hlo : (99/100:ℝ)*((n:ℝ)-1)*ν≤pairEnergy (z x) := by
        by_contra hh; exact h (Or.inl (Or.inr (Or.inl (lt_of_not_ge hh))))
      have hhi : pairEnergy (z x)≤(101/100:ℝ)*((n:ℝ)-1)*χ*ν := by
        by_contra hh; exact h (Or.inl (Or.inr (Or.inr (lt_of_not_ge hh))))
      have hr : ∀ t∈S, (99/100:ℝ)*t.val*ν≤earlierEnergy (z x) t := by
        intro t ht
        by_contra hh; exact h (Or.inr ⟨t,ht,le_of_lt (lt_of_not_ge hh)⟩)
      exact hbad (scalar_good_of_raw (z x) hn ν χ a S hν.le haShift hmean' ⟨hlo,hhi⟩ hr))
  have he : prob (product p) energyBad≤
      Real.exp (-(1/100:ℝ)^2*(Fintype.card (Edge n):ℝ)*ν/(4*B^2*χ))+
      Real.exp (-(1/100:ℝ)^2*(Fintype.card (Edge n):ℝ)*χ*ν/(4*B^2)) := by
    simpa only [energyBad,z,show (1:ℝ)-1/100=99/100 by norm_num,
      show (1:ℝ)+1/100=101/100 by norm_num] using henergy
  exact hsub.trans ((prob_union_le (product p) _ _).trans
    (add_le_add ((prob_union_le (product p) _ _).trans (add_le_add hmean he)) hrows))

end
end Max2SAT.IndependentPairs
