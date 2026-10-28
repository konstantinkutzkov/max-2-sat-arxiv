import Max2SAT.Random.FormulaGains
import Max2SAT.Random.SignMoments

/-! Incidences and exposed coordinates on a fixed observed graph. Original
variable labels are retained; the construction also applies after skipping
isolated labels. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {E : Finset (Edge n)} {i : Fin n}

def incident (E : Finset (Edge n)) (i : Fin n) : Finset E :=
  Finset.univ.filter (fun e => i=e.val.val.1 ∨ i=e.val.val.2)

abbrev Incidence (E : Finset (Edge n)) (i : Fin n) := ↥(incident E i)

def side (i : Fin n) (e : Edge n) : Bool := decide (i=e.val.1)
def vertex (e : Edge n) (left : Bool) : Fin n := if left then e.val.1 else e.val.2
def partner (i : Fin n) (e : Edge n) : Fin n := vertex e (!(side i e))

theorem incident_cases (e : Incidence E i) :
    i=e.val.val.val.1 ∨ i=e.val.val.val.2 := (Finset.mem_filter.mp e.property).2

theorem incident_vertex (e : Incidence E i) :
    vertex e.val.val (side i e.val.val) = i := by
  rcases incident_cases e with h | h
  · simp [side,vertex,h]
  · have hn := ne_of_lt e.val.val.property
    simp [side,vertex,h,Ne.symm hn]

theorem partner_ne (e : Incidence E i) : partner i e.val.val ≠ i := by
  rcases incident_cases e with h | h
  · simp [partner,side,vertex,h,Ne.symm (ne_of_lt e.val.val.property)]
  · simp [partner,side,vertex,h,ne_of_lt e.val.val.property,Ne.symm (ne_of_lt e.val.val.property)]

theorem sum_incident (E : Finset (Edge n)) (i : Fin n) (f : E → ℝ) :
    (∑ e : Incidence E i, f e.val) =
      ∑ e : E, if i=e.val.val.1 ∨ i=e.val.val.2 then f e else 0 := by
  rw [← Finset.sum_subtype (incident E i) (fun _ => Iff.rfl) f]
  exact Finset.sum_filter _ _

theorem generated_delta_incident (E : Finset (Edge n)) (K : E → Pattern m)
    (units : List (Literal n)) (free : Finset (Fin n)) (x : Assignment n)
    (i : Fin n) (hi : i ∈ free) :
    delta (generate E K units) free x i = unitBias units i +
      ∑ e : Incidence E i, edgeDelta (side i e.val.val) (K e.val)
        (decide (partner i e.val.val ∈ free)) (x (partner i e.val.val)) := by
  rw [generated_delta E K units free i x hi,
    sum_incident E i (fun e => edgeDelta (side i e.val) (K e)
      (decide (partner i e.val ∈ free)) (x (partner i e.val)))]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases h1 : i=e.val.val.1 <;> by_cases h2 : i=e.val.val.2 <;>
    simp [h1,h2,side,partner,vertex,Ne.symm (ne_of_lt e.val.property)]

/-- Each bit is either an assignment coordinate or the sign at one
specified endpoint of an edge. Distinct endpoints have distinct indices. -/
abbrev ExposureBit (E : Finset (Edge n)) := Fin n ⊕ (E × Bool)

def rho (z : ExposureBit E → Bool) (e : E) : Signs :=
  (z (.inr (e,true)),z (.inr (e,false)))
def assignment (z : ExposureBit E → Bool) : Assignment n := fun i => z (.inl i)
def sampled (K : E → Pattern m) (z : ExposureBit E → Bool) : E → Pattern m :=
  fun e => signedFlip (rho z e) (K e)

def current (i : Fin n) (e : Incidence E i) : ExposureBit E :=
  .inr (e.val,side i e.val.val)

theorem current_injective (i : Fin n) : Function.Injective (current (E:=E) i) := by
  intro e f h
  have hh : e.val=f.val := (Prod.mk.inj (Sum.inr.inj h)).1
  exact Subtype.ext hh

/-- The history before processing i contains all assignment bits and all
endpoint signs belonging to variables outside free. -/
def knownBefore (E : Finset (Edge n)) (free : Finset (Fin n)) : Finset (ExposureBit E) :=
  Finset.univ.filter (fun b => match b with
    | .inl j => j ∉ free
    | .inr (e,left) => vertex e.val left ∉ free)

def knownAfterSigns (E : Finset (Edge n)) (free : Finset (Fin n)) (i : Fin n) :=
  knownBefore E free ∪ Finset.univ.image (current (E:=E) i)

theorem current_fresh (free : Finset (Fin n)) (i : Fin n) (hi : i ∈ free)
    (e : Incidence E i) : current i e ∉ knownBefore E free := by
  simp [knownBefore,current,incident_vertex,hi]

theorem assignment_fresh (free : Finset (Fin n)) (i : Fin n) (hi : i ∈ free) :
    (Sum.inl i : ExposureBit E) ∉ knownAfterSigns E free i := by
  simp [knownAfterSigns,knownBefore,current,hi]

def coefficient (K : E → Pattern m) (free : Finset (Fin n))
    (z : ExposureBit E → Bool) (i : Fin n) (e : Incidence E i) : ℝ :=
  if partner i e.val.val ∈ free then signedCount (side i e.val.val) (K e.val)/2
  else pairGain (side i e.val.val) (K e.val)
    (theta (z (.inr (e.val,!(side i e.val.val)))) (assignment z (partner i e.val.val)))

theorem coefficient_known (K : E → Pattern m) (free : Finset (Fin n))
    (z w : ExposureBit E → Bool) (i : Fin n)
    (h : history (knownBefore E free) z w) (e : Incidence E i) :
    coefficient K free w i e = coefficient K free z i e := by
  unfold coefficient
  by_cases hp : partner i e.val.val ∈ free
  · simp [hp]
  · have hs := h (.inr (e.val,!(side i e.val.val)))
    have hx := h (.inl (partner i e.val.val))
    simp only [knownBefore,Finset.mem_filter,Finset.mem_univ,true_and] at hs hx
    have hv : vertex e.val.val (!(side i e.val.val)) ∉ free := hp
    simp [hv,hp] at hs hx
    simp [hp,assignment,hs,hx]

theorem delta_exposure (E : Finset (Edge n)) (K : E → Pattern m)
    (units : List (Literal n)) (free : Finset (Fin n))
    (z : ExposureBit E → Bool) (i : Fin n) (hi : i ∈ free) :
    delta (generate E (sampled K z) units) free (assignment z) i = unitBias units i +
      ∑ e : Incidence E i, sign (z (current i e)) * coefficient K free z i e := by
  rw [generated_delta_incident E _ units free _ i hi]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases hp : partner i e.val.val ∈ free
  · simp only [edgeDelta,hp,decide_true,↓reduceIte,sampled,signedCount_flip,coefficient]
    have hr : endpoint (side i e.val.val) (rho z e.val) = z (current i e) := by
      unfold endpoint current rho
      cases side i e.val.val <;> rfl
    rw [hr]
    ring
  · simp only [edgeDelta,hp,decide_false,Bool.false_eq_true,↓reduceIte,sampled,pairGain_flip,coefficient]
    have hr : endpoint (side i e.val.val) (rho z e.val) = z (current i e) := by
      unfold endpoint current rho
      cases side i e.val.val <;> rfl
    have hp' : endpoint (!(side i e.val.val)) (rho z e.val) =
        z (.inr (e.val,!(side i e.val.val))) := by
      unfold endpoint rho
      cases side i e.val.val <;> rfl
    rw [hr,hp']

theorem coefficient_bound (K : E → Pattern m) (hK : ∀ e, size (K e) ≤ m)
    (free : Finset (Fin n)) (z : ExposureBit E → Bool) (i : Fin n) (e : Incidence E i) :
    |coefficient K free z i e| ≤ m := by
  have hk : (size (K e.val) : ℝ) ≤ m := by exact_mod_cast hK e.val
  unfold coefficient
  split
  · rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hs := signedCount_bound (side i e.val.val) (K e.val)
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  · exact le_trans (pairGain_bound _ _ _) hk

theorem variance_bound (K : E → Pattern m) (hK : ∀ e, size (K e) ≤ m)
    (free : Finset (Fin n)) (z : ExposureBit E → Bool) (i : Fin n) :
    (∑ e : Incidence E i, (coefficient K free z i e)^2) ≤
      (m:ℝ)^2 * (incident E i).card := by
  calc
    _ ≤ ∑ _e : Incidence E i, (m:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro e _
      have hh := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg m)).mpr
        (coefficient_bound K hK free z i e)
      simpa only [sq_abs] using hh
    _ = _ := by simp [mul_comm]

end
end Max2SAT.RandomInput
