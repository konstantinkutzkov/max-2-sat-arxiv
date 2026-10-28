import Max2SAT.Random.Encoding
import Max2SAT.Random.EndpointSigns
import Max2SAT.Random.FullTree
import Max2SAT.Bias.PreprocessStats

/-! The probabilistic gains are the score comparisons and residual gaps
used by RandomFormula. Preprocessing changes neither comparison. -/
namespace Max2SAT.RandomInput
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000

def gain (F : Formula n) (i : Fin n) (x : Assignment n) : ℝ :=
  (score F (Function.update x i true) - score F (Function.update x i false) : ℤ)

def delta (F : Formula n) (free : Finset (Fin n)) (x : Assignment n) (i : Fin n) : ℝ :=
  (Bias.gap (Residual.restrict free x F).1 i : ℝ) / 2

def unitBias (units : List (Literal n)) (i : Fin n) : ℝ :=
  (units.map (fun a => if a.var=i then sign a.positive else 0)).sum

@[simp] theorem gain_append (F G : Formula n) (i : Fin n) (x : Assignment n) :
    gain (F++G) i x = gain F i x + gain G i x := by
  simp [gain]; ring

@[simp] theorem gap_append (F G : Formula n) (i : Fin n) :
    Bias.gap (F++G) i = Bias.gap F i + Bias.gap G i := by
  simp [Bias.gap,d1,d2]; ring

@[simp] theorem delta_append (F G : Formula n) (free : Finset (Fin n))
    (x : Assignment n) (i : Fin n) :
    delta (F++G) free x i = delta F free x i + delta G free x i := by
  simp [delta,Residual.restrict,Int.cast_add]; ring

theorem gain_unit (a : Literal n) (i : Fin n) (x : Assignment n) :
    gain [.unit a] i x = if a.var=i then sign a.positive else 0 := by
  by_cases hi : a.var=i
  · cases hp : a.positive <;> simp [gain,Clause.score,Literal.value,Literal.eval,hi,hp,sign]
  · simp [gain,Clause.score,Literal.value,Literal.eval,hi]

theorem delta_unit (a : Literal n) (free : Finset (Fin n)) (x : Assignment n)
    (i : Fin n) (hi : i ∈ free) :
    delta [.unit a] free x i = if a.var=i then sign a.positive else 0 := by
  by_cases ha : a.var=i
  · cases a with | mk j p =>
      simp only at ha
      subst j
      cases p <;> norm_num [delta,Residual.restrict,Residual.clause,hi,
        Bias.gap,d1,d2,Clause.unitCount,Clause.binaryCount,Bias.pos,Literal.neg,sign]
  · rcases a with ⟨j,p⟩
    by_cases hf : j ∈ free <;>
      simp [delta,Residual.restrict,Residual.clause,hf,Bias.gap,d1,d2,
        Clause.unitCount,Clause.binaryCount,Bias.pos,Literal.neg,Literal.mk.injEq,ha]

def edgeDelta (left : Bool) (K : Pattern m) (partnerFree : Bool) (x : Bool) : ℝ :=
  if partnerFree then signedCount left K / 2 else pairGain left K x

private theorem single_gain (e : Edge n) (s : Signs) (i : Fin n) (x : Assignment n) :
    gain [.pair ⟨e.val.1,s.1⟩ ⟨e.val.2,s.2⟩] i x =
      if i=e.val.1 then (if s.2 ≠ x e.val.2 then sign s.1 else 0)
      else if i=e.val.2 then (if s.1 ≠ x e.val.1 then sign s.2 else 0) else 0 := by
  have hne := ne_of_lt e.property
  by_cases hl : i=e.val.1
  · subst i
    rcases s with ⟨a,b⟩
    cases a <;> cases b <;> cases h : x e.val.2 <;>
      simp [gain,Clause.score,Literal.eval,sign,Ne.symm hne,h]
  · by_cases hr : i=e.val.2
    · subst i
      rcases s with ⟨a,b⟩
      cases a <;> cases b <;> cases h : x e.val.1 <;>
        simp [gain,Clause.score,Literal.eval,sign,hne,hl,h]
    · simp [gain,Clause.score,Literal.eval,hl,hr,Ne.symm hl,Ne.symm hr]

private theorem single_delta (e : Edge n) (s : Signs) (free : Finset (Fin n))
    (x : Assignment n) (i : Fin n) (hi : i ∈ free) :
    delta [.pair ⟨e.val.1,s.1⟩ ⟨e.val.2,s.2⟩] free x i =
      if i=e.val.1 then
        (if e.val.2 ∈ free then sign s.1/2 else if s.2 ≠ x e.val.2 then sign s.1 else 0)
      else if i=e.val.2 then
        (if e.val.1 ∈ free then sign s.2/2 else if s.1 ≠ x e.val.1 then sign s.2 else 0)
      else 0 := by
  have hne := ne_of_lt e.property
  by_cases hl : i=e.val.1
  · subst i
    rcases s with ⟨a,b⟩
    by_cases hf : e.val.2 ∈ free <;> cases a <;> cases b <;> cases h : x e.val.2 <;>
      norm_num [delta,Residual.restrict,Residual.clause,hi,hf,Literal.eval,h,
        Bias.gap,d1,d2,Clause.binaryCount,Clause.unitCount,Bias.pos,Literal.neg,
        Literal.mk.injEq,hne,Ne.symm hne,sign]
  · by_cases hr : i=e.val.2
    · subst i
      rcases s with ⟨a,b⟩
      by_cases hf : e.val.1 ∈ free <;> cases a <;> cases b <;> cases h : x e.val.1 <;>
        norm_num [delta,Residual.restrict,Residual.clause,hi,hf,Literal.eval,h,
          Bias.gap,d1,d2,Clause.binaryCount,Clause.unitCount,Bias.pos,Literal.neg,
          Literal.mk.injEq,hne,Ne.symm hne,sign]
    · by_cases h1 : e.val.1 ∈ free <;> by_cases h2 : e.val.2 ∈ free <;>
        cases a : (Literal.mk e.val.1 s.1).eval x <;>
        cases b : (Literal.mk e.val.2 s.2).eval x <;>
        simp [delta,Residual.restrict,Residual.clause,h1,h2,a,b,
          Bias.gap,d1,d2,Clause.binaryCount,Clause.unitCount,Bias.pos,Literal.neg,
          Literal.mk.injEq,hl,hr,Ne.symm hl,Ne.symm hr]

theorem gain_edge (e : Edge n) (K : Pattern m) (i : Fin n) (x : Assignment n) :
    gain (edgeClauses e K) i x =
      if i=e.val.1 then pairGain true K (x e.val.2)
      else if i=e.val.2 then pairGain false K (x e.val.1) else 0 := by
  have hsum : ∀ L : List Signs,
      gain (L.flatMap (fun s => List.replicate (K s).val
        (.pair ⟨e.val.1,s.1⟩ ⟨e.val.2,s.2⟩))) i x =
      (L.map (fun s => (K s).val * gain [.pair ⟨e.val.1,s.1⟩ ⟨e.val.2,s.2⟩] i x)).sum := by
    intro L
    induction L with
    | nil => simp [gain]
    | cons s L ih =>
      simp only [List.flatMap_cons,gain_append,List.map_cons,List.sum_cons,ih]
      congr 1
      simp [gain,score]; ring
  rw [edgeClauses,hsum]
  simp only [single_gain]
  by_cases hl : i=e.val.1 <;> by_cases hr : i=e.val.2 <;>
    simp [hl,hr,pairGain,endpoint,mul_ite]

theorem delta_edge (e : Edge n) (K : Pattern m) (free : Finset (Fin n))
    (x : Assignment n) (i : Fin n) (hi : i ∈ free) :
    delta (edgeClauses e K) free x i =
      if i=e.val.1 then edgeDelta true K (decide (e.val.2 ∈ free)) (x e.val.2)
      else if i=e.val.2 then edgeDelta false K (decide (e.val.1 ∈ free)) (x e.val.1)
      else 0 := by
  have hrep : ∀ c : Clause n, ∀ k : ℕ,
      delta (List.replicate k c) free x i = k * delta [c] free x i := by
    intro c k
    induction k with
    | zero => simp [delta,Residual.restrict,Bias.gap,d1,d2]
    | succ k ih =>
      change delta ([c] ++ List.replicate k c) free x i = _
      rw [delta_append,ih]
      push_cast
      ring
  have hsum : ∀ L : List Signs,
      delta (L.flatMap (fun s => List.replicate (K s).val
        (.pair ⟨e.val.1,s.1⟩ ⟨e.val.2,s.2⟩))) free x i =
      (L.map (fun s => (K s).val * delta [.pair ⟨e.val.1,s.1⟩ ⟨e.val.2,s.2⟩] free x i)).sum := by
    intro L
    induction L with
    | nil => simp [delta,Residual.restrict,Bias.gap,d1,d2]
    | cons s L ih => simp only [List.flatMap_cons,delta_append,List.map_cons,List.sum_cons,ih,hrep]
  rw [edgeClauses,hsum]
  simp only [single_delta e _ free x i hi]
  by_cases hl : i=e.val.1 <;> by_cases hr : i=e.val.2 <;>
    by_cases h1 : e.val.1 ∈ free <;> by_cases h2 : e.val.2 ∈ free <;>
    simp [hl,hr,h1,h2,edgeDelta,pairGain,signedCount,endpoint,mul_ite,
      mul_div_assoc,Finset.sum_div]

theorem generated_gain (E : Finset (Edge n)) (K : E → Pattern m)
    (units : List (Literal n)) (i : Fin n) (x : Assignment n) :
    gain (generate E K units) i x = unitBias units i +
      ∑ e : E, if i=e.val.val.1 then pairGain true (K e) (x e.val.val.2)
        else if i=e.val.val.2 then pairGain false (K e) (x e.val.val.1) else 0 := by
  have hu : gain (units.map Clause.unit) i x = unitBias units i := by
    induction units with
    | nil => simp [gain,unitBias]
    | cons a as ih =>
      change gain ([.unit a] ++ as.map Clause.unit) i x = _
      rw [gain_append,gain_unit,ih]
      simp [unitBias]
  have he : ∀ L : List E,
      gain (L.flatMap (fun e => edgeClauses e.val (K e))) i x =
        (L.map (fun e => gain (edgeClauses e.val (K e)) i x)).sum := by
    intro L
    induction L with
    | nil => simp [gain]
    | cons e L ih => simp [ih]
  rw [generate,gain_append,hu,he]
  simp only [gain_edge,Finset.attach_eq_univ]
  simp [-Finset.univ_eq_attach]

theorem generated_delta (E : Finset (Edge n)) (K : E → Pattern m)
    (units : List (Literal n)) (free : Finset (Fin n)) (i : Fin n)
    (x : Assignment n) (hi : i ∈ free) :
    delta (generate E K units) free x i = unitBias units i +
      ∑ e : E, if i=e.val.val.1 then edgeDelta true (K e) (decide (e.val.val.2 ∈ free)) (x e.val.val.2)
        else if i=e.val.val.2 then edgeDelta false (K e) (decide (e.val.val.1 ∈ free)) (x e.val.val.1)
        else 0 := by
  have hu : delta (units.map Clause.unit) free x i = unitBias units i := by
    induction units with
    | nil => simp [delta,Residual.restrict,Bias.gap,d1,d2,unitBias]
    | cons a as ih =>
      simp only [List.map_cons]
      rw [show .unit a :: as.map Clause.unit = [.unit a] ++ as.map Clause.unit from rfl,
        delta_append,delta_unit _ _ _ _ hi,ih]
      simp [unitBias]
  have he : ∀ L : List E,
      delta (L.flatMap (fun e => edgeClauses e.val (K e))) free x i =
        (L.map (fun e => delta (edgeClauses e.val (K e)) free x i)).sum := by
    intro L
    induction L with
    | nil => simp [delta,Residual.restrict,Bias.gap,d1,d2]
    | cons e L ih => simp [ih]
  rw [generate,delta_append,hu,he]
  simp only [delta_edge _ _ _ _ _ hi,Finset.attach_eq_univ]
  simp [-Finset.univ_eq_attach]

theorem gain_preprocess (F : Formula n) (i : Fin n) (x : Assignment n) :
    gain (preprocess F).1 i x = gain F i x := by
  have h1 := preprocess_correct F (Function.update x i true)
  have h0 := preprocess_correct F (Function.update x i false)
  unfold gain
  rw [h1,h0]
  congr 1
  ring

theorem delta_equivalent (F G : Formula n) (s : ℤ) (h : EquivalentWithOffset F G s)
    (hF : wellFormed F) (hG : wellFormed G) (free : Finset (Fin n))
    (x : Assignment n) (i : Fin n) : delta F free x i = delta G free x i := by
  let rF := Residual.restrict free x F
  let rG := Residual.restrict free x G
  have hr : EquivalentWithOffset rF.1 rG.1 (s+rG.2-rF.2) := by
    intro y
    let z : Assignment n := fun j => if j ∈ free then y j else x j
    have hc : Compatible free x z := by intro j hj; simp [z,hj]
    have hFy := Residual.restrict_score F free x z hc
    have hGy := Residual.restrict_score G free x z hc
    have hzy : ∀ H : Formula n, score (Residual.restrict free x H).1 z =
        score (Residual.restrict free x H).1 y := by
      intro H
      induction H with
      | nil => simp [Residual.restrict]
      | cons c H ih =>
        simp only [Residual.restrict,List.flatMap_cons,score_append] at *
        rw [ih]
        congr 1
        cases c <;> simp only [Residual.clause]
        all_goals split_ifs <;> simp_all [Clause.score,Literal.eval,Literal.value,z]
    rw [hzy F] at hFy
    rw [hzy G] at hGy
    have hh := h z
    change score F z = rF.2 + score rF.1 y at hFy
    change score G z = rG.2 + score rG.1 y at hGy
    omega
  unfold delta
  rw [Bias.equivalent_gap rF.1 rG.1 _
    (Residual.restrict_wellFormed F free x hF)
    (Residual.restrict_wellFormed G free x hG) hr]

theorem delta_preprocess (F : Formula n) (hF : wellFormed F)
    (free : Finset (Fin n)) (x : Assignment n) (i : Fin n) :
    delta (preprocess F).1 free x i = delta F free x i :=
  (delta_equivalent F _ _ (preprocess_correct F) hF
    (preprocess_finished F hF).1 free x i).symm

theorem branch_preference (F : Formula n) (free : List (Fin n))
    (x : Assignment n) (i : Fin n) :
    (Random.branchLiteral F free x i).positive = decide (0 ≤ delta F free.toFinset x i) := by
  simp only [Random.branchLiteral,Bias.initialPreference,delta]
  congr 1
  norm_cast
  simp

end
end Max2SAT.RandomInput
