import Max2SAT.Random.ExposureGraph

/-! The degree in the exposure bound is the algorithm's observed degree,
and the prescribed histories really advance one variable at a time. -/
namespace Max2SAT.RandomInput
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {E : Finset (Edge n)} {i : Fin n}

theorem partner_left (e : Edge n) (h : i=e.val.1) : partner i e=e.val.2 := by
  unfold partner side
  rw [decide_eq_true h]
  rfl

theorem partner_right (e : Edge n) (h : i=e.val.2) : partner i e=e.val.1 := by
  have hn : ¬ i=e.val.1 := by rw [h]; exact Ne.symm (ne_of_lt e.property)
  unfold partner side
  rw [decide_eq_false hn]
  rfl

def opposite (e : Incidence E i) : Incidence E (partner i e.val.val) :=
  ⟨e.val,by
    rcases incident_cases e with h | h
    · rw [partner_left _ h]
      simp [incident]
    · rw [partner_right _ h]
      simp [incident]⟩

theorem opposite_side (e : Incidence E i) :
    side (partner i e.val.val) e.val.val = !(side i e.val.val) := by
  by_cases h : i=e.val.val.val.1
  · rw [partner_left _ h]
    have hs : side i e.val.val=true := by simp [side,h]
    rw [hs]
    simp [side,Ne.symm (ne_of_lt e.val.val.property)]
  · have hr : i=e.val.val.val.2 := (incident_cases e).resolve_left h
    rw [partner_right _ hr]
    have hs : side i e.val.val=false := by simp [side,h]
    rw [hs]
    simp [side]

/-- The theta coordinate in the deviation identity is precisely the
current-row coordinate when the opposite endpoint is processed. -/
theorem opposite_current (e : Incidence E i) :
    current (partner i e.val.val) (opposite e) =
      (Sum.inr (e.val,!(side i e.val.val)) : ExposureBit E) := by
  change Sum.inr (e.val,side (partner i e.val.val) e.val.val) = _
  rw [opposite_side]

theorem current_image_iff (e : E) (left : Bool) (i : Fin n) :
    (Sum.inr (e,left) : ExposureBit E) ∈ Finset.univ.image (current (E:=E) i) ↔
      vertex e.val left = i := by
  constructor
  · rintro h
    obtain ⟨f,_,hf⟩ := Finset.mem_image.mp h
    have he : f.val=e := (Prod.mk.inj (Sum.inr.inj hf)).1
    have hl : side i f.val.val=left := (Prod.mk.inj (Sum.inr.inj hf)).2
    have hv := incident_vertex f
    rw [hl,he] at hv
    exact hv
  · intro h
    have hi : i=e.val.val.1 ∨ i=e.val.val.2 := by
      cases left <;> simp_all [vertex]
    let f : Incidence E i := ⟨e,by simp [incident,hi]⟩
    have hl : side i e.val=left := by
      cases left with
      | false =>
        have hn : ¬i=e.val.val.1 := by
          have hh : e.val.val.2=i := h
          have hh' := e.val.property
          omega
        simp [side,hn]
      | true => have hh : e.val.val.1=i := h; simp [side,hh]
    exact Finset.mem_image.mpr ⟨f,Finset.mem_univ f,by simp [current,f,hl]⟩

theorem history_step (free : Finset (Fin n)) (i : Fin n) :
    knownBefore E (free.erase i) = insert (Sum.inl i) (knownAfterSigns E free i) := by
  ext b
  cases b with
  | inl j =>
    simp [knownBefore,knownAfterSigns,current]
    tauto
  | inr a =>
    rcases a with ⟨e,left⟩
    simp only [knownBefore,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,
      knownAfterSigns,Finset.mem_insert,Finset.mem_union,Sum.inr_ne_inl,false_or,
      current_image_iff]
    tauto

theorem partner_injective (i : Fin n) :
    Function.Injective (fun e : Incidence E i => partner i e.val.val) := by
  intro e f h
  change partner i e.val.val = partner i f.val.val at h
  have he := e.val.val.property
  have hf := f.val.val.property
  rcases incident_cases e with he' | he' <;> rcases incident_cases f with hf' | hf'
  · rw [partner_left (i:=i) e.val.val he',partner_left (i:=i) f.val.val hf'] at h
    exact Subtype.ext (Subtype.ext (Subtype.ext (Prod.ext (he'.symm.trans hf') h)))
  · rw [partner_left (i:=i) e.val.val he',partner_right (i:=i) f.val.val hf'] at h
    omega
  · rw [partner_right (i:=i) e.val.val he',partner_left (i:=i) f.val.val hf'] at h
    omega
  · rw [partner_right (i:=i) e.val.val he',partner_right (i:=i) f.val.val hf'] at h
    exact Subtype.ext (Subtype.ext (Subtype.ext (Prod.ext h (he'.symm.trans hf'))))

theorem neighbors_eq_partners (E : Finset (Edge n)) (K : E → Pattern m)
    (hK : ∀ e, present (K e)) (units : List (Literal n)) (i : Fin n) :
    Random.neighbors (generate E K units) i =
      Finset.univ.image (fun e : Incidence E i => partner i e.val.val) := by
  ext v
  rw [neighbors_iff_pairSupport,generated_support,generated_support]
  constructor
  · rintro (⟨e,he,_⟩ | ⟨e,he,_⟩)
    · have hi : i=e.val.val.1 := (congrArg Prod.fst he).symm
      have hv : e.val.val.2=v := congrArg Prod.snd he
      let f : Incidence E i := ⟨e,by simp [incident,hi]⟩
      exact Finset.mem_image.mpr ⟨f,Finset.mem_univ f,by simp [partner,side,vertex,f,hi,hv]⟩
    · have hi : i=e.val.val.2 := (congrArg Prod.snd he).symm
      have hv : e.val.val.1=v := congrArg Prod.fst he
      let f : Incidence E i := ⟨e,by simp [incident,hi]⟩
      exact Finset.mem_image.mpr ⟨f,Finset.mem_univ f,(partner_right e.val hi).trans hv⟩
  · intro h
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp h
    rcases incident_cases e with he | he
    · left
      refine ⟨e.val,?_,hK e.val⟩
      simp [partner,side,vertex,he]
    · right
      refine ⟨e.val,?_,hK e.val⟩
      simp [partner,side,vertex,he,Ne.symm (ne_of_lt e.val.val.property)]

theorem observed_degree (E : Finset (Edge n)) (K : E → Pattern m)
    (hK : ∀ e, present (K e)) (units : List (Literal n)) (i : Fin n) :
    (Random.neighbors (generate E K units) i).card = (incident E i).card := by
  rw [neighbors_eq_partners E K hK units i,
    Finset.card_image_of_injective _ (partner_injective i)]
  simp

theorem variance_observed_degree (K : E → Pattern m) (hK : ∀ e, size (K e) ≤ m)
    (hp : ∀ e, present (K e)) (units : List (Literal n)) (free : Finset (Fin n))
    (z : ExposureBit E → Bool) (i : Fin n) :
    (∑ e : Incidence E i, (coefficient K free z i e)^2) ≤
      (m:ℝ)^2 * (Random.neighbors (generate E (sampled K z) units) i).card := by
  rw [observed_degree E (sampled K z) (fun e => by simpa [sampled,signedFlip] using hp e)]
  exact variance_bound K hK free z i

end
end Max2SAT.RandomInput
