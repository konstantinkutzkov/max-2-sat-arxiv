import Max2SAT.Random.PairModel
import Max2SAT.Random.Support

/-! Connect the finite pair-multiset model to the actual Formula type used
by the verified algorithm. An edge is represented once, in increasing
variable-label order. Fixed units never affect the observed pair support. -/
namespace Max2SAT.RandomInput
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Edge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

def edgeClauses (e : Edge n) (K : Pattern m) : Formula n :=
  (Finset.univ : Finset Signs).toList.flatMap (fun s =>
    List.replicate (K s).val (.pair ⟨e.val.1,s.1⟩ ⟨e.val.2,s.2⟩))

theorem mem_edgeClauses (e : Edge n) (K : Pattern m) (c : Clause n) :
    c ∈ edgeClauses e K ↔ ∃ s, 0 < (K s).val ∧
      c = .pair ⟨e.val.1,s.1⟩ ⟨e.val.2,s.2⟩ := by
  simp [edgeClauses, Nat.pos_iff_ne_zero]

theorem edgeClauses_wellFormed (e : Edge n) (K : Pattern m) : wellFormed (edgeClauses e K) := by
  intro c hc
  obtain ⟨s,_,rfl⟩ := (mem_edgeClauses e K c).mp hc
  exact ne_of_lt e.property

theorem present_iff_count (K : Pattern m) : present K ↔ ∃ s, 0 < (K s).val := by
  simp only [present,size]
  exact Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _) |>.trans (by simp)

def generate (E : Finset (Edge n)) (K : E → Pattern m) (units : List (Literal n)) : Formula n :=
  units.map Clause.unit ++ E.attach.toList.flatMap (fun e => edgeClauses e.val (K e))

theorem generate_wellFormed (E : Finset (Edge n)) (K : E → Pattern m)
    (units : List (Literal n)) : wellFormed (generate E K units) := by
  intro c hc
  simp only [generate, List.mem_append, List.mem_map, List.mem_flatMap] at hc
  rcases hc with ⟨a,_,rfl⟩ | ⟨e,_,he⟩
  · trivial
  · exact edgeClauses_wellFormed e.val (K e) c he

/-- The canonical ordered edge set extracted from a generated formula.
The formula generator always places the smaller endpoint first. -/
def pairSupport (F : Formula n) : Finset (Fin n × Fin n) :=
  (F.flatMap (fun c => match c with
    | .unit _ => []
    | .pair a b => [(a.var,b.var)])).toFinset

theorem neighbors_iff_pairSupport (F : Formula n) (u v : Fin n) :
    v ∈ Random.neighbors F u ↔ (u,v) ∈ pairSupport F ∨ (v,u) ∈ pairSupport F := by
  simp only [Random.neighbors,pairSupport,List.mem_toFinset,List.mem_flatMap]
  constructor
  · rintro ⟨c,hc,hv⟩
    cases c with
    | unit a => simp at hv
    | pair a b =>
      by_cases ha : a.var=u
      · have hb : v=b.var := by simpa [ha] using hv
        exact Or.inl ⟨.pair a b,hc,by simp [ha,hb]⟩
      · have hb : b.var=u := by
          by_contra hb
          simp [ha,hb] at hv
        have hv' : v=a.var := by simpa [ha,hb] using hv
        exact Or.inr ⟨.pair a b,hc,by simp [hb,hv']⟩
  · rintro (⟨c,hc,h⟩ | ⟨c,hc,h⟩)
    · cases c with
      | unit a => simp at h
      | pair a b =>
        have he : u=a.var ∧ v=b.var := by simpa using h
        exact ⟨.pair a b,hc,by simp [he.1,he.2]⟩
    · cases c with
      | unit a => simp at h
      | pair a b =>
        have he : v=a.var ∧ u=b.var := by simpa using h
        exact ⟨.pair a b,hc,by by_cases hh : a.var=b.var <;> simp [he.1,he.2,hh]⟩

theorem generated_support (E : Finset (Edge n)) (K : E → Pattern m)
    (units : List (Literal n)) (uv : Fin n × Fin n) :
    uv ∈ pairSupport (generate E K units) ↔
      ∃ e : E, e.val.val = uv ∧ present (K e) := by
  simp only [pairSupport, List.mem_toFinset, List.mem_flatMap]
  constructor
  · rintro ⟨c,hc,huv⟩
    simp only [generate, List.mem_append, List.mem_map, List.mem_flatMap] at hc
    rcases hc with ⟨a,_,rfl⟩ | ⟨e,_,he⟩
    · simp at huv
    · obtain ⟨s,hs,rfl⟩ := (mem_edgeClauses e.val (K e) c).mp he
      have huv' : uv = e.val.val := by simpa using huv
      exact ⟨e,huv'.symm,(present_iff_count _).mpr ⟨s,hs⟩⟩
  · rintro ⟨e,he,hK⟩
    obtain ⟨s,hs⟩ := (present_iff_count _).mp hK
    refine ⟨.pair ⟨e.val.val.1,s.1⟩ ⟨e.val.val.2,s.2⟩,?_,?_⟩
    · apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨e,by simp,(mem_edgeClauses _ _ _).mpr ⟨s,hs,rfl⟩⟩
    · simp [he]

theorem generated_edge_present (E : Finset (Edge n)) (K : E → Pattern m)
    (units : List (Literal n)) (e : E) :
    e.val.val ∈ pairSupport (generate E K units) ↔ present (K e) := by
  rw [generated_support]
  constructor
  · rintro ⟨f,hf,hK⟩
    have hfe : f=e := Subtype.ext (Subtype.ext hf)
    simpa [hfe] using hK
  · intro hK
    exact ⟨e,rfl,hK⟩

theorem generated_edge_neighbors (E : Finset (Edge n)) (K : E → Pattern m)
    (units : List (Literal n)) (e : E) :
    e.val.val.2 ∈ Random.neighbors (generate E K units) e.val.val.1 ↔ present (K e) := by
  rw [neighbors_iff_pairSupport, generated_edge_present]
  have hr : (e.val.val.2,e.val.val.1) ∉ pairSupport (generate E K units) := by
    rw [generated_support]
    rintro ⟨f,hf,_⟩
    have hh : e.val.val.2 < e.val.val.1 := by
      simpa only [hf] using f.val.property
    exact (not_lt_of_ge e.val.property.le) hh
  simp [hr]

/-- Equality with the observed graph is exactly the coordinate event used
in the conditioning theorem, with no hidden sampling information supplied
to the algorithm. -/
theorem generated_observed_event (E : Finset (Edge n)) (K : E → Pattern m)
    (units : List (Literal n)) (H : E → Prop) :
    (∀ e : E, (e.val.val ∈ pairSupport (generate E K units) ↔ H e)) ↔
      observedEvent H K := by
  simp only [generated_edge_present, observedEvent]
  constructor
  · intro h e
    by_cases he : H e <;> simp [he, h e]
  · intro h e
    have hh := h e
    by_cases he : H e <;> simpa [he] using hh

end
end Max2SAT.RandomInput
