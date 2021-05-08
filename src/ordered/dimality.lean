import .convex set_theory.cardinal order.well_founded set_theory.cardinal_ordinal

open_locale cardinal

section
universe u
parameters {α : Type u} [has_betweenness α]

@[reducible]
def generates (b : set α) (s : set α) (h : is_affine s) : Prop :=
affine_hull b = s

theorem generates.of_span {s : set α} (h : is_affine s) : generates s s h :=
h

@[reducible]
def generators (s : set α) (h : is_affine s) : set (set α) :=
{b | generates b s h}

namespace generators

theorem self_gens {s : set α} : ∀ h, s ∈ generators s h :=
generates.of_span

theorem is_nonempty {s : set α} (h : is_affine s) : (generators s h).nonempty :=
⟨s, self_gens h⟩

end generators

@[reducible]
def is_basis (s : set α) (h : is_affine s) (b : generators s h) : Prop :=
∀ b' ∈ generators s h, #b ≤ #b'

@[reducible]
def bases : Π {s} h, set (generators s h) :=
is_basis

end

protected def {u} bases.univ (α : Type u) [has_betweenness α] :
  set (generators set.univ is_affine.univ) :=
@bases α _ _ _

section
universe u

theorem cardinal.le_mk_le_iff_ex_sub_right {α : Type u} {s t : set α} (h : #s ≤ #t) :
  ∃ s' ⊆ t, #s' = #s :=
begin
  rw cardinal.le_mk_iff_exists_subset at h,
  rcases h with ⟨s', _, _⟩,
  exact ⟨s', ‹_›, ‹_›⟩
end

parameters {α : Type u} [has_betweenness α]

namespace bases

theorem is_nonempty {s : set α} (h : is_affine s) : (bases h).nonempty :=
begin
  have gne : (@set.univ $ generators s h).nonempty,
    { cases generators.is_nonempty h with w h, exact ⟨⟨w, h⟩, trivial⟩ },
  let f := λ l r : generators s h, #l < #r,
  rcases well_founded.has_min (inv_image.wf _ cardinal.wf) _ gne with ⟨b, _, hb⟩,
  refine ⟨b, λ b' hb', _⟩,
  specialize hb ⟨b', hb'⟩ trivial,
  change ¬ _ < _ at hb,
  simp at hb,
  assumption
end

instance {s : set α} (h : is_affine s) : nonempty (bases h) :=
⟨⟨(is_nonempty h).some, (is_nonempty h).some_mem⟩⟩

def basis_card {s : set α} (h : is_affine s) : cardinal :=
#(nonempty h).some

theorem all_bases_same_card {s : set α} {h : is_affine s} (b : bases h) : #b = basis_card h :=
begin
  rcases b with ⟨⟨g, hg⟩, hbg⟩,
  have : nonempty (bases h) := infer_instance,
  let b' := this.some,
  change #g = #b',
  exact le_antisymm (hbg b'.val b'.val.property) (b'.property g hg)
end

/-
theorem ex_union_basis_of_gen {s : set α} (hs : is_affine s) (g : generators _ hs) :
  ∃ (s' : set α) (b : bases hs), s' ∪ b = g :=
begin
  by_cases hg : is_basis _ _ g, { exact ⟨∅, ⟨g, hg⟩, by simp⟩ },
  rw is_basis at hg, push_neg at hg,
  rcases hg with ⟨b, hbg, ⟨hb : _ ≤ #g.val, hb' : ¬ (#g.val ≤ _)⟩⟩,
  by_contra h,
  push_neg at h,
  specialize h b,
end

--theorem ex_subgen {s : set α} {hs : is_affine s} {g : generators _ hs} (h : )

theorem ex_basis_sub_gen {s : set α} (hs : is_affine s) (g : generators _ hs) :
  ∃ b : bases hs, b.val.val ⊆ g.val :=
begin
  by_cases hg : is_basis _ _ g, { exact ⟨⟨g, hg⟩, set.subset.rfl⟩ },
  rw is_basis at hg, push_neg at hg,
  rcases hg with ⟨b, hbg, ⟨hb : _ ≤ #g.val, hb' : ¬ (#g.val ≤ _)⟩⟩,
  rw cardinal.le_mk_iff_exists_subset at hb hb',
  rcases hb with ⟨w, hw, hw'⟩,
  push_neg at hb',
  refine ⟨⟨⟨w, _⟩, _⟩, hw⟩,
end
-/

end bases
end
