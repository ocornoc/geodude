/-
  Copyright 2020 Grayson Burton
  License available in the LICENSE file.
-/
import data.set tactic .between .convex .dimality

open_locale cardinal

section
universe u

/-- For any set `S`, `S₁` and `S₂` form a dependent bipartition of `S` iff
    their union `S₁ ∪ S₂ = S` and there is no point in one that is between two
    points of the other. -/
def dep_bipartition {α : Type u} [has_betweenness α] (s s₁ s₂ : set α) : Prop :=
s₁ ∪ s₂ = s ∧ (∀ p ∈ s₁, ¬ ∃ q r ∈ s₂, between q p r) ∧
  (∀ p ∈ s₂, ¬ ∃ q r ∈ s₁, between q p r)

/-- Ordered geometry, without an axiom of dimension. -/
class ordered_geo_nodim (α : Type u) extends has_betweenness α :=
(pasch {v₁ v₂ v₃ v₄ v₅ : α} : @lin_indep α _ {v₁, v₂, v₃} → between v₂ v₃ v₄ →
  between v₃ v₅ v₂ → ∃ z ∈ line v₄ v₅, between v₁ z v₂)
(dedekind {p q : α} {s₁ s₂ : set α} : nonempty s₁ → nonempty s₂ →
  dep_bipartition (line p q) s₁ s₂ →
    (∃ v₁ ∈ s₁, ∀ (v₂ ∈ s₁ \ {v₁}) (v₃ ∈ s₂), between v₂ v₁ v₃)
    ∨ (∃ v₁ ∈ s₂, ∀ (v₂ ∈ s₂ \ {v₁}) (v₃ ∈ s₁), between v₂ v₁ v₃))

/-- Ordered geometry, indexed by a dimension `d` for which the appropriate
    axioms of dimensionality apply for any set of points up to some
    cardinality. -/
class ordered_geo (α : Type u) (d : cardinal) extends ordered_geo_nodim α :=
(card_lt_basis : ∃ b : @bases.univ α _, d < #b)

/-- Ordered geometry with a dimension `d`. -/
class ordered_geo_limited (α : Type u) (d : cardinal) extends ordered_geo α d :=
(card_eq_basis : ∃ b : @bases.univ α _, d.succ = #b)

section
parameter {α : Type u}

namespace ordered_geo
section
parameters {d : cardinal.{u}} [ordered_geo α d]

theorem ex_univ_basis : (bases.univ α).nonempty :=
let ⟨⟨w, _⟩, _⟩ := @card_lt_basis α d _ in ⟨w, ‹_›⟩

def sub_geo {d' : cardinal} (h : d' ≤ d) : ordered_geo α d' := {
  card_lt_basis := let ⟨w, hw⟩ := card_lt_basis in ⟨w, lt_of_le_of_lt h hw⟩,
  ..to_ordered_geo_nodim d
}

theorem cards_lt_basis {d' : cardinal} (h : d' ≤ d) : ∃ b : bases.univ α, d' < #b :=
(sub_geo h).card_lt_basis

end

instance (d : cardinal.{u}) [ordered_geo α d] : nonempty α :=
begin
  rw ←cardinal.ne_zero_iff_nonempty,
  intro hα,
  rcases @cards_lt_basis α _ _ _ (zero_le d) with ⟨w, h⟩,
  rw ←hα at h,
  exact not_le.mpr h (cardinal.mk_set_le w)
end

section
parameters {d : cardinal.{u}} [ordered_geo α d]

theorem ex_two_points (hd : 0 < d) : ∃ p q : α, p ≠ q :=
begin
  rw ←cardinal.one_le_iff_pos at hd,
  rcases @cards_lt_basis α _ _ _ hd with ⟨⟨⟨w, _⟩, _⟩, h⟩,
  suffices h : (#bool).lift ≤ #w,
  rcases h with ⟨f, hf⟩,
  refine ⟨f (ulift.up tt), f (ulift.up ff), λ h, _⟩,
  rw ←subtype.ext_iff at h, replace h := hf h, rw ulift.ext_iff at h,
  contradiction,
  change 1 < #w at h,
  refine le_trans (le_of_eq _) (cardinal.succ_le.mpr h),
  rw cardinal.mk_bool,
  have : ↑(2 : ℕ) = (2 : cardinal) := by simp,
  rw [(by simp : (2 : cardinal) = ↑(2 : ℕ)), cardinal.lift_nat_cast],
  norm_cast
end

instance (hd : 0 < d) : nontrivial α :=
⟨ex_two_points hd⟩

theorem basis_min_card {d' : cardinal} (hd : d' < d) {s : set α} (hd' : #s = d') :
  affine_hull s ⊂ set.univ :=
begin
  refine ⟨set.subset_univ _, λ hs : _ ⊆ _, _⟩,
  rw set.univ_subset_iff at hs,
  rcases @card_lt_basis α d _ with ⟨⟨⟨w, hwg⟩, hwb⟩, hw : _ < #w⟩,
  specialize hwb s hs, change #w ≤ _ at hwb,
  rw hd' at hwb,
  exact not_lt.mpr (le_of_lt (lt_of_lt_of_le hw hwb)) hd
end

theorem ex_not_in_affine_hull {d' : cardinal} (hd : d' < d) {s : set α} (hd' : #s = d') :
  ∃ p, p ∉ affine_hull s :=
begin
  by_contra h, push_neg at h,
  have h : affine_hull s = set.univ := by rwa set.eq_univ_iff_forall,
  have := basis_min_card hd hd',
  rw h at this,
  exact (irrefl _) this
end

theorem not_generator_of_less {d' : cardinal} (hd : d' < d) {s : set α} (hd' : #s = d') :
  ¬(generates s _ is_affine.univ) :=
ne_of_lt $ basis_min_card hd hd'

end
end ordered_geo

namespace ordered_geo_limited
section
parameters {d : cardinal.{u}} [ordered_geo α d]

--theorem unique_limited 

end
end ordered_geo_limited

/-
section
universe u
parameters {α : Type u} [ordered_geo_inf α]
namespace ordered_geo_inf

instance (d : ℕ) : ordered_geo α d := {lin_simp := λ l _, lin_any_simp l}

/-- For any point, there exists another point that's not equal to it. -/
theorem ex_not_eq (p : α) : ∃ q, p ≠ q :=
@ordered_geo.ex_not_eq _ 0 (ordered_geo _) p

instance : nonempty α := @ordered_geo.nonempty _ 0 _
instance : nontrivial α := @ordered_geo.nontrivial _ 0 _

/-- For any line, there exists a point that's not in it. -/
theorem ex_not_on_line (p q : α) : ∃ r, r ∉ line p q :=
@ordered_geo.ex_not_on_line _ 0 (ordered_geo _) p q

/-- For any plane, there exists a point that's not in it. -/
theorem ex_not_on_plane (p q r : α) :
  ∃ x, x ∉ convex_hull {y | y ∈ [p, q, r]} :=
@ordered_geo.ex_not_on_plane _ 0 (ordered_geo _) p q r

/-- For any potentially-degenerate simplex defined by the vertices `l`, there
    is a point that's not in the convex hull of `l`. -/
lemma ex_point_not_mem_simplex_hull (l : list α) :
  ∃ p, p ∉ convex_hull {q | q ∈ l} :=
begin
  classical,
  by_contra h,
  push_neg at h,
  rcases lin_any_simp l with ⟨w, _, hw⟩,
  rcases collinear.ex_collinear_of_mem (h w) with ⟨_, _, hp, hq, hpq⟩,
  replace h : {z : α | z ∈ l} ⊆ {w} ∪ {z : α | z ∈ l} := λ _, or.inr,
  replace h := convex_hull.is_mono h,
  specialize hw w _ _ (convex_hull.of_set $ or.inl rfl) (h hp) (h hq),
  
end

theorem psig_nondegen_simplex [inhabited α]
  (hlas : Π vs, @lindep_to_simplex_psig α _ vs) (d : ℕ) :
    Σ' vs : vector α d, nondegen_simplex vs.val :=
begin
  induction d with d hd, { exact ⟨vector.nil, nondegen_simplex.of_nil⟩ },
  induction d with d hd,
    { exact ⟨⟨[arbitrary α], rfl⟩, by simp, by finish⟩ },
  rcases hd with ⟨⟨l, h⟩, hvs⟩,
  rcases hlas l with ⟨p, hp⟩,
  suffices : (p ::ᵥ ⟨l, h⟩ : vector α _).val.nodup,
  refine ⟨vector.cons p ⟨l, h⟩, this, λ v₁ v₂ v₃ hv₁ hv₂ hv₃, _⟩,
  rw [lin_indep_sets, lin_indep] at hp,
  have : subtype.val (p ::ᵥ (⟨l, h⟩ : vector _ _)) = p :: l := rfl,
  rw [this, list.mem_cons_iff] at hv₁ hv₂ hv₃,
  rw (rfl : subtype.val (subtype.mk l h) = l) at hvs,
  cases hp with hp₀ hp₁,
  replace hp₀ : p ∉ l := by simp at hp₀; assumption,
  specialize hp₁ v₁ v₂ v₃ (convex_hull.of_set hv₁) (convex_hull.of_set hv₂),
  specialize hp₁ (convex_hull.of_set hv₃),
  by_cases hv₁₂ : v₁ = v₂, { exact or.inl hv₁₂.symm },
  by_cases hv₂₃ : v₂ = v₃, { exact or.inr (or.inl hv₂₃) },
  by_cases hv₁₃ : v₁ = v₃, swap,
    { rw collinear.swap_iff', exact or.inr (or.inr $ hp₁ hv₁₂ hv₁₃ hv₂₃) },
  induction hv₁₃,-- repeat { cases hv₁ }, repeat { cases hv₂ }, { exact or.inl rfl },
    { apply or.inl,
      rw (⟨ne.symm, ne.symm⟩ : v₁ ≠ v₂ ↔ v₂ ≠ v₁) at hp₁,
      revert v₁,
      rw collinear.none_collinear_iff_empty at hp₁, }
  /-
  rw [imp_iff_not_or, imp_iff_not_or, imp_iff_not_or] at hp₁,
  push_neg at hp₁,
  repeat { cases hp₁ },
    { exact or.inl rfl },
  rotate, { exact (or.inr ∘ or.inl) rfl },
    { rw collinear.swap_iff' at hp₁, exact (or.inr ∘ or.inr) hp₁ },
  swap,
    { apply or.inl, repeat { cases hv₁ }, repeat { cases hv₂ },
        { refl }, }
  -/
end

/-- For any length `d`, there is a nondegenerate simplex with `d` vertices. -/
theorem ex_nondegen_simplex (d : ℕ) :
  ∃ vs : vector α d, nondegen_simplex vs.val :=
begin
  induction d with d hd, { exact ⟨vector.nil, nondegen_simplex.of_nil⟩ },
  induction d with d hd,
    { cases ordered_geo_inf.nonempty with w,
      exact ⟨⟨[w], rfl⟩, by simp, by finish⟩ },
  rcases hd with ⟨⟨l, h⟩, hvs⟩,
  rcases lin_any_simp l with ⟨p, hp⟩,
  suffices : (p :: ⟨l, h⟩ : vector α _).val.nodup,
  refine ⟨vector.cons p ⟨l, h⟩, this, λ v₁ v₂ v₃ hv₁ hv₂ hv₃, _⟩,
  rw lin_indep at hp,
  have : subtype.val (p :: (⟨l, h⟩ : vector _ _)) = p :: l := rfl,
  rw [this, list.mem_cons_iff] at hv₁ hv₂ hv₃,
  rw (rfl : subtype.val (subtype.mk l h) = l) at hvs,
  rw collinear.none_collinear_iff_empty_fixed_1'' at hp,
  rw [convex_hull.is_empty_iff, set.eq_empty_iff_forall_not_mem] at hp,
  have : 0 < l.length := by rw h; exact nat.succ_pos',
  cases list.length_pos_iff_exists_mem.mp this with w hw,
  exact (hp _).elim hw,
  apply list.nodup_cons_of_nodup (λ hp₁, _) hvs.left,
  change p ∈ {z : α | z ∈ subtype.val (⟨l, h⟩ : vector α _)} at hp₁,
  exact lin_indep.not_indep_of_mem (convex_hull.of_set hp₁) hp
end

/-- It's false that for any nondegenerate simplex with `d` vertices and point
    `p`, there are two points in the convex hull of the simplex -/
theorem not_all_in_space (d : ℕ) : ¬ ∀ {vs : vector α d.succ},
  nondegen_simplex vs.val → ∀ v₁, ∃ v₂ v₃ ∈ convex_hull {p | p ∈ vs.val},
    collinear v₁ v₂ v₃ :=
begin
  intro hvs,
  rcases ex_nondegen_simplex (d + 1) with ⟨vs, hl⟩,
  cases ordered_geo_inf.lin_any_simp vs.val with w hw,
  rcases hvs hl w with ⟨_, _, hp, hq, hpq⟩,
  apply hw _ _ hp hq,
  rwa ←collinear.rotate_iff
end

/-- For any `d`, there's a nondegenerate simplex with `d` vertices and a point
    `p` that's linearly independent to the convex hull of the simplex. -/
theorem ex_ndsimp_ex_p_lindep (d : ℕ) : ∃ vs : vector α d.succ,
  nondegen_simplex vs.val ∧ ∃ p, lin_indep p (convex_hull {p | p ∈ vs.val}) :=
begin
  have := not_all_in_space d,
  push_neg at this,
  rcases this with ⟨v, hv1, x, hx⟩,
  refine ⟨v, hv1, x, _⟩,
  rw collinear.none_collinear_iff_empty_fixed_1 at hx,
  rwa [lin_indep.indep_def, collinear.none_collinear_iff_empty_fixed_1'']
end

end ordered_geo_inf-/
end
end
