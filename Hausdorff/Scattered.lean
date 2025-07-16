import Hausdorff.Isomorphisms

open Classical
universe u

/-- A linear order is scattered if the rationals do not embed into it -/
def Scattered (L : LinOrd) : Prop := IsEmpty (ℚ ↪o L)

/-- Any order isomoprhic to a scattered order is scattered -/
lemma scatttered_of_iso_to_scattered (L : LinOrd) (M : LinOrd) (f : L ≃o M)
    (h : Scattered M) : Scattered L := by
  rw [Scattered, <-not_nonempty_iff, <-exists_true_iff_nonempty] at h
  by_contra h₀
  rw [Scattered, not_isEmpty_iff] at h₀
  rcases h₀ with ⟨g⟩
  apply h
  use OrderEmbedding_comp g (OrderIso.toOrderEmbedding f)

/-- Well orders are scattered -/
lemma scattered_of_wellFounded (L : LinOrd) (h : WellFounded L.str.lt) : Scattered L := by
  by_contra h₀
  rw [Scattered, <-not_nonempty_iff, not_not] at h₀
  rcases h₀ with ⟨f⟩
  rcases WellFounded.has_min h (Set.range f) (Set.range_nonempty f) with ⟨m, h₁, h₂⟩
  let ⟨x, hx⟩ := Set.mem_range.mp h₁
  let ⟨y, hy⟩ := (NoBotOrder.to_noMinOrder ℚ).exists_lt x
  apply h₂ (f y) (Set.mem_range_self y)
  rw [<- hx]
  exact (OrderEmbedding.lt_iff_lt f).mpr hy

/-- Reverse well orders are scattered -/
lemma scattered_of_rev_wellFounded (X : LinOrd) : WellFounded (X.str.swap).lt → Scattered X := by
  intro hwf
  by_contra h
  rw [Scattered, <-not_nonempty_iff, not_not] at h
  rcases h with ⟨f⟩
  rcases WellFounded.has_min hwf (Set.range f) (Set.range_nonempty f) with ⟨m, h₁, h₂⟩
  let ⟨x, hx⟩ := Set.mem_range.mp h₁
  let ⟨y, hy⟩ := (NoTopOrder.to_noMaxOrder ℚ).exists_gt x
  apply h₂ (f y) (Set.mem_range_self y)
  rw [<- hx]
  exact (OrderEmbedding.lt_iff_lt f).mpr hy
