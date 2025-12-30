import Mathlib.Tactic
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Order.Category.LinOrd
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sigma.Lex
import Mathlib.Order.Basic
import Hausdorff.WellOrderedCofinalSubset
import Hausdorff.Isomorphisms

open Classical
universe u

#check Order.iso_of_countable_dense
/-- We define scattered from the perspective of Cantor's theorem -/
def Scattered (X : LinOrd) : Prop := IsEmpty (ℚ ↪o X)
  -- ∀ (S : Set (X.carrier)),
  -- let suborder : LinOrd :=
  --     ({carrier := S,
  --       str := inferInstance})
  -- ¬(Countable suborder ∧ DenselyOrdered suborder
  --   ∧ NoMinOrder suborder ∧ NoMaxOrder suborder ∧ Nonempty suborder)

lemma Scattered_to_subset_props (X : LinOrd) (h : Scattered X) (S : Set (X.carrier)):
  ¬(Countable (LinOrd.mk S) ∧ DenselyOrdered (LinOrd.mk S)
    ∧ NoMinOrder (LinOrd.mk S) ∧ NoMaxOrder (LinOrd.mk S) ∧ Nonempty (LinOrd.mk S)) := by
  by_contra! contra
  rcases contra with ⟨p1, p2, p3, p4, p5⟩
  apply (not_isEmpty_iff.mpr (Order.iso_of_countable_dense ℚ S))
  by_contra Eiso
  rcases not_isEmpty_iff.mp Eiso with ⟨f⟩
  apply (not_nonempty_iff.mpr h)
  let g : ℚ ↪ X :=
        { toFun := fun x => f.toFun x
          inj' := by
            intro a b h
            apply OrderIso.injective f
            exact SetCoe.ext_iff.mp h }
  use g
  intro a b
  simp [g]

lemma Scattered_of_subset_props (X : LinOrd)
    (h : ∀ S : Set X, ¬(Countable (LinOrd.mk S) ∧ DenselyOrdered (LinOrd.mk S) ∧
      NoMinOrder (LinOrd.mk S) ∧ NoMaxOrder (LinOrd.mk S) ∧ Nonempty (LinOrd.mk S))) :
    Scattered X := by
    by_contra nonempt
    -- we show there exists a subset of X isomorphic to ℚ, and prove that subset contradicts
    -- the scattered-ness of X
    rcases not_isEmpty_iff.mp nonempt with ⟨f⟩
    have : ∃ A : Set X.carrier, Nonempty (ℚ ≃o A) := by
      use ↑(Set.range ⇑f)
      use @OrderEmbedding.orderIso ℚ X _ _ f
      exact (@OrderEmbedding.orderIso ℚ X _ _ f).map_rel_iff'
    rcases this with ⟨A, hA⟩
    let hA' := hA
    rcases hA with ⟨f⟩
    by_contra
    apply h A
    split_ands
    · exact @Countable.of_equiv _ _ (@Encodable.countable ℚ _) f
    · exact dense_of_iso_from_dense LinearOrderedSemiField.toDenselyOrdered hA'
    · exact (unbounded_of_iso_from_unbounded (NoBotOrder.to_noMinOrder ℚ)
             (NoTopOrder.to_noMaxOrder ℚ) hA').left
    · exact (unbounded_of_iso_from_unbounded (NoBotOrder.to_noMinOrder ℚ)
             (NoTopOrder.to_noMaxOrder ℚ) hA').right
    · rcases @instNonemptyOfInhabited ℚ _ with ⟨a⟩
      use f a; simp

-- /-- The above definition is equivalent to the conventional definition
--     of scattered via embedding of the rationals-/
-- lemma scattered_iff_not_embeds_rat (X : LinOrd) : Scattered X ↔ IsEmpty (ℚ ↪o X) := by
--   constructor
--   · intro h
    -- by_contra nonempt
    -- -- we show there exists a subset of X isomorphic to ℚ, and prove that subset contradicts
    -- -- the scattered-ness of X
    -- rcases not_isEmpty_iff.mp nonempt with ⟨f⟩
    -- have : ∃ A : Set X.carrier, Nonempty (ℚ ≃o A) := by
    --   use ↑(Set.range ⇑f)
    --   use @OrderEmbedding.orderIso ℚ X _ _ f
    --   exact (@OrderEmbedding.orderIso ℚ X _ _ f).map_rel_iff'
    -- rcases this with ⟨A, hA⟩
    -- let hA' := hA
    -- rcases hA with ⟨f⟩
    -- by_contra
    -- apply h A
    -- split_ands
    -- · exact @Countable.of_equiv _ _ (@Encodable.countable ℚ _) f
    -- · exact dense_of_iso_from_dense LinearOrderedSemiField.toDenselyOrdered hA'
    -- · exact (unbounded_of_iso_from_unbounded (NoBotOrder.to_noMinOrder ℚ)
    --          (NoTopOrder.to_noMaxOrder ℚ) hA').left
    -- · exact (unbounded_of_iso_from_unbounded (NoBotOrder.to_noMinOrder ℚ)
    --          (NoTopOrder.to_noMaxOrder ℚ) hA').right
    -- · rcases @instNonemptyOfInhabited ℚ _ with ⟨a⟩
    --   use f a; simp
--   · -- proceed by contradiction and directly apply Cantor's theorem
--     intro h
--     by_contra contra
--     simp only [Scattered, not_forall, not_not] at contra
--     rcases contra with ⟨A, p1, p2, p3, p4, p5⟩
--     have : Countable ↑A := by exact p1
--     have : Nonempty ↑A := by rcases p5 with ⟨a, ha⟩; use a
--     apply (not_isEmpty_iff.mpr (Order.iso_of_countable_dense ℚ A))
--     by_contra Eiso
--     rcases not_isEmpty_iff.mp Eiso with ⟨f⟩
--     apply (not_nonempty_iff.mpr h)
--     let g : ℚ ↪ X :=
--           { toFun := fun x => f.toFun x
--             inj' := by
--               intro a b h
--               apply OrderIso.injective f
--               exact SetCoe.ext_iff.mp h }
--     use g
--     intro a b
--     simp [g]

/-- Any order isomoprhic to a scattered order is scattered -/
lemma scatttered_of_iso_to_scattered (X : LinOrd) (Y : LinOrd) (f : X ≃o Y)
  (h : Scattered Y) : Scattered X := by
  rw [Scattered, <-not_nonempty_iff, <-exists_true_iff_nonempty] at h
  by_contra contra
  rw [Scattered, not_isEmpty_iff] at contra
  rcases contra with ⟨g⟩
  apply h
  use comp_is_orderEmb (OrderIso.toOrderEmbedding f) g

/-- Well orders are scattered -/
lemma scattered_of_wellFounded (X : LinOrd) : WellFounded X.str.lt → Scattered X := by
  intro hwf
  by_contra h
  rw [Scattered, <-not_nonempty_iff, not_not] at h
  rcases h with ⟨f⟩
  rcases WellFounded.has_min hwf (Set.range f) (Set.range_nonempty f) with ⟨m, h₁, h₂⟩
  let ⟨x, hx⟩ := Set.mem_range.mp h₁
  let ⟨y, hy⟩ := (NoBotOrder.to_noMinOrder ℚ).exists_lt x
  apply h₂ (f y) (by exact Set.mem_range_self y)
  rw [<- hx]
  exact (OrderEmbedding.lt_iff_lt f).mpr hy

#check LinearOrder.toDecidableLE
lemma rat_swap : Nonempty (@OrderIso (linOrd_swap (LinOrd.mk ℚ)) (LinOrd.mk ℚ) Rat.linearOrder.swap.toLE Rat.instLE) := by
  sorry
/-- If X a linear order is scattered, so is its reversal -/
lemma scattered_swap (X : LinOrd) : Scattered X →
  Scattered {carrier := X.carrier, str := X.str.swap} := by
  -- intro h₁
  -- by_contra h₂
  -- rw [Scattered, <-not_nonempty_iff, not_not] at h₂
  -- simp only [Scattered] at h₁
  -- rcases h₂ with ⟨f⟩
  -- rcases rat_swap with ⟨g⟩
  -- apply (@IsEmpty.exists_iff _ h₁).mp

  -- use {
  --   toFun := f ∘ g
  --   inj' := by
  --     apply Function.Injective.comp
  --       (RelEmbedding.injective f)
  --       (RelEmbedding.injective (@OrderIso.toOrderEmbedding _ _ Rat.linearOrder.swap.toLE Rat.instLE g))
  --   map_rel_iff' := by
  --     intro p q
  --     simp
  --     change f (g p) ≥ f (g q) ↔ p ≤ q
  --     let t := @f.map_rel_iff' (g.toEquiv p) (g.toEquiv q)
  --     let e := @g.map_rel_iff' p q
  --     change g.toEquiv p ≤ g.toEquiv q ↔ p ≥ q at e
  --     change @LE.le (LinOrd.mk X) _ (f (g p)) (f (g q)) ↔ p ≤ q
  --     #check not_lt_iff_eq_or_lt
  --     rw [<- not_lt, ge_iff_le, <- not_lt, iff_not_comm] at e
  --     push_neg at e


      -- rw [<- e, <- t]
      -- change f (g p) ≥ f (g q) ↔ f (g p) ≤ f (g q)
      -- change @LE.le (LinOrd.mk X) _ (f (g p)) (f (g q)) ↔ @GE.ge (LinOrd.mk X) _ (f (g p)) (f (g q))

      -- rfl

      -- sorry
  -- }

  -- intro X_Scat
  -- rintro A A_ord ⟨p1, p2, p3, p4, p5⟩
  -- apply X_Scat A
  -- split_ands
  -- · exact p1
  -- · constructor
  --   intro a b hab
  --   rcases p2.dense b a hab with ⟨c, hc⟩
  --   use c
  --   exact And.intro hc.right hc.left
  -- · constructor
  --   intro a
  --   rcases p4.exists_gt a with ⟨b, hb⟩
  --   use b, hb
  -- · constructor
  --   intro a
  --   rcases p3.exists_lt a with ⟨b, hb⟩
  --   use b, hb
  -- · rcases exists_true_iff_nonempty.mpr p5 with ⟨a, _⟩
  --   use a, a.2
  sorry

/-- .swap is its own inverse -/
lemma swap_swap_elim {X : LinOrd}: (X.str.swap).swap = X.str := by
  ext; rfl

/-- Reverse well orders are scattered -/
lemma scattered_of_rev_wellFounded (X : LinOrd) : WellFounded (X.str.swap).lt → Scattered X := by
  intro h
  have aux := scattered_swap {carrier := X.carrier, str := X.str.swap}
    (scattered_of_wellFounded {carrier := X.carrier, str := X.str.swap} h)
  rw [<-swap_swap_elim] at aux
  exact aux
