import Mathlib.Tactic
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Order.Category.LinOrd
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sigma.Lex
import Mathlib.Order.Basic
import Hausdorff.WO_cofinal_subset

open Classical
universe u

/-- The composition of order embeddings is an order embedding -/
def OrderEmbedding_comp {α β γ: Type*} [Preorder α] [Preorder β] [Preorder γ] (g: β ↪o γ)
  (f: α ↪o β) : α ↪o γ :=
  { toFun := g ∘ f
    inj' := by
      apply (EmbeddingLike.comp_injective (⇑f) g).mpr f.inj'
    map_rel_iff' := by intro _ _; simp }

/-- Order isomoprhism preserves (order) density -/
lemma dense_of_iso_from_dense {α β: Type*} [Preorder α] [Preorder β] (h: DenselyOrdered α) :
  Nonempty (α ≃o β) → DenselyOrdered β := by
  intro h
  rcases h with ⟨f⟩
  constructor
  intro a b hab
  rcases h.dense (f.symm a) (f.symm b) (f.symm.lt_iff_lt.mpr hab) with ⟨x, hx⟩
  use (f x)
  rw [<-OrderIso.symm_apply_apply f x, f.symm.lt_iff_lt, f.symm.lt_iff_lt] at hx
  exact hx

/-- Order isomorphism preserves unboundedness -/
lemma unbounded_of_iso_from_unbounded {α β: Type*} [Preorder α] [Preorder β] (h: NoMinOrder α)
  (h1: NoMaxOrder α): Nonempty (α ≃o β) → NoMinOrder β ∧ NoMaxOrder β := by
  intro h
  rcases h with ⟨f⟩
  constructor
  · constructor
    intro a
    rcases h.exists_lt (f.symm a) with ⟨x, hx⟩
    use f x
    rw [<-OrderIso.symm_apply_apply f x, f.symm.lt_iff_lt] at hx
    exact hx
  · constructor
    intro a
    rcases h1.exists_gt (f.symm a) with ⟨x, hx⟩
    use f x
    rw [<-OrderIso.symm_apply_apply f x, f.symm.lt_iff_lt] at hx
    exact hx

--/////////////////////////////////////////////////////////////////////////////////////////
--  Definitions + Lemmas about new definitions -
--/////////////////////////////////////////////////////////////////////////////////////////

/-- We define scattered from the perspective of Cantor's theorem -/
def IsScattered : LinOrd → Prop := fun (X : LinOrd) =>
  ∀ (S : Set (X.carrier)),
  let suborder : LinOrd :=
      ({carrier := S,
        str := inferInstance})
  ¬(Countable suborder ∧ DenselyOrdered suborder
    ∧ NoMinOrder suborder ∧ NoMaxOrder suborder ∧ Nonempty suborder)

/-- The above definition is equivalent to the conventional definition
    of scattered via embedding of the rationals-/
lemma scat_iff_not_embeds_Q (X : LinOrd) : IsScattered X ↔ IsEmpty (ℚ ↪o X) := by
  constructor
  · intro h
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
  · -- proceed by contradiction and directly apply Cantor's theorem
    intro h
    by_contra contra
    simp only [IsScattered, not_forall, not_not] at contra
    rcases contra with ⟨A, p1, p2, p3, p4, p5⟩
    have : Countable ↑A := by exact p1
    have : Nonempty ↑A := by rcases p5 with ⟨a, ha⟩; use a
    apply (not_isEmpty_iff.mpr (Order.iso_of_countable_dense ℚ A))
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

/-- Any order isomoprhic to a scattered order is scattered -/
lemma scat_of_iso_to_scat (X : LinOrd) (Y : LinOrd) (f : X ≃o Y)
  (h : IsScattered Y) : IsScattered X := by
  rw [scat_iff_not_embeds_Q X]
  rw [scat_iff_not_embeds_Q Y, <-not_nonempty_iff, <-exists_true_iff_nonempty] at h
  by_contra contra
  rw [not_isEmpty_iff] at contra
  rcases contra with ⟨g⟩
  apply h
  use OrderEmbedding_comp (OrderIso.toOrderEmbedding f) g

/-- Well orders are scattered -/
lemma scat_of_well_founded (X : LinOrd) : WellFounded X.str.lt → IsScattered X := by
  intro hwf
  intro A LO props
  rcases props.right.right.right.right with ⟨y, hy⟩
  rcases Decidable.em (Nonempty ↑A) with nonempt | empt
  · have : A.Nonempty := by
      rw [Set.nonempty_iff_ne_empty, <- Set.nonempty_iff_ne_empty']
      exact props.right.right.right.right
    rcases WellFounded.has_min hwf A this with ⟨lb, hlb⟩
    rcases (props.right.right.left).exists_lt ⟨lb, hlb.left⟩ with ⟨a, ha⟩
    apply hlb.right a.1 a.2
    exact ha
  · apply empt
    exact props.right.right.right.right

/-- If X a linear order is scattered, so is its reversal -/
lemma rev_scattered_of_scattered (X : LinOrd) : IsScattered X →
  IsScattered {carrier := X.carrier, str := X.str.swap} := by
  intro X_Scat
  rintro A A_ord ⟨p1, p2, p3, p4, p5⟩
  apply X_Scat A
  split_ands
  · exact p1
  · constructor
    intro a b hab
    rcases p2.dense b a hab with ⟨c, hc⟩
    use c
    exact And.intro hc.right hc.left
  · constructor
    intro a
    rcases p4.exists_gt a with ⟨b, hb⟩
    use b, hb
  · constructor
    intro a
    rcases p3.exists_lt a with ⟨b, hb⟩
    use b, hb
  · rcases exists_true_iff_nonempty.mpr p5 with ⟨a, _⟩
    use a, a.2

/-- .swap is its own inverse -/
lemma swap_of_swap_elim {X : LinOrd}: (X.str.swap).swap = X.str := by
  ext; rfl

/-- Reverse well orders are scattered -/
lemma scat_of_rev_well_founded (X : LinOrd) : WellFounded (X.str.swap).lt → IsScattered X := by
  intro h
  have p := rev_scattered_of_scattered
    {carrier := X.carrier, str := X.str.swap}
    (scat_of_well_founded {carrier := X.carrier, str := X.str.swap} h)
  rw [<-swap_of_swap_elim] at p
  exact p
