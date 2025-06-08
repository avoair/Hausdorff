-- This file contains a mostly complete version of the easy direction of
-- the proof of Hausdorff's theorem.
-- There are a few sorrys (mainly) due to type problems


import Mathlib.Tactic
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Order.Category.LinOrd
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sigma.Lex
import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Batteries.Logic

open Classical

--//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/- Lemmas that I cant find in the library, that should be there -/
--//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

-- this is supposed to be in the library... but it doesnt recognize it
-- theorem heq_cast_iff_heq {α β γ : Sort _} (e : β = γ) (a : α) (b : β) :
--     HEq a (cast e b) ↔ HEq a b := by subst e; rfl

/-- the composition of order embeddings is an order embedding -/
def OrderEmbedding_comp {α β γ: Type*} [Preorder α] [Preorder β] [Preorder γ] (g: β ↪o γ) (f: α ↪o β) : α ↪o γ :=
  { toFun := g ∘ f
    inj' := by
      apply (EmbeddingLike.comp_injective (⇑f) g).mpr f.inj'
    map_rel_iff' := by
      intro a b
      simp}

/-- the composition of order embeddings is an order embedding -/
lemma Q_CDNE : Countable ℚ ∧ DenselyOrdered ℚ ∧ NoMinOrder ℚ ∧ NoMaxOrder ℚ ∧ Nonempty ℚ := by
  split_ands
  · exact Encodable.countable
  · exact LinearOrderedSemiField.toDenselyOrdered
  · exact NoBotOrder.to_noMinOrder ℚ
  · exact NoTopOrder.to_noMaxOrder ℚ
  · exact instNonemptyOfInhabited

/-- order isomoprhism preserves (order) density -/
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

/-- order isomorphism preserves unboundedness -/
lemma unbounded_of_iso_from_unbounded {α β: Type*} [Preorder α] [Preorder β] (h: NoMinOrder α) (h1: NoMaxOrder α):
  Nonempty (α ≃o β) → NoMinOrder β ∧ NoMaxOrder β := by
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

--//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/--  Definitions + Lemmas about new definitions -/
--//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

-- We define scattered from the perspective of Cantor's theorem
def IsScattered : LinOrd → Prop := fun (X : LinOrd) =>
  ∀ (S : Set (X.carrier)),
  let suborder : LinOrd :=
      ({carrier := S,
        str := inferInstance})
  ¬(Countable suborder ∧ DenselyOrdered suborder
    ∧ NoMinOrder suborder ∧ NoMaxOrder suborder ∧ Nonempty suborder)

/-- The above definition is equivalent to the conventional definition of scattered -/
lemma Scat_iff_not_embeds_Q (X : LinOrd) : IsScattered X ↔ IsEmpty (ℚ ↪o X) := by
  constructor
  · intro h
    by_contra nonempt
    -- we show there exists a subset of X isomorphic to ℚ, and prove that subset contradicts the scattered-ness of X
    rcases not_isEmpty_iff.mp nonempt with ⟨f⟩
    have : ∃ A : Set X.carrier, Nonempty (ℚ ≃o A) := by
      use ↑(Set.range ⇑f)
      use @OrderEmbedding.orderIso ℚ X _ _ f
      exact (@OrderEmbedding.orderIso ℚ X _ _ f).map_rel_iff'
    rcases this with ⟨A, hA⟩
    let hA' := hA; rcases hA with ⟨f⟩
    specialize h A
    by_contra _
    apply h
    simp
    split_ands
    · exact @Countable.of_equiv _ _ Q_CDNE.left f
    · exact dense_of_iso_from_dense Q_CDNE.right.left hA'
    · exact (unbounded_of_iso_from_unbounded Q_CDNE.right.right.left
             Q_CDNE.right.right.right.left hA').left
    · exact (unbounded_of_iso_from_unbounded Q_CDNE.right.right.left
             Q_CDNE.right.right.right.left hA').right
    · rcases Q_CDNE.right.right.right.right with ⟨a⟩
      use f a
      simp
  · -- we proceed by contradiction and directly apply Cantor's theorem
    intro h
    by_contra contra
    simp [IsScattered] at contra
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

lemma Scat_of_iso_to_scat (X : LinOrd) (Y : LinOrd) (f : @OrderIso X Y _ inferInstance) (h : IsScattered Y) : IsScattered X := by
  rw [Scat_iff_not_embeds_Q X]
  rw [Scat_iff_not_embeds_Q Y, <-not_nonempty_iff, <-exists_true_iff_nonempty] at h
  by_contra contra
  simp at contra
  rcases contra with ⟨g⟩
  apply h
  use OrderEmbedding_comp (OrderIso.toOrderEmbedding f) g

/-- Hausdorff's recursive definition of scattered -/
inductive Scattered_ind_prop : LinOrd → Prop
| base {L : LinOrd} (x : L.carrier) (h : {x} = @Set.univ L.carrier) : Scattered_ind_prop L
| closed_under_op (WO: LinOrd)
                  (hwo : WellFounded WO.str.le
                       ∨ WellFounded (LinearOrder.swap WO.carrier WO.str).le) ---
                  (f: WO.carrier → LinOrd)
                  (h : ∀ w, Scattered_ind_prop (f w))
                  (L : LinOrd)
                  (h : L ≃o ({carrier := Σₗ w, (f w).carrier, str := Sigma.Lex.linearOrder} : LinOrd)): Scattered_ind_prop L

/-- every linear order has a well-founded cofinal subset -/
lemma exists_cof_WF_subset  {α : Type*} [LinearOrder α]:
  ∃ (A : Set α), IsCofinal A ∧ A.WellFoundedOn (· < ·) := by sorry -- proof in other file
                                                                   -- how do you import local files?

/-- a helper fxn for the next theorem: a lienar order α is well-ordered iff for any x, every set containing x is bounded below-/
private lemma WO_iff_lem {α : Type*} [r : LinearOrder α]: IsWellFounded α r.lt ↔ ∀ x, ∀ A : Set α, x ∈ A → ∃ lb ∈ A, ∀ a ∈ A, r.le lb a := by
  constructor
  · intro hwf x
    apply IsWellFounded.induction r.lt x
    intro x IH A
    intro hxA
    rcases Classical.em (∀ a ∈ A, r.le x a) with hxlb | hnxlb
    · use x
    · push_neg at hnxlb
      rcases hnxlb with ⟨a, ha⟩
      exact IH a (ha.right) A ha.left
  · intro h
    constructor
    apply WellFounded.intro
    by_contra contra
    push_neg at contra
    let S := {a : α | ¬ Acc LT.lt a}
    rcases contra with ⟨x, hx⟩
    rcases h x S hx with ⟨lb, hlb⟩
    apply hlb.left
    apply Acc.intro
    intro y hy
    by_contra hyacc
    apply not_lt_of_ge (LE.le.ge (hlb.right y hyacc))
    exact hy

/-- A linear order is well-founded iff every subset is bounded below -/
theorem WO_iff_subsets_bdd_below {α : Type*} [r : LinearOrder α]: IsWellFounded α r.lt ↔ ∀ (A: Set α), A.Nonempty → ∃ lb ∈ A, ∀ x ∈ A, r.le lb x := by
  constructor
  · rw [WO_iff_lem]
    intro h A hA
    rcases hA with ⟨x, hx⟩
    exact h x A hx
  · rw [WO_iff_lem]
    intro h x A hA
    apply h A
    rw [Set.nonempty_def]
    use x


/-- Well orders are scattered -/
lemma Well_Ord_Scattered (X : LinOrd) : WellFounded X.str.le → IsScattered X := by
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
    exact le_of_lt ha
  · apply empt
    exact props.right.right.right.right

/-- If X a linear order is scattered, so is its reversal -/
-- I didnt actually end up using this elsewhere in the file
lemma Rev_Scattered_of_Scattered (X : LinOrd) : IsScattered X → IsScattered {carrier := X.carrier, str := LinearOrder.swap X.carrier X.str} := by
  intro X_Scat

  simp [LinearOrder.swap]
  intro A A_ord props
  simp at A --- ?

  apply X_Scat A
  simp
  split_ands
  · exact props.left
  · constructor
    intro a b hab
    rcases props.right.left.dense b a hab with ⟨c, hc⟩
    use c
    exact And.intro hc.right hc.left
  · constructor
    intro a
    rcases props.right.right.right.left.exists_gt a with ⟨b, hb⟩
    use b, hb
  · constructor
    intro a
    rcases props.right.right.left.exists_lt a with ⟨b, hb⟩
    use b, hb
  · rcases exists_true_iff_nonempty.mpr props.right.right.right.right with ⟨a, _⟩
    use a, a.2

/-- Reverse well orders are scattered -/
-- I originally attempted to use the previous lemma for this proof, but I found this to actually be easier
-- as Lean was unable to simplify nested LinearOrder.swaps
lemma Rev_Well_Ord_Scattered (X : LinOrd) : WellFounded (LinearOrder.swap X.carrier X.str).le → IsScattered X := by
  intro hwf
  intro A LO props
  rcases props.right.right.right.right with ⟨y, hy⟩
  rcases Decidable.em (Nonempty ↑A) with nonempt | empt
  · have : A.Nonempty := by
      rw [Set.nonempty_iff_ne_empty, <- Set.nonempty_iff_ne_empty']
      exact props.right.right.right.right
    rcases WellFounded.has_min hwf A this with ⟨lb, hlb⟩
    rcases (props.right.right.right.left).exists_gt ⟨lb, hlb.left⟩ with ⟨a, ha⟩
    apply hlb.right a.1 a.2
    exact le_of_lt ha
  · apply empt
    exact props.right.right.right.right


/-- Hausdorff's theorem -/
theorem Hausdorff_Scattered_Orders (X : LinOrd): IsScattered X ↔ Scattered_ind_prop X := by
  constructor
  · sorry

-- RIGHT TO LEFT
  · intro X_scat_prop
    induction' X_scat_prop with lo x single_lo lo_lex WF_RWF ind scat_prop_of_ind L Liso is_scat_f
    · -- singleton case
      intro A A_ord props
      have A_s : A.Subsingleton := by
        apply @Set.subsingleton_of_subset_singleton ↑lo x
        rw [single_lo]
        exact Set.subset_univ A
      rcases props.right.right.right.right with ⟨y, hy⟩
      rcases (props.right.right.left).exists_lt ⟨y, hy⟩ with ⟨a, ha⟩
      simp [A_ord] at a
      have hay: a.1 < y := by
        exact ha
      apply ne_of_lt hay
      exact symm (A_s hy a.2)

    · -- inductive case
      apply Scat_of_iso_to_scat L { carrier := Σₗ (w : ↑lo_lex), ↑(ind w), str := Sigma.Lex.linearOrder } Liso

      intro A A_ord props
      let f : A → lo_lex := fun x => x.val.1 -- map elements to their position in the larger well ordering

      rcases Decidable.em (Function.Injective f) with inj | ninj
      · -- assume every suborder is hit at most once
        -- f takes an element of the sigma order and returns its position is the WO/RWO
        let f : A ↪o lo_lex.carrier :=
          { toFun := fun x => (x.val).fst,
            inj' := inj
            map_rel_iff' := by
              intro a b
              simp
              constructor
              · intro h
                rcases lt_or_eq_of_le h with h1 | h1
                · exact Sigma.Lex.le_def.mpr (Or.inl h1)
                · exact le_of_eq (inj h1)
              · intro h
                rcases Sigma.Lex.le_def.mp h with h1 | h1
                · exact le_of_lt h1
                · rcases h1 with ⟨h2, _⟩
                  exact le_of_eq h2}

        have lo_scat: IsScattered lo_lex := by
          rcases WF_RWF with WF | RWF
          · apply Well_Ord_Scattered lo_lex WF
          · apply Rev_Well_Ord_Scattered lo_lex RWF

        apply not_nonempty_iff.mpr ((Scat_iff_not_embeds_Q lo_lex).mp lo_scat)
        rcases props with ⟨p1, p2, p3, p4, p5⟩
        rcases Order.iso_of_countable_dense ℚ A with ⟨g⟩
        rw [<-exists_true_iff_nonempty]
        use OrderEmbedding_comp f (OrderIso.toOrderEmbedding g)

      · -- assume there exists a suborder with contribuing two elements
        rw [Function.not_injective_iff] at ninj
        have : ∃ a b, f a = f b ∧ a < b := by -- essentially WLOG x < y
          rcases ninj with ⟨x, y, hxy⟩
          rcases (ne_iff_lt_or_gt.mp hxy.right) with hgt | hlt
          · use x, y; exact And.intro hxy.left hgt
          · use y, x; exact And.intro (Eq.symm hxy.left) hlt

        rcases this with ⟨a, b, hab⟩
        let B := {y | a < y ∧ y < b}
        -- we first show that ℚ embeds into an interval of itself
        have A_iso_B: Nonempty (A ≃o B) := by
          have p1 : Countable B := by
            apply @Subtype.countable _ props.left
          have p2 : DenselyOrdered B := by
            constructor
            intro c d hcd
            rcases props.right.left.dense c d hcd with ⟨y, hy⟩
            have : y ∈ B := by
              exact And.intro (lt_trans c.2.left hy.left) (lt_trans hy.right d.2.right)
            use ⟨y, this⟩
            exact hy
          have p3 : NoMinOrder B := by
            constructor
            intro c
            rcases props.right.left.dense a c c.2.left with ⟨y, hy⟩
            have : y ∈ B := by
              exact And.intro hy.left (lt_trans hy.right c.2.right)
            use ⟨y, this⟩
            exact hy.right
          have p4 : NoMaxOrder B := by
            constructor
            intro c
            rcases props.right.left.dense c b c.2.right with ⟨y, hy⟩
            have : y ∈ B := by
              exact And.intro (lt_trans c.2.left hy.left) hy.right
            use ⟨y, this⟩
            exact hy.left
          have p5 : Nonempty B := by
            rcases props.right.left.dense a b hab.right with ⟨y, hy⟩
            use ⟨y, y.2⟩
            exact hy
          rcases props with ⟨q1, q2, q3, q4, q5⟩
          apply Order.iso_of_countable_dense

        -- everything in the inverval B maps to the same suborder
        have fix_fst (x : B) : x.1.1.1 = f a := by
          simp [f]
          by_contra contra
          rcases lt_or_gt_of_ne contra with h1 | h1
          · rcases Sigma.Lex.lt_def.mp (x.2.left) with h2 | h2
            · exact not_lt_of_le (le_of_lt h1) h2
            · rcases h2 with ⟨h, hh⟩
              exact contra (Eq.symm h)
          · have : (a.1).fst ≤ (b.1).fst := by
              rcases Sigma.Lex.lt_def.mp hab.right with h | h
              · exact le_of_lt h
              · rcases h with ⟨h, _⟩
                exact le_of_eq h
            simp [f] at hab
            rcases Sigma.Lex.lt_def.mp (x.2.right) with h2 | h2
            · apply ne_of_gt (lt_trans (GT.gt.lt h1) h2)
              exact (Eq.symm hab.left)
            · rcases h2 with ⟨h, hh⟩
              rw [<-hab.left] at h
              exact contra h

        have g_help (x : B) : (ind (x.1.1.1)).1 = (ind (f a)).1 := by rw [fix_fst]

        let g : B ↪o ind (f a) := {
            -- toFun := fun x => cast (g_help x) x.1.1.2,
            toFun := fun x => g_help x ▸ x.1.1.2
            inj' := by
              intro x y hxy
              simp at hxy
              apply SetCoe.ext_iff.mp
              apply SetCoe.ext_iff.mp
              apply Sigma.ext_iff.mpr
              constructor
              · rw [fix_fst x, fix_fst y]
              · apply HEq.symm
                exact (heq_cast_iff_heq _ _ _).mp (HEq.symm (heq_of_eq_cast (g_help y) hxy))
            map_rel_iff' := by
              intro x y
              simp
              constructor
              · intro h
                have : x.1.1 ≤ y.1.1 := by
                  rw [Sigma.Lex.le_def]
                  apply Or.inr
                  simp [fix_fst x, fix_fst y]
                  sorry
                apply this
              · intro h
                have : x.1.1 ≤ y.1.1 := by exact h
                rw [Sigma.Lex.le_def] at this
                simp [fix_fst x, fix_fst y] at this
                sorry
        }
        -- compose the isomorphisms/ embeddings
        rcases props with ⟨p1, p2, p3, p4, p5⟩
        rcases Order.iso_of_countable_dense ℚ A with ⟨h⟩
        have h' := OrderIso.toOrderEmbedding h
        rcases A_iso_B with ⟨i⟩
        have i' :=   OrderIso.toOrderEmbedding i
        have F := OrderEmbedding_comp g (OrderEmbedding_comp i' h')
        apply isEmpty_iff.mp
        apply (Scat_iff_not_embeds_Q (ind (f a))).mp (is_scat_f (f a))
        exact F
