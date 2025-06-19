-- lake update
-- lake exe cache get
import Mathlib.Tactic
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Order.Category.LinOrd
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sigma.Lex
import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Batteries.Logic

open Classical

--////////////////////////////////////////////////////////////////////////////////////////
/- Lemmas that I cant find in the library, that should be there -/
--////////////////////////////////////////////////////////////////////////////////////////

/-- the composition of order embeddings is an order embedding -/
def OrderEmbedding_comp {α β γ: Type*} [Preorder α] [Preorder β] [Preorder γ] (g: β ↪o γ)
  (f: α ↪o β) : α ↪o γ :=
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
/--  Definitions + Lemmas about new definitions -/
--/////////////////////////////////////////////////////////////////////////////////////////

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
    -- we show there exists a subset of X isomorphic to ℚ, and prove that subset contradicts
    -- the scattered-ness of X
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

lemma Scat_of_iso_to_scat (X : LinOrd) (Y : LinOrd) (f : @OrderIso X Y _ inferInstance)
  (h : IsScattered Y) : IsScattered X := by
  rw [Scat_iff_not_embeds_Q X]
  rw [Scat_iff_not_embeds_Q Y, <-not_nonempty_iff, <-exists_true_iff_nonempty] at h
  by_contra contra
  simp at contra
  rcases contra with ⟨g⟩
  apply h
  use OrderEmbedding_comp (OrderIso.toOrderEmbedding f) g

/-- Hausdorff's recursive definition of scattered -/
inductive Scattered_ind_prop.{u} : LinOrd.{u} → Prop
| base {L : LinOrd} (x : L.carrier) (h : {x} = @Set.univ L.carrier) : Scattered_ind_prop L
| lex_sum (WO: LinOrd)
                  (hwo : WellFounded WO.str.lt
                       ∨ WellFounded (WO.str.swap).lt) ---
                  (f: WO.carrier → LinOrd)
                  (h : ∀ w, Scattered_ind_prop (f w))
                  (L : LinOrd)
                  (h : L ≃o ({carrier := Σₗ w, (f w).carrier,
                              str := Sigma.Lex.linearOrder} : LinOrd)): Scattered_ind_prop L

lemma ind_scat_of_empty (X : LinOrd.{u}) (empt : IsEmpty X) : Scattered_ind_prop.{u, u} X := by
  apply Scattered_ind_prop.lex_sum.{u,u} X (Or.inl (wellFounded_of_isEmpty X.str.lt)) (fun x => X)
  simp
  have : IsEmpty ({ carrier := Σₗ (w : ↑X), ↑X, str := Sigma.Lex.linearOrder } : LinOrd) := by
    apply IsEmpty.mk
    intro a; apply (@IsEmpty.exists_iff _ empt).mp
    use a.1
  use Equiv.equivOfIsEmpty _ _
  intro a; by_contra
  apply (@IsEmpty.exists_iff _ empt).mp
  use a


def IsCoinitial [LE α] (s : Set α) : Prop :=
  ∀ x, ∃ y ∈ s, y ≤ x

/-- every linear order has a well-founded cofinal subset -/
lemma exists_cof_WF_subset  {α : Type*} [LinearOrder α]:
  ∃ (A : Set α), IsCofinal A ∧ A.WellFoundedOn (· < ·) := by sorry -- proof in other file
                                                                   -- how do you import local files?

lemma exists_coi_RWF_subset  {α : Type*} [LinearOrder α]:
  ∃ (A : Set α), IsCoinitial A ∧ A.WellFoundedOn (· > ·) := by sorry -- need to adapt above proof

/-- a helper fxn for the next theorem: a lienar order α is well-ordered iff for any x, every set containing x is bounded below-/
private lemma WO_iff_lem {α : Type*} [r : LinearOrder α]:
  IsWellFounded α r.lt ↔ ∀ x, ∀ A : Set α, x ∈ A → ∃ lb ∈ A, ∀ a ∈ A, r.le lb a := by
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
theorem WO_iff_subsets_bdd_below {α : Type*} [r : LinearOrder α]:
  IsWellFounded α r.lt ↔ ∀ (A: Set α), A.Nonempty → ∃ lb ∈ A, ∀ x ∈ A, r.le lb x := by
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
lemma Well_Ord_Scattered (X : LinOrd) : WellFounded X.str.lt → IsScattered X := by
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
-- I didnt actually end up using this elsewhere in the file
lemma Rev_Scattered_of_Scattered (X : LinOrd) : IsScattered X →
  IsScattered {carrier := X.carrier, str := X.str.swap} := by
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
lemma swap_of_swap_elim {X : LinOrd}: (X.str.swap).swap = X.str := by
  ext
  rfl

lemma swap_of_swap_elim' {X : LinOrd}: X = {carrier := X, str := (X.str.swap).swap} := by
  exact rfl

lemma Rev_Well_Ord_Scattered (X : LinOrd) : WellFounded (X.str.swap).lt → IsScattered X := by
  intro h
  have p := Rev_Scattered_of_Scattered
    {carrier := X.carrier, str := X.str.swap}
    (Well_Ord_Scattered {carrier := X.carrier, str := X.str.swap} h)
  rw [<-swap_of_swap_elim] at p
  exact p

lemma Well_Ord_ind_scat_prop (X: LinOrd.{u}) (h : WellFounded X.str.lt): Scattered_ind_prop.{u,u} X := by
  let L : LinOrd := { carrier := Σₗ (w : ↑X), (fun w => (↑{ carrier := PUnit.{u+1}, str := inferInstance } : LinOrd)) w,
                      str := Sigma.Lex.linearOrder }
  have : X ≃o L := by
    let g : X → L := fun x => ⟨x, PUnit.unit⟩
    use {
      toFun := fun x => ⟨x, PUnit.unit⟩
      invFun := fun ⟨a, b⟩ => a
      left_inv := by intro a ; simp
      right_inv := by intro a ; constructor
    }
    intro a b
    simp
    rw [Sigma.Lex.le_def]
    constructor
    · intro h1
      rcases h1 with h1 | h1
      · simp at h1; exact le_of_lt h1
      · simp at h1;  exact le_of_eq h1
    · intro h1
      rcases lt_or_eq_of_le h1 with h1 | h1
      · left; simp; exact h1
      · right; use h1
  let p := (Scattered_ind_prop.lex_sum X (Or.inl h)
    (fun x => {carrier := PUnit, str := inferInstance})
    (fun x => by
      simp
      apply Scattered_ind_prop.base PUnit.unit
      exact Set.eq_univ_of_univ_subset fun ⦃a⦄ => congrFun rfl) X this)

  apply Scattered_ind_prop.lex_sum X (Or.inl h)
      (fun x => {carrier := PUnit, str := inferInstance})
      (fun x => by
        simp
        apply Scattered_ind_prop.base PUnit.unit
        exact Set.eq_univ_of_univ_subset fun ⦃a⦄ => congrFun rfl) X this

lemma subsingleton_lem (M : Type*) (a : M) (h : {a} = Set.univ) : Subsingleton M := by
  apply Set.subsingleton_of_univ_subsingleton
  apply ((Set.subsingleton_iff_singleton _).mpr (Eq.symm h))
  simp

def initial_segment_iso {L M : LinOrd} (f : L ≃o M) (a : L) :
  ({carrier := {x | x ≤ a}, str := inferInstance} : LinOrd) ≃o
    ({carrier := {x | x ≤ f a}, str := inferInstance} : LinOrd) := by
  use {
    toFun := fun x => ⟨f x, by simp ; exact x.2⟩
    invFun := fun x => ⟨f.symm x, by
      apply f.le_iff_le.mp
      simp
      exact x.2⟩
    left_inv := by intro x ; simp
    right_inv := by intro x ; simp
  }
  intro x y
  simp

lemma scat_ind_of_iso {L M : LinOrd.{u}} (f : M ≃o L) (h: Scattered_ind_prop.{u, u} M) :
  Scattered_ind_prop.{u, u} L := by
  rcases h with ⟨a, h1⟩ | ⟨N, WF_RWF, map, scat_map, _, g⟩
  · apply Scattered_ind_prop.base (f a)
    apply @Subsingleton.eq_univ_of_nonempty _ (@Equiv.subsingleton _ _ (f.symm).1 (subsingleton_lem M a h1))
    simp
  · apply Scattered_ind_prop.lex_sum.{u} N WF_RWF map scat_map L
    use OrderIso.trans f.symm g
    exact (OrderIso.trans f.symm g).map_rel_iff

-- (x, y] inductively scattered
def scat_int {L : LinOrd.{u}} (x y : L) : Prop :=
  let M : LinOrd.{u} := {carrier := {a | (x < a ∧ a ≤ y) ∨ (y < a ∧ a ≤ x)}, str := inferInstance}
  Scattered_ind_prop.{u, u} M

abbrev Two : LinOrd.{u_1} := {carrier := ULift.{u_1} (Fin 2), str := inferInstance}
lemma Two_def (x : Two) : x = 0 ∨ x = 1 := by
  match x with
  | 0 => left; rfl
  | 1 => right; rfl

lemma Two_le (x y : Two.{u}) (h : x < y) : x = 0 ∧ y = 1 := by
  rcases Two_def x, Two_def y with ⟨hx | hx, hy | hy⟩
  · by_contra; rw [hx, hy] at h ; exact (lt_irrefl 0) h
  · exact And.intro hx hy
  · by_contra; rw [hx, hy] at h ;
    have : (0 : Two.{u}) ≥ ULift.down.{u+1} 0 := by rfl
    apply not_lt_of_ge this
    exact lt_trans (Fin.zero_lt_one) h
  · by_contra; rw [hx, hy] at h ; exact (lt_irrefl 1) h

def g {L : LinOrd} (a : L) : Two → LinOrd
    | ⟨0, _⟩ => {carrier := {x | x < a}, str := inferInstance}
    | ⟨1, _⟩ => {carrier := {x | x ≥ a}, str := inferInstance}

def g' (M N: LinOrd) : Two → LinOrd
    | ⟨0, _⟩ => M
    | ⟨1, _⟩ => N

--set_option maxHeartbeats 1000000
-- one scattered order ontop of another scattered order is scattered
lemma scat_of_layered_scats (L M N : LinOrd.{u}) (h1 : Scattered_ind_prop.{u, u} M)
  (h2: Scattered_ind_prop.{u, u} N)
  (iso : L ≃o ({carrier := Σₗ (w : Two), ((g' M N) w), str := inferInstance } : LinOrd.{u})):
  Scattered_ind_prop.{u, u} L := by
  have : Finite Two := by simp [Fintype.finite]
  apply Scattered_ind_prop.lex_sum Two (Or.inl (Finite.to_wellFoundedLT).1) (g' M N)
  · intro w
    match w with
    | 0 => {simp [g']; exact h1}
    | 1 => {simp [g']; exact h2}
  · exact iso

-- a subset of a inductively scattered order is inductively scattered
lemma ind_scat_of_subset {L : LinOrd.{u}} (A : Set L) (h : Scattered_ind_prop.{u, u} L) :
  Scattered_ind_prop.{u, u} { carrier  := A, str := inferInstance} := by
  induction' h with M m hm WO WF_RWF f f_scat N Niso IH
  · -- base case
    have A_sub: A.Subsingleton := by
      apply @Set.subsingleton_of_subset_singleton _ m A
      rw [hm]; exact Set.subset_univ A
    rcases Classical.em (Set.Nonempty A) with nonempt | empt
    · rcases Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr
        (And.intro nonempt A_sub) with ⟨m', hm'⟩
      apply Scattered_ind_prop.base (⟨m', by rw[hm']; apply Set.mem_singleton⟩ : A)
      apply Set.eq_univ_of_image_val_eq
      simp; exact hm'.symm
    · apply ind_scat_of_empty
      simp [<-Mathlib.Tactic.PushNeg.ne_empty_eq_nonempty] at empt
      simp; exact empt
  · -- inductive step
    let B := Niso '' A
    have A_to_B : ({ carrier := A, str := inferInstance } : LinOrd) ≃o
                  ({ carrier := B, str := inferInstance } : LinOrd) := by
      simp [B]
      use {
        toFun := fun x => ⟨Niso x, by simp⟩
        invFun := fun x => ⟨Niso.symm x.1,
                            by
                            rcases (Set.mem_image Niso A x.1).mp x.2 with ⟨y, hy⟩
                            rw [<-hy.right]; simp; exact hy.left⟩
        left_inv := by intro x ; simp
        right_inv := by intro x ;simp
      }
      intro x y
      simp

    let g (w : WO): LinOrd := { carrier := {b | ⟨w, b⟩ ∈ B}, str := inferInstance }
    let Biso : B ≃o ({ carrier := Σₗ (w : WO), (g w), str := Sigma.Lex.linearOrder } : LinOrd) :=
      {
        toFun := fun x => ⟨x.1.1, ⟨x.1.2, by simp⟩⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        left_inv := by intro x ; simp
        right_inv := by intro x ; simp
        map_rel_iff' := by
          rintro ⟨⟨x, hx0⟩, hx⟩ ⟨⟨y, hy0⟩, hy⟩
          simp only [Equiv.coe_fn_mk, Sigma.Lex.le_def, Subtype.mk_le_mk]
          apply or_congr_right
          constructor <;> { rintro ⟨rfl, h⟩; use rfl, h }
      }
    apply scat_ind_of_iso (OrderIso.trans Biso.symm A_to_B.symm)
    apply Scattered_ind_prop.lex_sum WO WF_RWF g
    · intro w; exact IH w { x | ⟨w, x⟩ ∈ B }
    · rfl

lemma ind_scat_of_subset' {L : LinOrd.{u}} (A : Set L)
  (h : Scattered_ind_prop.{u, u} { carrier := A, str := inferInstance}) (B : Set L) (h1 : B ⊆ A) :
  Scattered_ind_prop.{u, u} { carrier := B, str := inferInstance} := by
  let C : Set ({ carrier := A, str := inferInstance} : LinOrd) := {x | x.1 ∈ B}
  apply @scat_ind_of_iso _ { carrier := C, str := inferInstance}
  · use {
      toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, h1 x.2⟩, x.2⟩
      left_inv := by intro x ; simp
      right_inv := by intro x ; simp
    }
    intro x y; simp
  apply ind_scat_of_subset _ h

lemma ind_scat_of_subset'' {L : LinOrd.{u}} (P : L → Prop) (T : L → Prop)
  (h : Scattered_ind_prop.{u, u} { carrier := {x | P x}, str := inferInstance}) :
  Scattered_ind_prop.{u, u} { carrier := {x : {x // T x} | P x}, str := inferInstance} := by
  apply @scat_ind_of_iso _ { carrier := {x | T x ∧ P x}, str := inferInstance}
  · use {
      toFun := fun x => ⟨⟨x.1, x.2.left⟩, x.2.right⟩
      invFun := fun x => ⟨x.1.1, And.intro x.1.2 x.2⟩
      left_inv := by intro _ ; simp
      right_inv := by intro _ ; simp
    }
    intro _ _; simp
  · apply ind_scat_of_subset' _ h _ ?_
    simp

lemma ind_scat_of_rev_ind_scat {L : LinOrd.{u}} (h : Scattered_ind_prop.{u,u} L) :
  Scattered_ind_prop.{u,u} {carrier := L.carrier , str := L.str.swap} := by
  induction' h with M m hm WO hWO f f_scat L Liso IH
  · apply Scattered_ind_prop.base
    exact hm
  · let map (w : ({ carrier := WO.carrier, str := WO.str.swap } : LinOrd)) : LinOrd :=
      { carrier := (f w), str := (f w).str.swap }
    let iso : ({ carrier := ↑L, str := L.str.swap } : LinOrd.{u}) ≃o
      ({ carrier := Σₗ (w : ({ carrier := WO.carrier, str := WO.str.swap } : LinOrd)), (map w),
         str := Sigma.Lex.linearOrder} : LinOrd.{u}) :=
      { toFun := fun x => Liso x
        invFun := fun x => Liso.symm x
        left_inv := by exact Liso.left_inv
        right_inv := by exact Liso.right_inv
        map_rel_iff' := by
          intro a b
          simp
          constructor
          · intro h
            change L.str.le b a
            simp [Sigma.Lex.le_def] at h
            rw [<-OrderIso.le_iff_le Liso]
            rcases h with h1 | h1
            · change WO.str.lt (Liso b).fst (Liso a).fst at h1
              left; exact h1
            · rcases h1 with ⟨h2, h3⟩
              change (f (Liso b).fst).str.le ((Liso b).snd) (h2 ▸ (Liso a).snd) at h3
              rw [Sigma.Lex.le_def]; right
              constructor
              · sorry
              · simp [h2]
          · sorry}

    apply Scattered_ind_prop.lex_sum { carrier := WO.carrier, str := WO.str.swap } ?_ map IH _ iso
    · rcases hWO with WO | RWO
      · right; apply WO
      · left;
        apply RWO

lemma scat_int_convex {L : LinOrd} (a b c : L) (h : a < b ∧ b < c) (h1 : scat_int a c): scat_int a b := by
  simp [scat_int]
  simp [scat_int] at h1
  have : { x | a < x ∧ x ≤ b ∨ b < x ∧ x ≤ a } ⊆ { x | a < x ∧ x ≤ c ∨ c < x ∧ x ≤ a } := by
    simp; intro x hx
    rcases hx with hx1 | hx1
    · left; exact And.intro hx1.left (le_trans hx1.right (le_of_lt h.right))
    · left; exact And.intro (lt_trans h.left hx1.left) (le_of_lt (lt_of_le_of_lt hx1.right (lt_trans h.left h.right)))
  exact ind_scat_of_subset' _ h1 _ this

-- scat_int is an equivalence relation
lemma scat_int_equiv {L : LinOrd}: Equivalence (@scat_int L) := by
  constructor
  · intro x
    apply (Well_Ord_ind_scat_prop
      { carrier := { x_1 // x < x_1 ∧ x_1 ≤ x ∨ x < x_1 ∧ x_1 ≤ x }, str := inferInstance })
    apply @wellFounded_of_isEmpty _ ?_
    by_contra nonempt
    simp at nonempt
    rcases nonempt with ⟨x_1, hx_1⟩
    exact lt_irrefl x (lt_of_lt_of_le hx_1.left hx_1.right)
  · intro x y h
    simp [scat_int] at h
    simp [scat_int]
    have : ({ carrier := { x_1 // x < x_1 ∧ x_1 ≤ y ∨ y < x_1 ∧ x_1 ≤ x },
              str := inferInstance } : LinOrd)
          = { carrier := { x_1 // y < x_1 ∧ x_1 ≤ x ∨ x < x_1 ∧ x_1 ≤ y },
              str := inferInstance } := by
      have (x_1): (x < x_1 ∧ x_1 ≤ y ∨ y < x_1 ∧ x_1 ≤ x) ↔
             (y < x_1 ∧ x_1 ≤ x ∨ x < x_1 ∧ x_1 ≤ y) := by
        constructor
        · intro h; exact Or.symm h
        · intro h; exact Or.symm h
      simp [this]
      sorry -- idk to show equivalence of infers...
    simpa [this] using h
  · intro x y z scat_xy scat_yz
    simp [ scat_int] at scat_xy
    simp [scat_int] at scat_yz
    rcases L.str.le_total x y, L.str.le_total y z with ⟨hxy | hxy, hyz | hyz⟩
    -- every case is either a subset or layered intervals
    · apply scat_of_layered_scats _ _ _ scat_xy scat_yz
      simp
      -- use {
      --   toFun := fun a =>
      --     if h : a ≤ y
      --     then ⟨0, ⟨a, by
      --                   left; constructor
      --                   · rcases a.2 with ha | ha
      --                     · exact ha.left
      --                     · by_contra h
      --                       exact propDecidable (x < ↑a)
      --                       apply not_le_of_lt ha.left
      --                       exact le_trans ha.right (le_trans hxy hyz)
      --                   · exact h⟩⟩
      --     else ⟨1, ⟨a, by sorry⟩⟩
      -- }
      sorry
    · sorry
    · sorry
    · sorry

--//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
-- Hausdorff's theorem
--//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

lemma dense_quotient {L : LinOrd} {a b : L} (h : ¬ scat_int a b) (hl : a < b) :
  ∃ c,¬ scat_int a c ∧ ¬ scat_int c b := by
  by_contra contra; simp at contra
  let A := { x | scat_int a x}
  let B := { x | scat_int x b}
  have all_A_or_B (x : L): x ∈ A ∪ B := by
   by_contra hc
   simp at hc
   exact hc.right (contra x hc.left)
  have empty_inter : ¬ Set.Nonempty (A ∩ B) := by
    by_contra contra
    rcases contra with ⟨x, hx⟩
    apply h
    rcases L.str.le_total a x , L.str.le_total b x with ⟨hax | hax, hab | hab⟩
    · sorry
    · sorry
    · sorry
    · sorry
  have A_lt_B {x y : L} (hx : x ∈ A) (hy : y ∈ B) : x < y := by

    sorry
  apply h
  simp [scat_int]
  apply scat_of_layered_scats _ {carrier := A, str := inferInstance}
                                {carrier := B, str := inferInstance}
  sorry -- need to show same as in single equivalence class case
  sorry
  sorry

lemma ind_scat_of_fin_seg_of_one_class {X : LinOrd.{u}} (X_scat : IsScattered X)
  (x : X) (one_class : ∀ x y : X, scat_int x y) : Scattered_ind_prop.{u,u} {carrier := {x_1 // x < x_1}, str := inferInstance} := by
  rcases @exists_cof_WF_subset {x_1 // x_1 > x} inferInstance with ⟨Cof, hCof⟩
  let S1 : LinOrd.{u} := {carrier := Cof, str := inferInstance}
  have : IsWellOrder S1.carrier S1.str.lt :=
      { toIsTrichotomous := instIsTrichotomousLt,
              toIsTrans := instIsTransLt,
              toIsWellFounded := by
              constructor
              simp [Set.WellFoundedOn] at hCof
              exact hCof.right }
  rcases Classical.em (NoMaxOrder ({carrier := {x_1 // x < x_1}, str := inferInstance} : LinOrd.{u})) with nomax | max
  · let J (a : S1) :=
      ({carrier := {z : {x_1 // x < x_1} | z ≤ a ∧ ∀ a' < a, a' < z}, str := inferInstance} : LinOrd.{u})

    have J_partition (z : {x_1 // x < x_1}) : ∃! (a : S1), z ≤ a ∧ ∀ a' < a, a' < z := by
      let above := {a : S1 | z ≤ a}
      have above_nonempt : above.Nonempty := by
        rw [Set.nonempty_def]
        rcases nomax.exists_gt z with ⟨z', hz'⟩
        rcases hCof.left z' with ⟨y, hy⟩
        use ⟨y, hy.left⟩
        exact le_of_lt (lt_of_lt_of_le hz' hy.right)

      rcases WO_iff_subsets_bdd_below.mp IsWellOrder.toIsWellFounded
              above above_nonempt with ⟨lb, hlb⟩
      use lb
      constructor
      · constructor
        · exact hlb.left
        · intro a ha
          by_contra contra
          apply not_le_of_lt ha
          exact hlb.right a (not_lt.mp contra)
      · intro y hy
        apply eq_of_le_of_le
        · by_contra contra;
          apply not_lt_of_le hlb.left
          exact hy.right lb (not_le.mp contra)
        · exact hlb.right y hy.left

    let Jiso : ({ carrier := { x_1 // x < x_1 }, str := inferInstance } : LinOrd) ≃o
                ({ carrier := Σₗ (w : ↑S1), ↑(J w), str := Sigma.Lex.linearOrder } : LinOrd) :=
      {
        toFun := fun x => ⟨choose (J_partition x), ⟨x,(choose_spec (J_partition x)).left⟩⟩
        invFun := fun x => x.2.1
        left_inv := by intro x; simp
        right_inv := by
          intro x
          simp
          apply Sigma.ext_iff.mpr
          constructor
          · simp
            have : choose (J_partition x.2) = x.1 := by
              apply Eq.symm
              apply (choose_spec (J_partition x.2)).right _ x.2.2
            sorry -- cannot apply above because in the goal "J_partition x.2"
                  -- is cast to another type
          · simp
            have : HEq x.2.1 x.2 := by sorry
            apply HEq.trans _ this
            simp
            sorry -- should be trivial

        map_rel_iff' := by
          intro x y
          simp
          rw [Sigma.Lex.le_def]
          constructor
          · intro h
            rcases h with h | h
            · simp at h
              apply le_of_lt
              have (a b) (h1 : x ≤ a) (h1 : b ≤ y) : a < b → x < y := by sorry
              apply this _ _ _ _ h
              · --simp [(choose_spec _).left]
                sorry
              · sorry
            · sorry
          · sorry
      }

    apply Scattered_ind_prop.lex_sum.{u,u} S1
      ?_ J ?_ _
    · sorry
    · left; exact wellFounded_lt
    · intro w
      simp [J]
      specialize one_class x w
      simp [scat_int] at one_class

      let p :=  ind_scat_of_subset'' ((fun x_1 => x < x_1 ∧ x_1 ≤ ↑↑w ∨ ↑↑w < x_1 ∧ x_1 ≤ x))
                                      (fun x_1 => x < x_1 ) one_class
      apply @ind_scat_of_subset' {carrier := { x_2 // (fun x_1 => x < x_1) x_2 },
                                  str := inferInstance} _ p
                                  { x_1 | x_1 ≤ ↑w ∧ ∀ a' < w, ↑a' < x_1 }
      simp; intro a ha haw h
      left; exact And.intro ha haw

  · rcases isEmpty_or_nonempty ({carrier := { x_1 // x < x_1 },
                                  str := inferInstance} : LinOrd) with empt | nonempt
    · exact ind_scat_of_empty _ empt
    have : ∃ a : ({carrier := {x_1 // x < x_1}, str := inferInstance} : LinOrd),
            ∀ b, b ≤ a := by
      by_contra h ; simp at h
      apply max
      constructor
      intro a
      rcases h a a.2 with ⟨b ,hb⟩
      use ⟨b, hb.left⟩ ; exact hb.right
    rcases this with ⟨m, hm⟩
    apply scat_ind_of_iso ?_ (one_class x m)
    use {
      toFun := fun y =>
        ⟨y.1, by
              rcases y.2 with h | h
              · exact h.left
              · by_contra;
                apply not_lt_of_le h.right
                rcases nonempt with ⟨n⟩
                exact lt_trans (lt_of_lt_of_le n.2 (hm n)) h.left⟩
      invFun := fun y =>
        ⟨y.1 , Or.inl (And.intro y.2 (hm y))⟩
      left_inv := by intro x ; simp
      right_inv := by intro x ; simp
    }
    intro a b
    simp

theorem Hausdorff_Scattered_Orders (X : LinOrd.{u}): IsScattered X ↔ Scattered_ind_prop.{u,u} X := by
  constructor
  · intro X_scat
    rcases Classical.em (Nonempty X) with nonempt | empt
    rcases Classical.em (∀ x y : X, scat_int x y) with one_class | mult_class
    · rcases Classical.exists_true_of_nonempty nonempt with ⟨x⟩
      have part1 : Scattered_ind_prop.{u,u} {carrier := {x_1 // x < x_1}, str := inferInstance} := by
        exact @ind_scat_of_fin_seg_of_one_class _ X_scat x one_class
      have part2 : Scattered_ind_prop.{u,u} {carrier := {x_1 // x_1 < x}, str := inferInstance} := by
        rw [@swap_of_swap_elim' { carrier := { x_1 // x_1 < x }, str := inferInstance } ]
        let X' : LinOrd := { carrier := X.carrier, str := X.str.swap}
        have X_eq: X.carrier = X'.carrier := by exact rfl
        have : Scattered_ind_prop { carrier := { x_1 // x_1 < x },
                                    str := (LinearOrder.swap { x_1 // x_1 < x } inferInstance) } := by
          let iso : @OrderIso ({ carrier := { x_1 // x_1 < x }, str := LinearOrder.swap { x_1 // x_1 < x } inferInstance } : LinOrd)
            ({ carrier := { x_1 : X' // @LT.lt X' Preorder.toLT (X_eq ▸ x) x_1}, str := inferInstance } : LinOrd) :=
            {
              toFun := fun y => ⟨y.1, y.2⟩
              invFun := fun y => ⟨y.1, y.2⟩
              left_inv := by intro _; simp
              right_inv := by intro _; simp
              map_rel_iff' := by
                intro a b
                simp
                constructor
                · intro h
                  --change ({ x_1 // x_1 < x } inferInstance : LinearOrder).le a b
                  -- change ({ carrier := { x_1 // x_1 < x }, str := LinearOrder.swap { x_1 // x_1 < x } inferInstance } : LinOrd).str.le b a
                  -- change (LinearOrder.swap { x_1 // x_1 < x } inferInstance).le a b
                  sorry
                · sorry

            }
        exact ind_scat_of_rev_ind_scat this


      sorry
    · sorry
    simp at empt
    exact ind_scat_of_empty X empt

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

        let T := (ind (f a)).1
        have g_help (x : B) : (ind (x.1.1.1)).1 = (ind (f a)).1:= by rw [fix_fst]
        have g_help' (x : B) : (ind (x.1.1.1)) = (ind (f a)) := by rw [fix_fst]
        have g_help_2 (x y : B) : (ind (x.1.1.1)).1 = (ind (y.1.1.1)).1 := by rw [g_help x, g_help y]

        -- subst h -- h proves type equality

        let g : B ↪o (ind (f a)).1 := {
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
              rintro ⟨⟨x, hx0⟩, hx⟩ ⟨⟨y, hy0⟩, hy⟩
              simp only [Equiv.coe_fn_mk, Sigma.Lex.le_def, Subtype.mk_le_mk]
              simp
              constructor
              · intro h
                right; use (Eq.trans (fix_fst ⟨⟨x, hx0⟩, hx⟩) (fix_fst ⟨⟨y, hy0⟩, hy⟩).symm)
                have (indfa) (x_type) (x : ind x_type) (y_type) (y : ind y_type)
                     (hx : ind x_type = indfa) (hy : ind y_type = indfa)
                     (hxy : x_type =  y_type)
                     (h : hx ▸ x ≤ hy ▸ y): hxy ▸ x ≤ y := by
                  subst x_type
                  subst indfa
                  simp at h
                  exact h
                apply this (ind (f a)) _ x.2 _ y.2 _  _ _ _
                · let p := g_help' ⟨⟨x, hx0⟩, hx⟩
                  simp at p
                  exact p
                · let p := g_help' ⟨⟨y, hy0⟩, hy⟩
                  simp at p
                  exact p
                · --exact h
                  sorry
              · sorry

              -- intro x y
              -- simp
              -- constructor
              -- · intro h
              --   have : x.1.1 ≤ y.1.1 := by
              --     rw [Sigma.Lex.le_def]
              --     apply Or.inr
              --     simp [fix_fst x, fix_fst y]
              --     --subst (g_help y)
              --     have :  g_help y ▸ (g_help x ▸ (x.1.1).snd) ≤ g_help y ▸ (g_help y ▸ (y.1.1).snd) := by sorry

              --     generalize (ind (f a)).1 = p
              --     have : p = (ind (x.1.1.1)).1 := by sorry
              --     have : p = (ind (y.1.1.1)).1 := by sorry
              --     subst p
              --     revert h
              --     sorry

              --   apply this
              -- · intro h
              --   have : x.1.1 ≤ y.1.1 := by exact h
              --   rw [Sigma.Lex.le_def] at this
              --   simp [fix_fst x, fix_fst y] at this
              --   sorry
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
