import Mathlib.Tactic
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Order.Category.LinOrd
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sigma.Lex
import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Batteries.Logic
import Hausdorff.WO_cofinal_subset
import Hausdorff.IsScattered
import Hausdorff.Isomorphisms

open Classical
universe u

/-- Hausdorff's recursive definition of scattered -/
inductive Scattered_ind_prop : LinOrd → Prop
| base {L : LinOrd} (x : L.carrier) (h : {x} = @Set.univ L.carrier) : Scattered_ind_prop L
| lex_sum (WO: LinOrd)
                  (hwo : WellFounded WO.str.lt
                       ∨ WellFounded (WO.str.swap).lt) ---
                  (f: WO.carrier → LinOrd)
                  (h : ∀ w, Scattered_ind_prop (f w))
                  (L : LinOrd)
                  (h : L ≃o ({carrier := Σₗ w, (f w).carrier,
                              str := Sigma.Lex.linearOrder} : LinOrd)): Scattered_ind_prop L

lemma iscat_of_empty (X : LinOrd.{u}) (empt : IsEmpty X) : Scattered_ind_prop.{u, u} X := by
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

def IsCoinitial {α : Type*} [LE α] (s : Set α) : Prop :=
  ∀ x, ∃ y ∈ s, y ≤ x

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

lemma iscat_of_well_founded (X: LinOrd.{u}) (h : WellFounded X.str.lt): Scattered_ind_prop.{u,u} X := by
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

-- lemma iscat_of_singleton {α : LinOrd.{u}} (x : α) :
--   Scattered_ind_prop.{u} {carrier := ({x} : Set α), str := inferInstance} := by
  -- apply iscat_of_well_founded _
  --   (@Finite.to_wellFoundedLT
  --     ({ carrier := ({x} : Set α), str := inferInstance } : LinOrd)
  --     (Set.finite_singleton x)).1

lemma subsingleton_lem (M : Type*) (a : M) (h : {a} = Set.univ) : Subsingleton M := by
  apply Set.subsingleton_of_univ_subsingleton
  apply ((Set.subsingleton_iff_singleton _).mpr (Eq.symm h))
  simp

lemma iscat_of_iso {L M : LinOrd.{u}} (f : @OrderIso M L (M.str.toLE) (L.str.toLE)) (h: Scattered_ind_prop.{u, u} M) :
  Scattered_ind_prop.{u, u} L := by
  rcases h with ⟨a, h1⟩ | ⟨N, WF_RWF, map, scat_map, _, g⟩
  · apply Scattered_ind_prop.base (f a)
    apply @Subsingleton.eq_univ_of_nonempty _ (@Equiv.subsingleton _ _ (f.symm).1 (subsingleton_lem M a h1))
    simp
  · apply Scattered_ind_prop.lex_sum.{u} N WF_RWF map scat_map L
    use OrderIso.trans f.symm g
    exact (OrderIso.trans f.symm g).map_rel_iff

--set_option maxHeartbeats 1000000
-- one scattered order ontop of another scattered order is scattered
lemma iscat_of_layered_iscats (L M N : LinOrd.{u}) (h1 : Scattered_ind_prop.{u, u} M)
  (h2: Scattered_ind_prop.{u, u} N)
  (iso : L ≃o ({carrier := Σₗ (w : Two), ((g' M N) w), str := inferInstance } : LinOrd.{u})):
  Scattered_ind_prop.{u, u} L := by
  apply Scattered_ind_prop.lex_sum Two.L (Or.inl (@Finite.to_wellFoundedLT _ Two.finite).1) (g' M N)
  · intro w
    match w with
    | Two.zero => {simp [g']; exact h1}
    | Two.one => {simp [g']; exact h2}
  · exact iso

-- a subset of a inductively scattered order is inductively scattered
lemma iscat_of_subset {L : LinOrd.{u}} (A : Set L) (h : Scattered_ind_prop.{u, u} L) :
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
    · apply iscat_of_empty
      simp
      exact Set.not_nonempty_iff_eq_empty.mp empt
  · -- inductive step
    let B := Niso '' A
    let A_to_B : ({ carrier := A, str := inferInstance } : LinOrd) ≃o
                  ({ carrier := B, str := inferInstance } : LinOrd) := OrderIso_restrict Niso A

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
    apply iscat_of_iso (OrderIso.trans Biso.symm (A_to_B).symm)
    apply Scattered_ind_prop.lex_sum WO WF_RWF g
    · intro w; exact IH w { x | ⟨w, x⟩ ∈ B }
    · rfl

lemma iscat_of_subset' {L : LinOrd.{u}} (A : Set L)
  (h : Scattered_ind_prop.{u, u} { carrier := A, str := inferInstance}) (B : Set L) (h1 : B ⊆ A) :
  Scattered_ind_prop.{u, u} { carrier := B, str := inferInstance} := by
  let C : Set ({ carrier := A, str := inferInstance} : LinOrd) := {x | x.1 ∈ B}
  apply @iscat_of_iso _ { carrier := C, str := inferInstance}
  use subtype_iso A B h1
  intro a b
  simp
  apply iscat_of_subset _ h

lemma iscat_of_subset'' {L : LinOrd.{u}} (P : L → Prop) (T : L → Prop)
  (h : Scattered_ind_prop.{u, u} { carrier := {x | P x}, str := inferInstance}) :
  Scattered_ind_prop.{u, u} { carrier := {x : {x // T x} | P x}, str := inferInstance} := by
  apply @iscat_of_iso _ { carrier := {x | T x ∧ P x}, str := inferInstance}
  · use {
      toFun := fun x => ⟨⟨x.1, x.2.left⟩, x.2.right⟩
      invFun := fun x => ⟨x.1.1, And.intro x.1.2 x.2⟩
      left_inv := by intro _ ; simp
      right_inv := by intro _ ; simp
    }
    intro _ _; simp
  · apply iscat_of_subset' _ h _ ?_
    simp

lemma iscat_of_rev_iscat {L : LinOrd.{u}} (h : Scattered_ind_prop.{u,u} L) :
   Scattered_ind_prop.{u,u} {carrier := L.carrier , str := L.str.swap} := by
  induction' h with M m hm WO hWO f f_scat L Liso IH
  · apply Scattered_ind_prop.base
    exact hm
  · let map (w : ({ carrier := WO.carrier, str := WO.str.swap } : LinOrd)) : LinOrd :=
      { carrier := (f w), str := (f w).str.swap }
    let iso := Sigma_swap_alt_def f
    let p := (swap_iso_of_iso Liso)
    sorry
    -- apply iscat_of_iso p.symm
    -- apply Scattered_ind_prop.lex_sum { carrier := WO.carrier, str := WO.str.swap } ?_ map IH _ iso
    -- · rcases hWO with WO | RWO
    --   · right; apply WO
    --   · left;
    --     apply RWO

-- (x, y] inductively scattered
def iscat_int {L : LinOrd.{u}} (x y : L) : Prop :=
  let M : LinOrd.{u} := LinOrd.mk {a | (x < a ∧ a ≤ y) ∨ (y < a ∧ a ≤ x)}
  Scattered_ind_prop.{u, u} M

lemma iscat_int_convex {L : LinOrd} (a b c : L) (h : a < b ∧ b < c) (h1 : iscat_int a c): iscat_int a b := by
  simp [iscat_int]
  simp [iscat_int] at h1
  have : { x | a < x ∧ x ≤ b ∨ b < x ∧ x ≤ a } ⊆ { x | a < x ∧ x ≤ c ∨ c < x ∧ x ≤ a } := by
    simp; intro x hx
    rcases hx with hx1 | hx1
    · left; exact And.intro hx1.left (le_trans hx1.right (le_of_lt h.right))
    · left; exact And.intro (lt_trans h.left hx1.left) (le_of_lt (lt_of_le_of_lt hx1.right (lt_trans h.left h.right)))
  exact iscat_of_subset' _ h1 _ this

lemma scat_int_layered_case {L : LinOrd} {a b c : L} (hab : a ≤ b) (hbc : b ≤ c) (scat_ab : iscat_int a b)
  (scat_bc : iscat_int b c) : iscat_int a c := by
  apply iscat_of_layered_iscats _ _ _ scat_ab scat_bc
  apply Two_iso_helper
  · apply Set.eq_of_subset_of_subset
    · rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
      · rcases le_or_gt a b with hy | hy
        · left; left; constructor <;> order
        · right; left; constructor <;> order
      · by_contra; order
    · rintro a (⟨⟨ha1, ha2⟩ | ⟨ha1, ha2⟩⟩ | ⟨⟨ha1, ha2⟩ | ⟨ha1, ha2⟩⟩)
      <;> (left; constructor <;> order)
  · intro c hc b hb
    rcases hb, hc with ⟨⟨hb1, hb2⟩ | ⟨hb1, hb2⟩, ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩⟩
    <;> order

lemma LinearOrder_subtype_HEq {L : LinOrd} {P Q : L → Prop} (h : P = Q): HEq (Subtype.instLinearOrder fun x_1 ↦ P x_1)
  (Subtype.instLinearOrder fun x_1 ↦ Q x_1) := by
  subst h
  rfl

lemma scat_int_symm {L : LinOrd} : ∀ {x y : L}, iscat_int x y → iscat_int y x := by
  intro x y h
  simp [iscat_int] at h
  simp [iscat_int]
  have : LinOrd.mk { x_1 // x < x_1 ∧ x_1 ≤ y ∨ y < x_1 ∧ x_1 ≤ x }
        = LinOrd.mk { x_1 // y < x_1 ∧ x_1 ≤ x ∨ x < x_1 ∧ x_1 ≤ y } := by
    have : (fun x_1 => x < x_1 ∧ x_1 ≤ y ∨ y < x_1 ∧ x_1 ≤ x) =
            (fun x_1 => y < x_1 ∧ x_1 ≤ x ∨ x < x_1 ∧ x_1 ≤ y) := by
      refine Set.setOf_inj.mp ?_ ; apply Set.eq_of_subset_of_subset
      <;> (rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩) ;
           right; constructor <;> order ;
           left; constructor <;> order)
    simp [this]
    exact LinearOrder_subtype_HEq this
  simpa [this] using h

-- scat_int is an equivalence relation
lemma scat_int_equiv {L : LinOrd}: Equivalence (@iscat_int L) := by
  constructor
  · intro x
    apply (iscat_of_well_founded
      { carrier := { x_1 // x < x_1 ∧ x_1 ≤ x ∨ x < x_1 ∧ x_1 ≤ x }, str := inferInstance })
    apply @wellFounded_of_isEmpty _ ?_
    by_contra nonempt
    simp at nonempt
    rcases nonempt with ⟨x_1, hx_1⟩
    exact lt_irrefl x (lt_of_lt_of_le hx_1.left hx_1.right)
  · exact scat_int_symm
  · intro x y z scat_xy scat_yz
    rcases L.str.le_total x y, L.str.le_total y z with ⟨hxy | hxy, hyz | hyz⟩
    -- every case is either a subset or layered intervals
    · exact scat_int_layered_case hxy hyz scat_xy scat_yz
    · simp[iscat_int]
      rcases (le_or_gt x z) with hxz | hz
      · apply iscat_of_subset' _ scat_xy
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (left; constructor <;> order)
      · apply iscat_of_subset' _ scat_yz
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (right; constructor <;> order)
    · simp[iscat_int]
      rcases (le_or_gt x z) with hxz | hz
      · apply iscat_of_subset' _ scat_yz
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (left; constructor <;> order)
      · apply iscat_of_subset' _ scat_xy
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (right; constructor <;> order)
    · exact scat_int_symm (scat_int_layered_case hyz hxy
                          (scat_int_symm scat_yz) (scat_int_symm scat_xy))

lemma iscat_to_closed_interval {L : LinOrd.{u}} (x y : L) (h : iscat_int x y):
  Scattered_ind_prop.{u, u} (LinOrd.mk {a | (x ≤ a ∧ a ≤ y) ∨ (y ≤ a ∧ a ≤ x)}) := by
  simp
  have helper {L : LinOrd.{u}} (x y : L) (h : iscat_int x y) (hxy : x ≤ y):
  Scattered_ind_prop.{u, u} (LinOrd.mk {a | (x ≤ a ∧ a ≤ y) ∨ (y ≤ a ∧ a ≤ x)}) := by
    · apply iscat_of_layered_iscats _ (LinOrd.mk ({x} : Set L))
                                      (LinOrd.mk {a | x < a ∧ a ≤ y})
      · apply iscat_of_well_founded
        exact wellFounded_lt
      · simp [iscat_int] at h
        apply iscat_of_iso _ h
        exact {
          toFun := fun a => ⟨a.1,
            by
              rcases a.2 with h | ⟨h1, h2⟩
              · exact h
              · by_contra
                apply not_lt_of_le hxy
                exact lt_of_lt_of_le h1 h2⟩
          invFun := fun a => ⟨a.1, Or.inl a.2⟩
          left_inv := by intro _; simp
          right_inv := by intro _; simp
          map_rel_iff' := by intro _ _; simp
        }
      · apply (Two_iso_helper _ {x} {a | x < a ∧ a ≤ y} _ _)
        · ext a
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            <;> (simp [or_iff_not_imp_left];
                  intro h;
                  constructor <;> order)
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            <;> (left;
                  constructor <;> order)
        · rintro c hc b ⟨hb1, hb2⟩
          exact hc.left
  rcases lt_or_le x y with hxy | hxy
  · exact helper x y h (le_of_lt hxy)
  · apply iscat_of_iso _ (helper y x (Equivalence.symm scat_int_equiv h) hxy)
    exact {
      toFun := fun a => ⟨a.1,
        by
          rcases a.2 with h | h
          · right; exact h
          · left; exact h⟩
      invFun := fun a => ⟨a.1,
        by
          rcases a.2 with h | h
          · right; exact h
          · left; exact h⟩
      left_inv := by intro _; simp
      right_inv := by intro _; simp
      map_rel_iff' := by intro _; simp
    }

lemma isact_of_interval_flip {L : LinOrd.{u}} (x y : L) (h : iscat_int x y):
  Scattered_ind_prop.{u, u} (LinOrd.mk {a | (x ≤ a ∧ a < y) ∨ (y ≤ a ∧ a < x)}) := by
  simp [iscat_int] at h
  apply iscat_of_subset' _ (iscat_to_closed_interval x y h)
  rintro a (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · left; exact And.intro h1 (le_of_lt h2)
  · right; exact And.intro h1 (le_of_lt h2)
--//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
-- Hausdorff's theorem
--//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

-- lemma dense_quotient {L : LinOrd} {a b : L} (h : ¬ scat_int a b) (hl : a < b) :
--   ∃ c,¬ scat_int a c ∧ ¬ scat_int c b := by
--   by_contra contra; simp at contra
--   let A := { x | scat_int a x}
--   let B := { x | scat_int x b}
--   have all_A_or_B (x : L): x ∈ A ∪ B := by
--    by_contra hc
--    simp at hc
--    exact hc.right (contra x hc.left)
--   have empty_inter : ¬ Set.Nonempty (A ∩ B) := by
--     by_contra contra
--     rcases contra with ⟨x, hx⟩
--     apply h
--     rcases L.str.le_total a x , L.str.le_total b x with ⟨hax | hax, hab | hab⟩
--     · sorry
--     · sorry
--     · sorry
--     · sorry
--   have A_lt_B {x y : L} (hx : x ∈ A) (hy : y ∈ B) : x < y := by

--     sorry
--   apply h
--   simp [scat_int]
--   apply scat_of_layered_scats _ {carrier := A, str := inferInstance}
--                                 {carrier := B, str := inferInstance}
--   sorry -- need to show same as in single equivalence class case
--   sorry
--   sorry

lemma ind_scat_of_fin_seg_of_one_class {X : LinOrd.{u}}
  (x : X) (one_class : ∀ x y : X, iscat_int x y) : Scattered_ind_prop.{u,u} {carrier := {x_1 // x < x_1}, str := inferInstance} := by
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

    let j (a : S1) := {z : {x_1 // x < x_1} | z ≤ a ∧ ∀ a' < a, a' < z}

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
                ({ carrier := Σₗ (w : ↑S1), ↑(J w), str := Sigma.Lex.linearOrder } : LinOrd) := by
      apply @iso_of_sigma_partition (LinOrd.mk {x_1 // x < x_1}) S1 j J_partition
      · intro a b hab c hc d hd
        exact lt_of_le_of_lt hc.left (hd.right a hab)

    apply Scattered_ind_prop.lex_sum.{u,u} S1
      ?_ J ?_ _ Jiso
    · left; exact wellFounded_lt
    · intro w
      simp [J]
      specialize one_class x w
      simp [iscat_int] at one_class

      let p :=  iscat_of_subset'' ((fun x_1 => x < x_1 ∧ x_1 ≤ ↑↑w ∨ ↑↑w < x_1 ∧ x_1 ≤ x))
                                      (fun x_1 => x < x_1 ) one_class
      apply @iscat_of_subset' {carrier := { x_2 // (fun x_1 => x < x_1) x_2 },
                                  str := inferInstance} _ p
                                  { x_1 | x_1 ≤ ↑w ∧ ∀ a' < w, ↑a' < x_1 }
      simp; intro a ha haw h
      left; exact And.intro ha haw

  · rcases isEmpty_or_nonempty ({carrier := { x_1 // x < x_1 },
                                  str := inferInstance} : LinOrd) with empt | nonempt
    · exact iscat_of_empty _ empt
    have : ∃ a : ({carrier := {x_1 // x < x_1}, str := inferInstance} : LinOrd),
            ∀ b, b ≤ a := by
      by_contra h ; simp at h
      apply max
      constructor
      intro a
      rcases h a a.2 with ⟨b ,hb⟩
      use ⟨b, hb.left⟩ ; exact hb.right
    rcases this with ⟨m, hm⟩
    apply iscat_of_iso ?_ (one_class x m)
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
    rcases Classical.em (∀ x y : X, iscat_int x y) with one_class | mult_class
    · rcases Classical.exists_true_of_nonempty nonempt with ⟨x⟩
      have part1 : Scattered_ind_prop.{u,u} {carrier := {x_1 // x < x_1}, str := inferInstance} := by
        exact @ind_scat_of_fin_seg_of_one_class _ x one_class
      have part2 : Scattered_ind_prop.{u,u} {carrier := {x_1 // x_1 < x}, str := inferInstance} := by
        let X' : LinOrd := { carrier := X.carrier, str := X.str.swap}
        have X_eq: X.carrier = X'.carrier := by exact rfl

        let L : LinOrd := { carrier := { x_1 // x_1 < x }, str := LinearOrder.swap { x_1 // x_1 < x } inferInstance }
        let M : LinOrd := { carrier := { x_1 : X' // @LT.lt X' Preorder.toLT (X_eq ▸ x) x_1}, str := inferInstance }
        rw [@swap_of_swap_elim' { carrier := { x_1 // x_1 < x }, str := inferInstance } ]

        have : Scattered_ind_prop L := by
          let iso : @OrderIso L M L.str.toLE M.str.toLE := by
            use {
            toFun := fun y => y
            invFun := fun y => y
            left_inv := by intro x; trivial
            right_inv := by intro x; trivial
            }
            intro x y
            simp [X']

          apply iscat_of_iso iso
          apply @ind_scat_of_fin_seg_of_one_class X' (X_eq ▸ x)
          intro x y

          let p := iscat_of_rev_iscat (@isact_of_interval_flip X y x (one_class y x))
          apply iscat_of_iso _ p
          have : { x_1 : X | @LE.le (↑X) Preorder.toLE y x_1 ∧ x_1 < x ∨ @LE.le (↑X) Preorder.toLE x x_1 ∧ x_1 < y }
            = { x_1 : X' | x < x_1 ∧ @LE.le (↑X') Preorder.toLE x_1 y ∨ y < x_1 ∧ x_1 ≤ x } := by
            ext a
            have h1 : (@LE.le (↑X) Preorder.toLE y a ∧ a < x)
                    = (x < a ∧ @LE.le (↑X') Preorder.toLE a y) := by
              simp; constructor
              <;> (rintro ⟨h1, h2⟩ ; exact And.intro h2 h1)
            have h2 : (@LE.le (↑X) Preorder.toLE x a ∧ a < y)
                    = (y < a ∧ @LE.le (↑X') Preorder.toLE a x) := by
              simp; constructor
              <;> (rintro ⟨h1, h2⟩ ; exact And.intro h2 h1)
            simp [h1, h2]
            rfl
          exact {
            toFun := fun x => ⟨x.1, subset_of_eq this x.2⟩
            invFun := fun x => ⟨x.1, subset_of_eq this.symm x.2⟩
            left_inv := by intro _; simp
            right_inv := by intro _; simp
            map_rel_iff' := by
              rintro ⟨x1, x2⟩ ⟨y1, y2⟩
              constructor
              · intro h
                simp at h
                apply h
              · intro h
                simp
                apply h
          }
        exact iscat_of_rev_iscat this

      let j : Three.L.{u} → Set X
        | Three.zero => { x_1 | x_1 < x }
        | Three.one => {x}
        | Three.two =>  { x_1 | x < x_1 }

      · have : Finite Three.L := Three.finite
        apply Scattered_ind_prop.lex_sum Three.L (Or.inl (Finite.to_wellFoundedLT).1)
          (fun w => LinOrd.mk (j w))
        · intro w
          cases w
          · exact part2
          · simp [j]
            apply iscat_of_well_founded
            exact (@Finite.to_wellFoundedLT
              ({ carrier := ({x} : Set X), str := inferInstance } : LinOrd)
              (Set.finite_singleton x)).1
          · exact part1
        · apply (iso_of_sigma_partition j _ _)
          · intro z
            apply existsUnique_of_exists_of_unique
            · rcases ne_or_eq z x with h | h
              · rcases lt_or_gt_of_ne h with h' | h'
                · use Three.zero; simp [j, h']
                · use Three.two; simp [j, h']
              · use Three.one; simp [j, h]
            · intro y1 y2 hy1 hy2 -- way cleaner with other construction
              cases y1 <;>
                (cases y2 <;>
                  (simp [j] at hy1 ; simp [j] at hy2; order))
          · intro y1 y2 hy a ha b hb
            cases y1 <;>
              (simp [j] at ha ; cases y2 <;>
                (first | simp [j] at hb; order
                       | by_contra; apply not_le_of_lt hy ; trivial))
    · sorry
    simp at empt
    exact iscat_of_empty X empt

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
      apply scat_of_iso_to_scat L { carrier := Σₗ (w : ↑lo_lex), ↑(ind w), str := Sigma.Lex.linearOrder } Liso

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
                  exact le_of_eq h2 }

        have lo_scat: IsScattered lo_lex := by
          rcases WF_RWF with WF | RWF
          · apply scat_of_well_founded lo_lex WF
          · apply scat_of_rev_well_founded lo_lex RWF

        apply not_nonempty_iff.mpr ((scat_iff_not_embeds_Q lo_lex).mp lo_scat)
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
          rcases props with ⟨_, _, _, _, _⟩
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

        let B' := (fun b => b.1) '' B
        let g' : B' ↪o (ind (f a)) :=
          embed_dlexord (f a) B'
          (by
            rintro b1 ⟨b2, hb⟩
            rw [<-hb.right]
            exact fix_fst ⟨b2, hb.left⟩)
        let g_help : B ↪o B' :=
          { toFun := fun b => ⟨b.1, by simp [B']⟩
            inj' := by
              intro a b hab
              simp at hab
              ext
              exact hab
            map_rel_iff' := by
              intro a b
              simp }

        let g : B ↪o (ind (f a)) := OrderEmbedding_comp g' g_help

        -- compose the isomorphisms/ embeddings
        rcases props with ⟨p1, p2, p3, p4, p5⟩
        rcases Order.iso_of_countable_dense ℚ A with ⟨h⟩
        have h' := OrderIso.toOrderEmbedding h
        rcases A_iso_B with ⟨i⟩
        have i' :=   OrderIso.toOrderEmbedding i
        have F := OrderEmbedding_comp g (OrderEmbedding_comp i' h')
        apply isEmpty_iff.mp
        apply (scat_iff_not_embeds_Q (ind (f a))).mp (is_scat_f (f a))
        exact F
