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

lemma scat_of_3_layered_scats (L K M N : LinOrd.{u}) (h1 : Scattered_ind_prop.{u, u} K)
  (h2: Scattered_ind_prop.{u, u} M) (h3: Scattered_ind_prop.{u, u} N)
  (iso : L ≃o ({carrier := Σₗ (w : Three), ((g'' K M N) w), str := inferInstance } : LinOrd.{u})):
  Scattered_ind_prop.{u, u} L := by
  have : Finite Three := by simp [Fintype.finite]
  apply Scattered_ind_prop.lex_sum Three (Or.inl (Finite.to_wellFoundedLT).1) (g'' K M N)
  · intro w
    match w with
    | 0 => {simp [g'']; exact h1}
    | 1 => {simp [g'']; exact h2}
    | 2 => {simp [g'']; exact h3}
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
    apply scat_ind_of_iso (OrderIso.trans Biso.symm (A_to_B).symm)
    apply Scattered_ind_prop.lex_sum WO WF_RWF g
    · intro w; exact IH w { x | ⟨w, x⟩ ∈ B }
    · rfl

lemma ind_scat_of_subset' {L : LinOrd.{u}} (A : Set L)
  (h : Scattered_ind_prop.{u, u} { carrier := A, str := inferInstance}) (B : Set L) (h1 : B ⊆ A) :
  Scattered_ind_prop.{u, u} { carrier := B, str := inferInstance} := by
  let C : Set ({ carrier := A, str := inferInstance} : LinOrd) := {x | x.1 ∈ B}
  apply @scat_ind_of_iso _ { carrier := C, str := inferInstance}
  use subtype_iso A B h1
  intro a b
  simp
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
    let iso := Sigma_swap_alt_def f

    apply scat_ind_of_iso (swap_iso_of_iso Liso).symm
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
      apply Two_iso_helper
      · apply Set.eq_of_subset_of_subset
        · intro a ha
          rcases ha with ha | ha
          · rcases le_or_gt a y with hy | hy
            · left; left; exact And.intro ha.left hy
            · right; left; exact And.intro (gt_iff_lt.mp hy) ha.right
          · by_contra
            apply not_le_of_lt (lt_of_lt_of_le ha.left ha.right)
            exact le_trans hxy hyz
        · intro a ha
          rcases ha with ⟨ha | ha⟩ | ⟨ha | ha⟩
          · left; exact And.intro ha.left (le_trans ha.right hyz)
          · by_contra
            apply not_le_of_lt (lt_of_lt_of_le ha.left ha.right)
            exact hxy
          · left; exact And.intro (lt_of_le_of_lt hxy ha.left) ha.right
          · by_contra; apply not_lt_of_le ha.right
            exact lt_of_le_of_lt hyz ha.left
      · intro c hc b hb
        rcases hb, hc with ⟨⟨hb1, hb2⟩ | ⟨hb1, hb2⟩, ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩⟩
        · exact lt_of_le_of_lt hb2 hc1
        · exact lt_of_le_of_lt (le_trans hb2 hyz) hc1
        ·
          sorry
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

lemma ind_scat_of_fin_seg_of_one_class {X : LinOrd.{u}}
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
      apply @iso_of_sigma_partition (LinOrd.mk {x_1 // x < x_1}) S1 j
      intro z ; exact J_partition z

    apply Scattered_ind_prop.lex_sum.{u,u} S1
      ?_ J ?_ _ Jiso
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
        exact @ind_scat_of_fin_seg_of_one_class _ x one_class
      have part2 : Scattered_ind_prop.{u,u} {carrier := {x_1 // x_1 < x}, str := inferInstance} := by
        rw [@swap_of_swap_elim' { carrier := { x_1 // x_1 < x }, str := inferInstance } ]
        let X' : LinOrd := { carrier := X.carrier, str := X.str.swap}
        have X_eq: X.carrier = X'.carrier := by exact rfl
        have : Scattered_ind_prop { carrier := { x_1 // x_1 < x },
                                    str := (LinearOrder.swap { x_1 // x_1 < x } inferInstance) } := by
          let iso : OrderIso ({ carrier := { x_1 // x_1 < x }, str := LinearOrder.swap { x_1 // x_1 < x } inferInstance } : LinOrd)
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
          sorry
        exact ind_scat_of_rev_ind_scat this

      apply scat_of_3_layered_scats _ _ {carrier := ({x} : Set X), str := inferInstance} _ part2 ?_ part1
      · use {
        toFun := fun y => if h : y > x then ⟨2, ⟨y, h⟩⟩
                          else if h1 : y = x then ⟨1, ⟨y, h1⟩⟩
                          else ⟨0, ⟨y, lt_of_le_of_ne (le_of_not_gt h) h1⟩⟩
        invFun := fun y => if h0 : y.1 = 0 then ((g''0 y h0) ▸ y.2).1
                           else if h1 : y.1 = 1 then ((g''1 y h1) ▸ y.2).1
                           else ((g''2 y (by
                                          exact Or.elim3 (Three_def y.1) (by intro h; by_contra; exact h0 h)
                                           (by intro h; by_contra; exact h1 h) (by simp))) ▸ y.2).1
        left_inv := by
          intro y
          simp
          --split_ifs with h1 h2 h3 h4 h5 h6
          -- this gives 17 goals
          sorry
        right_inv := by
          sorry
        }
        intro a b
        sorry
      · apply Well_Ord_ind_scat_prop
        exact (@Finite.to_wellFoundedLT
          ({ carrier := ({x} : Set X), str := inferInstance } : LinOrd)
          (Set.finite_singleton x)).1
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

        -- subst h -- h proves type equality
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
        apply (Scat_iff_not_embeds_Q (ind (f a))).mp (is_scat_f (f a))
        exact F
