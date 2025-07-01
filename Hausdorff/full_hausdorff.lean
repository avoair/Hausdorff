import Mathlib.Tactic
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Order.Category.LinOrd
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sigma.Lex
import Mathlib.Data.Setoid.Partition
import Hausdorff.WO_cofinal_subset
import Hausdorff.IsScattered
import Hausdorff.Isomorphisms


open Classical
universe u

/-- Hausdorff's recursive definition of scattered -/
inductive IndScattered : LinOrd.{u} → Prop
| base {L : LinOrd.{u}} (x : L.carrier) (h : {x} = @Set.univ L.carrier) : IndScattered L
| lex_sum (I: LinOrd.{u})
  (hwo : WellFounded I.str.lt ∨ WellFounded (I.str.swap).lt)
  (f: I.carrier → LinOrd)
  (h1 : ∀ w, IndScattered (f w))
  (L : LinOrd.{u})
  (h2 : L ≃o dLexOrd I f) : IndScattered L

/-- Empty LinOrds are indscatttered -/
lemma indscat_of_empty (X : LinOrd) (empt : IsEmpty X) : IndScattered X := by
  apply IndScattered.lex_sum X (Or.inl (wellFounded_of_isEmpty X.str.lt)) (fun x => X)
  simp only [IsEmpty.forall_iff]
  have : IsEmpty (dLexOrd X (fun x => X)) := by
    apply IsEmpty.mk
    intro a; apply (@IsEmpty.exists_iff _ empt).mp
    use a.1
  use Equiv.equivOfIsEmpty X (dLexOrd X (fun x => X))
  intro a; by_contra
  apply (@IsEmpty.exists_iff X empt).mp
  use a

/-- a helper lemma: a linear order is well-ordered iff for any x,
    every set containing x is bounded below-/
private lemma aux_WO_iff {α : Type*} [r : LinearOrder α]:
  IsWellFounded α r.lt ↔ ∀ x, ∀ A : Set α, x ∈ A → ∃ lb ∈ A, ∀ a ∈ A, r.le lb a := by
  constructor
  · intro _ x
    apply IsWellFounded.induction r.lt x
    intro y IH A _
    rcases Classical.em (∀ a ∈ A, r.le y a) with hxlb | hnxlb
    · use y
    · push_neg at hnxlb
      rcases hnxlb with ⟨a, ha⟩
      exact IH a (ha.right) A ha.left
  · intro h
    constructor
    apply WellFounded.intro
    by_contra! contra
    let S := {a : α | ¬ Acc LT.lt a}
    rcases contra with ⟨x, hx⟩
    rcases h x S hx with ⟨lb, hlb⟩
    apply hlb.left
    apply Acc.intro
    intro y hy
    by_contra hy_acc
    apply not_lt_of_ge (LE.le.ge (hlb.right y hy_acc)) hy

/-- A linear order is well-founded iff every (nonempty) subset is bounded below -/
theorem WO_iff_subsets_bdd_below {α : Type*} [r : LinearOrder α]:
  IsWellFounded α r.lt ↔ ∀ (A: Set α), A.Nonempty → ∃ lb ∈ A, ∀ x ∈ A, r.le lb x := by
  rw [aux_WO_iff]
  constructor
  · intro h A hA
    rcases hA with ⟨x, hx⟩
    exact h x A hx
  · intro h x A hA
    apply h A
    use x

/-- Well founded LinOrds are indscattered -/
lemma indscat_of_well_founded (X: LinOrd) (h : WellFounded X.str.lt) : IndScattered X := by
  let L := dLexOrd X (fun w => LinOrd.mk PUnit)
  let f : X ≃o L := {
    toFun := fun x => ⟨x, PUnit.unit⟩
    invFun := fun ⟨a, b⟩ => a
    left_inv := by intro _ ; simp
    right_inv := by intro _ ; constructor
    map_rel_iff' := by
      intro a b
      rw [Sigma.Lex.le_def]
      simp only [le_refl, exists_prop, and_true]
      exact Iff.symm le_iff_lt_or_eq }
  exact IndScattered.lex_sum X (Or.inl h)
    (fun x => LinOrd.mk PUnit)
    (fun x => by
      apply IndScattered.base PUnit.unit
      exact Set.eq_univ_of_univ_subset fun ⦃a⦄ => congrFun rfl) X f

/-- Singleton orders are indscattered -/
lemma indscat_of_singleton {α : LinOrd} (x : α) :
  IndScattered (LinOrd.mk ({x} : Set α)) := by
  apply indscat_of_well_founded _
    (@Finite.to_wellFoundedLT (LinOrd.mk ({x} : Set α)) (Set.finite_singleton x)).1

/-- Orders isomorphic to an indscattered order are indscattered -/
lemma indscat_of_iso {L M : LinOrd.{u}} (f : @OrderIso M L (M.str.toLE) (L.str.toLE))
  (h: IndScattered M) : IndScattered L := by
  rcases h with ⟨a, h1⟩ | ⟨N, I, map, scat_of_map, _, iso⟩
  · apply IndScattered.base (f a)
    apply @Subsingleton.eq_univ_of_nonempty L ?_
    · exact Set.singleton_nonempty (f a)
    · apply @Equiv.subsingleton _ _ (f.symm).1 ?_
      apply Set.subsingleton_of_univ_subsingleton
        ((Set.subsingleton_iff_singleton _).mpr (Eq.symm h1))
      simp
  · apply IndScattered.lex_sum N I map scat_of_map L
    use OrderIso.trans f.symm iso
    exact (OrderIso.trans f.symm iso).map_rel_iff

/-- One scattered order ontop of another scattered order is scattered -/
lemma indscat_of_layered_indscats (L M N : LinOrd.{u}) (h1 : IndScattered M)
  (h2: IndScattered N)
  (iso : L ≃o dLexOrd Two.L.{u} (g' M N)) :
  IndScattered L := by
  apply IndScattered.lex_sum Two.L
    (Or.inl (@Finite.to_wellFoundedLT _ Two.finite).1) (g' M N)
  · intro w
    match w with
    | Two.zero => {simp only [g']; exact h1}
    | Two.one => {simp only [g']; exact h2}
  · exact iso

/-- A suborder of a indscat order is indscattered -/
lemma indscat_of_subset {L : LinOrd} (A : Set L) (h : IndScattered L) :
  IndScattered (LinOrd.mk A) := by
  induction' h with M m hm I WF_RWF map scat_map N Niso IH
  · -- base case
    have A_sub: A.Subsingleton := by
      apply @Set.subsingleton_of_subset_singleton _ m A
      rw [hm]; exact Set.subset_univ A
    rcases Set.Subsingleton.eq_empty_or_singleton A_sub with h | h
    · apply indscat_of_empty _ (Set.isEmpty_coe_sort.mpr h)
    · rcases h with ⟨m', hm'⟩
      apply IndScattered.base (⟨m', by rw[hm']; apply Set.mem_singleton⟩ : A)
      apply Set.eq_univ_of_image_val_eq
      simp only [Set.image_singleton]; apply hm'.symm
  · -- inductive step
    let B := Niso '' A
    let g (w : I) := LinOrd.mk {b | ⟨w, b⟩ ∈ B}
    let Biso : B ≃o dLexOrd I g :=
      {
        toFun := fun x => ⟨x.1.1, ⟨x.1.2, by simp⟩⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        left_inv := by intro x ; simp
        right_inv := by intro x ; simp
        map_rel_iff' := by
          rintro ⟨⟨x, hx0⟩, hx⟩ ⟨⟨y, hy0⟩, hy⟩
          simp only [Equiv.coe_fn_mk, Sigma.Lex.le_def, Subtype.mk_le_mk]
          apply or_congr_right
          constructor <;> ( rintro ⟨rfl, h⟩; use rfl, h )
      }
    apply indscat_of_iso (OrderIso.trans Biso.symm
      (OrderIso_restrict Niso A).symm)
    apply IndScattered.lex_sum I WF_RWF g
    · intro w; exact IH w { x | ⟨w, x⟩ ∈ B }
    · rfl

/-- A subset of a suborder which is indscat is indscat-/
lemma indscat_of_subset' {L : LinOrd} (A : Set L)
  (h : IndScattered (LinOrd.mk A)) (B : Set L) (h1 : B ⊆ A) :
  IndScattered (LinOrd.mk B) := by
  let C : Set (LinOrd.mk A) := {x | x.1 ∈ B}
  apply @indscat_of_iso _ (LinOrd.mk C)
  use subtype_iso A B h1
  · intro a b
    simp only [EquivLike.coe_coe, map_le_map_iff]
  · exact indscat_of_subset _ h

/-- given that the subordering given by a property P is indscattered,
    the subset of any other subordering given by P is also indscattered -/
lemma indscat_of_subset'' {L : LinOrd} (P : L → Prop) (T : L → Prop)
  (h : IndScattered (LinOrd.mk {x | P x})) :
  IndScattered (LinOrd.mk {x : {x // T x} | P x}) := by
  apply @indscat_of_iso _ (LinOrd.mk {x | T x ∧ P x})
  · exact {
      toFun := fun x => ⟨⟨x.1, x.2.left⟩, x.2.right⟩
      invFun := fun x => ⟨x.1.1, And.intro x.1.2 x.2⟩
      left_inv := by intro _ ; simp
      right_inv := by intro _ ; simp
      map_rel_iff' := by intro _ _; simp
    }
  · apply indscat_of_subset' _ h
    simp

/-- The reversal of an indscattered order is indscattered -/
lemma indscat_of_rev_indscat {L : LinOrd} (h : IndScattered L) :
  IndScattered (LinOrd_swap L) := by
  induction' h with M m hm WO hWO f f_scat L Liso IH
  · exact @IndScattered.base (LinOrd_swap M) _ hm
  · let map (w : LinOrd_swap WO) := LinOrd_swap (f w)
    let iso := Sigma_swap_alt_def f
    let p := (swap_iso_of_iso Liso)
    let p' := @OrderIso.symm L _ (LinOrd_swap L).str.toLE
              (LinOrd_swap (dLexOrd WO f)).str.toLE p
    apply indscat_of_iso p'
    apply IndScattered.lex_sum (LinOrd_swap WO) ?_ map IH _ iso
    · rcases hWO with WO | RWO
      · right; apply WO
      · left;
        apply RWO

/-- A relation describing that (x, y] inductively scattered -/
def indscat_rel {L : LinOrd} (x y : L) : Prop :=
  let M : LinOrd := LinOrd.mk {a | (x < a ∧ a ≤ y) ∨ (y < a ∧ a ≤ x)}
  IndScattered M

/-- The indscat_rel relation is convex -/
lemma indscat_rel_convex {L : LinOrd} (a b c : L) (h : a < b ∧ b < c) (h1 : indscat_rel a c):
  indscat_rel a b := by
  have : { x | a < x ∧ x ≤ b ∨ b < x ∧ x ≤ a } ⊆ { x | a < x ∧ x ≤ c ∨ c < x ∧ x ≤ a } := by
    intro x hx
    rcases hx with hx1 | hx1
    · left; exact And.intro hx1.left (le_trans hx1.right (le_of_lt h.right))
    · left; exact And.intro (lt_trans h.left hx1.left)
                            (le_of_lt (lt_of_le_of_lt hx1.right (lt_trans h.left h.right)))
  exact indscat_of_subset' _ h1 _ this

/-- special case of the proof that scat_rel is transitive
    where the inputs are increasing -/
lemma aux_indscat_rel_trans {L : LinOrd} {a b c : L} (hab : a ≤ b) (hbc : b ≤ c)
  (scat_ab : indscat_rel a b) (scat_bc : indscat_rel b c) : indscat_rel a c := by
  apply indscat_of_layered_indscats _ _ _ scat_ab scat_bc
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

/-- the indscat_rel relation is symmetric -/
lemma indscat_rel_symm {L : LinOrd} : ∀ {x y : L}, indscat_rel x y → indscat_rel y x := by
  intro x y h
  simp only [indscat_rel] at h
  have : (fun x_1 => x < x_1 ∧ x_1 ≤ y ∨ y < x_1 ∧ x_1 ≤ x) =
          (fun x_1 => y < x_1 ∧ x_1 ≤ x ∨ x < x_1 ∧ x_1 ≤ y) := by
    apply Set.eq_of_subset_of_subset
    <;> (rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩) ;
          right; constructor <;> order ;
          left; constructor <;> order)
  have : LinOrd.mk { x_1 // x < x_1 ∧ x_1 ≤ y ∨ y < x_1 ∧ x_1 ≤ x }
         = LinOrd.mk { x_1 // y < x_1 ∧ x_1 ≤ x ∨ x < x_1 ∧ x_1 ≤ y } := by
    simp only [LinOrd.mk.injEq, this, true_and]
    exact LinearOrder_subtype_HEq this
  simpa only [Set.coe_setOf, this] using h

/-- indscat_rel is an equivalence relation -/
lemma indscat_rel_equiv {L : LinOrd}: Equivalence (@indscat_rel L) := by
  constructor
  · intro x
    apply (indscat_of_well_founded (LinOrd.mk { x_1 // x < x_1 ∧ x_1 ≤ x ∨ x < x_1 ∧ x_1 ≤ x }))
    apply @wellFounded_of_isEmpty _ ?_
    by_contra nonempt
    simp only [or_self, not_isEmpty_iff] at nonempt
    rcases nonempt with ⟨x_1, hx_1⟩
    exact lt_irrefl x (lt_of_lt_of_le hx_1.left hx_1.right)
  · exact indscat_rel_symm
  · intro x y z scat_xy scat_yz
    rcases L.str.le_total x y, L.str.le_total y z with ⟨hxy | hxy, hyz | hyz⟩
    -- every case is either a subset or layered intervals
    · exact aux_indscat_rel_trans hxy hyz scat_xy scat_yz
    · rcases (le_or_gt x z) with hxz | hz
      · apply indscat_of_subset' _ scat_xy
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (left; constructor <;> order)
      · apply indscat_of_subset' _ scat_yz
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (right; constructor <;> order)
    · rcases (le_or_gt x z) with hxz | hz
      · apply indscat_of_subset' _ scat_yz
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (left; constructor <;> order)
      · apply indscat_of_subset' _ scat_xy
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (right; constructor <;> order)
    · exact indscat_rel_symm (aux_indscat_rel_trans hyz hxy
        (indscat_rel_symm scat_yz) (indscat_rel_symm scat_xy))

/-- if indscat_rel x y, then the LinOrd restricted to [x, y] is also indscattered -/
lemma indscat_to_closed_interval {L : LinOrd} (x y : L) (h : indscat_rel x y):
  IndScattered (LinOrd.mk {a | (x ≤ a ∧ a ≤ y) ∨ (y ≤ a ∧ a ≤ x)}) := by
  wlog hxy : x ≤ y
  · push_neg at hxy
    apply indscat_of_iso _ (this y x (Equivalence.symm indscat_rel_equiv h) (le_of_lt hxy))
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
  · apply indscat_of_layered_indscats _ (LinOrd.mk ({x} : Set L))
                                      (LinOrd.mk {a | x < a ∧ a ≤ y})
    · apply indscat_of_well_founded
      exact wellFounded_lt
    · apply indscat_of_iso _ h
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
    · apply (Two_iso_helper _ {x} {a | x < a ∧ a ≤ y})
      · ext a
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          <;> ( apply or_iff_not_imp_left.mpr;
                simp only [Set.mem_singleton_iff]
                intro h;
                constructor <;> order )
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          <;> (left; constructor <;> order)
      · rintro c hc b ⟨hb1, hb2⟩
        exact hc.left

/-- if (x, y] is indscattered, so is [x, y) -/
lemma indscat_of_interval_flip {L : LinOrd} (x y : L) (h : indscat_rel x y):
  IndScattered (LinOrd.mk {a | (x ≤ a ∧ a < y) ∨ (y ≤ a ∧ a < x)}) := by
  apply indscat_of_subset' _ (indscat_to_closed_interval x y h)
  rintro a (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · left; exact And.intro h1 (le_of_lt h2)
  · right; exact And.intro h1 (le_of_lt h2)

/-- any order which is not a NoMaxOrder has a maximum element-/
lemma max_of_NoMaxOrder {L : LinOrd} (hm : ¬ NoMaxOrder L):
  ∃ a : L, ∀ b, b ≤ a := by
  by_contra! h
  apply hm
  constructor
  intro a
  rcases h a with ⟨b ,hb⟩
  use b

--//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
-- Hausdorff's theorem
--//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/-- Given a LinOrd and a subset I, map each element a of I to all the elements of the
    LinOrd less than a, but not less than any earlier element of I -/
def part_fxn {L : LinOrd} {I : Set L} (a : I) := {z : L | z ≤ a ∧ ∀ a' < a, a' < z}

/-- If the indexing set is WF cofinal, the part_fxn partitions the LinOrd -/
lemma part_fxn_prop {L : LinOrd} {Cof : Set L}
  (hCof : IsCofinal Cof ∧ Cof.WellFoundedOn fun x1 x2 ↦ x1 < x2)
  (nomax : NoMaxOrder L) : ∀ z : L, ∃! (a : Cof), z ∈ part_fxn a := by
  intro z
  let final := {a : Cof | z ≤ a}
  have final_nonempt : final.Nonempty := by
    rw [Set.nonempty_def]
    rcases nomax.exists_gt z with ⟨z', hz'⟩
    rcases hCof.left z' with ⟨y, hy⟩
    use ⟨y, hy.left⟩
    exact le_of_lt (lt_of_lt_of_le hz' hy.right)

  rcases WO_iff_subsets_bdd_below.mp ((isWellFounded_iff (↑Cof) LT.lt).mpr hCof.right)
          final final_nonempt with ⟨lb, ⟨hlb1, hlb2⟩⟩
  use lb
  constructor
  · constructor
    · exact hlb1
    · intro a ha
      by_contra! contra
      apply not_le_of_lt ha
      exact hlb2 a contra
  · intro y hy
    apply eq_of_le_of_le
    · by_contra! contra
      apply not_lt_of_le hlb1
      exact hy.right lb contra
    · exact hlb2 y hy.left

/-- Given a LinOrd and a WF cofinal subset, if the output of the part_fxn on that
    subset is always indscat, then L is also indscat -/
lemma indscat_of_WF_parition (L : LinOrd) (Cof : Set L)
  (hCof : IsCofinal Cof ∧ Cof.WellFoundedOn fun x1 x2 ↦ x1 < x2)
  (all_indscat : ∀ (w : LinOrd.mk Cof), IndScattered (LinOrd.mk (part_fxn w)))
  (nomax : NoMaxOrder L):
  IndScattered L := by
  have : IsWellOrder Cof _ :=
      { toIsTrichotomous := instIsTrichotomousLt,
              toIsTrans := instIsTransLt,
              toIsWellFounded := by
              constructor
              exact hCof.right }
  let J (a : Cof) := LinOrd.mk (part_fxn a)
  let Jiso : L ≃o dLexOrd (LinOrd.mk Cof) J := by
    apply @iso_of_sigma_partition L (LinOrd.mk Cof) part_fxn (part_fxn_prop hCof nomax)
    intro a b hab c hc d hd
    exact lt_of_le_of_lt hc.left (hd.right a hab)
  apply IndScattered.lex_sum (LinOrd.mk Cof) ?_ J ?_ L Jiso
  · left; exact wellFounded_lt
  · exact fun w ↦ all_indscat w

/-- given a,b in a LinOrd, the set of x ∈ (a, b] such that a and x are related is indscat -/
lemma aux_dense_quotient {L : LinOrd} {a b : L} :
  IndScattered (LinOrd.mk {x | a < x ∧ x ≤ b ∧ indscat_rel a x}) := by
  let A := { x | a < x ∧ x ≤ b ∧ indscat_rel a x}
  rcases @exists_cof_WF_subset A inferInstance with ⟨Cof, hCof⟩
  rcases Classical.em (NoMaxOrder (LinOrd.mk A)) with nomax | max
  · apply indscat_of_WF_parition _ Cof hCof ?_ nomax
    intro w
    let k := indscat_of_subset'' _ A w.1.2.right.right
    apply @indscat_of_subset' (LinOrd.mk A) _ k { x : A | x ≤ ↑w ∧ ∀ a' < w, ↑a' < x }
    intro x ⟨hx1, hx2⟩
    left; exact And.intro x.2.left hx1
  · rcases (max_of_NoMaxOrder max) with ⟨m, hm⟩
    let p := m.2.right.right
    apply indscat_of_subset' _ p
    intro x ⟨hx1, hx2, hx3⟩
    repeat constructor
    · exact hx1
    · exact hm ⟨x, And.intro hx1 (And.intro hx2 hx3)⟩

/-- Taking the subrelation of a swapped order is equivalent to swapping
    a subrelation of the original order -/
lemma subtype_swap {α : Type*} {L : LinearOrder α} {p : α → Prop}:
  @Subtype.instLinearOrder α (L.swap) p = (@Subtype.instLinearOrder α L p).swap := by
  exact rfl

/-- If a and b are related in the LinOrd L, they are also related from the
    perspective of the swapped version of L -/
lemma indscat_rel_in_L_swap {L : LinOrd} (a b : L) :
  @indscat_rel L a b → @indscat_rel (LinOrd_swap L) a b := by
  simp only [indscat_rel]
  intro h
  rw [subtype_swap]
  let p := indscat_of_rev_indscat (indscat_of_interval_flip a b h)
  simp [LinOrd_swap] at p
  apply indscat_of_iso _ p
  exact {
    toFun := fun x => ⟨x,
      by
      rcases x.2 with x2 | x2
      · right; exact And.symm x2
      · left; exact And.symm x2 ⟩
    invFun := fun x => ⟨x,
      by
      rcases x.2 with x2 | x2
      · right; exact And.symm x2
      · left; exact And.symm x2 ⟩
    left_inv := by intro _; simp
    right_inv := by intro _; simp
    map_rel_iff' := by intro _ _; trivial }

/-- The quotient of indscat is dense -/
lemma dense_quotient {L : LinOrd} {a b : L} (h : ¬ indscat_rel a b) (hl : a < b) :
  ∃ c, a < c ∧ c ≤ b ∧ ¬ indscat_rel a c ∧ ¬ indscat_rel c b := by
  by_contra! contra
  -- split the interval into elements related to a and elements related to b
  let A := { x | a < x ∧ x ≤ b ∧ indscat_rel a x}
  let B := { x | a < x ∧ x ≤ b ∧ indscat_rel x b}
  -- show that A and B partition the interval
  have all_A_or_B (x : L) (h1 : a < x) (h2 : x ≤ b): x ∈ A ∪ B := by
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, A] at hc
    push_neg at hc
    apply hc.right; split_ands
    · exact h1
    · exact h2
    · exact contra x h1 h2 (hc.left h1 h2)
  have empty_inter : ¬ (A ∩ B).Nonempty := by
    by_contra! contra
    rcases contra with ⟨x, ⟨hxA1, hxA2, hxA3⟩, ⟨hxB1, hxB2, hxB3⟩⟩
    apply h
    apply indscat_of_layered_indscats _ _ _ hxA3 hxB3
    apply Two_iso_helper
    · apply Set.eq_of_subset_of_subset
      · rintro t ht
        rcases ht, (lt_or_le x t) with ⟨(⟨ht1, ht2⟩ | ⟨ht1, ht2⟩), h | h⟩
        · right; left; exact And.intro h ht2
        · left; left; exact And.intro ht1 h
        · left; right; exact And.intro h ht2
        · right; right; exact And.intro ht1 h
      · rintro t (⟨⟨ht1, ht2⟩ | ⟨ht1, ht2⟩⟩ | ⟨⟨ht1, ht2⟩ | ⟨ht1, ht2⟩⟩)
        <;> (first | left; constructor <;> order)
    · rintro c (⟨hc1, hc2⟩ | ⟨hc1, hc2⟩) b (⟨hb1, hb2⟩ | ⟨hb1, hb2⟩)
      <;> order
  -- show that the interval must be indscat by showing it is isomorphic to the LinOrd with
  -- B ontop of A
  apply h
  apply indscat_of_layered_indscats _ (LinOrd.mk A) (LinOrd.mk B)
  · exact aux_dense_quotient
  · -- use the previous case to show that the result holds for modified interval bounds
    have : IndScattered (LinOrd.mk { x // a ≤ x ∧ x < b ∧ indscat_rel x b }) := by
      apply @indscat_of_rev_indscat
        (LinOrd_swap (LinOrd.mk { x // a ≤ x ∧ x < b ∧ indscat_rel x b }))
      apply indscat_of_iso _ (@aux_dense_quotient (LinOrd_swap L) b a)
      exact {
        toFun := fun x => ⟨x,
          by
          split_ands; exact x.2.right.left ; exact x.2.left
          exact indscat_rel_in_L_swap x.1 b
            (Equivalence.symm indscat_rel_equiv x.2.right.right)⟩
        invFun := fun x => ⟨x,
          by
            split_ands; exact x.2.right.left ; exact x.2.left
            exact indscat_rel_in_L_swap b x.1
              (Equivalence.symm indscat_rel_equiv x.2.right.right)⟩
        left_inv := by intro _; trivial
        right_inv := by intro _; trivial
        map_rel_iff' := by intro _ _; trivial }

    have : IndScattered (LinOrd.mk { x | a < x ∧ x < b ∧ indscat_rel x b }) := by
      apply indscat_of_subset' _ this
      rintro x ⟨hx1, hx2, hx3⟩
      exact And.intro (le_of_lt hx1) (And.intro hx2 hx3)

    apply indscat_of_layered_indscats _
      (LinOrd.mk { x | a < x ∧ x < b ∧ indscat_rel x b })
      (LinOrd.mk ({b} : Set L)) this
    · exact indscat_of_singleton b
    · apply Two_iso_helper
      · ext x; simp only [Set.union_singleton, Set.mem_insert_iff, A]
        constructor
        · rintro ⟨h1, h2, h3⟩
          rw [or_iff_not_imp_left]
          intro h
          split_ands <;> (first | order | exact h3)
        · rintro (h | ⟨h1, h2, h3⟩)
          · subst x
            split_ands
            · exact hl
            · rfl
            · exact Equivalence.refl indscat_rel_equiv b
          · split_ands <;> (first | order | exact h3)
      · rintro c hc d ⟨hd1, hd2, hd3⟩
        simp at hc
        order

  · apply Two_iso_helper
    · ext x
      constructor
      · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩)
        · exact all_A_or_B x hA hB
        · order
      · rintro (h | h)
        <;> (left; exact And.intro h.left h.right.left)
    · rintro c ⟨hc1, hc2, hc3⟩ d ⟨hd1, hd2, hd3⟩
      by_contra! h;
      have : indscat_rel a c := by
        apply indscat_of_subset' _ hd3
        rintro x (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩)
        · left; constructor <;> order
        · right; constructor <;> order
      apply empty_inter
      use c
      split_ands <;> (first | order | exact this | exact hc3)

/-- Given a LinOrd where all elements are related by indscat_rel, any final segment
    of the LinOrd is indscatttered -/
lemma ind_scat_of_fin_seg_of_one_class {X : LinOrd}
  (x : X) (one_class : ∀ x y : X, indscat_rel x y) : IndScattered (LinOrd.mk {x_1 // x < x_1}) := by
  rcases @exists_cof_WF_subset {x_1 // x_1 > x} inferInstance with ⟨Cof, hCof⟩
  rcases Classical.em (NoMaxOrder (LinOrd.mk {x_1 // x < x_1})) with nomax | max
  · apply indscat_of_WF_parition (LinOrd.mk {x_1 // x < x_1}) Cof hCof ?_ nomax
    intro w
    specialize one_class x w
    let p :=  indscat_of_subset'' ((fun x_1 => x < x_1 ∧ x_1 ≤ ↑↑w ∨ ↑↑w < x_1 ∧ x_1 ≤ x))
                                    (fun x_1 => x < x_1 ) one_class
    apply @indscat_of_subset' (LinOrd.mk { x_2 // x < x_2 }) _ p
                            { x_1 | x_1 ≤ ↑w ∧ ∀ a' < w, ↑a' < x_1 }
    simp only [Subtype.forall, Set.setOf_subset_setOf]
    intro a ha haw
    left; exact And.intro ha haw.left
  · rcases isEmpty_or_nonempty (LinOrd.mk { x_1 // x < x_1 }) with empt | nonempt
    · exact indscat_of_empty _ empt
    rcases (max_of_NoMaxOrder max) with ⟨m, hm⟩
    apply indscat_of_iso ?_ (one_class x m)
    exact {
      toFun := fun y =>
        ⟨y.1, by
              rcases y.2 with h | ⟨h1, h2⟩
              · exact h.left
              · by_contra;
                apply not_lt_of_le h2
                rcases nonempt with ⟨n⟩;
                exact lt_trans (lt_of_lt_of_le n.2 (hm n)) h1⟩
      invFun := fun y =>
        ⟨y.1 , Or.inl (And.intro y.2 (hm y))⟩
      left_inv := by intro _ ; simp
      right_inv := by intro _ ; simp
      map_rel_iff' := by intro _; simp }

/-- The class of IsScattered orders is the same as the class of IndScattered orders-/
theorem Hausdorff_Scattered_Orders (X : LinOrd): IsScattered X ↔ IndScattered X := by
  constructor
  · intro X_scat
    rcases Classical.em (Nonempty X) with nonempt | empt; swap
    · rw [not_nonempty_iff] at empt
      exact indscat_of_empty X empt
    rcases Classical.em (∀ x y : X, indscat_rel x y) with one_class | mult_class
    · rcases Classical.exists_true_of_nonempty nonempt with ⟨x⟩
      have part1 : IndScattered (LinOrd.mk {x_1 // x < x_1}) := by
        exact @ind_scat_of_fin_seg_of_one_class _ x one_class
      have part2 : IndScattered (LinOrd.mk {x_1 // x_1 < x}) := by
        let X' := LinOrd_swap X
        have X_eq: X.carrier = X'.carrier := by exact rfl

        let L : LinOrd := LinOrd_swap (LinOrd.mk { x_1 // x_1 < x })
        let M : LinOrd := LinOrd.mk { x_1 : X' // @LT.lt X' _ (X_eq ▸ x) x_1}

        apply @indscat_of_rev_indscat L

        let iso : @OrderIso L M L.str.toLE M.str.toLE := by
          exact {
          toFun := fun y => y
          invFun := fun y => y
          left_inv := by intro _; trivial
          right_inv := by intro _; trivial
          map_rel_iff' := by intro _ _; simp only [Equiv.coe_fn_mk] }

        apply indscat_of_iso iso
        apply @ind_scat_of_fin_seg_of_one_class X' (X_eq ▸ x)

        intro x y
        let p := indscat_of_rev_indscat (@indscat_of_interval_flip X y x (one_class y x))
        apply indscat_of_iso _ p

        -- the underlying sets in the goal are equal
        have : { x_1 : X | @LE.le (↑X) _ y x_1 ∧ x_1 < x ∨ @LE.le (↑X) _ x x_1 ∧ x_1 < y }
          = { x_1 : X' | x < x_1 ∧ @LE.le (↑X') _ x_1 y ∨ y < x_1 ∧ x_1 ≤ x } := by
          ext a
          have h1 : (@LE.le (↑X) _ y a ∧ a < x)
                  = (x < a ∧ @LE.le (↑X') _ a y) := by
            simp only [eq_iff_iff]; constructor
            <;> (rintro ⟨h1, h2⟩ ; exact And.intro h2 h1)
          have h2 : (@LE.le (↑X) Preorder.toLE x a ∧ a < y)
                    = (y < a ∧ @LE.le (↑X') Preorder.toLE a x) := by
            simp only [eq_iff_iff]; constructor
            <;> (rintro ⟨h1, h2⟩ ; exact And.intro h2 h1)
          rw [Set.mem_setOf_eq, h1, h2]
          rfl

        exact {
          toFun := fun x => ⟨x.1, subset_of_eq this x.2⟩
          invFun := fun x => ⟨x.1, subset_of_eq this.symm x.2⟩
          left_inv := by intro _; simp
          right_inv := by intro _; simp
          map_rel_iff' := by
            rintro ⟨x1, x2⟩ ⟨y1, y2⟩
            constructor
            <;> (intro h ; simp only [Subtype.mk_le_mk] at h ; apply h)
        }

      let f : Three.L → Set X
        | Three.zero => { x_1 | x_1 < x }
        | Three.one => {x}
        | Three.two =>  { x_1 | x < x_1 }

      apply IndScattered.lex_sum Three.L (Or.inl (@Finite.to_wellFoundedLT Three Three.finite).1)
        (fun w => LinOrd.mk (f w))
      · intro w; cases w
        · exact part2
        · exact indscat_of_singleton x
        · exact part1
      · apply (iso_of_sigma_partition f _ _)
        · intro z
          apply existsUnique_of_exists_of_unique
          · rcases lt_trichotomy z x  with h | h | h
            · use Three.zero; simp only [Set.mem_setOf_eq, h, f]
            · use Three.one; simp only [h, Set.mem_singleton_iff, f]
            · use Three.two; simp only [Set.mem_setOf_eq, h, f]
          · intro y1 y2 hy1 hy2
            cases y1 <;>
              (cases y2 <;>
                (simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, f] at * ;
                   try order))
        · intro y1 y2 hy a ha b hb
          cases y1 <;>
          (simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, f] at ha ; cases y2 <;>
              (first | simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, f] at hb; order
                      | by_contra; apply not_le_of_lt hy ; trivial))

    · let K : Setoid X := ⟨indscat_rel, indscat_rel_equiv⟩
      let f := @Quotient.out X K
      let reps := Set.range f

      by_contra;
      rw [scat_iff_not_embeds_Q, <-not_nonempty_iff] at X_scat
      apply X_scat
      simp only [not_forall] at mult_class

      have : Nontrivial reps := by
        rcases mult_class with ⟨x1, x2, hx⟩
        use ⟨f ⟦x1⟧, by simp only [reps]; use ⟦x1⟧⟩,
            ⟨f ⟦x2⟧, by simp only [reps]; use ⟦x2⟧⟩
        by_contra! h; simp only [Subtype.mk.injEq , Quotient.out_inj, f] at h
        exact hx (Quotient.eq.mp h)

      have : DenselyOrdered reps := by
        constructor
        intro x y hxy
        have nequiv : ¬ indscat_rel x.1 y := by
          rcases x.2, y.2 with ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩
          simp only [f] at hx' hy'
          have : ⟦x.1⟧ = x' ∧ ⟦y.1⟧ = y' := by
            constructor
            <;> (refine Quotient.mk_eq_iff_out.mpr (Quotient.exact ?_) ;
                  simp [hx', hy'])
          have hne: ¬ x.1 = y.1 := ne_of_lt hxy
          rw [<-hx', <-hy', <-this.left, <- this.right] at hne
          simp only [Quotient.out_inj, Quotient.eq] at hne
          apply hne

        rcases dense_quotient nequiv hxy with ⟨c, hc1, hc2, hc3, hc4⟩
        let z : reps := ⟨(f ⟦c⟧), by simp [reps]⟩
        have hzc : indscat_rel z c := by
          apply Quotient.mk_out c
        use z
        by_contra! bounds
        rcases le_or_lt z x with h | h
        · apply hc3
          apply indscat_of_subset' _ hzc
          rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
          · left; exact And.intro (lt_of_le_of_lt h ha1) ha2
          · by_contra; apply not_lt_of_le ha2
            exact lt_trans hc1 ha1
        · apply hc4
          apply indscat_of_subset' _ hzc
          rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
          · right; exact And.intro ha1 (le_trans ha2 (bounds h))
          · by_contra; apply not_lt_of_le ha2
            exact lt_of_le_of_lt hc2 ha1

      rcases Order.embedding_from_countable_to_dense ℚ reps with ⟨f1⟩
      apply Nonempty.intro (OrderEmbedding_comp (coeEmb reps) f1)

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

      have hay: a.1 < y := by
        exact ha
      apply ne_of_lt hay
      exact symm (A_s hy a.2)

    · -- inductive case
      apply scat_of_iso_to_scat L (dLexOrd lo_lex ind) Liso

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
            use ⟨y, And.intro (lt_trans c.2.left hy.left) hy.right⟩
            exact hy.left
          have p5 : Nonempty B := by
            rcases props.right.left.dense a b hab.right with ⟨y, hy⟩
            use ⟨y, y.2⟩
            exact hy
          rcases props with ⟨_, _, _, _, _⟩
          apply Order.iso_of_countable_dense

        -- everything in the inverval B maps to the same suborder
        have fix_fst (x : B) : x.1.1.1 = f a := by
          by_contra contra
          rcases lt_or_gt_of_ne contra with h1 | h1
          · rcases Sigma.Lex.lt_def.mp (x.2.left) with h2 | h2
            · exact not_lt_of_le (le_of_lt h1) h2
            · rcases h2 with ⟨h, hh⟩
              exact contra (Eq.symm h)
          · simp only [f] at hab
            rcases Sigma.Lex.lt_def.mp (x.2.right) with h2 | h2
            · apply ne_of_gt (lt_trans (GT.gt.lt h1) h2)
              exact (Eq.symm hab.left)
            · rcases h2 with ⟨h, hh⟩
              rw [<-hab.left] at h
              exact contra h

        let B' := (fun b => b.1) '' B
        let g' : B' ↪o (ind (f a)) :=
          embed_dlexord (f a) B'
          (by
            rintro b1 ⟨b2, hb⟩
            rw [<-hb.right]
            exact fix_fst ⟨b2, hb.left⟩)

        let emb : B ↪o B' :=
          { toFun := fun b => ⟨b.1, by simp [B']⟩
            inj' := by
              intro a b hab
              simp only [Subtype.mk.injEq] at hab
              ext
              exact hab
            map_rel_iff' := by
              intro a b
              simp }

        let g : B ↪o (ind (f a)) := OrderEmbedding_comp g' emb

        -- compose the isomorphisms/ embeddings
        rcases props with ⟨p1, p2, p3, p4, p5⟩
        rcases Order.iso_of_countable_dense ℚ A with ⟨h⟩
        have h' := OrderIso.toOrderEmbedding h
        rcases A_iso_B with ⟨i⟩
        have i' := OrderIso.toOrderEmbedding i
        have F := OrderEmbedding_comp g (OrderEmbedding_comp i' h')
        apply isEmpty_iff.mp
        apply (scat_iff_not_embeds_Q (ind (f a))).mp (is_scat_f (f a))
        exact F
