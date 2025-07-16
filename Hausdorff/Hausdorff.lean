import Mathlib.Tactic
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Order.Category.LinOrd
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sigma.Lex
import Mathlib.Data.Setoid.Partition
import Hausdorff.WellOrderedCofinalSubset
import Hausdorff.Scattered
import Hausdorff.Isomorphisms


open Classical
universe u

/-- Hausdorff's recursive definition of scattered -/
inductive HausdorffScattered : LinOrd.{u} → Prop
| base {L : LinOrd.{u}} (x : L.carrier) (h : {x} = @Set.univ L.carrier) : HausdorffScattered L
| lex_sum (I: LinOrd.{u})
  (hwo : WellFounded I.str.lt ∨ WellFounded (I.str.swap).lt)
  (f: I.carrier → LinOrd)
  (h1 : ∀ w, HausdorffScattered (f w))
  (L : LinOrd.{u})
  (h2 : L ≃o dLexOrd I f) : HausdorffScattered L

/-- Empty LinOrds are HausdorffScatteredttered -/
lemma hausdorffScattered_empty (X : LinOrd) (empt : IsEmpty X) : HausdorffScattered X := by
  apply HausdorffScattered.lex_sum X (Or.inl (wellFounded_of_isEmpty X.str.lt)) (fun x => X)
  simp only [IsEmpty.forall_iff]
  have : IsEmpty (dLexOrd X (fun x => X)) := by
    apply IsEmpty.mk
    intro a; apply (@IsEmpty.exists_iff _ empt).mp
    use a.1
  use Equiv.equivOfIsEmpty X (dLexOrd X (fun x => X))
  intro a; by_contra
  apply (@IsEmpty.exists_iff X empt).mp
  use a

/-- Well founded LinOrds are HausdorffScatteredtered -/
lemma hausdorffScattered_of_wellFounded (X: LinOrd) (h : WellFounded X.str.lt) : HausdorffScattered X := by
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
  exact HausdorffScattered.lex_sum X (Or.inl h)
    (fun x => LinOrd.mk PUnit)
    (fun x => by
      apply HausdorffScattered.base PUnit.unit
      exact Set.eq_univ_of_univ_subset fun ⦃a⦄ => congrFun rfl) X f

/-- Singleton orders are HausdorffScatteredtered -/
lemma hausdorffScattered_of_singleton {α : LinOrd} (x : α) :
  HausdorffScattered (LinOrd.mk ({x} : Set α)) := by
  apply hausdorffScattered_of_wellFounded _
    (@Finite.to_wellFoundedLT (LinOrd.mk ({x} : Set α)) (Set.finite_singleton x)).1

/-- Orders isomorphic to an HausdorffScatteredtered order are HausdorffScatteredtered -/
lemma hausdorffScattered_of_orderIso {L M : LinOrd.{u}} (f : @OrderIso M L (M.str.toLE) (L.str.toLE))
  (h: HausdorffScattered M) : HausdorffScattered L := by
  rcases h with ⟨a, h1⟩ | ⟨N, I, map, scat_of_map, _, iso⟩
  · apply HausdorffScattered.base (f a)
    apply @Subsingleton.eq_univ_of_nonempty L ?_
    · exact Set.singleton_nonempty (f a)
    · apply @Equiv.subsingleton _ _ (f.symm).1 ?_
      apply Set.subsingleton_of_univ_subsingleton
        ((Set.subsingleton_iff_singleton _).mpr (Eq.symm h1))
      simp
  · apply HausdorffScattered.lex_sum N I map scat_of_map L
    use OrderIso.trans f.symm iso
    exact (OrderIso.trans f.symm iso).map_rel_iff

/-- One scattered order ontop of another scattered order is scattered -/
lemma hausdorffScattered_of_two_dLexOrd (L M N : LinOrd.{u}) (h1 : HausdorffScattered M)
  (h2: HausdorffScattered N)
  (iso : L ≃o dLexOrd Two.L.{u} (two_map M N)) :
  HausdorffScattered L := by
  apply HausdorffScattered.lex_sum Two.L
    (Or.inl (@Finite.to_wellFoundedLT _ Two.instFinite).1) (two_map M N)
  · intro w
    match w with
    | Two.zero => {simp only [two_map]; exact h1}
    | Two.one => {simp only [two_map]; exact h2}
  · exact iso

/-- A suborder of a HausdorffScattered order is HausdorffScatteredtered -/
lemma hausdorffScattered_of_subset {L : LinOrd} (A : Set L) (h : HausdorffScattered L) :
  HausdorffScattered (LinOrd.mk A) := by
  induction' h with M m hm I WF_RWF map scat_map N Niso IH
  · -- base case
    have A_subsingleton: A.Subsingleton := by
      apply @Set.subsingleton_of_subset_singleton _ m A
      rw [hm]; exact Set.subset_univ A
    rcases Set.Subsingleton.eq_empty_or_singleton A_subsingleton with h | h
    · apply hausdorffScattered_empty _ (Set.isEmpty_coe_sort.mpr h)
    · rcases h with ⟨m', hm'⟩
      apply HausdorffScattered.base (⟨m', by rw[hm']; apply Set.mem_singleton⟩ : A)
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
    apply hausdorffScattered_of_orderIso (OrderIso.trans Biso.symm
      (OrderIso_restrict Niso A).symm)
    apply HausdorffScattered.lex_sum I WF_RWF g
    · intro w; exact IH w { x | ⟨w, x⟩ ∈ B }
    · rfl

/-- A subset of a suborder which is HausdorffScattered is HausdorffScattered-/
lemma hausdorffScattered_of_subset' {L : LinOrd} (A : Set L)
  (h : HausdorffScattered (LinOrd.mk A)) (B : Set L) (h1 : B ⊆ A) :
  HausdorffScattered (LinOrd.mk B) := by
  let C : Set (LinOrd.mk A) := {x | x.1 ∈ B}
  apply @hausdorffScattered_of_orderIso _ (LinOrd.mk C)
  use linOrd_subtype_iso A B h1
  · intro a b
    simp only [EquivLike.coe_coe, map_le_map_iff]
  · exact hausdorffScattered_of_subset _ h

/-- given that the subordering given by a property P is HausdorffScatteredtered,
    the subset of any other subordering given by P is also HausdorffScatteredtered -/
lemma hausdorffScattered_of_subset'' {L : LinOrd} (P : L → Prop) (T : L → Prop)
  (h : HausdorffScattered (LinOrd.mk {x | P x})) :
  HausdorffScattered (LinOrd.mk {x : {x // T x} | P x}) := by
  apply @hausdorffScattered_of_orderIso _ (LinOrd.mk {x | T x ∧ P x})
  · exact {
      toFun := fun x => ⟨⟨x.1, x.2.left⟩, x.2.right⟩
      invFun := fun x => ⟨x.1.1, And.intro x.1.2 x.2⟩
      left_inv := by intro _ ; simp
      right_inv := by intro _ ; simp
      map_rel_iff' := by intro _ _; simp
    }
  · apply hausdorffScattered_of_subset' _ h
    simp

/-- The reversal of an HausdorffScatteredtered order is HausdorffScatteredtered -/
lemma hausdorffScattered_swap {L : LinOrd} (h : HausdorffScattered L) :
  HausdorffScattered (linOrd_swap L) := by
  induction' h with M m hm WO hWO f f_scat L Liso IH
  · exact @HausdorffScattered.base (linOrd_swap M) _ hm
  · let map (w : linOrd_swap WO) := linOrd_swap (f w)
    let iso := Sigma_swap_alt_def f
    let p := (swap_iso_of_iso Liso)
    let p' := @OrderIso.symm L _ (linOrd_swap L).str.toLE
              (linOrd_swap (dLexOrd WO f)).str.toLE p
    apply hausdorffScattered_of_orderIso p'
    apply HausdorffScattered.lex_sum (linOrd_swap WO) ?_ map IH _ iso
    · rcases hWO with WO | RWO
      · right; apply WO
      · left;
        apply RWO

/-- A relation describing that (x, y] inductively scattered -/
def hausdorffScattered_rel {L : LinOrd} (x y : L) : Prop :=
  let M : LinOrd := LinOrd.mk {a | (x < a ∧ a ≤ y) ∨ (y < a ∧ a ≤ x)}
  HausdorffScattered M

/-- The hausdorffScattered_rel relation is convex -/
lemma hausdorffScattered_rel_convex {L : LinOrd} (a b c : L) (h : a < b ∧ b < c) (h1 : hausdorffScattered_rel a c):
  hausdorffScattered_rel a b := by
  have : { x | a < x ∧ x ≤ b ∨ b < x ∧ x ≤ a } ⊆ { x | a < x ∧ x ≤ c ∨ c < x ∧ x ≤ a } := by
    intro x hx
    rcases hx with hx1 | hx1
    · left; exact And.intro hx1.left (le_trans hx1.right (le_of_lt h.right))
    · left; exact And.intro (lt_trans h.left hx1.left)
                            (le_of_lt (lt_of_le_of_lt hx1.right (lt_trans h.left h.right)))
  exact hausdorffScattered_of_subset' _ h1 _ this

/-- special case of the proof that scat_rel is transitive
    where the inputs are increasing -/
lemma aux_hausdorffScattered_rel_trans {L : LinOrd} {a b c : L} (hab : a ≤ b) (hbc : b ≤ c)
  (scat_ab : hausdorffScattered_rel a b) (scat_bc : hausdorffScattered_rel b c) : hausdorffScattered_rel a c := by
  apply hausdorffScattered_of_two_dLexOrd _ _ _ scat_ab scat_bc
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

/-- the hausdorffScattered_rel relation is symmetric -/
lemma hausdorffScattered_rel_symm {L : LinOrd} : ∀ {x y : L}, hausdorffScattered_rel x y → hausdorffScattered_rel y x := by
  intro x y h
  simp only [hausdorffScattered_rel] at h
  have : (fun x_1 => x < x_1 ∧ x_1 ≤ y ∨ y < x_1 ∧ x_1 ≤ x) =
          (fun x_1 => y < x_1 ∧ x_1 ≤ x ∨ x < x_1 ∧ x_1 ≤ y) := by
    apply Set.eq_of_subset_of_subset
    <;> (rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩) ;
          right; constructor <;> order ;
          left; constructor <;> order)
  have : LinOrd.mk { x_1 // x < x_1 ∧ x_1 ≤ y ∨ y < x_1 ∧ x_1 ≤ x }
         = LinOrd.mk { x_1 // y < x_1 ∧ x_1 ≤ x ∨ x < x_1 ∧ x_1 ≤ y } := by
    simp only [LinOrd.mk.injEq, this, true_and]
    exact linOrd_subtype_HEq this
  simpa only [Set.coe_setOf, this] using h

/-- hausdorffScattered_rel is an equivalence relation -/
lemma hausdorffScattered_rel_equivalence {L : LinOrd}: Equivalence (@hausdorffScattered_rel L) := by
  constructor
  · intro x
    apply (hausdorffScattered_of_wellFounded (LinOrd.mk { x_1 // x < x_1 ∧ x_1 ≤ x ∨ x < x_1 ∧ x_1 ≤ x }))
    apply @wellFounded_of_isEmpty _ ?_
    by_contra nonempt
    simp only [or_self, not_isEmpty_iff] at nonempt
    rcases nonempt with ⟨x_1, hx_1⟩
    exact lt_irrefl x (lt_of_lt_of_le hx_1.left hx_1.right)
  · exact hausdorffScattered_rel_symm
  · intro x y z scat_xy scat_yz
    rcases L.str.le_total x y, L.str.le_total y z with ⟨hxy | hxy, hyz | hyz⟩
    -- every case is either a subset or layered intervals
    · exact aux_hausdorffScattered_rel_trans hxy hyz scat_xy scat_yz
    · rcases (le_or_gt x z) with hxz | hz
      · apply hausdorffScattered_of_subset' _ scat_xy
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (left; constructor <;> order)
      · apply hausdorffScattered_of_subset' _ scat_yz
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (right; constructor <;> order)
    · rcases (le_or_gt x z) with hxz | hz
      · apply hausdorffScattered_of_subset' _ scat_yz
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (left; constructor <;> order)
      · apply hausdorffScattered_of_subset' _ scat_xy
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (right; constructor <;> order)
    · exact hausdorffScattered_rel_symm (aux_hausdorffScattered_rel_trans hyz hxy
        (hausdorffScattered_rel_symm scat_yz) (hausdorffScattered_rel_symm scat_xy))

/-- if hausdorffScattered_rel x y, then the LinOrd restricted to [x, y] is also HausdorffScatteredtered -/
lemma hausdorffScattered_closed_interval {L : LinOrd} (x y : L) (h : hausdorffScattered_rel x y):
  HausdorffScattered (LinOrd.mk {a | (x ≤ a ∧ a ≤ y) ∨ (y ≤ a ∧ a ≤ x)}) := by
  wlog hxy : x ≤ y
  · push_neg at hxy
    apply hausdorffScattered_of_orderIso _ (this y x (Equivalence.symm hausdorffScattered_rel_equivalence h) (le_of_lt hxy))
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
  · apply hausdorffScattered_of_two_dLexOrd _ (LinOrd.mk ({x} : Set L))
                                      (LinOrd.mk {a | x < a ∧ a ≤ y})
    · apply hausdorffScattered_of_wellFounded
      exact wellFounded_lt
    · apply hausdorffScattered_of_orderIso _ h
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

/-- if (x, y] is HausdorffScatteredtered, so is [x, y) -/
lemma hausdorffScattered_interval_flip_bounds {L : LinOrd}
  (x y : L) (h : hausdorffScattered_rel x y):
  HausdorffScattered (LinOrd.mk {a | (x ≤ a ∧ a < y) ∨ (y ≤ a ∧ a < x)}) := by
  apply hausdorffScattered_of_subset' _ (hausdorffScattered_closed_interval x y h)
  rintro a (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · left; exact And.intro h1 (le_of_lt h2)
  · right; exact And.intro h1 (le_of_lt h2)

/-- any order which is not a NoMaxOrder has a maximum element-/
lemma max_of_noMaxOrder {L : LinOrd} (hm : ¬ NoMaxOrder L):
  ∃ a : L, ∀ b, b ≤ a := by
  by_contra! h
  apply hm
  constructor
  intro a
  rcases h a with ⟨b ,hb⟩
  use b

--//////////////////////////////////////////////////////////////////////////////////////////////////////////
-- Hausdorff's theorem
--//////////////////////////////////////////////////////////////////////////////////////////////////////////

/-- Given a LinOrd and a subset I, map each element a of I to all the elements of the
    LinOrd less than a, but not less than any earlier element of I -/
def partition_mk {L : LinOrd} {I : Set L} (a : I) := {z : L | z ≤ a ∧ ∀ a' < a, a' < z}

/-- If the indexing set is WF cofinal, the partition_mk partitions the LinOrd -/
lemma partition_mk_of_cofinal {L : LinOrd} {Cof : Set L}
  (hCof : IsCofinal Cof ∧ Cof.WellFoundedOn fun x1 x2 ↦ x1 < x2)
  (nomax : NoMaxOrder L) : ∀ z : L, ∃! (a : Cof), z ∈ partition_mk a := by
  intro z
  let final := {a : Cof | z ≤ a}
  have final_nonempt : final.Nonempty := by
    rw [Set.nonempty_def]
    rcases nomax.exists_gt z with ⟨z', hz'⟩
    rcases hCof.left z' with ⟨y, hy⟩
    use ⟨y, hy.left⟩
    exact le_of_lt (lt_of_lt_of_le hz' hy.right)

  rcases (@WellFounded.wellFounded_iff_has_min _ (· < ·)).mp hCof.right final final_nonempt
    with ⟨lb, ⟨hlb1, hlb2⟩⟩
  use lb
  constructor
  · constructor
    · exact hlb1
    · intro a ha
      by_contra! contra
      exact (hlb2 a contra) ha
  · intro y hy
    apply eq_of_le_of_le
    · by_contra! contra
      apply not_lt_of_le hlb1
      exact hy.right lb contra
    · exact le_of_not_lt (hlb2 y hy.left)

/-- Given a LinOrd and a WF cofinal subset, if the output of the partition_mk on that
    subset is always HausdorffScattered, then L is also HausdorffScattered -/
lemma hausdorffScattered_of_wellFounded_cofinal_parition (L : LinOrd) (Cof : Set L)
  (hCof : IsCofinal Cof ∧ Cof.WellFoundedOn fun x1 x2 ↦ x1 < x2)
  (all_HausdorffScattered : ∀ (w : LinOrd.mk Cof), HausdorffScattered (LinOrd.mk (partition_mk w)))
  (nomax : NoMaxOrder L):
  HausdorffScattered L := by
  have : IsWellOrder Cof _ :=
      { toIsTrichotomous := instIsTrichotomousLt,
              toIsTrans := instIsTransLt,
              toIsWellFounded := by
              constructor
              exact hCof.right }
  let J (a : Cof) := LinOrd.mk (partition_mk a)
  let Jiso : L ≃o dLexOrd (LinOrd.mk Cof) J := by
    apply @iso_of_sigma_partition L (LinOrd.mk Cof) partition_mk (partition_mk_of_cofinal hCof nomax)
    intro a b hab c hc d hd
    exact lt_of_le_of_lt hc.left (hd.right a hab)
  apply HausdorffScattered.lex_sum (LinOrd.mk Cof) ?_ J ?_ L Jiso
  · left; exact wellFounded_lt
  · exact fun w ↦ all_HausdorffScattered w

/-- given a,b in a LinOrd, the set of x ∈ (a, b] such that a and x are related is HausdorffScattered -/
lemma aux_dense_quot {L : LinOrd} {a b : L} :
  HausdorffScattered (LinOrd.mk {x | a < x ∧ x ≤ b ∧ hausdorffScattered_rel a x}) := by
  let A := { x | a < x ∧ x ≤ b ∧ hausdorffScattered_rel a x}
  rcases @exists_cofinal_wellFoundedOn_subset A inferInstance with ⟨Cof, hCof⟩
  rcases Classical.em (NoMaxOrder (LinOrd.mk A)) with nomax | max
  · apply hausdorffScattered_of_wellFounded_cofinal_parition _ Cof hCof ?_ nomax
    intro w
    let k := hausdorffScattered_of_subset'' _ A w.1.2.right.right
    apply @hausdorffScattered_of_subset' (LinOrd.mk A) _ k { x : A | x ≤ ↑w ∧ ∀ a' < w, ↑a' < x }
    intro x ⟨hx1, hx2⟩
    left; exact And.intro x.2.left hx1
  · rcases (max_of_noMaxOrder max) with ⟨m, hm⟩
    let p := m.2.right.right
    apply hausdorffScattered_of_subset' _ p
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
lemma hausdorffScattered_rel_swap {L : LinOrd} (a b : L) :
  @hausdorffScattered_rel L a b → @hausdorffScattered_rel (linOrd_swap L) a b := by
  simp only [hausdorffScattered_rel]
  intro h
  rw [subtype_swap]
  let p := hausdorffScattered_swap (hausdorffScattered_interval_flip_bounds a b h)
  simp [linOrd_swap] at p
  apply hausdorffScattered_of_orderIso _ p
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

/-- The quotient of HausdorffScattered is dense -/
lemma hausdorffScattered_rel_dense_quot {L : LinOrd} {a b : L} (h : ¬ hausdorffScattered_rel a b) (hl : a < b) :
  ∃ c, a < c ∧ c ≤ b ∧ ¬ hausdorffScattered_rel a c ∧ ¬ hausdorffScattered_rel c b := by
  by_contra! contra
  -- split the interval into elements related to a and elements related to b
  let A := { x | a < x ∧ x ≤ b ∧ hausdorffScattered_rel a x}
  let B := { x | a < x ∧ x ≤ b ∧ hausdorffScattered_rel x b}
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
    apply hausdorffScattered_of_two_dLexOrd _ _ _ hxA3 hxB3
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
  -- show that the interval must be HausdorffScattered by showing it is isomorphic to the LinOrd with
  -- B ontop of A
  apply h
  apply hausdorffScattered_of_two_dLexOrd _ (LinOrd.mk A) (LinOrd.mk B)
  · exact aux_dense_quot
  · -- use the previous case to show that the result holds for modified interval bounds
    have : HausdorffScattered (LinOrd.mk { x // a ≤ x ∧ x < b ∧ hausdorffScattered_rel x b }) := by
      apply @hausdorffScattered_swap
        (linOrd_swap (LinOrd.mk { x // a ≤ x ∧ x < b ∧ hausdorffScattered_rel x b }))
      apply hausdorffScattered_of_orderIso _ (@aux_dense_quot (linOrd_swap L) b a)
      exact {
        toFun := fun x => ⟨x,
          by
          split_ands; exact x.2.right.left ; exact x.2.left
          exact hausdorffScattered_rel_swap x.1 b
            (Equivalence.symm hausdorffScattered_rel_equivalence x.2.right.right)⟩
        invFun := fun x => ⟨x,
          by
            split_ands; exact x.2.right.left ; exact x.2.left
            exact hausdorffScattered_rel_swap b x.1
              (Equivalence.symm hausdorffScattered_rel_equivalence x.2.right.right)⟩
        left_inv := by intro _; trivial
        right_inv := by intro _; trivial
        map_rel_iff' := by intro _ _; trivial }

    have : HausdorffScattered (LinOrd.mk { x | a < x ∧ x < b ∧ hausdorffScattered_rel x b }) := by
      apply hausdorffScattered_of_subset' _ this
      rintro x ⟨hx1, hx2, hx3⟩
      exact And.intro (le_of_lt hx1) (And.intro hx2 hx3)

    apply hausdorffScattered_of_two_dLexOrd _
      (LinOrd.mk { x | a < x ∧ x < b ∧ hausdorffScattered_rel x b })
      (LinOrd.mk ({b} : Set L)) this
    · exact hausdorffScattered_of_singleton b
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
            · exact Equivalence.refl hausdorffScattered_rel_equivalence b
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
      have : hausdorffScattered_rel a c := by
        apply hausdorffScattered_of_subset' _ hd3
        rintro x (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩)
        · left; constructor <;> order
        · right; constructor <;> order
      apply empty_inter
      use c
      split_ands <;> (first | order | exact this | exact hc3)

/-- Given a LinOrd where all elements are related by hausdorffScattered_rel, any final segment
    of the LinOrd is HausdorffScatteredttered -/
lemma hausdorffScattered_of_final_segment_of_one_class (X : LinOrd)
  (x : X) (one_class : ∀ x y : X, hausdorffScattered_rel x y) : HausdorffScattered (LinOrd.mk {x_1 // x < x_1}) := by
  rcases @exists_cofinal_wellFoundedOn_subset {x_1 // x_1 > x} inferInstance with ⟨Cof, hCof⟩
  rcases Classical.em (NoMaxOrder (LinOrd.mk {x_1 // x < x_1})) with nomax | max
  · apply hausdorffScattered_of_wellFounded_cofinal_parition (LinOrd.mk {x_1 // x < x_1}) Cof hCof ?_ nomax
    intro w
    specialize one_class x w
    let p :=  hausdorffScattered_of_subset'' ((fun x_1 => x < x_1 ∧ x_1 ≤ ↑↑w ∨ ↑↑w < x_1 ∧ x_1 ≤ x))
                                    (fun x_1 => x < x_1 ) one_class
    apply @hausdorffScattered_of_subset' (LinOrd.mk { x_2 // x < x_2 }) _ p
                            { x_1 | x_1 ≤ ↑w ∧ ∀ a' < w, ↑a' < x_1 }
    simp only [Subtype.forall, Set.setOf_subset_setOf]
    intro a ha haw
    left; exact And.intro ha haw.left
  · rcases isEmpty_or_nonempty (LinOrd.mk { x_1 // x < x_1 }) with empt | nonempt
    · exact hausdorffScattered_empty _ empt
    rcases (max_of_noMaxOrder max) with ⟨m, hm⟩
    apply hausdorffScattered_of_orderIso ?_ (one_class x m)
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

/-- The class of Scattered orders is the same as the class of HausdorffScattered orders-/
theorem hausdorff_scattered_orders (X : LinOrd): Scattered X ↔ HausdorffScattered X := by
  constructor
  · intro X_scat
    rcases Classical.em (Nonempty X) with nonempt | empt; swap
    · rw [not_nonempty_iff] at empt
      exact hausdorffScattered_empty X empt
    rcases Classical.em (∀ x y : X, hausdorffScattered_rel x y) with one_class | mult_class
    · rcases Classical.exists_true_of_nonempty nonempt with ⟨x⟩
      have final_HS : HausdorffScattered (LinOrd.mk {x_1 // x < x_1}) := by
        exact hausdorffScattered_of_final_segment_of_one_class _ x one_class
      have initial_HS : HausdorffScattered (LinOrd.mk {x_1 // x_1 < x}) := by
        let X' := linOrd_swap X
        have X_eq: X.carrier = X'.carrier := by exact rfl

        let L : LinOrd := linOrd_swap (LinOrd.mk { x_1 // x_1 < x })
        let M : LinOrd := LinOrd.mk { x_1 : X' // @LT.lt X' _ (X_eq ▸ x) x_1}

        apply @hausdorffScattered_swap L

        let iso : @OrderIso L M L.str.toLE M.str.toLE := by
          exact {
          toFun := fun y => y
          invFun := fun y => y
          left_inv := by intro _; trivial
          right_inv := by intro _; trivial
          map_rel_iff' := by intro _ _; simp only [Equiv.coe_fn_mk] }

        apply hausdorffScattered_of_orderIso iso
        apply hausdorffScattered_of_final_segment_of_one_class X' (X_eq ▸ x)

        intro x y
        let p := hausdorffScattered_swap (@hausdorffScattered_interval_flip_bounds X y x (one_class y x))
        apply hausdorffScattered_of_orderIso _ p

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

      apply HausdorffScattered.lex_sum Three.L (Or.inl (@Finite.to_wellFoundedLT Three Three.instFinite).1)
        (fun w => LinOrd.mk (f w))
      · intro w; cases w
        · exact initial_HS
        · exact hausdorffScattered_of_singleton x
        · exact final_HS
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

    · let K : Setoid X := ⟨hausdorffScattered_rel, hausdorffScattered_rel_equivalence⟩
      let f := @Quotient.out X K
      let reps := Set.range f

      by_contra;
      rw [Scattered, <-not_nonempty_iff] at X_scat
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
        have nrel : ¬ hausdorffScattered_rel x.1 y := by
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

        rcases hausdorffScattered_rel_dense_quot nrel hxy with ⟨c, hc1, hc2, hc3, hc4⟩
        let z : reps := ⟨(f ⟦c⟧), by simp [reps]⟩
        have hzc : hausdorffScattered_rel z c := by
          apply Quotient.mk_out c
        use z
        by_contra! bounds
        rcases le_or_lt z x with h | h
        · apply hc3
          apply hausdorffScattered_of_subset' _ hzc
          rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
          · left; exact And.intro (lt_of_le_of_lt h ha1) ha2
          · by_contra; apply not_lt_of_le ha2
            exact lt_trans hc1 ha1
        · apply hc4
          apply hausdorffScattered_of_subset' _ hzc
          rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
          · right; exact And.intro ha1 (le_trans ha2 (bounds h))
          · by_contra; apply not_lt_of_le ha2
            exact lt_of_le_of_lt hc2 ha1

      rcases Order.embedding_from_countable_to_dense ℚ reps with ⟨f1⟩
      apply Nonempty.intro (OrderEmbedding_comp f1 (Set.coeEmb reps))

-- RIGHT TO LEFT
  · intro X_scat_prop
    induction' X_scat_prop with lo x single_lo lo_lex WF_RWF ind scat_prop_of_ind L Liso is_scat_f
    · -- singleton case
      by_contra h
      rw [Scattered, <-not_nonempty_iff, not_not] at h
      rcases h with ⟨f⟩
      apply Rat.zero_ne_one
      apply @f.inj' 0 1
      have (y : lo) : y ∈ ({x} : Set lo) := by
        rw [single_lo]
        exact Set.mem_univ y
      exact Eq.trans (this (f 0)) (this (f 1)).symm
    · -- inductive case
      apply scatttered_of_iso_to_scattered L (dLexOrd lo_lex ind) Liso
      by_contra h
      rw [Scattered, <-not_nonempty_iff, not_not] at h
      rcases h with ⟨f⟩
      let f' (x) := (f x).1
      rcases Decidable.em (Function.Injective f') with inj | ninj
      · have : Scattered lo_lex := by
          rcases WF_RWF with h₁ | h₁
          · exact scattered_of_wellFounded lo_lex h₁
          · exact scattered_of_rev_wellFounded lo_lex h₁
        apply not_nonempty_iff.mpr this
        exact Nonempty.intro {
          toFun := f'
          inj' := inj
          map_rel_iff' := by
            intro a b; simp [f']
            constructor
            · intro h
              apply (@f.map_rel_iff' a b).mp
              apply Sigma.Lex.le_def.mpr
              rcases le_iff_lt_or_eq.mp h with h₁ | h₁
              · left; exact h₁
              · right; use h₁
                cases inj h₁
                trivial
            · intro h
              rcases Sigma.Lex.le_def.mp ((@f.map_rel_iff' a b).mpr h) with h₁ | h₁
              · exact le_of_lt h₁
              · rcases h₁ with ⟨h₂, _⟩
                exact le_of_eq h₂ }
      · rw [Function.not_injective_iff] at ninj
        rcases ninj with ⟨x, y, h⟩
        wlog hxy : x < y
        · apply this X lo_lex WF_RWF ind scat_prop_of_ind L Liso is_scat_f f y x
            ((And.intro h.left.symm) h.right.symm)
            (lt_of_le_of_ne (le_of_not_lt hxy) h.right.symm)
        let s := {z | x < z ∧ z < y}
        have sQ : Nonempty (ℚ ≃o s) := by
          apply @Order.iso_of_countable_dense ℚ s _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
          · exact SetCoe.countable s
          · constructor; intro x' y' h
            let ⟨z, h₁⟩ := LinearOrderedSemiField.toDenselyOrdered.dense x'.1 y'.1 h
            use ⟨z, And.intro (lt_trans x'.2.left h₁.left) (lt_trans h₁.right y'.2.right)⟩
            exact h₁
          · constructor
            intro x'
            let ⟨y', h₁⟩ := LinearOrderedSemiField.toDenselyOrdered.dense x x'.1 x'.2.left
            use ⟨y', And.intro h₁.left (lt_trans h₁.right x'.2.right)⟩
            exact h₁.right
          · constructor
            intro x'
            let ⟨y', h₁⟩ := LinearOrderedSemiField.toDenselyOrdered.dense x'.1 y x'.2.right
            use ⟨y', And.intro (lt_trans x'.2.left h₁.left) h₁.right⟩
            exact h₁.left
          · let ⟨z, h₁⟩ := LinearOrderedSemiField.toDenselyOrdered.dense x y hxy
            exact ⟨z, h₁⟩
        rcases sQ with ⟨sQf⟩
        let g' : (f '' s) ↪o (ind (f x).1) :=
          embed_dLexOrd (f x).1 (f '' s)
            (by
              rintro b1 ⟨b2, hb⟩
              rw [<-hb.right]
              rcases Sigma.Lex.le_def.mp (f.map_rel_iff'.mpr (le_of_lt hb.left.left))
                with h₁ | ⟨h₁, _⟩
              · by_contra
                apply not_lt_of_le (le_of_eq h.left.symm)
                rcases Sigma.Lex.le_def.mp (f.map_rel_iff'.mpr (le_of_lt hb.left.right))
                  with h₂ | ⟨h₂, _⟩
                · exact lt_trans h₁ h₂
                · rw [h₂] at h₁
                  exact h₁
              · exact h₁.symm)

        apply not_nonempty_iff.mpr (is_scat_f (f x).1)
        let f' := OrderEmbedding_restrict f s
        exact Nonempty.intro (OrderEmbedding_comp (OrderEmbedding_comp sQf.toOrderEmbedding f') g')
