import KltDP.Geometry.QuadraticRootBaseChange

/-!
# Actual root-zero pair and triple intersections

The original quadratic atlas determines root-zero charts on its original
opens and intersections. Their maps are the previously constructed maps
of actual root quotients. The proved frame composition and base-change
range laws give the pair transitions, triple pullbacks, and triple cocycle.
No additional atlas, overlap identification, or gluing conclusion is input.

Reuse: the diagram follows `QuadraticCoverAtlasIntersections`, replacing
its frame maps with the actual quotient maps and their already proved
base-change laws. The project helper `SchemeTwoOpenGluing.isPullback_of_range`
constructs the actual triple pullback from its commuting square and range.
The existing pinned scheme and category gluing APIs, also inspected in
official Mathlib revision `80cbd0498ab39e21d24d6730b3f932cec672a702`
(Apache 2.0), need no newer source port for these diagrams.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

/-- The actual root-zero quotient belonging to an original subopen frame. -/
abbrev rootZeroFrame {i : ι} {W : X.Opens} (hi : W ≤ D.opens i) : Scheme.{u} :=
  rootZeroScheme (res X hi (D.sections i))

/-- Its map to the original base factors through the original quadratic chart. -/
abbrev rootZeroFrameToBase {i : ι} {W : X.Opens}
    (hi : W ≤ D.opens i) (hW : IsAffineOpen W) : D.rootZeroFrame hi ⟶ X :=
  rootZeroι (res X hi (D.sections i)) ≫ D.frameToBase hi hW

@[reassoc]
theorem rootZeroFrameMap_toBase {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    D.rootZeroFrameMap hi hj hWV ≫ D.rootZeroFrameToBase hi hV =
      D.rootZeroFrameToBase hj hW := by
  change D.rootZeroFrameMap hi hj hWV ≫
      (rootZeroι (res X hi (D.sections i)) ≫ D.frameToBase hi hV) =
    rootZeroι (res X hj (D.sections j)) ≫ D.frameToBase hj hW
  rw [← Category.assoc, D.rootZeroFrameMap_ι, Category.assoc,
    D.map_toBase hi hj hWV hV hW]

theorem rootZeroFrameToBase_mem {i : ι} {W : X.Opens}
    (hi : W ≤ D.opens i) (hW : IsAffineOpen W) (x : D.rootZeroFrame hi) :
    (D.rootZeroFrameToBase hi hW).base x ∈ W :=
  D.frameToBase_mem hi hW ((rootZeroι (res X hi (D.sections i))).base x)

/-- Two opposite actual open inclusions give inverse root-zero frame maps. -/
def rootZeroFrameIso {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V) (hVW : V ≤ W) :
    D.rootZeroFrame hj ≅ D.rootZeroFrame hi where
  hom := D.rootZeroFrameMap hi hj hWV
  inv := D.rootZeroFrameMap hj hi hVW
  hom_inv_id := by rw [D.rootZeroFrameMap_comp, D.rootZeroFrameMap_self]
  inv_hom_id := by rw [D.rootZeroFrameMap_comp, D.rootZeroFrameMap_self]

abbrev rootZeroChart (i : ι) : Scheme.{u} :=
  D.rootZeroFrame (le_refl (D.opens i))

abbrev rootZeroChartToBase (i : ι) : D.rootZeroChart i ⟶ X :=
  D.rootZeroFrameToBase (le_refl (D.opens i)) (D.affine i)

abbrev rootZeroOverlap (i j : ι) : Scheme.{u} :=
  D.rootZeroFrame (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)

abbrev rootZeroOverlapToBase (i j : ι) : D.rootZeroOverlap i j ⟶ X :=
  D.rootZeroFrameToBase (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
    (D.pair_affine i j)

def rootZeroOverlapToChart (i j : ι) : D.rootZeroOverlap i j ⟶ D.rootZeroChart i :=
  D.rootZeroFrameMap (le_refl (D.opens i))
    (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i) inf_le_left

instance rootZeroOverlapToChart_isOpenImmersion (i j : ι) :
    IsOpenImmersion (D.rootZeroOverlapToChart i j) :=
  D.rootZeroFrameMap_isOpenImmersion _ _ _ (D.affine i) (D.pair_affine i j)

instance rootZeroOverlapToChart_self_isIso (i : ι) :
    IsIso (D.rootZeroOverlapToChart i i) := by
  let e := D.rootZeroFrameIso (le_refl (D.opens i))
    (inf_le_left : D.opens i ⊓ D.opens i ≤ D.opens i)
    inf_le_left (le_inf le_rfl le_rfl)
  exact (inferInstance : IsIso e.hom)

@[reassoc]
theorem rootZeroOverlapToChart_toBase (i j : ι) :
    D.rootZeroOverlapToChart i j ≫ D.rootZeroChartToBase i =
      D.rootZeroOverlapToBase i j :=
  D.rootZeroFrameMap_toBase _ _ _ (D.affine i) (D.pair_affine i j)

/-- The reverse pair transition is induced by the original reverse unit and restriction. -/
def rootZeroTransition (i j : ι) : D.rootZeroOverlap i j ⟶ D.rootZeroOverlap j i :=
  D.rootZeroFrameMap (inf_le_left : D.opens j ⊓ D.opens i ≤ D.opens j)
    (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
    (le_inf inf_le_right inf_le_left)

@[simp]
theorem rootZeroTransition_self (i : ι) :
    D.rootZeroTransition i i = 𝟙 (D.rootZeroOverlap i i) :=
  D.rootZeroFrameMap_self _ _

@[reassoc]
theorem rootZeroTransition_toBase (i j : ι) :
    D.rootZeroTransition i j ≫ D.rootZeroOverlapToBase j i =
      D.rootZeroOverlapToBase i j :=
  D.rootZeroFrameMap_toBase _ _ _ (D.pair_affine j i) (D.pair_affine i j)

abbrev rootZeroTriple (i j k : ι) : Scheme.{u} :=
  D.rootZeroFrame
    (inf_le_left.trans inf_le_left : (D.opens i ⊓ D.opens j) ⊓ D.opens k ≤ D.opens i)

def rootZeroTripleFst (i j k : ι) : D.rootZeroTriple i j k ⟶ D.rootZeroOverlap i j :=
  D.rootZeroFrameMap (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
    (inf_le_left.trans inf_le_left : (D.opens i ⊓ D.opens j) ⊓ D.opens k ≤ D.opens i)
    inf_le_left

def rootZeroTripleSnd (i j k : ι) : D.rootZeroTriple i j k ⟶ D.rootZeroOverlap i k :=
  D.rootZeroFrameMap (inf_le_left : D.opens i ⊓ D.opens k ≤ D.opens i)
    (inf_le_left.trans inf_le_left : (D.opens i ⊓ D.opens j) ⊓ D.opens k ≤ D.opens i)
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)

instance rootZeroTripleFst_isOpenImmersion (i j k : ι) :
    IsOpenImmersion (D.rootZeroTripleFst i j k) :=
  D.rootZeroFrameMap_isOpenImmersion _ _ _ (D.pair_affine i j) (D.triple_affine i j k)

instance rootZeroTripleSnd_isOpenImmersion (i j k : ι) :
    IsOpenImmersion (D.rootZeroTripleSnd i j k) :=
  D.rootZeroFrameMap_isOpenImmersion _ _ _ (D.pair_affine i k) (D.triple_affine i j k)

/-- The actual triple square commutes by the original frame-map composition law. -/
theorem rootZeroTriple_condition (i j k : ι) :
    D.rootZeroTripleFst i j k ≫ D.rootZeroOverlapToChart i j =
      D.rootZeroTripleSnd i j k ≫ D.rootZeroOverlapToChart i k := by
  simp only [rootZeroTripleFst, rootZeroTripleSnd, rootZeroOverlapToChart,
    rootZeroFrameMap_comp]

/-- The actual triple image is exactly the inverse image of the other pair overlap. -/
theorem rootZeroTriple_range (i j k : ι) :
    Set.range (D.rootZeroTripleFst i j k).base =
      (D.rootZeroOverlapToChart i j).base ⁻¹'
        Set.range (D.rootZeroOverlapToChart i k).base := by
  rw [rootZeroTripleFst,
    D.range_rootZeroFrameMap _ _ _ (D.pair_affine i j) (D.triple_affine i j k)]
  have hk : Set.range (D.rootZeroOverlapToChart i k).base =
      (D.rootZeroChartToBase i).base ⁻¹' ((D.opens i ⊓ D.opens k : X.Opens) : Set X) :=
    D.range_rootZeroFrameMap _ _ _ (D.affine i) (D.pair_affine i k)
  rw [hk]
  change (D.rootZeroOverlapToBase i j).base ⁻¹'
      (((D.opens i ⊓ D.opens j) ⊓ D.opens k : X.Opens) : Set X) =
    (D.rootZeroOverlapToChart i j ≫ D.rootZeroChartToBase i).base ⁻¹'
      ((D.opens i ⊓ D.opens k : X.Opens) : Set X)
  rw [D.rootZeroOverlapToChart_toBase]
  ext x
  have hx := D.rootZeroFrameToBase_mem
    (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i) (D.pair_affine i j) x
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨hx, h.2⟩⟩

/-- The original root-zero triple chart is the actual pair-chart pullback. -/
def rootZeroTripleIsPullback (i j k : ι) :
    IsPullback (D.rootZeroTripleFst i j k) (D.rootZeroTripleSnd i j k)
      (D.rootZeroOverlapToChart i j) (D.rootZeroOverlapToChart i k) :=
  KltDP.SchemeTwoOpenGluing.isPullback_of_range _ _ _ _
    (D.rootZeroTriple_condition i j k) (D.rootZeroTriple_range i j k)

/-- The actual cyclic permutation of the triple open and its root-zero frame. -/
def rootZeroTripleCycle (i j k : ι) : D.rootZeroTriple i j k ⟶ D.rootZeroTriple j k i :=
  D.rootZeroFrameMap
    (inf_le_left.trans inf_le_left : (D.opens j ⊓ D.opens k) ⊓ D.opens i ≤ D.opens j)
    (inf_le_left.trans inf_le_left : (D.opens i ⊓ D.opens j) ⊓ D.opens k ≤ D.opens i)
    (le_inf (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      (inf_le_left.trans inf_le_left))

/-- The actual root-zero maps satisfy the triple projection compatibility. -/
@[reassoc]
theorem rootZeroTripleCycle_fac (i j k : ι) :
    D.rootZeroTripleCycle i j k ≫ D.rootZeroTripleSnd j k i =
      D.rootZeroTripleFst i j k ≫ D.rootZeroTransition i j := by
  simp only [rootZeroTripleCycle, rootZeroTripleSnd, rootZeroTripleFst,
    rootZeroTransition, rootZeroFrameMap_comp]

/-- The original unit cocycle gives the actual triple cyclic identity on root quotients. -/
@[reassoc]
theorem rootZeroTripleCycle_cocycle (i j k : ι) :
    D.rootZeroTripleCycle i j k ≫ D.rootZeroTripleCycle j k i ≫
        D.rootZeroTripleCycle k i j = 𝟙 (D.rootZeroTriple i j k) := by
  simp only [rootZeroTripleCycle, rootZeroFrameMap_comp, rootZeroFrameMap_self]

end KltDP.Geometry.QuadraticCoverAtlas.Data
