import KltDP.Geometry.QuadraticCoverAtlasMaps
import KltDP.Compatibility.SchemeTwoOpenCoverIso

/-!
# Actual pair and triple intersections for a quadratic affine atlas

The inputs are literal affine opens, affine pair/triple intersections, actual
transition units satisfying their sheaf cocycle, and literal branch sections.
The pair and triple quadratic charts and all maps are constructed. The triple
chart is proved to be the actual pullback of the two pair-chart inclusions.
No transition isomorphism, pullback identification or scheme gluing is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas

open TransitionUnitGluing QuadraticCover

/-- Literal affine-atlas input, including the actual affine intersection properties.
No separation property of an arbitrary base scheme is implicit in these fields. -/
structure Data (X : Scheme.{u}) (ι : Type u) where
  opens : ι → X.Opens
  affine : ∀ i, IsAffineOpen (opens i)
  pair_affine : ∀ i j, IsAffineOpen (opens i ⊓ opens j)
  triple_affine : ∀ i j k, IsAffineOpen ((opens i ⊓ opens j) ⊓ opens k)
  covers : (⨆ i, opens i) = ⊤
  units : ∀ i j, Γ(X, opens i ⊓ opens j)ˣ
  cocycle : IsCocycle X opens units
  sections : ∀ i, Γ(X, opens i)
  branch : ∀ i j,
    res X (inf_le_left : opens i ⊓ opens j ≤ opens i) (sections i) =
      (units i j : Γ(X, opens i ⊓ opens j)) ^ 2 *
        res X (inf_le_right : opens i ⊓ opens j ≤ opens j) (sections j)

namespace Data

variable {X : Scheme.{u}} {ι : Type u} (D : Data X ι)

abbrev frameChart {i : ι} {W : X.Opens} (hi : W ≤ D.opens i) : Scheme.{u} :=
  localChart X D.opens D.sections i hi

abbrev map {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V) :
    D.frameChart hj ⟶ D.frameChart hi :=
  localMap X D.opens D.units D.sections D.branch hi hj hWV

@[reassoc]
theorem map_comp {i j k : ι} {V W Z : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hk : Z ≤ D.opens k)
    (hWV : W ≤ V) (hZW : Z ≤ W) :
    D.map hj hk hZW ≫ D.map hi hj hWV = D.map hi hk (hZW.trans hWV) :=
  localMap_comp X D.opens D.units D.sections D.branch D.cocycle hi hj hk hWV hZW

@[simp]
theorem map_self {i : ι} {W : X.Opens} (hi : W ≤ D.opens i) (hWW : W ≤ W) :
    D.map hi hi hWW = 𝟙 (D.frameChart hi) :=
  localMap_self X D.opens D.units D.sections D.branch D.cocycle hi hWW

abbrev frameToBase {i : ι} {W : X.Opens}
    (hi : W ≤ D.opens i) (hW : IsAffineOpen W) : D.frameChart hi ⟶ X :=
  toBase (res X hi (D.sections i)) ≫ hW.fromSpec

@[reassoc]
theorem map_toBase {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    D.map hi hj hWV ≫ D.frameToBase hi hV = D.frameToBase hj hW :=
  localMap_toBase X D.opens D.units D.sections D.branch hi hj hWV hV hW

theorem map_isOpenImmersion {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    IsOpenImmersion (D.map hi hj hWV) :=
  localMap_isOpenImmersion X D.opens D.units D.sections D.branch hi hj hWV hV hW

theorem range_map {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    Set.range (D.map hi hj hWV).base =
      (D.frameToBase hi hV).base ⁻¹' (W : Set X) :=
  range_localMap X D.opens D.units D.sections D.branch hi hj hWV hV hW

theorem frameToBase_mem {i : ι} {W : X.Opens}
    (hi : W ≤ D.opens i) (hW : IsAffineOpen W) (x : D.frameChart hi) :
    (D.frameToBase hi hW).base x ∈ W := by
  exact (hW.isoSpec.inv.base ((toBase (res X hi (D.sections i))).base x)).2

abbrev chart (i : ι) : Scheme.{u} := D.frameChart (le_refl (D.opens i))
abbrev chartToBase (i : ι) : D.chart i ⟶ X :=
  D.frameToBase (le_refl (D.opens i)) (D.affine i)

abbrev overlap (i j : ι) : Scheme.{u} :=
  D.frameChart (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)

abbrev overlapToBase (i j : ι) : D.overlap i j ⟶ X :=
  D.frameToBase (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i) (D.pair_affine i j)

def overlapToChart (i j : ι) : D.overlap i j ⟶ D.chart i :=
  D.map (le_refl (D.opens i)) (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
    inf_le_left

instance overlapToChart_isOpenImmersion (i j : ι) :
    IsOpenImmersion (D.overlapToChart i j) :=
  D.map_isOpenImmersion _ _ _ (D.affine i) (D.pair_affine i j)

instance overlapToChart_self_isIso (i : ι) : IsIso (D.overlapToChart i i) := by
  let e := localIso X D.opens D.units D.sections D.branch D.cocycle
    (le_refl (D.opens i)) (inf_le_left : D.opens i ⊓ D.opens i ≤ D.opens i)
    inf_le_left (le_inf le_rfl le_rfl)
  exact (inferInstance : IsIso e.hom)

@[reassoc]
theorem overlapToChart_toBase (i j : ι) :
    D.overlapToChart i j ≫ D.chartToBase i = D.overlapToBase i j :=
  D.map_toBase _ _ _ (D.affine i) (D.pair_affine i j)

/-- Reversing the pair uses the original reverse transition unit and actual
restriction between the two presentations of the same intersection. -/
def transition (i j : ι) : D.overlap i j ⟶ D.overlap j i :=
  D.map (inf_le_left : D.opens j ⊓ D.opens i ≤ D.opens j)
    (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
    (le_inf inf_le_right inf_le_left)

@[simp]
theorem transition_self (i : ι) : D.transition i i = 𝟙 (D.overlap i i) := by
  exact D.map_self _ _

@[reassoc]
theorem transition_toBase (i j : ι) :
    D.transition i j ≫ D.overlapToBase j i = D.overlapToBase i j :=
  D.map_toBase _ _ _ (D.pair_affine j i) (D.pair_affine i j)

abbrev triple (i j k : ι) : Scheme.{u} :=
  D.frameChart
    (inf_le_left.trans inf_le_left : (D.opens i ⊓ D.opens j) ⊓ D.opens k ≤ D.opens i)

def tripleFst (i j k : ι) : D.triple i j k ⟶ D.overlap i j :=
  D.map (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
    (inf_le_left.trans inf_le_left : (D.opens i ⊓ D.opens j) ⊓ D.opens k ≤ D.opens i)
    inf_le_left

def tripleSnd (i j k : ι) : D.triple i j k ⟶ D.overlap i k :=
  D.map (inf_le_left : D.opens i ⊓ D.opens k ≤ D.opens i)
    (inf_le_left.trans inf_le_left : (D.opens i ⊓ D.opens j) ⊓ D.opens k ≤ D.opens i)
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)

instance tripleFst_isOpenImmersion (i j k : ι) : IsOpenImmersion (D.tripleFst i j k) :=
  D.map_isOpenImmersion _ _ _ (D.pair_affine i j) (D.triple_affine i j k)

instance tripleSnd_isOpenImmersion (i j k : ι) : IsOpenImmersion (D.tripleSnd i j k) :=
  D.map_isOpenImmersion _ _ _ (D.pair_affine i k) (D.triple_affine i j k)

/-- The triple square commutes by the proved restriction/unit composition rule. -/
theorem triple_condition (i j k : ι) :
    D.tripleFst i j k ≫ D.overlapToChart i j =
      D.tripleSnd i j k ≫ D.overlapToChart i k := by
  simp only [tripleFst, tripleSnd, overlapToChart, map_comp]

/-- The triple chart has exactly the range required by the actual pullback. -/
theorem triple_range (i j k : ι) :
    Set.range (D.tripleFst i j k).base =
      (D.overlapToChart i j).base ⁻¹' Set.range (D.overlapToChart i k).base := by
  rw [tripleFst, D.range_map _ _ _ (D.pair_affine i j) (D.triple_affine i j k)]
  have hk : Set.range (D.overlapToChart i k).base =
      (D.chartToBase i).base ⁻¹' ((D.opens i ⊓ D.opens k : X.Opens) : Set X) :=
    D.range_map _ _ _ (D.affine i) (D.pair_affine i k)
  rw [hk]
  change (D.overlapToBase i j).base ⁻¹'
      (((D.opens i ⊓ D.opens j) ⊓ D.opens k : X.Opens) : Set X) =
    (D.overlapToChart i j ≫ D.chartToBase i).base ⁻¹'
      ((D.opens i ⊓ D.opens k : X.Opens) : Set X)
  rw [D.overlapToChart_toBase]
  ext x
  have hx := D.frameToBase_mem
    (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i) (D.pair_affine i j) x
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨hx, h.2⟩⟩

/-- The constructed triple quadratic chart is the actual pair-chart pullback. -/
def tripleIsPullback (i j k : ι) :
    IsPullback (D.tripleFst i j k) (D.tripleSnd i j k)
      (D.overlapToChart i j) (D.overlapToChart i k) :=
  KltDP.SchemeTwoOpenGluing.isPullback_of_range _ _ _ _
    (D.triple_condition i j k) (D.triple_range i j k)

/-- Actual cyclic permutation of the triple intersection and its quadratic frame. -/
def tripleCycle (i j k : ι) : D.triple i j k ⟶ D.triple j k i :=
  D.map
    (inf_le_left.trans inf_le_left : (D.opens j ⊓ D.opens k) ⊓ D.opens i ≤ D.opens j)
    (inf_le_left.trans inf_le_left : (D.opens i ⊓ D.opens j) ⊓ D.opens k ≤ D.opens i)
    (le_inf (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      (inf_le_left.trans inf_le_left))

/-- This is the actual chart compatibility required by the gluing library. -/
@[reassoc]
theorem tripleCycle_fac (i j k : ι) :
    D.tripleCycle i j k ≫ D.tripleSnd j k i =
      D.tripleFst i j k ≫ D.transition i j := by
  simp only [tripleCycle, tripleSnd, tripleFst, transition, map_comp]

/-- Three actual cyclic transitions compose to the identity by the original
unit cocycle, before any chosen-pullback transport is performed. -/
@[reassoc]
theorem tripleCycle_cocycle (i j k : ι) :
    D.tripleCycle i j k ≫ D.tripleCycle j k i ≫ D.tripleCycle k i j =
      𝟙 (D.triple i j k) := by
  simp only [tripleCycle, map_comp, map_self]

end Data

end KltDP.Geometry.QuadraticCoverAtlas
