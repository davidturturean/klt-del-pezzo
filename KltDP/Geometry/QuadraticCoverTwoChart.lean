import KltDP.Geometry.QuadraticCoverRestriction
import KltDP.Compatibility.SchemeTwoOpenGluing

/-!
# Actual quadratic-cover descent on two affine open charts

The inputs are two actual affine opens covering one scheme, actual branch
coefficients, and a unit on their affine intersection relating the coefficients
by its square. The overlap cover and both open immersion maps are constructed
from coefficient restriction and unit rescaling. Existing scheme gluing then
constructs the cover scheme, its chart inclusions, their actual intersection,
and the structural map to the original base. The structural map is flat.

No covering scheme, lifted overlap, quotient isomorphism or scheme cocycle is
supplied as an input. Arbitrary multi-chart descent, global finiteness and the
geometric branch/smoothness/integrality arguments remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCoverTwoChart

open TransitionUnitGluing QuadraticCover QuadraticCoverOpen

/-- Literal two-chart branch data on actual opens of the original scheme. -/
structure Data (X : Scheme.{u}) where
  leftOpen : X.Opens
  rightOpen : X.Opens
  left_affine : IsAffineOpen leftOpen
  right_affine : IsAffineOpen rightOpen
  overlap_affine : IsAffineOpen (leftOpen ⊓ rightOpen)
  covers : leftOpen ⊔ rightOpen = ⊤
  leftSection : Γ(X, leftOpen)
  rightSection : Γ(X, rightOpen)
  transition : Γ(X, leftOpen ⊓ rightOpen)ˣ
  branch_eq : res X (inf_le_left : leftOpen ⊓ rightOpen ≤ leftOpen) leftSection =
    (transition : Γ(X, leftOpen ⊓ rightOpen)) ^ 2 *
      res X (inf_le_right : leftOpen ⊓ rightOpen ≤ rightOpen) rightSection

/-- Actual data exist for every affine base and every global branch section,
using the two identical whole-space open charts and transition unit one. -/
def globalSectionData (X : Scheme.{u}) [IsAffine X] (a : Γ(X, ⊤)) : Data X where
  leftOpen := ⊤
  rightOpen := ⊤
  left_affine := isAffineOpen_top X
  right_affine := isAffineOpen_top X
  overlap_affine := by simpa only [inf_idem] using isAffineOpen_top X
  covers := sup_idem _
  leftSection := a
  rightSection := a
  transition := 1
  branch_eq := by simp only [Units.val_one, one_pow, one_mul]

namespace Data

variable {X : Scheme.{u}} (D : Data X)

abbrev leftChart : Scheme.{u} := affineScheme D.leftSection
abbrev rightChart : Scheme.{u} := affineScheme D.rightSection

/-- The actual overlap quadratic algebra is expressed using the left branch coefficient. -/
abbrev overlap : Scheme.{u} :=
  affineScheme (res X (inf_le_left : D.leftOpen ⊓ D.rightOpen ≤ D.leftOpen) D.leftSection)

/-- Restriction on the left requires no change of generator. -/
def leftOverlap : D.overlap ⟶ D.leftChart :=
  restrictionMap X (inf_le_left : D.leftOpen ⊓ D.rightOpen ≤ D.leftOpen) D.leftSection

/-- Restriction on the right follows the derived inverse rescaling of its generator. -/
def rightOverlap : D.overlap ⟶ D.rightChart :=
  (rescaleSpecIso
    (res X (inf_le_left : D.leftOpen ⊓ D.rightOpen ≤ D.leftOpen) D.leftSection)
    (res X (inf_le_right : D.leftOpen ⊓ D.rightOpen ≤ D.rightOpen) D.rightSection)
    D.transition D.branch_eq).inv ≫
      restrictionMap X (inf_le_right : D.leftOpen ⊓ D.rightOpen ≤ D.rightOpen) D.rightSection

instance leftOverlap_isOpenImmersion : IsOpenImmersion D.leftOverlap :=
  restrictionMap_isOpenImmersion X inf_le_left D.left_affine D.overlap_affine D.leftSection

instance rightOverlap_isOpenImmersion : IsOpenImmersion D.rightOverlap := by
  letI : IsOpenImmersion
      (restrictionMap X (inf_le_right : D.leftOpen ⊓ D.rightOpen ≤ D.rightOpen)
        D.rightSection) :=
    restrictionMap_isOpenImmersion X inf_le_right D.right_affine D.overlap_affine D.rightSection
  dsimp only [rightOverlap]
  infer_instance

/-- The original left chart structural map into the actual base scheme. -/
def leftToBase : D.leftChart ⟶ X := toBase D.leftSection ≫ D.left_affine.fromSpec

/-- The original right chart structural map into the actual base scheme. -/
def rightToBase : D.rightChart ⟶ X := toBase D.rightSection ≫ D.right_affine.fromSpec

/-- The two maps agree by the literal branch equation and actual restriction squares. -/
theorem overlap_toBase : D.leftOverlap ≫ D.leftToBase = D.rightOverlap ≫ D.rightToBase := by
  change restrictionMap X inf_le_left D.leftSection ≫
      toBase D.leftSection ≫ D.left_affine.fromSpec =
    (_ ≫ restrictionMap X inf_le_right D.rightSection) ≫
      toBase D.rightSection ≫ D.right_affine.fromSpec
  rw [restrictionMap_toBase X inf_le_left D.left_affine D.overlap_affine,
    Category.assoc, restrictionMap_toBase X inf_le_right D.right_affine D.overlap_affine,
    ← Category.assoc, rescaleSpecIso_inv_toBase]

/-- The actual scheme constructed by gluing the two quadratic charts. -/
abbrev cover : Scheme.{u} := KltDP.SchemeTwoOpenGluing.glued D.leftOverlap D.rightOverlap

/-- The actual open immersion of the left quadratic chart into the constructed scheme. -/
def leftι : D.leftChart ⟶ D.cover :=
  KltDP.SchemeTwoOpenGluing.leftι D.leftOverlap D.rightOverlap

/-- The actual open immersion of the right quadratic chart into the constructed scheme. -/
def rightι : D.rightChart ⟶ D.cover :=
  KltDP.SchemeTwoOpenGluing.rightι D.leftOverlap D.rightOverlap

instance leftι_isOpenImmersion : IsOpenImmersion D.leftι := by
  dsimp only [leftι]
  infer_instance

instance rightι_isOpenImmersion : IsOpenImmersion D.rightι := by
  dsimp only [rightι]
  infer_instance

/-- Actual chart inclusions cover the newly constructed scheme. -/
theorem jointly_surjective (y : D.cover) :
    (∃ a : D.leftChart, D.leftι.base a = y) ∨
      (∃ b : D.rightChart, D.rightι.base b = y) :=
  KltDP.SchemeTwoOpenGluing.jointly_surjective D.leftOverlap D.rightOverlap y

/-- The prescribed quadratic overlap is the actual scheme-theoretic chart intersection. -/
def overlapIsPullback : IsPullback D.leftOverlap D.rightOverlap D.leftι D.rightι :=
  KltDP.SchemeTwoOpenGluing.overlapIsPullback D.leftOverlap D.rightOverlap

/-- The structural morphism is constructed by descent, not supplied as an input. -/
def morphism : D.cover ⟶ X :=
  KltDP.SchemeTwoOpenGluing.toTarget D.leftOverlap D.rightOverlap
    D.leftToBase D.rightToBase D.overlap_toBase

@[simp, reassoc]
theorem leftι_morphism : D.leftι ≫ D.morphism = D.leftToBase :=
  KltDP.SchemeTwoOpenGluing.leftι_toTarget D.leftOverlap D.rightOverlap
    D.leftToBase D.rightToBase D.overlap_toBase

@[simp, reassoc]
theorem rightι_morphism : D.rightι ≫ D.morphism = D.rightToBase :=
  KltDP.SchemeTwoOpenGluing.rightι_toTarget D.leftOverlap D.rightOverlap
    D.leftToBase D.rightToBase D.overlap_toBase

/-- Uniqueness with respect to the actual two chart restrictions. -/
theorem morphism_unique (f : D.cover ⟶ X)
    (hl : D.leftι ≫ f = D.leftToBase) (hr : D.rightι ≫ f = D.rightToBase) :
    f = D.morphism :=
  KltDP.SchemeTwoOpenGluing.hom_ext D.leftOverlap D.rightOverlap f D.morphism
    (hl.trans D.leftι_morphism.symm) (hr.trans D.rightι_morphism.symm)

/-- The source open cover comes from the constructed scheme gluing. -/
def chartCover : D.cover.OpenCover :=
  (KltDP.SchemeTwoOpenGluing.data D.leftOverlap D.rightOverlap).openCover

/-- The descended structural map is flat, proved on the actual source open cover. -/
theorem morphism_flat : AlgebraicGeometry.Flat D.morphism := by
  apply IsLocalAtSource.of_openCover (P := @AlgebraicGeometry.Flat) D.chartCover
  intro i
  cases i
  · change AlgebraicGeometry.Flat (D.leftι ≫ D.morphism)
    rw [D.leftι_morphism]
    letI := toBase_flat D.leftSection
    change AlgebraicGeometry.Flat (toBase D.leftSection ≫ D.left_affine.fromSpec)
    infer_instance
  · change AlgebraicGeometry.Flat (D.rightι ≫ D.morphism)
    rw [D.rightι_morphism]
    letI := toBase_flat D.rightSection
    change AlgebraicGeometry.Flat (toBase D.rightSection ≫ D.right_affine.fromSpec)
    infer_instance

/-- The base-chart immersions really cover the original scheme, by the input open cover. -/
theorem base_charts_cover (x : X) :
    (∃ a : Spec Γ(X, D.leftOpen), D.left_affine.fromSpec.base a = x) ∨
      (∃ b : Spec Γ(X, D.rightOpen), D.right_affine.fromSpec.base b = x) := by
  have hx : x ∈ D.leftOpen ⊔ D.rightOpen := by rw [D.covers]; trivial
  rcases hx with hl | hr
  · apply Or.inl
    change x ∈ Set.range D.left_affine.fromSpec.base
    rw [IsAffineOpen.range_fromSpec]
    exact hl
  · apply Or.inr
    change x ∈ Set.range D.right_affine.fromSpec.base
    rw [IsAffineOpen.range_fromSpec]
    exact hr

end Data

-- Retain the original namespace API while exposing methods in their data namespace.
export Data (leftChart rightChart overlap leftOverlap rightOverlap
  leftOverlap_isOpenImmersion rightOverlap_isOpenImmersion leftToBase rightToBase
  overlap_toBase cover leftι rightι leftι_isOpenImmersion rightι_isOpenImmersion
  jointly_surjective overlapIsPullback morphism leftι_morphism leftι_morphism_assoc
  rightι_morphism rightι_morphism_assoc morphism_unique chartCover morphism_flat
  base_charts_cover)

end KltDP.Geometry.QuadraticCoverTwoChart
