import KltDP.Geometry.PrimeCurveLineDegree
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# Degree of the actual restriction to a prime curve

The coefficient sheaf is the existing pullback along the original closed
immersion `C.inclusion`. The Euler value is taken on the original curve
with its original map `C.toSpec`. All comparisons below use actual
module-sheaf isomorphisms or their existing Picard class comparisons.

This constructs restriction degree, the right side of Stacks 0BEY. It does
not identify it with an independently constructed numerical intersection,
nor prove tensor additivity or symmetry.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open ModuleCohomology

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}
  (C : X.PrimeCurve)

/-- Pullback along the identity has the original sheaf's degree, by the
actual pullback identity isomorphism. -/
theorem lineDegree_pullback_id (L : InvertibleSheaf C.toScheme) :
    C.lineDegree (pullbackInvertibleSheaf (𝟙 C.toScheme) L) = C.lineDegree L :=
  C.lineDegree_eq_of_iso ((schemeModulePullbackIdIso C.toScheme).app L.obj)

/-- Iterated and composite pullback have equal degree on this same curve.
The cohomology base morphism remains `C.toSpec` on both sides. -/
theorem lineDegree_pullback_comp {Y Z : Scheme.{u}}
    (g : C.toScheme ⟶ Y) (f : Y ⟶ Z) (L : InvertibleSheaf Z) :
    C.lineDegree (pullbackInvertibleSheaf g (pullbackInvertibleSheaf f L)) =
      C.lineDegree (pullbackInvertibleSheaf (g ≫ f) L) :=
  C.lineDegree_eq_of_iso ((schemeModulePullbackCompIso g f).app L.obj)

/-- The exact same pullback composition comparison transports the
explicit finite-dimensionality contract, for each original cohomology group. -/
theorem pullback_comp_finiteDimensional_iff {Y Z : Scheme.{u}}
    (g : C.toScheme ⟶ Y) (f : Y ⟶ Z) (M : Z.Modules) (n : ℕ) :
    FiniteDimensional k ((baseFunctor C.toSpec n).obj
      ((schemeModulePullback g).obj ((schemeModulePullback f).obj M))) ↔
    FiniteDimensional k ((baseFunctor C.toSpec n).obj
      ((schemeModulePullback (g ≫ f)).obj M)) :=
  finiteDimensional_iff_of_iso C.toSpec
    ((schemeModulePullbackCompIso g f).app M) n

/-- Degree of the original surface line bundle restricted along the
actual prime curve's original closed immersion. -/
def restrictionDegree (L : InvertibleSheaf X.toScheme) : ℤ :=
  C.lineDegree (pullbackInvertibleSheaf C.inclusion L)

/-- The restriction construction computes the Euler difference of the
actual pulled-back surface module, on the actual curve. -/
theorem restrictionDegree_eq_euler (L : InvertibleSheaf X.toScheme) :
    C.restrictionDegree L =
      eulerCharacteristic C.toSpec ((schemeModulePullback C.inclusion).obj L.obj) -
        eulerCharacteristic C.toSpec
          (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf) := rfl

/-- The actual restriction has no cohomology above one. -/
theorem restriction_cohomology_subsingleton (L : InvertibleSheaf X.toScheme)
    (n : ℕ) (hn : 1 < n) :
    Subsingleton (H ((schemeModulePullback C.inclusion).obj L.obj) n) :=
  C.cohomology_subsingleton _ n hn

/-- Finiteness of actual restriction cohomology reduces to H0 and H1. -/
theorem restriction_cohomology_finiteDimensional_iff
    (L : InvertibleSheaf X.toScheme) :
    (∀ n, FiniteDimensional k ((baseFunctor C.toSpec n).obj
      ((schemeModulePullback C.inclusion).obj L.obj))) ↔
      FiniteDimensional k ((baseFunctor C.toSpec 0).obj
        ((schemeModulePullback C.inclusion).obj L.obj)) ∧
      FiniteDimensional k ((baseFunctor C.toSpec 1).obj
        ((schemeModulePullback C.inclusion).obj L.obj)) :=
  C.cohomology_finiteDimensional_iff _

/-- Surface coefficient isomorphisms induce actual isomorphisms after
restriction, hence equal degrees. -/
theorem restrictionDegree_eq_of_iso {L M : InvertibleSheaf X.toScheme}
    (e : L.obj ≅ M.obj) : C.restrictionDegree L = C.restrictionDegree M :=
  C.lineDegree_eq_of_iso ((schemeModulePullback C.inclusion).mapIso e)

/-- Pulling back the actual surface structure sheaf gives the actual
curve structure sheaf; its restriction degree is zero. -/
@[simp]
theorem restrictionDegree_trivial :
    C.restrictionDegree (InvertibleSheaf.trivial X.toScheme) = 0 :=
  C.lineDegree_eq_zero_of_iso_unit _ (schemeModulePullbackUnitIso C.inclusion)

/-- Restricting a line bundle already pulled back to the surface equals
the degree of pullback along the original composite curve morphism. -/
theorem restrictionDegree_pullback {Y : Scheme.{u}}
    (f : X.toScheme ⟶ Y) (L : InvertibleSheaf Y) :
    C.restrictionDegree (pullbackInvertibleSheaf f L) =
      C.lineDegree (pullbackInvertibleSheaf (C.inclusion ≫ f) L) :=
  C.lineDegree_pullback_comp C.inclusion f L

/-- Restriction degree on the original surface Picard group. -/
def picardRestrictionDegree (p : X.toScheme.Pic) : ℤ :=
  C.picardDegree (schemePicardPullbackHom C.inclusion p)

/-- The class-level construction computes the original sheaf restriction. -/
@[simp]
theorem picardRestrictionDegree_toPic (L : InvertibleSheaf X.toScheme) :
    C.picardRestrictionDegree L.toPic = C.restrictionDegree L := by
  unfold picardRestrictionDegree restrictionDegree
  rw [schemePicardPullbackHom_toPic, C.picardDegree_toPic]

/-- Trivial surface Picard class has restriction degree zero. -/
@[simp]
theorem picardRestrictionDegree_one : C.picardRestrictionDegree 1 = 0 := by
  simp only [picardRestrictionDegree, map_one, picardDegree_one]

/-- The restriction degree depends only on the original surface Picard
class, without using any tensor-additivity theorem for degree. -/
theorem restrictionDegree_eq_of_toPic_eq {L M : InvertibleSheaf X.toScheme}
    (h : L.toPic = M.toPic) : C.restrictionDegree L = C.restrictionDegree M := by
  rw [← C.picardRestrictionDegree_toPic L, ← C.picardRestrictionDegree_toPic M, h]

/-- Picard pullback composition agrees with the same composite restriction
used in the original coefficient-sheaf comparison. -/
theorem picardRestrictionDegree_pullback {Y : Scheme.{u}}
    (f : X.toScheme ⟶ Y) (p : Y.Pic) :
    C.picardRestrictionDegree (schemePicardPullbackHom f p) =
      C.picardDegree (schemePicardPullbackHom (C.inclusion ≫ f) p) := by
  unfold picardRestrictionDegree
  rw [schemePicardPullbackHom_comp]
  rfl

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
