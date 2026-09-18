import KltDP.Geometry.AffineSplitIntersectionPullbackConditional
import KltDP.Geometry.InvertibleQuadraticPushforwardSplitting
import KltDP.Geometry.OriginalCartierQuadraticNumericalCanonical

/-!
# Actual original quadratic-cover canonical intersection formulas

The original square-root atlas supplies its actual structure-sheaf
pushforward splitting. The proved affine projection adapter therefore
doubles intersections on that same cover. Combined with the actual
numerical Hurwitz identity, this gives the canonical mixed and square
formulas used in the manuscript. No splitting, degree, canonical-class
identity, or isomorphic replacement cover is supplied.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

open ModuleCohomology SmoothCanonicalCartierRepresentative
attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance originalIntersectionModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (hAffine : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsAffineHom f] (n : ℕ),
    ∃ e : ∀ (M : X.Modules), M.IsQuasicoherent →
      H ((schemeModulePushforward f).obj M) n ≃+ H M n,
      ∀ (M N : X.Modules) (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
        (φ : M ⟶ N) (x : H ((schemeModulePushforward f).obj M) n),
        e N hN ((zariskiFunctor Y n).map ((schemeModulePushforward f).map φ) x) =
          (zariskiFunctor X n).map φ (e M hM x))

include hAffine

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance originalIntersectionSeparated : S.toScheme.IsSeparated :=
  NormalProjectiveSurface.surfaceSeparated S

local instance originalIntersectionSectionsComm :
    ∀ U, IsMulCommutative (S.toScheme.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (S.toScheme.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

variable (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
  (L : InvertibleSheaf S.toScheme)
  (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
  (hred : IsReduced (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
  (hne : Nonempty (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)

local notation "A" => effectiveCartierQuadraticAtlas S.toScheme E hE L e
local notation "T" => OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne

/-- Pullback by the original constructed cover doubles actual intersections. -/
theorem originalCover_picardPairing_pullback
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hT : ∀ y : (T).Point, RegularPoint (T).toScheme y)
    (p q : S.toScheme.Pic) :
    (T).picardPairing hT (schemePicardPullbackHom (A).morphism p)
        (schemePicardPullbackHom (A).morphism q) = 2 * S.picardPairing hS p q := by
  letI : IsFinite (A).morphism := (A).morphism_isFinite
  let N : InvertibleSheaf S.toScheme :=
    ⟨KltDP.SheafOfModules.dual S.toScheme.ringCatSheaf L.obj, schemeDualSheaf_isInvertible L⟩
  have es : (schemeModulePushforward (A).morphism).obj
      (_root_.SheafOfModules.unit (T).toScheme.ringCatSheaf) ≅
      _root_.SheafOfModules.unit S.toScheme.ringCatSheaf ⊞ N.obj :=
    InvertibleQuadraticAtlas.squareRootPushforwardDualIso S.toScheme L
      (cartierDivisorModule S.toScheme E) e (effectiveCartierSection S.toScheme E hE)
  exact NormalProjectiveSurface.picardPairing_pullback_of_affine_line_split
    hAffine S (T) (A).morphism rfl hS hT N es p q

variable [IsSmoothOfRelativeDimension 2 S.structureMorphism]
  [IsSmoothOfRelativeDimension 1
    ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism)]

/-- The canonical mixed intersection for the same original cover and an
arbitrary original base Picard class. -/
theorem originalCover_canonical_pairing_pullback
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hT : ∀ y : (T).Point, RegularPoint (T).toScheme y)
    (p : S.toScheme.Pic) :
    letI : IsIntegral (T).toScheme := (T).integral
    letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
      originalCover_smoothTwo S E hE L e h2 hred hne
    (T).picardPairing hT
        (cartierPicardClass (T).toScheme (cartierRepresentative (T).structureMorphism))
        (schemePicardPullbackHom (A).morphism p) =
      2 * S.picardPairing hS
        (cartierPicardClass S.toScheme (cartierRepresentative S.structureMorphism) * L.toPic) p := by
  letI : IsIntegral (T).toScheme := (T).integral
  letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
    originalCover_smoothTwo S E hE L e h2 hred hne
  rw [originalCartierHurwitz_picardPairing S E hE L e h2 hred hne hT]
  exact originalCover_picardPairing_pullback hAffine S E hE L e h2 hred hne hS hT _ p

/-- The canonical square on the actual original cover is twice the square
of the actual base canonical plus half-branch line class. -/
theorem originalCover_canonical_selfIntersection
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hT : ∀ y : (T).Point, RegularPoint (T).toScheme y) :
    letI : IsIntegral (T).toScheme := (T).integral
    letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
      originalCover_smoothTwo S E hE L e h2 hred hne
    let P := cartierPicardClass S.toScheme (cartierRepresentative S.structureMorphism) * L.toPic
    (T).intersectionPairing hT (cartierRepresentative (T).structureMorphism)
        (cartierRepresentative (T).structureMorphism) = 2 * S.picardPairing hS P P := by
  letI : IsIntegral (T).toScheme := (T).integral
  letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
    originalCover_smoothTwo S E hE L e h2 hred hne
  dsimp only
  rw [originalCartierHurwitz_selfIntersection S E hE L e h2 hred hne hT]
  exact originalCover_picardPairing_pullback hAffine S E hE L e h2 hred hne hS hT _ _

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.originalCover_picardPairing_pullback
#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.originalCover_canonical_pairing_pullback
#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.originalCover_canonical_selfIntersection
