import KltDP.Geometry.OriginalCartierQuadraticCanonicalFactor
import KltDP.Geometry.SmoothCanonicalCartierExterior
import KltDP.Geometry.CartierPicardHom

/-!
# Hurwitz for the same original Cartier quadratic cover

The proved original normalized factor gives the actual sheaf identity
Ω²_T ≅ π*Ω²_S ⊗ O(R), where R is the already constructed original
ramification divisor. The original smooth Cartier representatives then
satisfy the corresponding equality in the actual Picard group. No
cancellation of two-torsion or equality of arbitrary representatives is used.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

open SchemeTopDifferentialFactorSquare SmoothCanonicalCartierRepresentative
open SmoothCanonicalCartierExterior

variable {k : Type u} [Field k] [IsAlgClosed k]
  (S : NormalProjectiveSurface k) [IsSmoothOfRelativeDimension 2 S.structureMorphism]

local instance originalHurwitzSeparated : S.toScheme.IsSeparated :=
  NormalProjectiveSurface.surfaceSeparated S
local instance originalHurwitzModules (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y
local instance originalHurwitzSymmetric (Y : Scheme.{u}) : SymmetricCategory Y.Modules :=
  Scheme.Modules.symmetricCategory Y

variable (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
  (L : InvertibleSheaf S.toScheme)
  (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
  (hred : IsReduced (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
  (hne : Nonempty (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
  [IsSmoothOfRelativeDimension 1
    ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism)]

local notation "A" => effectiveCartierQuadraticAtlas S.toScheme E hE L e
local notation "T" => OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "R₀" => originalRamificationDivisor S E hE L e h2 hred hne

/-- The canonical sheaf of the same original quadratic cover is the
original pulled canonical sheaf tensored with its actual ramification line. -/
def originalCartierHurwitzIso :
    top (T).structureMorphism 2 ≅
      (schemeModulePullback (A).morphism).obj (top S.structureMorphism 2) ⊗
        cartierDivisorModule (T).toScheme (R₀) := by
  letI : IsIntegral (T).toScheme := (T).integral
  let e0 : cartierDivisorModule (T).toScheme 0 ≅ 𝟙_ (T).toScheme.Modules :=
    (by simpa only [ofMul_one, map_zero] using
      principalCartierModuleIsoUnit (T).toScheme (1 : (T).toScheme.functionFieldˣ)) ≪≫
        SchemeModuleStructureUnit.iso (T).toScheme
  let er : cartierDivisorModule (T).toScheme (R₀) ⊗
      cartierDivisorModule (T).toScheme (-(R₀)) ≅ 𝟙_ (T).toScheme.Modules :=
    cartierTensorIso (T).toScheme (R₀) (-(R₀)) ≪≫
      eqToIso (congrArg (cartierDivisorModule (T).toScheme) (add_neg_cancel (R₀))) ≪≫ e0
  exact (λ_ (top (T).structureMorphism 2)).symm ≪≫
    tensorIso er.symm (Iso.refl _) ≪≫ (α_ _ _ _) ≪≫
    tensorIso (Iso.refl (cartierDivisorModule (T).toScheme (R₀)))
      (originalCartierCanonicalFactor S E hE L e h2 hred hne).symm ≪≫
    BraidedCategory.braiding _ _

/-- The actual smooth Cartier canonical representatives satisfy Hurwitz
in the original Picard group, with the actual ramification Cartier divisor. -/
theorem originalCartierHurwitzPicard :
    letI : IsIntegral (T).toScheme := (T).integral
    letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
      originalCover_smoothTwo S E hE L e h2 hred hne
    cartierPicardHom (T).toScheme (cartierRepresentative (T).structureMorphism) =
      @Add.add (Additive (T).toScheme.Pic) inferInstance
        ((schemePicardPullbackHom (A).morphism).toAdditive
          (cartierPicardHom S.toScheme (cartierRepresentative S.structureMorphism)))
        (cartierPicardHom (T).toScheme (R₀)) := by
  letI : IsIntegral (T).toScheme := (T).integral
  letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
    originalCover_smoothTwo S E hE L e h2 hred hne
  let KS := cartierRepresentative S.structureMorphism
  let KT := cartierRepresentative (T).structureMorphism
  let ep : cartierDivisorModule (T).toScheme (-(R₀) + KT) ≅
      (schemeModulePullback (A).morphism).obj (cartierDivisorModule S.toScheme KS) :=
    (cartierTensorIso (T).toScheme (-(R₀)) KT).symm ≪≫
      tensorIso (Iso.refl _) (representativeIsoExterior (T).structureMorphism) ≪≫
      (originalCartierCanonicalFactor S E hE L e h2 hred hne).symm ≪≫
      (schemeModulePullback (A).morphism).mapIso (representativeIsoExterior S.structureMorphism).symm
  have hc := SchemeKernelIdealIsoTransport.toPic_eq_pullback_of_iso (A).morphism
    (cartierDivisorInvertibleSheaf S.toScheme KS)
    (cartierDivisorInvertibleSheaf (T).toScheme (-(R₀) + KT)) ep
  have hadd : cartierPicardHom (T).toScheme (-(R₀) + KT) =
      (schemePicardPullbackHom (A).morphism).toAdditive (cartierPicardHom S.toScheme KS) :=
    congrArg Additive.ofMul hc
  change cartierPicardHom (T).toScheme KT = _
  calc
    _ = cartierPicardHom (T).toScheme (-(R₀) + KT) + cartierPicardHom (T).toScheme (R₀) := by
      rw [map_add, map_neg]
      abel
    _ = _ := by
      rw [hadd]
      rfl

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.originalCartierHurwitzIso
#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.originalCartierHurwitzPicard
