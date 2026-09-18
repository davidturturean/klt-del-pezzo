import KltDP.Geometry.NormalModelLocalFrameConstructor
import KltDP.Geometry.CanonicalCoordinateOpenComposition
import KltDP.Geometry.CanonicalOpenCoordinateCongruence

/-!
# The existing canonical-frame constructor on an original open chart

Apply `ofCanonicalDivisor` to the actual signed pullback and the original
normalized differential isomorphism. Its normalization and order follow
from the same original open-composition and stalk-order formulas. In
particular the source can be the literal spectrum of an affine chart ring.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalModelCanonical.LocalFrame

open CartierRationalCoordinate DominantCartierPullback OpenImmersionRational

attribute [local instance] integralSchemeStalk_isDomain
attribute [local irreducible] canonicalOpenPullbackIso

local instance openFrameIntegralOpen {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

local instance openFrameOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- The existing original Cartier-frame constructor on any original open
chart retains both normalization and the original model order. -/
theorem ofCanonicalDivisor_open_normalized
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (U : X.toScheme.Opens) [Nonempty U.toScheme]
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    {V Y : Scheme.{u}} [IsIntegral V] [IsIntegral Y]
    (v : V ⟶ X.toScheme) (x : V) [IsDiscreteValuationRing (V.presheaf.stalk x)]
    (F : LocalFrame (v ≫ X.structureMorphism) x)
    (hF : IsNormalized X U KU eKU v x F)
    (j : Y ⟶ F.neighborhood) [IsOpenImmersion j]
    (y : Y) (hy : j.base y = F.point) :
    let sY := (j ≫ F.toModel) ≫ (v ≫ X.structureMorphism)
    let hp : (j ≫ F.toModel).base y = x := by
      rw [Scheme.comp_base_apply, hy, F.point_eq]
    letI : IsSmoothOfRelativeDimension 2 sY := by
      change IsSmoothOfRelativeDimension 2 ((j ≫ F.toModel) ≫ (v ≫ X.structureMorphism))
      rw [Category.assoc]
      exact IsLocalAtSource.comp (P := @IsSmoothOfRelativeDimension 2) F.smooth j
    let G := ofCanonicalDivisor (v ≫ X.structureMorphism) (j ≫ F.toModel) y x hp
      (pullbackHom j F.divisor)
      (canonicalOpenPullbackIso j (F.toModel ≫ (v ≫ X.structureMorphism)) sY
        (Category.assoc j F.toModel (v ≫ X.structureMorphism)).symm F.divisor F.canonicalIso)
    IsNormalized X U KU eKU v x G ∧ G.order = F.order := by
  let sF := F.toModel ≫ (v ≫ X.structureMorphism)
  let sY := (j ≫ F.toModel) ≫ (v ≫ X.structureMorphism)
  have hjbase : j ≫ sF = sY := (Category.assoc j F.toModel (v ≫ X.structureMorphism)).symm
  have hp : (j ≫ F.toModel).base y = x := by
    rw [Scheme.comp_base_apply, hy, F.point_eq]
  letI : IsSmoothOfRelativeDimension 2 sY := by
    change IsSmoothOfRelativeDimension 2 ((j ≫ F.toModel) ≫ (v ≫ X.structureMorphism))
    rw [Category.assoc]
    exact IsLocalAtSource.comp (P := @IsSmoothOfRelativeDimension 2) F.smooth j
  let G := ofCanonicalDivisor (v ≫ X.structureMorphism) (j ≫ F.toModel) y x hp
    (pullbackHom j F.divisor)
    (canonicalOpenPullbackIso j sF sY hjbase F.divisor F.canonicalIso)
  change IsNormalized X U KU eKU v x G ∧ G.order = F.order
  constructor
  · obtain ⟨A, hne, aU, haU, htriangle, hcoordinate⟩ := hF
    letI := hne
    letI : Nonempty A := ⟨Classical.choice hne⟩
    letI : IsIntegral A.toScheme := isIntegral_of_isOpenImmersion A.ι
    letI := haU
    let T := j ⁻¹ᵁ A
    letI : Nonempty T.toScheme := ⟨Classical.choice (preimage_nonempty j A)⟩
    letI : IsIntegral T.toScheme := isIntegral_of_isOpenImmersion T.ι
    let i : T.toScheme ⟶ A.toScheme := j ∣_ A
    have hi : i ≫ A.ι = T.ι ≫ j := morphismRestrict_ι j A
    have hnew : (i ≫ aU) ≫ U.ι = (T.ι ≫ (j ≫ F.toModel)) ≫ v := by
      rw [Category.assoc, htriangle]
      simpa only [Category.assoc] using congrArg (fun a => a ≫ F.toModel ≫ v) hi
    refine ⟨T, inferInstance, i ≫ aU, inferInstance, hnew, ?_⟩
    let sU := U.ι ≫ X.structureMorphism
    let sA := A.ι ≫ sF
    let sT := T.ι ≫ sY
    have haBase : aU ≫ sU = sA := by
      simpa only [Category.assoc] using
        congrArg (fun a => a ≫ X.structureMorphism) htriangle
    have hibase : i ≫ sA = sT := by
      simpa only [Category.assoc] using congrArg (fun a => a ≫ sF) hi
    have hleftbase : (T.ι ≫ j) ≫ sF = sT := by rw [Category.assoc, hjbase]
    have hrightbase : (i ≫ A.ι) ≫ sF = sT := by rw [Category.assoc]; exact hibase
    have h₁ := coordinate_canonicalOpenPullbackIso_comp T.ι j sF sY sT
      hjbase rfl F.divisor F.canonicalIso
    have h₂ := coordinate_canonicalOpenPullbackIso_congr (T.ι ≫ j) (i ≫ A.ι)
      hi.symm sF sT hleftbase hrightbase F.divisor F.canonicalIso
    have h₃ := coordinate_canonicalOpenPullbackIso_comp i A.ι sF sA sT
      rfl hibase F.divisor F.canonicalIso
    have h₄ := canonicalOpenPullback_coordinate_congr sA sT i hibase
      (pullbackHom A.ι F.divisor) (pullbackHom aU KU)
      (canonicalOpenPullbackIso A.ι sF sA rfl F.divisor F.canonicalIso)
      (canonicalOpenPullbackIso aU sU sA haBase KU eKU) hcoordinate
    have h₅ := coordinate_canonicalOpenPullbackIso_comp i aU sU sA sT
      haBase hibase KU eKU
    exact h₁.trans (h₂.trans (h₃.symm.trans (h₄.trans h₅)))
  · letI : IsDiscreteValuationRing (Y.presheaf.stalk y) :=
      stalk_isDiscreteValuationRing_of_isOpenImmersion j y F.point hy
    calc
      G.order = cartierOrderAt Y (pullbackHom j F.divisor) y := order_eq_cartierOrderAt G
      _ = cartierOrderAt F.neighborhood F.divisor F.point := by
        rw [pullbackHom_eq_cartierRestrictionHom]
        exact cartierOrderAt_cartierRestrictionHom j F.divisor y F.point hy
      _ = F.order := (order_eq_cartierOrderAt F).symm

end KltDP.Geometry.NormalModelCanonical.LocalFrame

#check @KltDP.Geometry.NormalModelCanonical.LocalFrame.ofCanonicalDivisor_open_normalized
#print axioms KltDP.Geometry.NormalModelCanonical.LocalFrame.ofCanonicalDivisor_open_normalized
