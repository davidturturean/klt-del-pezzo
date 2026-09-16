import KltDP.Geometry.GluedIdealSheafLift
import KltDP.Geometry.SchematicImageDenseOpen
import KltDP.Geometry.PrimeCurveRestrictionDegree
import KltDP.Geometry.AffinePIDInvertibleTrivial
import KltDP.Geometry.SchemeModuleFunctorial
import KltDP.Geometry.SchemeModulePullbackUnit
import KltDP.Geometry.NumericalEquivalence
import KltDP.Geometry.RationalTreePicardMultidegree

/-!
# The prime-curve inclusion of a closed immersion, and degree zero over a point

Let `P` be a prime curve of a normal projective surface `X` whose carrier is the range of a closed
immersion `ι : C ⟶ X` with reduced source. Then `ι.ker` is the vanishing ideal of `P`
(`ker_eq_vanishingIdeal`), so `ι` lifts through the prime-curve inclusion `P.inclusion` by an
isomorphism `lift P ι hP : C ⟶ P.toScheme` (`lift_inclusion`, `lift_isIso`,
`inclusion_eq_inv_lift`). This is the accepted `exceptionalLift` construction of the newest
exceptional curve, made generic.

Consequently, if `ι ≫ π` factors through the spectrum of a principal ideal domain (for instance a
point `Spec F`), the restriction to `P` of the pullback along `π` of every invertible sheaf has
degree zero (`restrictionDegree_pullback_eq_zero`), in sheaf, Picard-class and
restriction-degree-homomorphism form: the pullback to `Spec R` is trivial (`pidInvertibleUnitIso`)
and pullbacks of the unit are the unit. This is the accepted argument for `E · π^*L = 0`, made
generic; it gives `C_j · π^*q = 0` for the older exceptional curves, which map to a point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PrimeCurveInclusionLift

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (P : X.PrimeCurve)
variable {C : Scheme.{u}} (ι : C ⟶ X.toScheme) [IsClosedImmersion ι] [IsReduced C]
variable (hP : (P : Set X.toScheme) = Set.range ι.base)

omit [IsReduced C] in
include hP in
/-- The support of the kernel of `ι` is the curve. -/
theorem ker_support : ι.ker.support = P.closedSubset := by
  apply TopologicalSpace.Closeds.ext
  rw [Scheme.Hom.support_ker]
  show closure (Set.range ι.base) = (P : Set X.toScheme)
  rw [hP]
  exact ι.isClosedEmbedding.isClosed_range.closure_eq

include hP in
/-- The kernel of `ι` is the vanishing ideal of the curve: the source is reduced, so the kernel is
radical with support the curve. -/
theorem ker_eq_vanishingIdeal : ι.ker = P.vanishingIdeal := by
  rw [← SchematicImageDenseOpen.ker_radical ι, ← Scheme.IdealSheafData.vanishingIdeal_support,
    ker_support P ι hP]
  rfl

/-- The closed immersion factors through the prime-curve scheme. -/
def lift : C ⟶ P.toScheme :=
  GluedIdealSheafLift.liftGlued P.vanishingIdeal ι (ker_eq_vanishingIdeal P ι hP).ge

@[reassoc] theorem lift_inclusion : lift P ι hP ≫ P.inclusion = ι :=
  GluedIdealSheafLift.liftGlued_gluedTo _ _ _

instance lift_isClosedImmersion : IsClosedImmersion (lift P ι hP) := by
  haveI : IsClosedImmersion (lift P ι hP ≫ P.inclusion) := by
    rw [lift_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ P.inclusion

instance lift_surjective : Surjective (lift P ι hP) := by
  refine ⟨fun y => ?_⟩
  have hy : P.inclusion.base y ∈ (P : Set X.toScheme) := by
    rw [← PrimeCurve.range_inclusion]
    exact ⟨y, rfl⟩
  rw [hP] at hy
  obtain ⟨z, hz⟩ := hy
  refine ⟨z, P.inclusion.isClosedEmbedding.injective ?_⟩
  have h := congrArg (fun f => f.base z) (lift_inclusion P ι hP)
  simp only [Scheme.comp_base_apply] at h
  rw [h]
  exact hz

/-- The factor is an isomorphism: a surjective closed immersion onto the reduced curve scheme. -/
instance lift_isIso : IsIso (lift P ι hP) :=
  isIso_of_isClosedImmersion_of_surjective _

/-- The prime-curve inclusion is `ι` transported along the isomorphism. -/
theorem inclusion_eq_inv_lift : P.inclusion = inv (lift P ι hP) ≫ ι := by
  symm
  rw [IsIso.inv_comp_eq]
  exact (lift_inclusion P ι hP).symm

/-! ## Degree zero of pullbacks along morphisms factoring through a point -/

section Point

variable {Y : Scheme.{u}} (π : X.toScheme ⟶ Y)
variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (t : C ⟶ Spec (CommRingCat.of R)) (c : Spec (CommRingCat.of R) ⟶ Y)
variable (hfac : ι ≫ π = t ≫ c)

omit [IsDomain R] [IsPrincipalIdealRing R] in
include hfac in
/-- The composite `P ⟶ X ⟶ Y` factors through `Spec R`. -/
theorem inclusion_comp_eq : P.inclusion ≫ π = (inv (lift P ι hP) ≫ t) ≫ c := by
  rw [inclusion_eq_inv_lift P ι hP, Category.assoc, hfac, Category.assoc]

include hP hfac in
/-- **`P · π^*L = 0`** when `P ⟶ Y` factors through the spectrum of a principal ideal domain. -/
theorem restrictionDegree_pullback_eq_zero (L : InvertibleSheaf Y) :
    P.restrictionDegree (pullbackInvertibleSheaf π L) = 0 := by
  unfold PrimeCurve.restrictionDegree
  apply P.lineDegree_eq_zero_of_iso_unit
  refine ((schemeModulePullbackCompIso P.inclusion π).app L.obj) ≪≫ ?_
  rw [inclusion_comp_eq P ι hP π t c hfac]
  refine ((schemeModulePullbackCompIso (inv (lift P ι hP) ≫ t) c).symm.app L.obj) ≪≫ ?_
  refine (schemeModulePullback (inv (lift P ι hP) ≫ t)).mapIso
    (AffineModuleTilde.pidInvertibleUnitIso (pullbackInvertibleSheaf c L)) ≪≫ ?_
  exact schemeModulePullbackUnitIso (inv (lift P ι hP) ≫ t)

include hP hfac in
/-- The Picard-class form of `restrictionDegree_pullback_eq_zero`. -/
theorem picardRestrictionDegree_pullback_eq_zero (q : Y.Pic) :
    P.picardRestrictionDegree (schemePicardPullbackHom π q) = 0 := by
  obtain ⟨L, hL⟩ := RationalTreePicard.toPic_surjective q
  rw [← hL, schemePicardPullbackHom_toPic, PrimeCurve.picardRestrictionDegree_toPic]
  exact restrictionDegree_pullback_eq_zero P ι hP π t c hfac L

include hP hfac in
/-- The restriction-degree-homomorphism form of `restrictionDegree_pullback_eq_zero`. -/
theorem picardRestrictionDegreeHom_pullback_eq_zero (q : Additive Y.Pic) :
    X.picardRestrictionDegreeHom P ((schemePicardPullbackHom π).toAdditive q) = 0 := by
  change P.picardRestrictionDegree (schemePicardPullbackHom π q.toMul) = 0
  exact picardRestrictionDegree_pullback_eq_zero P ι hP π t c hfac q.toMul

end Point

end KltDP.Geometry.PrimeCurveInclusionLift
