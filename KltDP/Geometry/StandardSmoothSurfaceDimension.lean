import KltDP.Compatibility.StandardSmoothLocalDimension
import KltDP.Compatibility.ClosedAlgebraResidue
import KltDP.Geometry.ClosedPointDimension
import KltDP.Geometry.SurfaceRegularCharts
import KltDP.Geometry.SmoothFieldCharts

/-!
# The dimension of actual smooth coordinates at a regular surface point

At an actual closed regular point, the surface stalk has Krull dimension
two. Its actual affine-chart localization has the same dimension and
regularity. The cotangent computation for a standard-smooth presentation
therefore identifies that presentation's relative dimension with two.

Regularity is an explicit hypothesis about the original stalk. This module
does not import the inactive smooth-over-regular literature candidate.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- The dimension of any actual standard-smooth affine presentation at a
closed regular point is two. -/
theorem standardSmooth_relativeDimension_eq_two
    {U : X.toScheme.Opens} (hU : IsAffineOpen U) (x : U)
    (hclosed : IsClosed ({(x : X.toScheme)} : Set X.toScheme))
    (hregular : RegularPoint X.toScheme x.1) {n : ℕ}
    (hsmooth : RingHom.IsStandardSmoothOfRelativeDimension n
      (baseToAffineSectionsMap X.structureMorphism hU).hom) : n = 2 := by
  letI := affineSectionsAlgebra X.structureMorphism hU
  letI : Algebra.FiniteType k Γ(X.toScheme, U) :=
    affineSectionsAlgebra_finiteType X.structureMorphism hU
  letI : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X.toScheme, U) := hsmooth
  let q : Ideal Γ(X.toScheme, U) := (hU.primeIdealOf x).asIdeal
  letI : q.IsMaximal := isMaximal_primeIdealOf_of_isClosed X.toScheme hU x hclosed
  letI := KltDP.Compatibility.closedResidueField_formallyEtale k q
  have hcot : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) = n :=
    KltDP.Compatibility.finrank_cotangent_localization_of_standardSmooth
      k Γ(X.toScheme, U) (Localization.AtPrime q) q.primeCompl n
  have hreg : RegularLocal (Localization.AtPrime q) :=
    (regularPoint_iff_regularLocal_affineLocalization hU x).mp hregular
  have heq : ringKrullDim (Localization.AtPrime q) = ringKrullDim (X.stalk x) := by
    calc
      ringKrullDim (Localization.AtPrime q) =
          ringKrullDim (X.stalk (hU.fromSpec.base (hU.primeIdealOf x))) :=
        (ringKrullDim_eq_of_ringEquiv
          (openImmersionStalkLocalizationEquiv hU.fromSpec (hU.primeIdealOf x))).symm
      _ = ringKrullDim (X.stalk x) :=
        congrArg (fun y : X.toScheme => ringKrullDim (X.stalk y))
          (hU.fromSpec_primeIdealOf x)
  have hdim : ringKrullDim (Localization.AtPrime q) = 2 :=
    heq.trans (X.closed_stalk_dimension_two x hclosed)
  have hdimn := hreg.2
  rw [hcot] at hdimn
  have hn : (n : WithBot ℕ∞) = 2 := by
    exact hdimn.symm.trans hdim
  exact ENat.coe_inj.mp (WithBot.coe_inj.mp hn)

/-- Smoothness supplies a standard-smooth affine neighborhood over the
original field; actual closed-point regularity forces relative dimension
two on that neighborhood. -/
theorem exists_affine_standardSmooth_two [IsSmooth X.structureMorphism]
    (x : X.toScheme) (hclosed : IsClosed ({x} : Set X.toScheme))
    (hregular : RegularPoint X.toScheme x) :
    ∃ (U : X.toScheme.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      RingHom.IsStandardSmoothOfRelativeDimension 2
        (baseToAffineSectionsMap X.structureMorphism hU).hom := by
  obtain ⟨U, hU, hx, hsmooth⟩ :=
    isSmooth_field_exists_affine_standardSmooth X.structureMorphism x
  letI := affineSectionsAlgebra X.structureMorphism hU
  obtain ⟨⟨P⟩⟩ := hsmooth
  letI : Algebra.IsStandardSmoothOfRelativeDimension P.dimension k Γ(X.toScheme, U) :=
    ⟨P, rfl⟩
  have hP : RingHom.IsStandardSmoothOfRelativeDimension P.dimension
      (baseToAffineSectionsMap X.structureMorphism hU).hom :=
    show Algebra.IsStandardSmoothOfRelativeDimension P.dimension k Γ(X.toScheme, U) from
      inferInstance
  have hdim : P.dimension = 2 :=
    X.standardSmooth_relativeDimension_eq_two hU ⟨x, hx⟩ hclosed hregular hP
  exact ⟨U, hU, hx, hdim ▸ hP⟩

end KltDP.Geometry.NormalProjectiveSurface
