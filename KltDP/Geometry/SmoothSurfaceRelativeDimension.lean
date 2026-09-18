import KltDP.Geometry.StandardSmoothSurfaceDimension
import KltDP.Geometry.SmoothSurfaceRegularity

/-!
# Relative dimension of the original smooth surface morphism

Every original standard-smooth affine chart contains a closed point. The
proved stalk-dimension and regularity theorems therefore force its relative
dimension to be two. The canonical global-sections isomorphism returns this
statement to the actual section maps in the pinned scheme smoothness class.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- Smoothness of the original structure morphism of a normal projective
surface over an algebraically closed field has relative dimension two. -/
theorem isSmoothOfRelativeDimension_two [IsSmooth X.structureMorphism] :
    IsSmoothOfRelativeDimension 2 X.structureMorphism := by
  letI : LocallyOfFiniteType X.structureMorphism := X.projective.locallyOfFiniteType
  letI : JacobsonSpace X.toScheme :=
    LocallyOfFiniteType.jacobsonSpace X.structureMorphism
  constructor
  intro x
  obtain ⟨U, hU, hx, hsmooth⟩ :=
    isSmooth_field_exists_affine_standardSmooth X.structureMorphism x
  obtain ⟨y, hy, hyclosed⟩ :=
    nonempty_inter_closedPoints (show (U : Set X.toScheme).Nonempty from ⟨x, hx⟩)
      U.isOpen.isLocallyClosed
  letI := affineSectionsAlgebra X.structureMorphism hU
  obtain ⟨⟨P⟩⟩ := hsmooth
  letI : Algebra.IsStandardSmoothOfRelativeDimension P.dimension k Γ(X.toScheme, U) :=
    ⟨P, rfl⟩
  have hP : RingHom.IsStandardSmoothOfRelativeDimension P.dimension
      (baseToAffineSectionsMap X.structureMorphism hU).hom :=
    show Algebra.IsStandardSmoothOfRelativeDimension P.dimension k Γ(X.toScheme, U) from
      inferInstance
  have hdim : P.dimension = 2 :=
    X.standardSmooth_relativeDimension_eq_two hU ⟨y, hy⟩ hyclosed
      (X.regularPoints_of_isSmooth y) hP
  have htwo : RingHom.IsStandardSmoothOfRelativeDimension 2
      (baseToAffineSectionsMap X.structureMorphism hU).hom := hdim ▸ hP
  have e : U ≤ X.structureMorphism ⁻¹ᵁ ⊤ := by simp
  refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨U, hU⟩, hx, e, ?_⟩
  let eR : Γ(Spec (CommRingCat.of k), ⊤) ≃+* k :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have heR : RingHom.IsStandardSmoothOfRelativeDimension 0 eR.toRingHom :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv eR
  have hcomp := htwo.comp heR
  change RingHom.IsStandardSmoothOfRelativeDimension 2
    (((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
      baseToAffineSectionsMap X.structureMorphism hU).hom) at hcomp
  rw [← affineBaseSections_appLE_eq_baseToAffineSectionsMap X.structureMorphism hU e,
    Iso.hom_inv_id_assoc] at hcomp
  exact hcomp

end KltDP.Geometry.NormalProjectiveSurface
