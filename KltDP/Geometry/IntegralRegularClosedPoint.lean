import KltDP.Geometry.FiniteTypeSurfaceRegularity
import KltDP.Geometry.ClosedPoints
import KltDP.Geometry.DivisorOrder
import KltDP.Literature.Stacks.FieldJ2

/-! The original integral finite-type scheme has a regular closed rational
point in dimension at most two. The actual affine charts use the approved
field-J2 input; integrality supplies the original local domains. The actual
generic point is regular, and Jacobson selects a closed point in that open.
No normality or smoothness of the original scheme is assumed. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.IntegralRegularClosedPoint

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]

include f

/-- The actual regular locus is open on an integral finite-type scheme
of dimension at most two, including a possibly singular original curve. -/
theorem regularLocus_isOpen (hdim : topologicalKrullDim X ≤ 2) :
    IsOpen (regularLocus X) := by
  apply isOpen_regularLocus_of_primeLocalizationOpen_on_affineCover X.affineOpenCover
  intro i
  letI : Algebra k (X.affineOpenCover.obj i) :=
    (Spec.preimage (X.affineOpenCover.map i ≫ f)).hom.toAlgebra
  letI : Algebra.FiniteType k (X.affineOpenCover.obj i) := by
    have hcomp : LocallyOfFiniteType (X.affineOpenCover.map i ≫ f) := inferInstance
    rw [← Spec.map_preimage (X.affineOpenCover.map i ≫ f)] at hcomp
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hcomp
  have hlocus : primeLocalizationRegularLocus (X.affineOpenCover.obj i) =
      Literature.generatorRegularLocus (X.affineOpenCover.obj i) := by
    ext p
    let j := X.affineOpenCover.map i
    letI : IsDomain (X.presheaf.stalk (j.base p)) := KltDP.Geometry.integralSchemeStalk_isDomain X _
    letI : IsDomain (Localization.AtPrime p.asIdeal) :=
      MulEquiv.isDomain (X.presheaf.stalk (j.base p))
        (openImmersionStalkLocalizationEquiv j p).symm.toMulEquiv
    have hlocal : ringKrullDim (Localization.AtPrime p.asIdeal) ≤ 2 := by
      calc
        ringKrullDim (Localization.AtPrime p.asIdeal) =
            ringKrullDim (X.presheaf.stalk (j.base p)) :=
          (ringKrullDim_eq_of_ringEquiv (openImmersionStalkLocalizationEquiv j p)).symm
        _ ≤ 2 := (ringKrullDim_stalk_le_topologicalKrullDim X (j.base p)).trans hdim
    exact (regularLocalByGenerators_iff_regularLocal_of_dimension_le_two hlocal).symm
  rw [hlocus]
  exact (Literature.Stacks.field_isJ2.{u, u} k).isOpen_generatorRegularLocus
    (X.affineOpenCover.obj i)

/-- The original generic point proves that the actual regular locus is
nonempty; its openness and the original finite-type map give a closed point. -/
theorem exists_closed_regularPoint (hdim : topologicalKrullDim X ≤ 2) :
    ∃ x : X, IsClosed ({x} : Set X) ∧ RegularPoint X x := by
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hx, hclosed⟩ := nonempty_inter_closedPoints
    (show (regularLocus X).Nonempty from ⟨genericPoint X, regularPoint_genericPoint X⟩)
    (regularLocus_isOpen f hdim).isLocallyClosed
  exact ⟨x, hclosed, hx⟩

/-- An actual regular closed rational point of the original structure map.
The local-principal Cartier construction at this point is a separate step. -/
theorem exists_closed_regularSection [IsAlgClosed k] (hdim : topologicalKrullDim X ≤ 2) :
    ∃ i : Spec (CommRingCat.of k) ⟶ X,
      IsClosedImmersion i ∧ i ≫ f = 𝟙 _ ∧ ∀ t, RegularPoint X (i.base t) := by
  obtain ⟨x, hclosed, hregular⟩ := exists_closed_regularPoint f hdim
  letI : IsClosedImmersion (X.fromSpecResidueField x) :=
    fromSpecResidueField_isClosedImmersion X x hclosed
  have hiClosed : IsClosedImmersion (closedPointSection f x hclosed) := by
    unfold closedPointSection
    infer_instance
  refine ⟨closedPointSection f x hclosed, hiClosed,
    closedPointSection_over_base f x hclosed, ?_⟩
  intro t
  rw [closedPointSection_base]
  exact hregular

#print axioms regularLocus_isOpen
#print axioms exists_closed_regularPoint
#print axioms exists_closed_regularSection

end KltDP.Geometry.IntegralRegularClosedPoint
