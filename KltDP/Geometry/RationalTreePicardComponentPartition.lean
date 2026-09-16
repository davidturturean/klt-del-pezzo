import KltDP.Geometry.PrimeCurveSubscheme
import Mathlib.Topology.NoetherianSpace

/-!
# Actual closed component partitions on a reduced scheme

A selection of the original irreducible components of a Noetherian scheme
defines its actual reduced closed union. The selection and its complement
cover the original scheme. On every original affine open, their vanishing
ideals intersect in zero when the scheme is reduced.

The quotient schemes are the charts of the actual closed unions, with the
original inclusion maps. This supplies the closed-cover hypothesis used by
affine frame descent for a future cut of a rational tree. It does not assert
that the scheme-theoretic intersection is a reduced node.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (X : Scheme.{u}) [NoetherianSpace X]

/-- The literal union of a selection of the original irreducible components. -/
def componentClosedUnion (S : Set ↥(irreducibleComponents X)) : Closeds X :=
  ⟨⋃ C ∈ S, C.1, by
    haveI : Finite ↥(irreducibleComponents X) := by
      rw [Set.finite_coe_iff]
      exact NoetherianSpace.finite_irreducibleComponents
    exact (Set.toFinite S).isClosed_biUnion
      (fun C _ => isClosed_of_mem_irreducibleComponents C.1 C.2)⟩

@[simp]
theorem mem_componentClosedUnion (S : Set ↥(irreducibleComponents X)) (x : X) :
    x ∈ componentClosedUnion X S ↔ ∃ C ∈ S, x ∈ C.1 := by
  change (x ∈ ⋃ C ∈ S, C.1) ↔ _
  simp only [Set.mem_iUnion, exists_prop]

@[simp]
theorem coe_componentClosedUnion_singleton (C : ↥(irreducibleComponents X)) :
    (componentClosedUnion X {C} : Set X) = C.1 := by
  change (⋃ D ∈ ({C} : Set ↥(irreducibleComponents X)), D.1) = C.1
  exact Set.biUnion_singleton C (fun D : ↥(irreducibleComponents X) => D.1)

/-- Coverage is proved from an original irreducible component through each
point; it is not a hypothesis on the selected family. -/
theorem componentClosedUnion_union_compl (S : Set ↥(irreducibleComponents X)) :
    (componentClosedUnion X S : Set X) ∪ componentClosedUnion X Sᶜ = Set.univ := by
  classical
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  let C : ↥(irreducibleComponents X) :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hxC : x ∈ C.1 := mem_irreducibleComponent
  by_cases hC : C ∈ S
  · exact Or.inl ((mem_componentClosedUnion X S x).2 ⟨C, hC, hxC⟩)
  · exact Or.inr ((mem_componentClosedUnion X Sᶜ x).2 ⟨C, hC, hxC⟩)

/-- The actual vanishing ideal sheaf of the selected component union. -/
def componentUnionIdeal (S : Set ↥(irreducibleComponents X)) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (componentClosedUnion X S)

@[simp]
theorem componentUnionIdeal_support (S : Set ↥(irreducibleComponents X)) :
    ((componentUnionIdeal X S).support : Set X) = componentClosedUnion X S := rfl

theorem componentUnionIdeal_radical (S : Set ↥(irreducibleComponents X)) :
    (componentUnionIdeal X S).radical = componentUnionIdeal X S :=
  (Scheme.IdealSheafData.vanishingIdeal_support (I := componentUnionIdeal X S)).symm

/-- The existing quotient-chart construction of the reduced closed union. -/
def componentUnionScheme (S : Set ↥(irreducibleComponents X)) : Scheme.{u} :=
  (componentUnionIdeal X S).glueData.glued

/-- Its actual inclusion into the original scheme. -/
def componentUnionInclusion (S : Set ↥(irreducibleComponents X)) :
    componentUnionScheme X S ⟶ X :=
  (componentUnionIdeal X S).gluedTo

instance (S : Set ↥(irreducibleComponents X)) :
    IsClosedImmersion (componentUnionInclusion X S) :=
  (componentUnionIdeal X S).gluedTo_isClosedImmersion

instance (S : Set ↥(irreducibleComponents X)) :
    AlgebraicGeometry.IsReduced (componentUnionScheme X S) :=
  (componentUnionIdeal X S).glued_isReduced (componentUnionIdeal_radical X S)

@[simp]
theorem range_componentUnionInclusion (S : Set ↥(irreducibleComponents X)) :
    Set.range (componentUnionInclusion X S).base = componentClosedUnion X S :=
  (componentUnionIdeal X S).range_gluedTo

/-- The two actual closed immersions jointly cover the original scheme. -/
theorem componentUnionInclusion_ranges_cover (S : Set ↥(irreducibleComponents X)) :
    Set.range (componentUnionInclusion X S).base ∪
      Set.range (componentUnionInclusion X Sᶜ).base = Set.univ := by
  rw [range_componentUnionInclusion, range_componentUnionInclusion,
    componentClosedUnion_union_compl]

/-- The selected component ideal in an original affine section ring. -/
def componentChartIdeal (S : Set ↥(irreducibleComponents X)) (U : X.affineOpens) :
    Ideal Γ(X, U.1) :=
  (componentUnionIdeal X S).ideal U

theorem componentChartIdeal_eq (S : Set ↥(irreducibleComponents X))
    (U : X.affineOpens) :
    componentChartIdeal X S U =
      PrimeSpectrum.vanishingIdeal (U.2.fromSpec.base ⁻¹' componentClosedUnion X S) := rfl

/-- The affine quotient is a chart of the actual selected closed union. -/
def componentUnionChartIso (S : Set ↥(irreducibleComponents X)) (U : X.affineOpens) :
    Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X S U)) ≅
      (componentUnionInclusion X S ⁻¹ᵁ U.1).toScheme :=
  (componentUnionIdeal X S).glueDataObjIso U

/-- The chart identification preserves the original quotient morphism. -/
theorem componentUnionChartIso_hom_restrict (S : Set ↥(irreducibleComponents X))
    (U : X.affineOpens) :
    (componentUnionChartIso X S U).hom ≫ componentUnionInclusion X S ∣_ U.1 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (componentChartIdeal X S U))) ≫
        U.2.isoSpec.inv :=
  (componentUnionIdeal X S).glueDataObjIso_hom_restrict U

/-- The quotient chart and the reduced closed union have the same actual
map into the original scheme. -/
@[reassoc]
theorem componentUnionChartIso_hom_over (S : Set ↥(irreducibleComponents X))
    (U : X.affineOpens) :
    (componentUnionChartIso X S U).hom ≫
      (componentUnionInclusion X S ∣_ U.1) ≫ U.1.ι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (componentChartIdeal X S U))) ≫
        U.2.fromSpec := by
  rw [← Category.assoc, componentUnionChartIso_hom_restrict, Category.assoc]
  rfl

/-- The support of the actual affine component ideal is its original
component union pulled back to the original affine chart. -/
theorem componentChartIdeal_zeroLocus (S : Set ↥(irreducibleComponents X))
    (U : X.affineOpens) :
    PrimeSpectrum.zeroLocus (componentChartIdeal X S U) =
      U.2.fromSpec.base ⁻¹' componentClosedUnion X S := by
  rw [componentChartIdeal_eq, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact ((componentClosedUnion X S).isClosed.preimage
    U.2.fromSpec.base.hom.continuous).closure_eq

/-- The sum ideal has exactly the actual intersection support. Reducedness
of this intersection is a separate nodal-geometric obligation. -/
theorem componentChartIdeal_sup_zeroLocus (S : Set ↥(irreducibleComponents X))
    (U : X.affineOpens) :
    PrimeSpectrum.zeroLocus
        (componentChartIdeal X S U ⊔ componentChartIdeal X Sᶜ U : Ideal Γ(X, U.1)) =
      U.2.fromSpec.base ⁻¹'
        ((componentClosedUnion X S : Set X) ∩ componentClosedUnion X Sᶜ) := by
  rw [PrimeSpectrum.zeroLocus_sup, componentChartIdeal_zeroLocus,
    componentChartIdeal_zeroLocus, Set.preimage_inter]

/-- The required affine closed-cover equation follows from the original
components covering the original reduced scheme. -/
theorem componentChartIdeal_inf_compl [AlgebraicGeometry.IsReduced X]
    (S : Set ↥(irreducibleComponents X)) (U : X.affineOpens) :
    componentChartIdeal X S U ⊓ componentChartIdeal X Sᶜ U = ⊥ := by
  rw [componentChartIdeal_eq, componentChartIdeal_eq,
    ← PrimeSpectrum.vanishingIdeal_union, ← Set.preimage_union,
    componentClosedUnion_union_compl, Set.preimage_univ,
    PrimeSpectrum.vanishingIdeal_univ]
  exact nilradical_eq_zero Γ(X, U.1)

end KltDP.Geometry.RationalTreePicard
