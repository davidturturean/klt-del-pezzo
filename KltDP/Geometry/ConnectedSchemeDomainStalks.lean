import Mathlib.AlgebraicGeometry.Stalk
import KltDP.Geometry.RationalTreePicardComponentPartition
import KltDP.Geometry.RegularLocalUFD
import Mathlib.Topology.Connected.Clopen

/-!
Domain stalks make the original irreducible components disjoint. Indeed,
the image of the original stalk spectrum contains every generization of
the point and has irreducible closure. Each component through the point
is consequently that same closure.

For a connected Noetherian scheme these disjoint components are clopen,
so the scheme is irreducible; domain stalks also prove reducedness.
This is the ordinary topological step toward geometric integrality.
It does not assert that smoothness has supplied the domain stalks.
-/

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ConnectedSchemeDomainStalks

/-- Two original components through a point with a domain stalk coincide. -/
theorem component_eq_of_mem (X : Scheme.{u}) (x : X)
    [IsDomain (X.presheaf.stalk x)]
    (C D : ↥(irreducibleComponents X)) (hxC : x ∈ C.1) (hxD : x ∈ D.1) :
    C = D := by
  let j := X.fromSpecStalk x
  have hirr : IsIrreducible (closure (Set.range j.base)) := by
    apply IsIrreducible.closure
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (Spec (X.presheaf.stalk x))).image
        j.base j.base.hom.2.continuousOn
  have hsub (E : ↥(irreducibleComponents X)) (hxE : x ∈ E.1) :
      E.1 ⊆ closure (Set.range j.base) := by
    have hη := E.2.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents E.1 E.2)
    have hmem : E.2.1.genericPoint ∈ Set.range j.base := by
      change E.2.1.genericPoint ∈ Set.range (X.fromSpecStalk x).base
      rw [Scheme.range_fromSpecStalk]
      exact hη.specializes hxE
    rw [← hη.def]
    exact closure_mono (Set.singleton_subset_iff.mpr hmem)
  apply Subtype.ext
  exact ((C.2 : Maximal IsIrreducible C.1).eq_of_le hirr (hsub C hxC)).trans
    ((D.2 : Maximal IsIrreducible D.1).eq_of_le hirr (hsub D hxD)).symm

/-- Connected Noetherian schemes with original domain stalks are integral. -/
theorem isIntegral (X : Scheme.{u}) [NoetherianSpace X] [ConnectedSpace X]
    (hstalk : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IsIntegral X := by
  classical
  letI (x : X) : IsDomain (X.presheaf.stalk x) := hstalk x
  letI (x : X) : _root_.IsReduced (X.presheaf.stalk x) := inferInstance
  letI : IsReduced X := isReduced_of_isReduced_stalk X
  obtain ⟨x⟩ : Nonempty X := inferInstance
  let C : ↥(irreducibleComponents X) :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hcompl : C.1 =
      (RationalTreePicard.componentClosedUnion X ({C}ᶜ) : Set X)ᶜ := by
    ext y
    constructor
    · intro hy hy'
      obtain ⟨D, hD, hyD⟩ :=
        (RationalTreePicard.mem_componentClosedUnion X ({C}ᶜ) y).mp hy'
      have hDC : D = C := component_eq_of_mem X y D C hyD hy
      exact hD (Set.mem_singleton_iff.mpr hDC)
    · intro hy
      let D : ↥(irreducibleComponents X) :=
        ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
      have hyD : y ∈ D.1 := mem_irreducibleComponent
      by_cases hDC : D = C
      · simpa only [hDC] using hyD
      · exact (hy ((RationalTreePicard.mem_componentClosedUnion X ({C}ᶜ) y).mpr
          ⟨D, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hDC, hyD⟩)).elim
  have hopen : IsOpen C.1 := by
    rw [hcompl]
    exact (RationalTreePicard.componentClosedUnion X ({C}ᶜ)).isClosed.isOpen_compl
  have htop : C.1 = Set.univ :=
    (show IsClopen C.1 from
      ⟨isClosed_of_mem_irreducibleComponents C.1 C.2, hopen⟩).eq_univ C.2.1.nonempty
  have huniv : IsIrreducible (Set.univ : Set X) := by
    rw [← htop]
    exact C.2.1
  letI : IrreducibleSpace X := (irreducibleSpace_def X).mpr huniv
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- The existing regular-local theorem supplies the original domain stalks. -/
theorem isIntegral_of_regularPoints (X : Scheme.{u})
    [NoetherianSpace X] [ConnectedSpace X]
    (hregular : ∀ x : X, RegularPoint X x) : IsIntegral X := by
  apply isIntegral X
  intro x
  obtain ⟨hDomain, _⟩ := regularPoint_stalk_isDomain_and_uniqueFactorizationMonoid
    X x (hregular x)
  exact hDomain

#check component_eq_of_mem
#print axioms component_eq_of_mem
#check isIntegral
#print axioms isIntegral
#check isIntegral_of_regularPoints
#print axioms isIntegral_of_regularPoints

end KltDP.Geometry.ConnectedSchemeDomainStalks
