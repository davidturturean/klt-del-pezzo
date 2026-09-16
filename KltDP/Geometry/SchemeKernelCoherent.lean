import KltDP.Geometry.SchemeKernelFiniteGenerators
import KltDP.Geometry.SchemeKernelRestriction
import KltDP.Geometry.ModuleOpenOverEquivalence
import KltDP.Geometry.CoherentFiniteSubobject
import KltDP.Geometry.ClosedPoints
import KltDP.Geometry.RationalPointIdealExact
import KltDP.Compatibility.SheafFiniteTypeLocality

/-!
# Literal coherence of actual scheme kernels and closed-point ideals

For a quasi-compact morphism into a locally Noetherian scheme, the
original structure-map kernel ideal sheaf is finite type. Actual affine
kernel generators are transported to the original Over-site restrictions
through the accepted scheme-kernel and open-site comparisons, and the
actual affine cover supplies locality. The original kernel inclusion is
a monomorphism into the coherent structure module, hence the kernel is
coherent in the project's literal all-open finite-section-family sense.

The closed-point corollary uses the actual residue-field immersion over
any field, with no rationality assumption. Over an algebraically closed
field the accepted rational-point section also has this coherent ideal
and the accepted original short exact ideal sequence. No coherent-ideal,
finite-generator, or section-existence witness is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsLocallyNoetherian Y]

/-- The actual kernel on an actual affine open is finite type after
transport to its original Over site. -/
theorem schemeKernelIdeal_over_isFiniteType (U : Y.affineOpens) :
    _root_.SheafOfModules.IsFiniteType ((schemeKernelIdeal f).over U.1) := by
  letI : IsAffine U.1.toScheme := U.2
  letI : IsLocallyNoetherian U.1.toScheme :=
    isLocallyNoetherian_of_isOpenImmersion U.1.ι
  letI : QuasiCompact (f ∣_ U.1) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U.1).flip inferInstance
  obtain ⟨I, hI, p, hp⟩ := exists_finite_free_epi_schemeKernelIdeal (f ∣_ U.1)
  letI := hI
  letI : Epi p := hp
  let q := (openToOverFreeIso U.1 I).hom ≫
    (openToOverFunctor U.1).map (p ≫ (schemeKernelRestrictionIso f U.1).inv) ≫
      (openToOverRestrictionIso U.1 (schemeKernelIdeal f)).hom
  letI : Epi q := inferInstanceAs (Epi
    ((openToOverFreeIso U.1 I).hom ≫
      (openToOverFunctor U.1).map (p ≫ (schemeKernelRestrictionIso f U.1).inv) ≫
        (openToOverRestrictionIso U.1 (schemeKernelIdeal f)).hom))
  letI : HasBinaryProducts (Over U.1) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
      (C := Y.Opens) (B := U.1)
  exact _root_.SheafOfModules.isFiniteType_of_free_epi
    (R := Y.ringCatSheaf.over U.1) (M := (schemeKernelIdeal f).over U.1)
    (I := I) (p := q)

/-- Finite generation on the actual affine cover gives finite type of
the original categorical scheme-kernel ideal sheaf. -/
theorem schemeKernelIdeal_isFiniteType :
    _root_.SheafOfModules.IsFiniteType (schemeKernelIdeal f) := by
  haveI (U : Y.affineOpens) :
      _root_.SheafOfModules.IsFiniteType ((schemeKernelIdeal f).over U.1) :=
    schemeKernelIdeal_over_isFiniteType f U
  apply _root_.SheafOfModules.IsFiniteType.of_coversTop (schemeKernelIdeal f)
    (fun U : Y.affineOpens => U.1)
  intro U x hx
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_affine_open Y) hx
  exact ⟨V, homOfLE hVU, ⟨⟨V, hV⟩, ⟨𝟙 V⟩⟩, hxV⟩

/-- A quasi-compact scheme morphism into a locally Noetherian scheme
has a coherent actual kernel ideal, with the original inclusion. -/
theorem schemeKernelIdeal_isCoherentModule : IsCoherentModule (schemeKernelIdeal f) := by
  letI := schemeKernelIdeal_isFiniteType f
  letI : Mono (schemeKernelIdealι f) :=
    inferInstanceAs (Mono (kernel.ι (structureToPushforwardUnit f)))
  exact IsCoherentModule.of_finiteType_mono (schemeKernelIdealι f)

end KltDP.Geometry

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The actual residue-field closed-point ideal is coherent. Neither
algebraic closure nor rationality of the closed point is required. -/
theorem closedPointKernel_isCoherentModule (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) (hclosed : IsClosed ({x} : Set X)) :
    IsCoherentModule (schemeKernelIdeal (X.fromSpecResidueField x)) := by
  letI : IsClosedImmersion (X.fromSpecResidueField x) :=
    fromSpecResidueField_isClosedImmersion X x hclosed
  exact schemeKernelIdeal_isCoherentModule (X.fromSpecResidueField x)

/-- The accepted actual rational-point section has a coherent original
ideal and the original short exact ideal sequence. -/
theorem closedPointSection_coherent_idealSequence
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (x : X) (hclosed : IsClosed ({x} : Set X)) :
    IsCoherentModule (schemeKernelIdeal (closedPointSection f x hclosed)) ∧
      (RationalPointIdeal.idealSequence (closedPointSection f x hclosed)).ShortExact := by
  letI : IsClosedImmersion (X.fromSpecResidueField x) :=
    fromSpecResidueField_isClosedImmersion X x hclosed
  letI : IsClosedImmersion (closedPointSection f x hclosed) := by
    dsimp only [closedPointSection]
    infer_instance
  exact ⟨schemeKernelIdeal_isCoherentModule (closedPointSection f x hclosed),
    RationalPointIdeal.idealSequence_shortExact (closedPointSection f x hclosed) f
      (closedPointSection_over_base f x hclosed)⟩

end KltDP.Geometry
