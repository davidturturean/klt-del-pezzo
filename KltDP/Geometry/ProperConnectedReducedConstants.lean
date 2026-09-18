import KltDP.Geometry.NoetherianZeroDimensionalSpectrum
import KltDP.Geometry.ProperGlobalSectionsFinite
import KltDP.Geometry.LocallyOfFiniteTypeNoetherian
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Original global functions on a connected reduced proper scheme

The actual affinization map is surjective. Thus its original spectrum
inherits connectedness and Noetherian topology. The original scalar map
is integral, so this spectrum has dimension zero. The existing finite
component, discrete-space, and reduced local-ring results make the
original global-section ring a field. Algebraic closedness then identifies
every original global section with a unique scalar through the original map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ProperConnectedReducedConstants

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The original scalar map is integral for every universally closed source. -/
theorem baseFieldToGlobalSections_isIntegral
    (f : X ⟶ Spec (CommRingCat.of k)) [UniversallyClosed f] :
    (baseFieldToGlobalSections f).IsIntegral := by
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed f

/-- The original affinization map of a universally closed field scheme is surjective. -/
theorem toSpecΓ_surjective (f : X ⟶ Spec (CommRingCat.of k)) [UniversallyClosed f] :
    Function.Surjective X.toSpecΓ.base := by
  letI : CompactSpace X := (quasiCompact_over_affine_iff f).mp inferInstance
  haveI : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rwa [← Scheme.toSpecΓ_naturality,
      MorphismProperty.cancel_right_of_respectsIso (P := @UniversallyClosed)]
  haveI : UniversallyClosed X.toSpecΓ :=
    UniversallyClosed.of_comp_of_isSeparated _ (Spec.map f.appTop)
  apply surjective_of_isClosed_range_of_injective
  · exact X.toSpecΓ.isClosedMap.isClosed_range
  · simp only [Scheme.toSpecΓ_appTop]
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(X, ⊤)).hom).1

/-- Every prime of the original section ring is maximal by integrality over the field. -/
theorem globalSections_krullDimLE_zero
    (f : X ⟶ Spec (CommRingCat.of k)) [UniversallyClosed f] :
    Ring.KrullDimLE 0 Γ(X, ⊤) := by
  apply Ring.KrullDimLE.mk₀
  intro I hI
  letI : I.IsPrime := hI
  letI : (I.comap (baseFieldToGlobalSections f)).IsPrime := hI.comap _
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap'
    (baseFieldToGlobalSections f) (baseFieldToGlobalSections_isIntegral f) I inferInstance

/-- Connectedness and reducedness suffice for the original global functions to form a field. -/
theorem globalSections_isField (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f] [IsReduced X] [ConnectedSpace X] : IsField Γ(X, ⊤) := by
  letI : NoetherianSpace X := noetherianSpace_of_locallyOfFiniteType_quasiCompact_spec f
  have hs : Function.Surjective X.toSpecΓ.base := toSpecΓ_surjective f
  letI : NoetherianSpace (Spec Γ(X, ⊤)) :=
    noetherianSpace_of_surjective X.toSpecΓ.base X.toSpecΓ.base.hom.continuous hs
  letI : ConnectedSpace (Spec Γ(X, ⊤)) := hs.connectedSpace X.toSpecΓ.base.hom.continuous
  letI : NoetherianSpace (PrimeSpectrum Γ(X, ⊤)) :=
    inferInstanceAs (NoetherianSpace (Spec Γ(X, ⊤)))
  letI : ConnectedSpace (PrimeSpectrum Γ(X, ⊤)) :=
    inferInstanceAs (ConnectedSpace (Spec Γ(X, ⊤)))
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  letI : Ring.KrullDimLE 0 Γ(X, ⊤) := globalSections_krullDimLE_zero f
  exact NoetherianZeroDimensionalSpectrum.isField_of_reduced_connected Γ(X, ⊤)

variable [IsAlgClosed k]

/-- Every original global function is a unique scalar on a connected reduced proper scheme. -/
theorem baseFieldToGlobalSections_bijective (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f] [IsReduced X] [ConnectedSpace X] :
    Function.Bijective (baseFieldToGlobalSections f) := by
  letI := (globalSections_isField f).toField
  exact IsAlgClosed.ringHom_bijective_of_isIntegral (baseFieldToGlobalSections f)
    (baseFieldToGlobalSections_isIntegral f)

/-- The actual scalar map gives the algebra equivalence for its original scalar action. -/
def baseFieldGlobalSectionsAlgEquiv (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f] [IsReduced X] [ConnectedSpace X] :
    letI := (baseFieldToGlobalSections f).toAlgebra
    k ≃ₐ[k] Γ(X, ⊤) := by
  letI := (baseFieldToGlobalSections f).toAlgebra
  exact AlgEquiv.ofBijective (Algebra.ofId k Γ(X, ⊤))
    (baseFieldToGlobalSections_bijective f)

theorem baseFieldGlobalSectionsAlgEquiv_apply (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f] [IsReduced X] [ConnectedSpace X] (a : k) :
    baseFieldGlobalSectionsAlgEquiv f a = baseFieldToGlobalSections f a := rfl

end KltDP.Geometry.ProperConnectedReducedConstants
