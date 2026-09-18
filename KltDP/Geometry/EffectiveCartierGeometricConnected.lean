import KltDP.Geometry.CurveEffectiveCartierSequence
import KltDP.Geometry.ClosedImmersionStructureEpi
import KltDP.Geometry.ProperGlobalSectionsConstants
import KltDP.Geometry.FieldBaseStructureSheaf
import KltDP.Geometry.ProperSteinConnected

/-! Negative-line H1 vanishing controls the actual Cartier member's
original global functions. For a nonempty member these are exactly k,
so the actual member is geometrically connected by the selected full
proper Stein theorem. No reducedness or connectedness is assumed. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace KltDP.Geometry.EffectiveCartierGeometricConnected
open ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)

private theorem scalar_comp_apply {Y : Scheme.{u}} (i : Y ⟶ X) (a : k) :
    baseFieldToGlobalSections (i ≫ f) a = i.appTop (baseFieldToGlobalSections f a) := by
  change (i ≫ f).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a) =
    i.appTop (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a))
  rw [Scheme.comp_appTop]
  rfl

/-- The actual ideal short exact sequence lifts every original member
function to a scalar, using the original source's constant functions. -/
theorem baseFieldToGlobalSections_surjective
    (hH1 : Subsingleton (H (cartierDivisorModule X (-E)) 1)) :
    Function.Surjective (baseFieldToGlobalSections
      (effectiveCartierInclusion X E hE ≫ f)) := by
  let i := effectiveCartierInclusion X E hE
  let S := effectiveCartierSequence X E hE
  letI : Subsingleton (H S.X₁ 1) := hH1
  have hS : S.ShortExact := effectiveCartierSequence_shortExact X E hE
    (effectiveCartier_structureToPushforwardUnit_epi X E hE)
  intro z
  obtain ⟨y, hy⟩ := sections_surjective_of_hOne_zero S hS z
  obtain ⟨a, ha⟩ := (KltDP.Geometry.baseFieldToGlobalSections_bijective f).surjective y
  refine ⟨a, ?_⟩
  rw [scalar_comp_apply f i a, ha]
  exact (structureToPushforwardUnit_app i ⊤ y).symm.trans hy

/-- Nonemptiness makes the original scalar map injective as well. -/
theorem baseFieldToGlobalSections_bijective
    [Nonempty (effectiveCartierScheme X E hE)]
    (hH1 : Subsingleton (H (cartierDivisorModule X (-E)) 1)) :
    Function.Bijective (baseFieldToGlobalSections
      (effectiveCartierInclusion X E hE ≫ f)) := by
  let Y := effectiveCartierScheme X E hE
  let y : Y := Classical.choice inferInstance
  letI : Nontrivial Γ(Y, ⊤) :=
    (Y.presheaf.germ ⊤ y (by trivial)).hom.domain_nontrivial
  exact ⟨(baseFieldToGlobalSections (effectiveCartierInclusion X E hE ≫ f)).injective,
    baseFieldToGlobalSections_surjective f E hE hH1⟩

/-- The actual member's structure-sheaf map to the original field is an isomorphism. -/
theorem structureMap_isIso
    [Nonempty (effectiveCartierScheme X E hE)]
    (hH1 : Subsingleton (H (cartierDivisorModule X (-E)) 1)) :
    IsIso (effectiveCartierInclusion X E hE ≫ f).c :=
  FieldBaseStructureSheaf.c_isIso_of_baseFieldToGlobalSections_bijective
    (effectiveCartierInclusion X E hE ≫ f)
    (baseFieldToGlobalSections_bijective f E hE hH1)

/-- Every actual field extension of the original nonempty Cartier
member is connected; its nilpotents need not be removed first. -/
theorem geometrically_connected
    [Nonempty (effectiveCartierScheme X E hE)]
    (hH1 : Subsingleton (H (cartierDivisorModule X (-E)) 1)) :
    ∀ (K : Type u) [Field K] (q : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)),
      ConnectedSpace (pullback (effectiveCartierInclusion X E hE ≫ f) q : Scheme.{u}) := by
  letI : IsIso (effectiveCartierInclusion X E hE ≫ f).c := structureMap_isIso f E hE hH1
  exact ProperSteinConnected.geometrically_connected (effectiveCartierInclusion X E hE ≫ f)

end KltDP.Geometry.EffectiveCartierGeometricConnected

#check @KltDP.Geometry.EffectiveCartierGeometricConnected.geometrically_connected
#print axioms KltDP.Geometry.EffectiveCartierGeometricConnected.geometrically_connected
