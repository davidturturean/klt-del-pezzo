import KltDP.Geometry.AffineFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Standard-smooth affine neighborhoods over the original field

These are the three unconditional algebra-identification and neighborhood
lemmas from the separately compiled inactive SmoothRegularSchemeProbe.
The source is reproduced without its conditional literature use sites or
its literature-probe import. Every map is the existing pinned scheme map.
A nonempty open of Spec k is all of Spec k, so the chart algebra is over
the original field through the actual structure morphism.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry

/-- Transporting the actual section map from the global sections of an
affine base gives the same ring map as the original chart-to-base morphism.
This identity holds over any commutative base ring. -/
theorem affineBaseSections_appLE_eq_baseToAffineSectionsMap
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) {V : X.Opens}
    (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ ⊤) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ V e =
      baseToAffineSectionsMap f hV := by
  apply Spec.map_injective
  calc
    Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ V e) =
        Spec.map (f.appLE ⊤ V e) ≫
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv := Spec.map_comp _ _
    _ = Spec.map (f.appLE ⊤ V e) ≫
        (isAffineOpen_top (Spec (CommRingCat.of R))).fromSpec := by
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    _ = hV.fromSpec ≫ f :=
      IsAffineOpen.Spec_map_appLE_fromSpec f
        (isAffineOpen_top (Spec (CommRingCat.of R))) hV e
    _ = Spec.map (baseToAffineSectionsMap f hV) :=
      (Spec_map_baseToAffineSectionsMap f hV).symm

/-- Standard smoothness survives this exact change from the base's global
sections to the original ring, because the intervening ring map is the
inverse of the canonical global-sections isomorphism. -/
theorem standardSmooth_baseToAffineSectionsMap
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) {V : X.Opens}
    (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ ⊤)
    (hsmooth : RingHom.IsStandardSmooth (f.appLE ⊤ V e).hom) :
    RingHom.IsStandardSmooth (baseToAffineSectionsMap f hV).hom := by
  let eR : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  have heR : RingHom.IsStandardSmooth eR.toRingHom :=
    (RingHom.IsStandardSmoothOfRelativeDimension.equiv eR).isStandardSmooth
  have hcomp := hsmooth.comp heR
  change RingHom.IsStandardSmooth
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ V e).hom) at hcomp
  rw [affineBaseSections_appLE_eq_baseToAffineSectionsMap f hV e] at hcomp
  exact hcomp

/-- The actual standard-smooth neighborhoods supplied by pinned scheme
smoothness can be taken over the original field. A base neighborhood
containing the image of the chosen point is all of `Spec k` because that
space has exactly one point. -/
theorem isSmooth_field_exists_affine_standardSmooth
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsSmooth f] (x : X) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V), x ∈ V ∧
      RingHom.IsStandardSmooth (baseToAffineSectionsMap f hV).hom := by
  obtain ⟨⟨U, hU⟩, ⟨V, hV⟩, hx, e, hsmooth⟩ :=
    IsSmooth.exists_isStandardSmooth (f := f) x
  have htop : U = ⊤ := by
    apply le_antisymm le_top
    intro y _
    have hy : y = f.base x := Subsingleton.elim _ _
    simpa only [hy] using e hx
  subst U
  exact ⟨V, hV, hx, standardSmooth_baseToAffineSectionsMap f hV e hsmooth⟩

end KltDP.Geometry
