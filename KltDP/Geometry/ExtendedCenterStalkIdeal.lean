import KltDP.Geometry.AffineBlowupParameterChartCoefficients
import KltDP.Geometry.AffineBlowupSchemeLift

/-!
# The original extended centre ideal at a chart stalk

The original ideal-sheaf definition extends the base ideal from actual
global sections. Restriction followed by the original germ map is the
global germ, and the actual scheme stalk-map square supplies the base
coefficient. No reduction of the centre ideal is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineBlowup

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))

/-- The original extended centre ideal maps to the extension of the
original base ideal through the actual scheme stalk map. -/
theorem extendedCenter_map_germ (U : Y.affineOpens) (x : Y) (hx : x ∈ U.1) :
    Ideal.map (Y.presheaf.germ U.1 x hx).hom ((extendedCenter I f).ideal U) =
      Ideal.map (f.stalkMap x).hom (Ideal.map (StructureSheaf.toStalk R (f.base x)).hom I) := by
  change Ideal.map (Y.presheaf.germ U.1 x hx).hom
    (Ideal.map (Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op).hom
      (Ideal.map (testGlobalRingMap f) I)) = _
  have hmap : (Y.presheaf.germ U.1 x hx).hom.comp
      ((Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op).hom.comp
        (testGlobalRingMap f)) =
      (f.stalkMap x).hom.comp (StructureSheaf.toStalk R (f.base x)).hom := by
    apply RingHom.ext
    intro r
    change Y.presheaf.germ U.1 x hx
      (Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op
        (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))) = _
    rw [Y.presheaf.germ_res_apply]
    change Y.presheaf.germ ⊤ x trivial (f.app ⊤ (StructureSheaf.toOpen R ⊤ r)) =
      f.stalkMap x (StructureSheaf.toStalk R (f.base x) r)
    calc
      _ = f.stalkMap x ((Spec (CommRingCat.of R)).presheaf.germ ⊤
          (f.base x) trivial (StructureSheaf.toOpen R ⊤ r)) :=
        (Scheme.stalkMap_germ_apply f ⊤ x trivial (StructureSheaf.toOpen R ⊤ r)).symm
      _ = _ := congrArg (f.stalkMap x) (StructureSheaf.germ_toOpen R ⊤ (f.base x) trivial r)
  simpa only [Ideal.map_map] using congrArg (fun φ => Ideal.map φ I) hmap

/-- On an original affine chart the same stalk ideal is the literal
localization of the ideal extended by the original chart base map. -/
theorem extendedCenter_native_stalk {A : Type u} [CommRing A]
    (i : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion i]
    (ρ : R →+* A) (h : i ≫ f = Spec.map (CommRingCat.ofHom ρ))
    (p : PrimeSpectrum A) (U : Y.affineOpens) (hx : i.base p ∈ U.1) :
    Ideal.map (openImmersionStalkLocalizationEquiv i p).toRingHom
      (Ideal.map (Y.presheaf.germ U.1 (i.base p) hx).hom ((extendedCenter I f).ideal U)) =
      Ideal.map (algebraMap A (Localization.AtPrime p.asIdeal)) (Ideal.map ρ I) := by
  rw [extendedCenter_map_germ]
  have hmap : (openImmersionStalkLocalizationEquiv i p).toRingHom.comp
      ((f.stalkMap (i.base p)).hom.comp (StructureSheaf.toStalk R (f.base (i.base p))).hom) =
      (algebraMap A (Localization.AtPrime p.asIdeal)).comp ρ := by
    apply RingHom.ext
    intro r
    have hr := openChart_projection_coefficient i f ρ h p r
    exact (congrArg (openImmersionStalkLocalizationEquiv i p) hr).symm.trans
      ((openImmersionStalkLocalizationEquiv i p).apply_symm_apply _)
  simpa only [Ideal.map_map] using congrArg (fun φ => Ideal.map φ I) hmap

end KltDP.Geometry.AffineBlowup
