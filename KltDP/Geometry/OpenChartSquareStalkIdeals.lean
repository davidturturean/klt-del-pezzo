import KltDP.Geometry.PointBlowupProjectionStalkCoefficients
import KltDP.Geometry.GluedSubschemeStalkKernel

/-!
# Original ideal transport in a commuting open-chart square

The proved native coefficient square is applied to the original sections
of the source chart. Only equality of the two actual point images is
eliminated. The resulting equality of original ring maps transports
arbitrary source-chart ideals, including their nonreduced structure.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem stalkCongr_inv_germ (X : Scheme.{u}) (U : X.Opens)
    (x y : X) (h : x = y) (hx : x ∈ U) (hy : y ∈ U) (s : Γ(X, U)) :
    (X.presheaf.stalkCongr (.of_eq h)).inv (X.presheaf.germ U y hy s) =
      X.presheaf.germ U x hx s := by
  subst y
  change X.presheaf.stalkSpecializes (specializes_refl x)
    (X.presheaf.germ U x hy s) = _
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

variable {R A : Type u} [CommRing R] [CommRing A] {X Y : Scheme.{u}}
variable (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
variable (i : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion i]
variable (π : Y ⟶ X) (ρ : R →+* A)
variable (h : i ≫ π = Spec.map (CommRingCat.ofHom ρ) ≫ j)
variable (p : PrimeSpectrum A) (hx : π.base (i.base p) ∈ j ''ᵁ ⊤)

include h

/-- The original section germ and the actual scheme stalk pullback agree
with the original affine ring map in the literal target chart local ring. -/
theorem openChartSquare_stalkMap_germ (s : Γ(X, j ''ᵁ ⊤)) :
    openImmersionStalkLocalizationEquiv i p
      (π.stalkMap (i.base p) (X.presheaf.germ (j ''ᵁ ⊤) (π.base (i.base p)) hx s)) =
      algebraMap A (Localization.AtPrime p.asIdeal) (ρ (chartSectionsEquiv j s)) := by
  have hpoint : π.base (i.base p) = j.base (PrimeSpectrum.comap ρ p) :=
    congrArg (fun f : Spec (CommRingCat.of A) ⟶ X => f.base p) h
  have hs := openChartSquare_stalkMap_coefficient j i π ρ h p (chartSectionsEquiv j s)
  rw [openImmersionStalkLocalizationEquiv_symm_algebraMap,
    RingEquiv.symm_apply_apply] at hs
  have ht := stalkCongr_inv_germ X (j ''ᵁ ⊤) (π.base (i.base p))
    (j.base (PrimeSpectrum.comap ρ p)) hpoint hx
    (mem_chart_image_top j (PrimeSpectrum.comap ρ p)) s
  have hnative : π.stalkMap (i.base p)
      (X.presheaf.germ (j ''ᵁ ⊤) (π.base (i.base p)) hx s) =
      (openImmersionStalkLocalizationEquiv i p).symm
        (algebraMap A (Localization.AtPrime p.asIdeal) (ρ (chartSectionsEquiv j s))) := by
    calc
      _ = π.stalkMap (i.base p)
          ((X.presheaf.stalkCongr (.of_eq hpoint)).inv
            (X.presheaf.germ (j ''ᵁ ⊤) (j.base (PrimeSpectrum.comap ρ p))
              (mem_chart_image_top j (PrimeSpectrum.comap ρ p)) s)) :=
        congrArg (π.stalkMap (i.base p)) ht.symm
      _ = _ := hs
  exact (congrArg (openImmersionStalkLocalizationEquiv i p) hnative).trans
    ((openImmersionStalkLocalizationEquiv i p).apply_symm_apply _)

/-- Extension of an arbitrary original source-chart ideal commutes with
the original scheme stalk pullback and the actual affine chart map. -/
theorem openChartSquare_stalkMap_ideal (J : Ideal Γ(X, j ''ᵁ ⊤)) :
    Ideal.map (openImmersionStalkLocalizationEquiv i p).toRingHom
      (Ideal.map (π.stalkMap (i.base p)).hom
        (Ideal.map (X.presheaf.germ (j ''ᵁ ⊤) (π.base (i.base p)) hx).hom J)) =
      Ideal.map (algebraMap A (Localization.AtPrime p.asIdeal))
        (Ideal.map ρ (Ideal.map (chartSectionsEquiv j).toRingHom J)) := by
  have hmap : (openImmersionStalkLocalizationEquiv i p).toRingHom.comp
      ((π.stalkMap (i.base p)).hom.comp
        (X.presheaf.germ (j ''ᵁ ⊤) (π.base (i.base p)) hx).hom) =
      (algebraMap A (Localization.AtPrime p.asIdeal)).comp
        (ρ.comp (chartSectionsEquiv j).toRingHom) := by
    apply RingHom.ext
    intro s
    exact openChartSquare_stalkMap_germ j i π ρ h p hx s
  simpa only [Ideal.map_map] using congrArg (fun f => Ideal.map f J) hmap

end KltDP.Geometry
