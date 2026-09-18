import KltDP.Geometry.SplitQuadraticMappedRescalingSpec

/-!
# Splitting the original quadratic chart with a proved unit root

The existing CRT isomorphism applies to the actual branch coefficient by
its proved square equation. Naturality retains the original coefficient
and rescaling maps, without replacing the atlas by newly chosen maps.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.QuadraticRootChartSplitting

open QuadraticCover
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Apply the existing original CRT to a proved square coefficient. -/
def splitIso (s : R) (a : Rˣ) (ha : (a : R) ^ 2 = s) (h2 : IsUnit (2 : R)) :
    affineScheme s ≅ Spec (.of R) ⨿ Spec (.of R) :=
  eqToIso (congrArg affineScheme ha.symm) ≪≫ splitQuadraticSpecIso a h2

/-- Naturality of the actual splitting for the original mapped rescaling. -/
@[reassoc]
theorem hom_mappedRescale (f : R →+* S) (s : R) (t : S) (a : Rˣ) (b v : Sˣ)
    (ha : (a : R) ^ 2 = s) (hb : (b : S) ^ 2 = t)
    (h : f s = (v : S) ^ 2 * t) (hr : f (a : R) = (v : S) * (b : S))
    (hR : IsUnit (2 : R)) (hS : IsUnit (2 : S)) :
    mappedRescaleMap f s t v h ≫ (splitIso s a ha hR).hom =
      (splitIso t b hb hS).hom ≫
        coprod.map (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom f)) := by
  subst s
  subst t
  simpa only [splitIso, eqToIso_refl, Iso.trans_hom, Iso.refl_hom, Category.id_comp] using
    splitQuadraticSpecIso_hom_mappedRescale f a b v h hr hR hS

/-- The inverse square uses exactly the same original mapped rescaling. -/
@[reassoc]
theorem inv_mappedRescale (f : R →+* S) (s : R) (t : S) (a : Rˣ) (b v : Sˣ)
    (ha : (a : R) ^ 2 = s) (hb : (b : S) ^ 2 = t)
    (h : f s = (v : S) ^ 2 * t) (hr : f (a : R) = (v : S) * (b : S))
    (hR : IsUnit (2 : R)) (hS : IsUnit (2 : S)) :
    (splitIso t b hb hS).inv ≫ mappedRescaleMap f s t v h =
      coprod.map (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom f)) ≫
        (splitIso s a ha hR).inv := by
  subst s
  subst t
  simpa only [splitIso, eqToIso_refl, Iso.trans_inv, Iso.refl_inv, Category.comp_id] using
    splitQuadraticSpecIso_mappedRescale f a b v h hr hR hS

/-- The inverse splitting preserves the original structural map. -/
@[reassoc]
theorem inv_toBase (s : R) (a : Rˣ) (ha : (a : R) ^ 2 = s) (h2 : IsUnit (2 : R)) :
    (splitIso s a ha h2).inv ≫ toBase s =
      coprod.desc (𝟙 (Spec (.of R))) (𝟙 (Spec (.of R))) := by
  subst s
  simpa only [splitIso, eqToIso_refl, Iso.trans_inv, Iso.refl_inv, Category.comp_id] using
    splitQuadraticSpecIso_inv_toBase a h2

/-- The forward splitting also preserves the original structural map. -/
@[reassoc]
theorem hom_fold (s : R) (a : Rˣ) (ha : (a : R) ^ 2 = s) (h2 : IsUnit (2 : R)) :
    (splitIso s a ha h2).hom ≫
      coprod.desc (𝟙 (Spec (.of R))) (𝟙 (Spec (.of R))) = toBase s := by
  rw [← inv_toBase s a ha h2, Iso.hom_inv_id_assoc]

end KltDP.Geometry.QuadraticRootChartSplitting

#print axioms KltDP.Geometry.QuadraticRootChartSplitting.hom_mappedRescale
