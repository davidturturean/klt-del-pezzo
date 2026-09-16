import KltDP.Geometry.AffineModuleTildeExteriorMap
import KltDP.Geometry.AffineDifferentialExteriorNormalization

/-!
# Native affine top forms mapped to the intrinsic differential exterior

Compose the actual affine tilde-to-exterior morphism with the inverse of the
original affine Kähler exterior comparison. The resulting map has exactly the
native exterior-module tilde as source and the intrinsic differential exterior
sheaf as target. Every ordered wedge of native coordinate differentials maps
to the ordered wedge of derivatives of the original scheme functions.

This records the actual normalized map, without assuming its invertibility or
compatibility with a supplied canonical-divisor formula.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineDifferentialExteriorTildeMap

open AffineKaehlerTildeDerivation AffineDifferentialExteriorNormalization
open SchemeKaehlerSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- The literal native differential exterior module's tilde maps to the
original intrinsic exterior of the scheme Kähler sheaf. -/
def map (n : ℕ) :
    ((differentialModule k A).exteriorPower n).tilde ⟶
      SchemeExteriorPower.sheaf
        (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n :=
  AffineModuleTildeExteriorMap.map (differentialModule k A) n ≫
    (exteriorIso k A n).inv

/-- The forward affine exterior comparison recovers the original
tilde-to-exterior morphism, on the whole original sheaf. -/
theorem map_comp_exteriorIso (n : ℕ) :
    map k A n ≫ (exteriorIso k A n).hom =
      AffineModuleTildeExteriorMap.map (differentialModule k A) n := by
  change (AffineModuleTildeExteriorMap.map (differentialModule k A) n ≫
    (exteriorIso k A n).inv) ≫ (exteriorIso k A n).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- All original native coordinate wedges retain their original intrinsic
derivatives under the actual comparison, on every original open. -/
theorem map_toOpen_D (n : ℕ) (U : Opens (PrimeSpectrum A)) (v : Fin n → A) :
    (map k A n).val.app (op U)
        (ModuleCat.Tilde.toOpen ((differentialModule k A).exteriorPower n) U
          (exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D k A (v i)))) =
      SchemeExteriorPower.wedge
        (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n U
        (fun i => (baseRingDerivation
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d
            (StructureSheaf.toOpen A U (v i))) := by
  apply ((_root_.SheafOfModules.evaluation
    (Spec (CommRingCat.of A)).ringCatSheaf (op U)).mapIso
      (exteriorIso k A n)).toLinearEquiv.injective
  have hc := congrArg (fun g : ((differentialModule k A).exteriorPower n).tilde ⟶
      SchemeExteriorPower.sheaf (differentialModule k A).tilde n => g.val.app (op U)
    (ModuleCat.Tilde.toOpen ((differentialModule k A).exteriorPower n) U
      (exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D k A (v i)))))
    (map_comp_exteriorIso k A n)
  exact hc.trans ((AffineModuleTildeExteriorMap.map_toOpen_wedge
    (differentialModule k A) n U (fun i => KaehlerDifferential.D k A (v i))).trans
      (exteriorIso_wedge_d_toOpen k A n U v).symm)

/-- In degree two this is the literal native ordered wedge, not an arbitrary
choice of a generator of either line. -/
theorem map_toOpen_pair (U : Opens (PrimeSpectrum A)) (a b : A) :
    (map k A 2).val.app (op U)
        (ModuleCat.Tilde.toOpen ((differentialModule k A).exteriorPower 2) U
          (exteriorPower.ιMulti A 2
            ![KaehlerDifferential.D k A a, KaehlerDifferential.D k A b])) =
      differentialWedge (Spec.map (CommRingCat.ofHom (algebraMap k A))) U
        (StructureSheaf.toOpen A U a) (StructureSheaf.toOpen A U b) := by
  have hv : ![KaehlerDifferential.D k A a, KaehlerDifferential.D k A b] =
      (fun i : Fin 2 => KaehlerDifferential.D k A (![a, b] i)) := by
    funext i
    fin_cases i <;> rfl
  refine (congrArg (fun w => (map k A 2).val.app (op U)
    (ModuleCat.Tilde.toOpen ((differentialModule k A).exteriorPower 2) U
      (exteriorPower.ιMulti A 2 w))) hv).trans ?_
  refine (map_toOpen_D k A 2 U ![a, b]).trans ?_
  apply congrArg (SchemeExteriorPower.wedge
    (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) 2 U)
  funext i
  fin_cases i <;> rfl

end KltDP.Geometry.AffineDifferentialExteriorTildeMap
