import KltDP.Geometry.SchemeExteriorPowerMap
import KltDP.Geometry.AffineKaehlerTildeLocalization

/-!
# Original affine differential wedges in the intrinsic exterior sheaf

Apply the existing exterior-sheaf functor to the proved actual affine Kähler
comparison. Its forward map preserves every wedge of original derivatives;
for original affine functions, these become the canonical native differential
tilde sections. The construction has no chosen line isomorphism or frame.

The existing universal derivation and the original alternating sheaf wedge
also give the product-coordinate determinant identity inside the intrinsic
exterior sheaf, on every open of every original base-ring scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineDifferentialExteriorNormalization

open AffineKaehlerTildeDerivation SchemeKaehlerSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Affine

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- The original intrinsic exterior sheaf compared with the exterior sheaf
of the original native affine differential tilde. -/
def exteriorIso (n : ℕ) :
    SchemeExteriorPower.sheaf
      (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n ≅
        SchemeExteriorPower.sheaf (differentialModule k A).tilde n :=
  SchemeExteriorPower.mapIso (AffineKaehlerTildeLocalization.iso k A) n

/-- The comparison preserves wedges of the original sectionwise derivatives. -/
theorem exteriorIso_wedge_d (n : ℕ) (U : Opens (PrimeSpectrum A))
    (v : Fin n → Γ(Spec (CommRingCat.of A), U)) :
    (exteriorIso k A n).hom.val.app (op U)
        (SchemeExteriorPower.wedge
          (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n U
          (fun i => (baseRingDerivation
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d (v i))) =
      SchemeExteriorPower.wedge (differentialModule k A).tilde n U
        (fun i => sectionD k A U (v i)) := by
  refine (SchemeExteriorPower.map_wedge
    (AffineKaehlerTildeLocalization.iso k A).hom n U
    (fun i => (baseRingDerivation
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d (v i))).trans ?_
  apply congrArg (SchemeExteriorPower.wedge (differentialModule k A).tilde n U)
  funext i
  exact AffineKaehlerTildeLocalization.iso_d k A U (v i)

/-- Actual affine coordinates retain their original native differentials. -/
theorem exteriorIso_wedge_d_toOpen (n : ℕ) (U : Opens (PrimeSpectrum A)) (v : Fin n → A) :
    (exteriorIso k A n).hom.val.app (op U)
        (SchemeExteriorPower.wedge
          (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n U
          (fun i => (baseRingDerivation
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d
              (StructureSheaf.toOpen A U (v i)))) =
      SchemeExteriorPower.wedge (differentialModule k A).tilde n U
        (fun i => ModuleCat.Tilde.toOpen (differentialModule k A) U
          (KaehlerDifferential.D k A (v i))) := by
  refine (exteriorIso_wedge_d k A n U (fun i => StructureSheaf.toOpen A U (v i))).trans ?_
  apply congrArg (SchemeExteriorPower.wedge (differentialModule k A).tilde n U)
  funext i
  exact sectionD_toOpen k A U (v i)

end Affine

section Intrinsic

variable {k : Type u} [CommRing k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The wedge of the two original global differential sections. -/
def differentialWedge (U : X.Opens) (a b : Γ(X, U)) :
    (SchemeExteriorPower.sheaf (baseRingSheaf f) 2).val.obj (op U) :=
  SchemeExteriorPower.wedge (baseRingSheaf f) 2 U
    ![(baseRingDerivation f).d a, (baseRingDerivation f).d b]

private theorem alternating_pair_leibniz {R M N : Type u}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (w : M [⋀^Fin 2]→ₗ[R] N) (a b : R) (x y : M) :
    w ![x, a • y + b • x] = a • w ![x, y] := by
  let B := w.curryLeft x
  change B ![a • y + b • x] = _
  rw [B.map_vecCons_add, B.map_vecCons_smul, B.map_vecCons_smul]
  change a • w ![x, y] + b • w ![x, x] = _
  have hx : w ![x, x] = 0 :=
    w.map_eq_zero_of_eq ![x, x] (i := (0 : Fin 2)) (j := (1 : Fin 2)) rfl (by decide)
  rw [hx, smul_zero, add_zero]

/-- Leibniz and alternation give the determinant equation in the actual
intrinsic exterior sheaf, with no coordinate-frame premise. -/
theorem differentialWedge_mul (U : X.Opens) (a b : Γ(X, U)) :
    differentialWedge f U a (a * b) = a • differentialWedge f U a b := by
  let w := SchemeExteriorPower.wedge (baseRingSheaf f) 2 U
  have hd := (baseRingDerivation f).d_mul a b
  exact (congrArg
    (fun z : (baseRingSheaf f).val.obj (op U) => w ![(baseRingDerivation f).d a, z]) hd).trans
      (alternating_pair_leibniz w a b ((baseRingDerivation f).d a)
        ((baseRingDerivation f).d b))

/-- The original alternating wedge retains its coordinate-order sign. -/
theorem differentialWedge_swap (U : X.Opens) (a b : Γ(X, U)) :
    differentialWedge f U a b = -differentialWedge f U b a := by
  let w := SchemeExteriorPower.wedge (baseRingSheaf f) 2 U
  have hv : ![(baseRingDerivation f).d a, (baseRingDerivation f).d b] =
      ![(baseRingDerivation f).d b, (baseRingDerivation f).d a] ∘
        Equiv.swap (0 : Fin 2) 1 := by
    funext i
    fin_cases i <;> rfl
  exact (congrArg w hv).trans
    (w.map_swap ![(baseRingDerivation f).d b, (baseRingDerivation f).d a]
      (by decide : (0 : Fin 2) ≠ 1))

end Intrinsic

section AffinePair

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- In degree two the same original comparison preserves the ordered pair
of actual affine coordinate differentials. -/
theorem exteriorIso_differentialWedge_toOpen
    (U : Opens (PrimeSpectrum A)) (a b : A) :
    (exteriorIso k A 2).hom.val.app (op U)
        (differentialWedge (Spec.map (CommRingCat.ofHom (algebraMap k A))) U
          (StructureSheaf.toOpen A U a) (StructureSheaf.toOpen A U b)) =
      SchemeExteriorPower.wedge (differentialModule k A).tilde 2 U
        (fun i => ModuleCat.Tilde.toOpen (differentialModule k A) U
          (KaehlerDifferential.D k A (![a, b] i))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  have hv : ![(baseRingDerivation f).d (StructureSheaf.toOpen A U a),
      (baseRingDerivation f).d (StructureSheaf.toOpen A U b)] =
      (fun i : Fin 2 => (baseRingDerivation f).d
        (StructureSheaf.toOpen A U (![a, b] i))) := by
    funext i
    fin_cases i <;> rfl
  exact (congrArg (fun v => (exteriorIso k A 2).hom.val.app (op U)
    (SchemeExteriorPower.wedge (baseRingSheaf f) 2 U v)) hv).trans
      (exteriorIso_wedge_d_toOpen k A 2 U ![a, b])

end AffinePair

end KltDP.Geometry.AffineDifferentialExteriorNormalization
