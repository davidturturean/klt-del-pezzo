import KltDP.Geometry.NormalModelCanonicalFrameOrder
import KltDP.Geometry.CartierRationalCoordinateEquality
import KltDP.Geometry.CanonicalOpenCoordinateCongruence
import KltDP.Geometry.CanonicalCoordinateOpenComposition
import KltDP.Geometry.OpenImmersionCommonPointNeighborhood
import KltDP.Geometry.OpenImmersionNonemptyOverlap

/-!
# Every normalized original local canonical frame has the same order

Both actual frame neighborhoods are restricted to a common neighborhood
through the original model point. Their two normalization witnesses have
a further actual nonempty overlap. Original canonical-coordinate composition
identifies the two coordinates there; rational restriction faithfulness and
the actual Cartier multiplier then identify the neighborhood divisors.
The original open-immersion order transport finishes the comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalModelCanonical.LocalFrame

open CartierRationalCoordinate OpenImmersionRational DominantCartierPullback

attribute [local instance] integralSchemeStalk_isDomain
attribute [local irreducible] canonicalOpenPullbackIso

local instance comparisonOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (f : A ⟶ B) [IsOpenImmersion f] : GenericPointPreserving f :=
  ⟨genericPoint_eq_of_isOpenImmersion f⟩

private theorem coordinate_square
    {k : Type u} [CommRing k] {S Y₁ Y₂ Z : Scheme.{u}}
    [IsIntegral S] [IsIntegral Y₁] [IsIntegral Y₂] [IsIntegral Z]
    (f₁ : Z ⟶ Y₁) (g₁ : Y₁ ⟶ S) (f₂ : Z ⟶ Y₂) (g₂ : Y₂ ⟶ S)
    [IsOpenImmersion f₁] [IsOpenImmersion g₁]
    [IsOpenImmersion f₂] [IsOpenImmersion g₂]
    (hsq : f₁ ≫ g₁ = f₂ ≫ g₂)
    (sS : S ⟶ Spec (CommRingCat.of k))
    (s₁ : Y₁ ⟶ Spec (CommRingCat.of k)) (s₂ : Y₂ ⟶ Spec (CommRingCat.of k))
    (sZ : Z ⟶ Spec (CommRingCat.of k))
    (hg₁ : g₁ ≫ sS = s₁) (hf₁ : f₁ ≫ s₁ = sZ)
    (hg₂ : g₂ ≫ sS = s₂) (hf₂ : f₂ ≫ s₂ = sZ)
    (D : CartierDivisor S)
    (e : cartierDivisorModule S D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sS 2) :
    coordinate Z (pullbackHom f₁ (pullbackHom g₁ D)) _
        (canonicalOpenPullbackIso f₁ s₁ sZ hf₁ (pullbackHom g₁ D)
          (canonicalOpenPullbackIso g₁ sS s₁ hg₁ D e)) =
      coordinate Z (pullbackHom f₂ (pullbackHom g₂ D)) _
        (canonicalOpenPullbackIso f₂ s₂ sZ hf₂ (pullbackHom g₂ D)
          (canonicalOpenPullbackIso g₂ sS s₂ hg₂ D e)) := by
  have h₁ : (f₁ ≫ g₁) ≫ sS = sZ := by rw [Category.assoc, hg₁, hf₁]
  have h₂ : (f₂ ≫ g₂) ≫ sS = sZ := by rw [Category.assoc, hg₂, hf₂]
  exact (coordinate_canonicalOpenPullbackIso_comp f₁ g₁ sS s₁ sZ hg₁ hf₁ D e).trans
    ((coordinate_canonicalOpenPullbackIso_congr (f₁ ≫ g₁) (f₂ ≫ g₂)
      hsq sS sZ h₁ h₂ D e).trans
      (coordinate_canonicalOpenPullbackIso_comp f₂ g₂ sS s₂ sZ hg₂ hf₂ D e).symm)

variable {k : Type u} [Field k] {V : Scheme.{u}} [IsIntegral V]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme]

local instance comparisonIntegralOpen : IsIntegral U.toScheme :=
  isIntegral_of_isOpenImmersion U.ι

/-- Every actual local frame normalized to the same original target
canonical reference has the same original model order. -/
theorem order_eq_of_isNormalized
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    (v : V ⟶ X.toScheme) (x : V) [IsDiscreteValuationRing (V.presheaf.stalk x)]
    (F G : LocalFrame (v ≫ X.structureMorphism) x)
    (hF : IsNormalized X U KU eKU v x F)
    (hG : IsNormalized X U KU eKU v x G) : F.order = G.order := by
  obtain ⟨ZF, hZF, hF⟩ := hF
  letI : Nonempty ZF.toScheme := hZF
  letI : IsIntegral ZF.toScheme := isIntegral_of_isOpenImmersion ZF.ι
  obtain ⟨fU, hfU, hF⟩ := hF
  letI : IsOpenImmersion fU := hfU
  obtain ⟨htF, hcF⟩ := hF
  obtain ⟨ZG, hZG, hG⟩ := hG
  letI : Nonempty ZG.toScheme := hZG
  letI : IsIntegral ZG.toScheme := isIntegral_of_isOpenImmersion ZG.ι
  obtain ⟨gU, hgU, hG⟩ := hG
  letI : IsOpenImmersion gU := hgU
  obtain ⟨htG, hcG⟩ := hG
  obtain ⟨W, jF, jG, w, hjF, hjG, hwF, hwG, hWG⟩ :=
    exists_common_neighborhood_at_point F.toModel G.toModel F.point G.point
      (F.point_eq.trans G.point_eq.symm)
  letI : IsOpenImmersion jF := hjF
  letI : IsOpenImmersion jG := hjG
  letI : Nonempty W := ⟨w⟩
  letI : IsIntegral W := isIntegral_of_isOpenImmersion jF
  letI : IsDiscreteValuationRing (W.presheaf.stalk w) :=
    stalk_isDiscreteValuationRing_of_isOpenImmersion jF w F.point hwF
  let sF := F.toModel ≫ (v ≫ X.structureMorphism)
  let sG := G.toModel ≫ (v ≫ X.structureMorphism)
  let sU := U.ι ≫ X.structureMorphism
  let sW := jF ≫ sF
  have hsG : jG ≫ sG = sW := by
    simpa only [sF, sG, sW, Category.assoc] using
      congrArg (fun m => m ≫ (v ≫ X.structureMorphism)) hWG.symm
  have huF : fU ≫ sU = ZF.ι ≫ sF := by
    simpa only [sU, sF, Category.assoc] using
      congrArg (fun m => m ≫ X.structureMorphism) htF
  have huG : gU ≫ sU = ZG.ι ≫ sG := by
    simpa only [sU, sG, Category.assoc] using
      congrArg (fun m => m ≫ X.structureMorphism) htG
  let DF : CartierDivisor W := pullbackHom jF F.divisor
  let DG : CartierDivisor W := pullbackHom jG G.divisor
  let eF : cartierDivisorModule W DF ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sW 2 :=
    canonicalOpenPullbackIso jF sF sW rfl F.divisor F.canonicalIso
  let eG : cartierDivisorModule W DG ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sW 2 :=
    canonicalOpenPullbackIso jG sG sW hsG G.divisor G.canonicalIso
  obtain ⟨Q, hQ, qG, hqG, hq⟩ := exists_nonempty_open_overlap
    (ZF.ι ≫ F.toModel) (ZG.ι ≫ G.toModel)
  letI : Nonempty Q.toScheme := hQ
  letI : IsIntegral Q.toScheme := isIntegral_of_isOpenImmersion Q.ι
  letI : IsOpenImmersion qG := hqG
  obtain ⟨Z, hZ, zQ, hzQ, hz⟩ := exists_nonempty_open_overlap
    (jF ≫ F.toModel) (Q.ι ≫ (ZF.ι ≫ F.toModel))
  letI : Nonempty Z.toScheme := hZ
  letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
  letI : IsOpenImmersion zQ := hzQ
  let rF : Z.toScheme ⟶ ZF.toScheme := zQ ≫ Q.ι
  let rG : Z.toScheme ⟶ ZG.toScheme := zQ ≫ qG
  have hpF : Z.ι ≫ jF = rF ≫ ZF.ι := by
    apply (cancel_mono F.toModel).mp
    simpa only [rF, Category.assoc] using hz
  have hpG : Z.ι ≫ jG = rG ≫ ZG.ι := by
    apply (cancel_mono G.toModel).mp
    have h : Z.ι ≫ (jG ≫ G.toModel) = zQ ≫ (qG ≫ (ZG.ι ≫ G.toModel)) := by
      calc
        _ = Z.ι ≫ (jF ≫ F.toModel) := congrArg (fun m => Z.ι ≫ m) hWG.symm
        _ = zQ ≫ (Q.ι ≫ (ZF.ι ≫ F.toModel)) := hz
        _ = _ := congrArg (fun m => zQ ≫ m) hq
    simpa only [rG, Category.assoc] using h
  have hU : rF ≫ fU = rG ≫ gU := by
    apply (cancel_mono U.ι).mp
    calc
      (rF ≫ fU) ≫ U.ι = ((rF ≫ ZF.ι) ≫ F.toModel) ≫ v := by
        simpa only [Category.assoc] using congrArg (fun m => rF ≫ m) htF
      _ = ((Z.ι ≫ jF) ≫ F.toModel) ≫ v := by rw [hpF]
      _ = ((Z.ι ≫ jG) ≫ G.toModel) ≫ v := by
        simpa only [Category.assoc] using congrArg (fun m => (Z.ι ≫ m) ≫ v) hWG
      _ = ((rG ≫ ZG.ι) ≫ G.toModel) ≫ v := by rw [hpG]
      _ = (rG ≫ gU) ≫ U.ι := by
        simpa only [Category.assoc] using (congrArg (fun m => rG ≫ m) htG).symm
  let sZ := Z.ι ≫ sW
  have hrF : rF ≫ (ZF.ι ≫ sF) = sZ := by
    simpa only [sZ, sW, Category.assoc] using
      congrArg (fun m => m ≫ sF) hpF.symm
  have hrG : rG ≫ (ZG.ι ≫ sG) = sZ := by
    calc
      _ = (Z.ι ≫ jG) ≫ sG := by
        simpa only [Category.assoc] using congrArg (fun m => m ≫ sG) hpG.symm
      _ = sZ := by rw [Category.assoc, hsG]
  have hleft := coordinate_square Z.ι jF rF ZF.ι hpF
    sF sW (ZF.ι ≫ sF) sZ rfl rfl rfl hrF F.divisor F.canonicalIso
  have hright := coordinate_square Z.ι jG rG ZG.ι hpG
    sG sW (ZG.ι ≫ sG) sZ hsG rfl rfl hrG G.divisor G.canonicalIso
  have hmiddle := coordinate_square rF fU rG gU hU
    sU (ZF.ι ≫ sF) (ZG.ι ≫ sG) sZ huF hrF huG hrG KU eKU
  have hF' := canonicalOpenPullback_coordinate_congr (ZF.ι ≫ sF) sZ rF hrF
    (pullbackHom ZF.ι F.divisor) (pullbackHom fU KU)
    (canonicalOpenPullbackIso ZF.ι sF (ZF.ι ≫ sF) rfl F.divisor F.canonicalIso)
    (canonicalOpenPullbackIso fU sU (ZF.ι ≫ sF) huF KU eKU) hcF
  have hG' := canonicalOpenPullback_coordinate_congr (ZG.ι ≫ sG) sZ rG hrG
    (pullbackHom ZG.ι G.divisor) (pullbackHom gU KU)
    (canonicalOpenPullbackIso ZG.ι sG (ZG.ι ≫ sG) rfl G.divisor G.canonicalIso)
    (canonicalOpenPullbackIso gU sU (ZG.ι ≫ sG) huG KU eKU) hcG
  have hcoordinates : coordinate Z.toScheme (pullbackHom Z.ι DF) _
        (canonicalOpenPullbackIso Z.ι sW sZ rfl DF eF) =
      coordinate Z.toScheme (pullbackHom Z.ι DG) _
        (canonicalOpenPullbackIso Z.ι sW sZ rfl DG eG) :=
    hleft.trans (hF'.trans (hmiddle.trans (hG'.symm.trans hright.symm)))
  have hdiv : DF = DG :=
    divisor_eq_of_canonicalOpenPullback_coordinate_eq DF DG Z.ι sW sZ rfl eF eG hcoordinates
  have horderF : cartierOrderAt W DF w = F.order := by
    calc
      _ = cartierOrderAt F.neighborhood F.divisor F.point := by
        dsimp only [DF]
        rw [pullbackHom_eq_cartierRestrictionHom]
        exact cartierOrderAt_cartierRestrictionHom jF F.divisor w F.point hwF
      _ = F.order := (order_eq_cartierOrderAt F).symm
  have horderG : cartierOrderAt W DG w = G.order := by
    calc
      _ = cartierOrderAt G.neighborhood G.divisor G.point := by
        dsimp only [DG]
        rw [pullbackHom_eq_cartierRestrictionHom]
        exact cartierOrderAt_cartierRestrictionHom jG G.divisor w G.point hwG
      _ = G.order := (order_eq_cartierOrderAt G).symm
  exact horderF.symm.trans
    ((congrArg (fun A : CartierDivisor W => cartierOrderAt W A w) hdiv).trans horderG)

end KltDP.Geometry.NormalModelCanonical.LocalFrame

#check @KltDP.Geometry.NormalModelCanonical.LocalFrame.order_eq_of_isNormalized
#print axioms KltDP.Geometry.NormalModelCanonical.LocalFrame.order_eq_of_isNormalized
