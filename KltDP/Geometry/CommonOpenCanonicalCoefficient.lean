import KltDP.Geometry.CanonicalExteriorCommonOpenComparison
import KltDP.Geometry.CanonicalCartierOpenPullback
import KltDP.Geometry.CartierOrderOpenRestriction
import KltDP.Geometry.NormalFiniteTypeValuationPoint
import KltDP.Geometry.QCartierPullback

/-!
# Fixed canonical coefficients on an original common open

The two original open immersions supplied by normal-model cofinality
transport the fixed source canonical divisor and the original rational
pullback orders. The original normal model need not be proper, and no
normality statement about its proper completion is used.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.CommonOpenCanonicalCoefficient

open OpenImmersionRational DominantCartierPullback

attribute [local instance] integralSchemeStalk_isDomain

local instance openGeneric {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (e : Y ⟶ Z) [IsOpenImmersion e] : GenericPointPreserving e :=
  ⟨genericPoint_eq_of_isOpenImmersion e⟩

/-- A common open carrying its original detected point is integral,
without any separate integrality assumption on that open. -/
theorem commonOpen_isIntegral {Y W : Scheme.{u}} [IsIntegral Y]
    (i : W ⟶ Y) [IsOpenImmersion i] (w : W) : IsIntegral W := by
  letI : Nonempty W := ⟨w⟩
  exact isIntegral_of_isOpenImmersion i

private theorem pullbackHom_congr
    {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (a b : Y ⟶ Z) [GenericPointPreserving a] [GenericPointPreserving b]
    (hab : a = b) : pullbackHom a = pullbackHom b := by
  cases hab
  rfl

private theorem exists_iso_of_hom_comp
    {𝒞 : Type*} [Category 𝒞] {A B C : 𝒞}
    (a : A ⟶ B) (e : B ≅ C) (b : A ⟶ C) (he : a ≫ e.hom = b) :
    ∃ e' : B ≅ C, a ≫ e'.hom = b := ⟨e, he⟩

variable {k : Type u} [Field k] (S X : NormalProjectiveSurface k)
    {V W : Scheme.{u}} [IsIntegral V] [IsIntegral W]
    (π : S.toScheme ⟶ X.toScheme) (v : V ⟶ X.toScheme)
    [GenericPointPreserving π] [GenericPointPreserving v]
    (iS : W ⟶ S.toScheme) (iV : W ⟶ V) [IsOpenImmersion iS] [IsOpenImmersion iV]
    (hcomm : iS ≫ π = iV ≫ v)

private theorem original_canonical_normalization
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2) :
    (modulePullbackIso iS KS).hom ≫
        (CanonicalCartierOpenPullback.canonicalModuleIso iS S.structureMorphism
          (iV ≫ (v ≫ X.structureMorphism))
          (CanonicalExteriorCommonOpen.structure_eq X.structureMorphism π v
            S.structureMorphism (v ≫ X.structureMorphism) hπ rfl iS iV hcomm) KS eKS).hom =
      (schemeModulePullback iS).map eKS.hom ≫
        SchemeKaehlerExteriorPullbackTransport.map S.structureMorphism iS
          (iV ≫ (v ≫ X.structureMorphism))
          (CanonicalExteriorCommonOpen.structure_eq X.structureMorphism π v
            S.structureMorphism (v ≫ X.structureMorphism) hπ rfl iS iV hcomm) 2 :=
  CanonicalCartierOpenPullback.canonicalModuleIso_comp iS S.structureMorphism
    (iV ≫ (v ≫ X.structureMorphism))
    (CanonicalExteriorCommonOpen.structure_eq X.structureMorphism π v
      S.structureMorphism (v ≫ X.structureMorphism) hπ rfl iS iV hcomm) KS eKS

/-- The literal fixed-source divisor on W represents the original relative
exterior sheaf, with its original frame/differential compatibility. -/
theorem exists_canonicalIso
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2) :
    ∃ e : cartierDivisorModule W (pullbackHom iS KS) ≅
        SmoothCanonicalExteriorComparison.relativeDifferentialExterior
          (iV ≫ (v ≫ X.structureMorphism)) 2,
      (modulePullbackIso iS KS).hom ≫ e.hom =
        (schemeModulePullback iS).map eKS.hom ≫
          SchemeKaehlerExteriorPullbackTransport.map S.structureMorphism iS
            (iV ≫ (v ≫ X.structureMorphism))
            (CanonicalExteriorCommonOpen.structure_eq X.structureMorphism π v
              S.structureMorphism (v ≫ X.structureMorphism) hπ rfl iS iV hcomm) 2 := by
  exact exists_iso_of_hom_comp
    (modulePullbackIso iS KS).hom
    (CanonicalCartierOpenPullback.canonicalModuleIso iS S.structureMorphism
      (iV ≫ (v ≫ X.structureMorphism))
      (CanonicalExteriorCommonOpen.structure_eq X.structureMorphism π v
        S.structureMorphism (v ≫ X.structureMorphism) hπ rfl iS iV hcomm) KS eKS)
    ((schemeModulePullback iS).map eKS.hom ≫
      SchemeKaehlerExteriorPullbackTransport.map S.structureMorphism iS
        (iV ≫ (v ≫ X.structureMorphism))
        (CanonicalExteriorCommonOpen.structure_eq X.structureMorphism π v
          S.structureMorphism (v ≫ X.structureMorphism) hπ rfl iS iV hcomm) 2)
    (original_canonical_normalization S X π v iS iV hcomm hπ KS eKS)

section Orders

variable (w : W) (D : S.PrimeCurve) (x : CodimensionOnePoint V)
    (hwS : iS.base w = D.genericPoint) (hwV : iV.base w = x.val)
    [LocallyOfFiniteType (v ≫ X.structureMorphism)] (hnormal : IsNormalScheme V)

include v hwV hnormal in
/-- The original common-open stalk is a DVR, derived at the original point. -/
theorem commonOpen_isDiscreteValuationRing : IsDiscreteValuationRing (W.presheaf.stalk w) := by
  letI := normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
  exact stalk_isDiscreteValuationRing_of_isOpenImmersion iV w x.val hwV

include hwS in
/-- The fixed source Cartier coefficient equals its actual common-open order. -/
theorem canonical_order (KS : CartierDivisor S.toScheme) :
    letI := commonOpen_isDiscreteValuationRing X v iV w x hwV hnormal
    S.cartierToWeilHom KS D = cartierOrderAt W (pullbackHom iS KS) w := by
  letI := commonOpen_isDiscreteValuationRing X v iV w x hwV hnormal
  letI := D.genericPoint_isDiscreteValuationRing
  rw [pullbackHom_eq_cartierRestrictionHom]
  exact (cartierOrderAt_cartierRestrictionHom iS KS w D.genericPoint hwS).symm

include hcomm hwS hwV in
/-- Original integral pullback orders agree at the two original model points. -/
theorem pullback_order (A : CartierDivisor X.toScheme) :
    letI := normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
    S.cartierToWeilHom (pullbackHom π A) D = cartierOrderAt V (pullbackHom v A) x.val := by
  letI := commonOpen_isDiscreteValuationRing X v iV w x hwV hnormal
  letI := normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
  have heq : pullbackHom iS (pullbackHom π A) = pullbackHom iV (pullbackHom v A) := by
    have hS := congrArg (fun F => F A) (pullbackHom_comp iS π)
    have hV := congrArg (fun F => F A) (pullbackHom_comp iV v)
    have hmaps := congrArg (fun F => F A) (pullbackHom_congr (iS ≫ π) (iV ≫ v) hcomm)
    exact hS.symm.trans (hmaps.trans hV)
  rw [canonical_order S X v iS iV w D x hwS hwV hnormal, heq,
    pullbackHom_eq_cartierRestrictionHom]
  exact cartierOrderAt_cartierRestrictionHom iV (pullbackHom v A) w x.val hwV

variable [IsAlgClosed k]

include hcomm hwS hwV in
/-- The actual discrepancy expression retains both original models and maps.
The Cartier numerator is produced from the original rational divisor. -/
theorem exists_discrepancy_expression (KS : CartierDivisor S.toScheme)
    (B : X.RationalWeilDivisor) (hB : X.QCartier B) :
    letI := commonOpen_isDiscreteValuationRing X v iV w x hwV hnormal
    letI := normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
    ∃ (n : ℕ) (_hn : 0 < n) (A : CartierDivisor X.toScheme),
      X.rationalCartierToWeilHom A = n • B ∧
      (S.cartierToWeilHom KS D : ℚ) - QCartierPullback.pullback π B hB D =
        (cartierOrderAt W (pullbackHom iS KS) w : ℚ) -
          (n : ℚ)⁻¹ * (cartierOrderAt V (pullbackHom v A) x.val : ℚ) := by
  letI := commonOpen_isDiscreteValuationRing X v iV w x hwV hnormal
  letI := normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
  obtain ⟨n, hn, A, hA⟩ := (X.qCartier_iff_exists_positive_multiple B).mp hB
  refine ⟨n, hn, A, hA, ?_⟩
  have hnum := QCartierPullback.pullbackToWeil_eq_of_positive_multiple π ⟨B, hB⟩ n hn A hA
  change (S.cartierToWeilHom KS D : ℚ) - QCartierPullback.pullbackToWeil π ⟨B, hB⟩ D = _
  rw [hnum]
  change (S.cartierToWeilHom KS D : ℚ) -
    (n : ℚ)⁻¹ * (S.cartierToWeilHom (pullbackHom π A) D : ℚ) = _
  rw [canonical_order S X v iS iV w D x hwS hwV hnormal,
    pullback_order S X π v iS iV hcomm w D x hwS hwV hnormal A]

end Orders

end KltDP.Geometry.CommonOpenCanonicalCoefficient
