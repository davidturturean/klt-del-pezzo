import KltDP.Geometry.RegularTargetCompatibleCanonicalFrame
import KltDP.Geometry.RegularSurfacePointNativeParameterChart
import KltDP.Geometry.AffinePrincipalNeighborhoodNativeParameters
import KltDP.Geometry.NormalModelFrameOverReferenceChart
import KltDP.Geometry.NormalModelCanonicalAffineSource
import KltDP.Geometry.NormalizedAffineCanonicalDifference
import KltDP.Geometry.CartierEquationChartNeighborhood
import KltDP.Geometry.CanonicalLocalReferenceChartDiscrepancy

/-!
# Positive canonical discrepancy over an original regular closed image

The compatible original source Cartier divisor fixes the rational top form.
Its canonical reference is extended near the regular image, with every
original Cartier numerator preserved. Genuine target parameters and native
bases are retained on an actual affine chart. Original frame restriction and
an actual smooth affine source chart then give the normalized affine
coefficient theorem, whose positive integer difference is identified with
the original rational Weil discrepancy by the original numerator equality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.RegularTargetCanonicalDiscrepancy

open NormalModelCanonical NormalProjectiveSurface CartierRationalCoordinate
open DominantCartierPullback IntrinsicNodal

attribute [local instance] integralSchemeStalk_isDomain

local instance finalOpenGeneric {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (i : Y ⟶ Z) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

private theorem generic_of_open_factor {Y A Z : Scheme.{u}}
    [hY : IsIntegral Y] [hA : IsIntegral A] [hZ : IsIntegral Z]
    (q : Y ⟶ A) (i : A ⟶ Z) [IsOpenImmersion i]
    (g : Y ⟶ Z) [GenericPointPreserving g] (h : q ≫ i = g) :
    GenericPointPreserving q := by
  refine ⟨?_⟩
  apply i.isOpenEmbedding.injective
  calc
    i.base (q.base (genericPoint Y)) = (q ≫ i).base (genericPoint Y) :=
      (Scheme.comp_base_apply q i (genericPoint Y)).symm
    _ = g.base (genericPoint Y) := congrArg (fun f => f.base (genericPoint Y)) h
    _ = genericPoint Z := @GenericPointPreserving.base_genericPoint Y Z hY hZ g inferInstance
    _ = i.base (genericPoint A) := (genericPoint_eq_of_isOpenImmersion i).symm

/-- A source prime mapping to an original regular closed target point has
strictly positive coefficient in the original compatible canonical difference.
No local canonical choice, coordinate compatibility, or coefficient premise
is supplied: all are derived from the original canonical data and maps. -/
theorem coefficient_pos_of_regular_closed_image
    {k : Type u} [Field k] [IsAlgClosed k]
    (S X : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (KX : X.WeilDivisor) (hcanonical : IsCanonicalWeilDivisor X KX)
    (hK : X.QCartier (rationalizeWeilDivisor X KX))
    (hpush : BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom KS) = KX)
    (C : S.PrimeCurve)
    (hclosed : IsClosed ({π.base C.genericPoint} : Set X.toScheme))
    (hregular : RegularPoint X.toScheme (π.base C.genericPoint)) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    0 < (S.rationalCartierToWeilHom KS -
      QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hK) C := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI := C.genericPoint_isDiscreteValuationRing
  obtain ⟨W, hxW, hW, hreference⟩ :=
    RegularTargetCompatibleCanonicalFrame.exists_compatible_frame
      S X π hbir hπ KS eKS KX hcanonical hpush C hclosed hregular
  letI : Nonempty W.toScheme := ⟨⟨π.base C.genericPoint, hxW⟩⟩
  letI : Nonempty W := ⟨⟨π.base C.genericPoint, hxW⟩⟩
  letI : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  obtain ⟨KW, eKW, F, p, hp, hF, hFord, hmultiple⟩ := hreference
  letI := stalkAlgebra X.structureMorphism (π.base C.genericPoint)
  obtain ⟨V, hVW, hxV, s, b₀, hparameters⟩ :=
    X.exists_regular_closed_native_parameter_chart S.structureMorphism π hπ hbir
      (π.base C.genericPoint) hclosed hregular W hxW
  letI := affineSectionsAlgebra X.structureMorphism V.2
  letI := X.toScheme.presheaf.algebra_section_stalk ⟨π.base C.genericPoint, hxV⟩
  letI := StalkKaehlerFiniteness.affine_stalk_scalarTower
    X.structureMorphism V.2 (π.base C.genericPoint) hxV
  letI := V.2.isLocalization_stalk ⟨π.base C.genericPoint, hxV⟩
  obtain ⟨r, hr, bA, hs, hb₀, hspan, hbA, hD, hopen, hstructure, pA, hpA⟩ := hparameters
  let A := Localization.Away r
  let jA : Spec (CommRingCat.of A) ⟶ X.toScheme :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X.toScheme, V.1) A)) ≫ V.2.fromSpec
  letI : IsOpenImmersion jA := hopen
  letI : Nonempty (Spec (CommRingCat.of A)) := ⟨pA⟩
  letI : IsIntegral (Spec (CommRingCat.of A)) := isIntegral_of_isOpenImmersion jA
  letI : IsDomain A := (affine_isIntegral_iff (CommRingCat.of A)).mp inferInstance
  let i : Spec (CommRingCat.of A) ⟶ W.toScheme :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X.toScheme, V.1) A)) ≫
      V.2.isoSpec.inv ≫ X.toScheme.homOfLE hVW
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X.toScheme, V.1) A))) := IsOpenImmersion.of_isLocalization r
  have hi : i ≫ W.ι = jA := by
    simp only [i, jA, Category.assoc, Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι]
  let sA := Spec.map (CommRingCat.ofHom (algebraMap k A))
  have hibase : i ≫ (W.ι ≫ X.structureMorphism) = sA := by
    rw [← Category.assoc, hi]
    exact hstructure
  have hpa : i.base pA = p.base F.point := by
    apply W.ι.isOpenEmbedding.injective
    calc
      W.ι.base (i.base pA) = (i ≫ W.ι).base pA :=
        (Scheme.comp_base_apply i W.ι pA).symm
      _ = jA.base pA := congrArg (fun f => f.base pA) hi
      _ = π.base C.genericPoint := hpA
      _ = π.base (F.toModel.base F.point) := congrArg π.base F.point_eq.symm
      _ = (F.toModel ≫ π).base F.point :=
        (Scheme.comp_base_apply F.toModel π F.point).symm
      _ = (p ≫ W.ι).base F.point := congrArg (fun f => f.base F.point) hp.symm
      _ = W.ι.base (p.base F.point) := Scheme.comp_base_apply p W.ι F.point
  obtain ⟨G, q₀, hq₀, hG, hGord, hq₀point⟩ :=
    exists_frame_over_reference_chart X W KW eKW π C.genericPoint F hF p hp i pA hpa
  letI := stalkAlgebra sA pA
  obtain ⟨bₚ, hbₚ, hvₚ⟩ :=
    AffinePrincipalNeighborhoodNativeParameters.exists_native_parameter_basis
      X.structureMorphism V.2 r pA (π.base C.genericPoint) hxV hpA s b₀ hb₀ hs
  obtain ⟨T, hT, hpoint, hsource⟩ :=
    LocalFrame.exists_affine_source_chart X W KW eKW π C.genericPoint G hG
  let sG := G.toModel ≫ (π ≫ X.structureMorphism)
  letI := affineSectionsAlgebra sG hT
  obtain ⟨bB, hsource⟩ := hsource
  let B := Γ(G.neighborhood, T)
  let j : Spec (CommRingCat.of B) ⟶ G.neighborhood := hT.fromSpec
  let pB : PrimeSpectrum B := hT.primeIdealOf ⟨G.point, hpoint⟩
  have hjpoint : j.base pB = G.point := hT.fromSpec_primeIdealOf ⟨G.point, hpoint⟩
  letI : Nonempty T := ⟨⟨G.point, hpoint⟩⟩
  letI : IsDomain B := inferInstance
  let jB := j ≫ G.toModel
  let sB := jB ≫ (π ≫ X.structureMorphism)
  have hpB : jB.base pB = C.genericPoint := by
    change (j ≫ G.toModel).base pB = C.genericPoint
    rw [Scheme.comp_base_apply, hjpoint, G.point_eq]
  letI : IsSmoothOfRelativeDimension 2 sB := by
    change IsSmoothOfRelativeDimension 2 ((j ≫ G.toModel) ≫ (π ≫ X.structureMorphism))
    rw [Category.assoc]
    exact IsLocalAtSource.comp (P := @IsSmoothOfRelativeDimension 2) G.smooth j
  let DS := pullbackHom j G.divisor
  let eS := canonicalOpenPullbackIso j sG sB
    (Category.assoc j G.toModel (π ≫ X.structureMorphism)).symm G.divisor G.canonicalIso
  let H := LocalFrame.ofCanonicalDivisor (π ≫ X.structureMorphism) jB pB C.genericPoint hpB DS eS
  have hsource' : sB = Spec.map (CommRingCat.ofHom (algebraMap k B)) ∧
      IsNormalized X W KW eKW π C.genericPoint H ∧ H.order = G.order := hsource
  obtain ⟨hB, hH, hHord⟩ := hsource'
  let q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) := j ≫ q₀
  have hq : (q ≫ i) ≫ W.ι = jB ≫ π := by
    change ((j ≫ q₀) ≫ i) ≫ W.ι = (j ≫ G.toModel) ≫ π
    simpa only [Category.assoc] using congrArg (fun a => j ≫ a) hq₀
  letI : GenericPointPreserving q := generic_of_open_factor q (i ≫ W.ι) (jB ≫ π)
    ((Category.assoc q i W.ι).symm.trans hq)
  have hqpoint : q.base pB = pA := by
    change (j ≫ q₀).base pB = pA
    rw [Scheme.comp_base_apply, hjpoint]
    exact hq₀point
  let DA := pullbackHom i KW
  obtain ⟨cS, cT, hpS, hST⟩ := CartierEquationChartNeighborhood.exists_compatible q DA DS pB
  let vA : Fin 2 → A := fun t => algebraMap Γ(X.toScheme, V.1) A (s t)
  have hnative :
      letI := AffineDifferentialExteriorStalkEvaluation.stalkGroundAlgebra
        (k := k) (A := A) (p := q.base pB)
      ∃ b : Basis (Fin 2) ((Spec (CommRingCat.of A)).presheaf.stalk (q.base pB))
          (KaehlerDifferential k ((Spec (CommRingCat.of A)).presheaf.stalk (q.base pB))),
        (∀ t, b t = KaehlerDifferential.D k
          ((Spec (CommRingCat.of A)).presheaf.stalk (q.base pB))
          (StructureSheaf.toStalk A (q.base pB) (vA t))) ∧
        (∀ t, StructureSheaf.toStalk A (q.base pB) (vA t) ∈
          IsLocalRing.maximalIdeal ((Spec (CommRingCat.of A)).presheaf.stalk (q.base pB))) := by
    rw [hqpoint]
    exact ⟨bₚ, hbₚ, hvₚ⟩
  letI := AffineDifferentialExteriorStalkEvaluation.stalkGroundAlgebra
    (k := k) (A := A) (p := q.base pB)
  obtain ⟨bq, hbq, hvq⟩ := hnative
  have hpositive := NormalizedAffineCanonicalDifference.order_difference_pos
    X W KW eKW A B i sA hibase rfl π C.genericPoint jB pB hpB hB DS eS hH
    q hq cS cT hST hpS bA bB vA hvq bq hbq
  have horder : H.order = S.cartierToWeilHom KS C := hHord.trans (hGord.trans hFord)
  obtain ⟨n, hn, L, hL⟩ := (X.qCartier_integral_iff KX).mp hK
  have hdelta := CanonicalLocalReferenceDiscrepancy.coefficient_eq_chart_difference
    S X π C H W i q hq KW KS horder KX hK n hn L hL (hmultiple n L hL)
  have hlocal : 0 < H.order - cartierOrderAt H.neighborhood (pullbackHom q DA) H.point := by
    rw [LocalFrame.order_eq_cartierOrderAt H]
    exact hpositive
  rw [hdelta]
  exact_mod_cast hlocal

end KltDP.Geometry.RegularTargetCanonicalDiscrepancy

#check @KltDP.Geometry.RegularTargetCanonicalDiscrepancy.coefficient_pos_of_regular_closed_image
#print axioms KltDP.Geometry.RegularTargetCanonicalDiscrepancy.coefficient_pos_of_regular_closed_image
