import KltDP.Literature.BlowupExceptionalLiterals
import KltDP.Geometry.PrimeCurveConormalDegree
import KltDP.Geometry.MinimalResolutionDebts
import KltDP.Geometry.PointBlowupCurveDimension
import KltDP.Geometry.PointBlowupSurface
import KltDP.Geometry.PrimeCurveOfClosedImmersion
import KltDP.Geometry.SchemeIsoEulerTransport
import KltDP.Geometry.FiniteTypeNoetherian

/-!
# The exceptional curve of a point blowup is a `(−1)`-curve (F10, E4)

Consumers of the Stacks literals `KltDP.Literature.Stacks.BlowupChartRegularLiteral` (0AGR) and
`BlowupRegularPointLiteral` (0AGQ), over the accepted glued point blowup
`KltDP.Geometry.PointBlowupGluing.scheme` of a regular `NormalProjectiveSurface k`, `k`
algebraically closed.

* `blowupSurface`: the glued blowup of `S` at the closed point `j.base q` **as a
  `NormalProjectiveSurface k`** — integral and of dimension two by the accepted
  `surface_scheme_isIntegral`, `surface_scheme_dimension_two`; normal because it is regular
  (0AGR + `isNormalScheme_of_regularPoint`); projective by 0C5P applied to the proper composite
  `projection ≫ S.structureMorphism`. `isPointBlowupAt_blowupSurface` shows that it is an
  `IsPointBlowupAt` of `S` at that point, so the hypothesis class of the `(−1)`-curve statement
  below is not empty.
* `exceptionalInclusion`: the accepted centre fibre included into any surface `S'` identified with
  the glued blowup by `e : S'.toScheme ≅ scheme j q hclosed`; its kernel ideal sheaf is invertible
  (accepted `globalCenterFiberIdeal_isInvertible` transported by the accepted
  `SchemeKernelIdealIsoTransport`), and `exceptionalConormalIso` identifies its conormal sheaf with
  the conormal sheaf of the centre fibre on the glued blowup.
* `exceptional_conormal_euler_difference`: the conormal line of the exceptional fibre has degree one
  (0AGQ, transported from `P¹` by the accepted Euler transport along isomorphisms over `k`).
* `exists_minusOne_of_chart`, `exists_minusOne_of_literal`: the exceptional curve is a prime curve,
  isomorphic to `P¹_k` over `k`, with `E·E = −1` (the generic conormal reduction
  `KltDP.Geometry.PrimeCurveConormalDegree.selfIntersectionNumber_eq_neg_lineDegree`), contracted
  to the centre.
* `blowupExceptionalMinusOne_of_literal`: the E2 named hypothesis
  `BlowupExceptionalMinusOne` follows from 0AGQ, and `minimalResolution_unique'` restates the E2
  uniqueness theorem with 0AGQ in its place.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.BlowupExceptional

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.PrimeCurveConormalDegree KltDP.Literature.Stacks

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

section Package

variable [IsAlgClosed k] {R : Type u} [CommRing R] (S : NormalProjectiveSurface k)
    (j : Spec (CommRingCat.of R) ⟶ S.toScheme) [IsOpenImmersion j] (q : PrimeSpectrum R)
    [q.asIdeal.IsMaximal] (hclosed : IsClosed ({j.base q} : Set S.toScheme))

omit [IsAlgClosed k] in
/-- The glued point blowup of a projective surface is proper over the surface. -/
theorem projection_isProper : IsProper (PointBlowupGluing.projection j q hclosed) := by
  letI : IsLocallyNoetherian S.toScheme := S.isLocallyNoetherian
  exact PointBlowupGluing.projection_isProper_of_locallyNoetherian j q hclosed

/-- **The glued point blowup as a normal projective surface** (0AGR for regularity, 0C5P for
projectivity). -/
def blowupSurface (hR : BlowupChartRegularLiteral k) (hP : RegularProperProjectiveLiteral k)
    (hreg : ∀ x : S.Point, RegularPoint S.toScheme x) : NormalProjectiveSurface k where
  toScheme := PointBlowupGluing.scheme j q hclosed
  structureMorphism := PointBlowupGluing.projection j q hclosed ≫ S.structureMorphism
  integral := PointBlowupGluing.surface_scheme_isIntegral S j q hclosed
  normal := isNormalScheme_of_regularPoint (hR.regular S R j q hclosed hreg)
  projective := by
    haveI : IsProper (PointBlowupGluing.projection j q hclosed) := projection_isProper S j q hclosed
    haveI : IsProper S.structureMorphism := S.projective.isProper
    exact hP.projective (PointBlowupGluing.scheme j q hclosed)
      (PointBlowupGluing.projection j q hclosed ≫ S.structureMorphism) inferInstance
      (hR.regular S R j q hclosed hreg) (PointBlowupGluing.surface_scheme_dimension_two S j q hclosed)
  dimension_two := PointBlowupGluing.surface_scheme_dimension_two S j q hclosed

@[simp] theorem blowupSurface_toScheme (hR : BlowupChartRegularLiteral k)
    (hP : RegularProperProjectiveLiteral k) (hreg : ∀ x : S.Point, RegularPoint S.toScheme x) :
    (blowupSurface S j q hclosed hR hP hreg).toScheme = PointBlowupGluing.scheme j q hclosed := rfl

@[simp] theorem blowupSurface_structureMorphism (hR : BlowupChartRegularLiteral k)
    (hP : RegularProperProjectiveLiteral k) (hreg : ∀ x : S.Point, RegularPoint S.toScheme x) :
    (blowupSurface S j q hclosed hR hP hreg).structureMorphism =
      PointBlowupGluing.projection j q hclosed ≫ S.structureMorphism := rfl

/-- The accepted gluing data as a blowup chart at the centre. -/
def chart : PointBlowupChart S.toScheme (j.base q) where
  R := R
  instCommRing := inferInstance
  j := j
  instOpenImmersion := inferInstance
  q := q
  instMaximal := inferInstance
  isClosed := hclosed
  base_eq := rfl

/-- **Nonvacuity**: the glued blowup, as a surface, is a point blowup of `S` at `j.base q`. -/
theorem isPointBlowupAt_blowupSurface (hR : BlowupChartRegularLiteral k)
    (hP : RegularProperProjectiveLiteral k) (hreg : ∀ x : S.Point, RegularPoint S.toScheme x) :
    IsPointBlowupAt (blowupSurface S j q hclosed hR hP hreg) S
      (PointBlowupGluing.projection j q hclosed) (j.base q) where
  over_base := rfl
  blowup := ⟨chart S j q hclosed, Iso.refl _, by
    rw [Iso.refl_hom, Category.id_comp]
    rfl⟩

end Package

section Exceptional

variable [IsAlgClosed k] {R : Type u} [CommRing R] {S' : NormalProjectiveSurface k}
    (j : Spec (CommRingCat.of R) ⟶ S'.toScheme) [IsOpenImmersion j] (q : PrimeSpectrum R)
    [q.asIdeal.IsMaximal] (hclosed : IsClosed ({j.base q} : Set S'.toScheme))
    {S : NormalProjectiveSurface k} (e : S.toScheme ≅ PointBlowupGluing.scheme j q hclosed)

/-- The accepted centre fibre, included into a surface identified with the glued blowup. -/
def exceptionalInclusion : PointBlowupGluing.globalCenterFiber j q hclosed ⟶ S.toScheme :=
  PointBlowupGluing.globalCenterFiberι j q hclosed ≫ e.inv

instance exceptionalInclusion_isClosedImmersion :
    IsClosedImmersion (exceptionalInclusion j q hclosed e) := by
  unfold exceptionalInclusion
  infer_instance

omit [IsAlgClosed k] in
/-- Its kernel ideal sheaf is invertible (accepted `globalCenterFiberIdeal_isInvertible`,
transported along the identification). -/
theorem exceptionalInclusion_kernel_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := S.toScheme.ringCatSheaf)
      (schemeKernelIdeal (exceptionalInclusion j q hclosed e)) :=
  SchemeKernelIdealIsoTransport.isInvertible_schemeKernelIdeal_comp
    (PointBlowupGluing.globalCenterFiberι j q hclosed) e.symm
    (PointBlowupGluing.globalCenterFiberIdeal_isInvertible j q hclosed)

omit [IsAlgClosed k] in
theorem exceptionalInclusion_comp_hom :
    exceptionalInclusion j q hclosed e ≫ e.hom =
      PointBlowupGluing.globalCenterFiberι j q hclosed := by
  rw [exceptionalInclusion, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The conormal sheaf of the exceptional fibre in `S` is the conormal sheaf of the centre fibre on
the glued blowup. -/
def exceptionalConormalIso :
    schemeConormalSheaf (exceptionalInclusion j q hclosed e) ≅
      schemeConormalSheaf (PointBlowupGluing.globalCenterFiberι j q hclosed) := by
  refine (schemeModulePullback (exceptionalInclusion j q hclosed e)).mapIso
    (SchemeKernelIdealIsoTransport.schemeKernelIsoTransport
      (PointBlowupGluing.globalCenterFiberι j q hclosed) e.symm) ≪≫ ?_
  refine (schemeModulePullbackCompIso (exceptionalInclusion j q hclosed e) e.hom).app
    (schemeKernelIdeal (PointBlowupGluing.globalCenterFiberι j q hclosed)) ≪≫ ?_
  rw [exceptionalInclusion_comp_hom j q hclosed e]
  exact Iso.refl _

omit [IsAlgClosed k] in
/-- The `k`-structure of the exceptional fibre through `S` is the one through the glued blowup. -/
theorem exceptionalInclusion_structure
    (hstr : e.inv ≫ S.structureMorphism =
      PointBlowupGluing.projection j q hclosed ≫ S'.structureMorphism) :
    exceptionalInclusion j q hclosed e ≫ S.structureMorphism =
      PointBlowupGluing.globalCenterFiberι j q hclosed ≫
        PointBlowupGluing.projection j q hclosed ≫ S'.structureMorphism := by
  rw [exceptionalInclusion, Category.assoc, hstr]

/-- **The conormal line of the exceptional fibre has degree one** (Stacks 0AGQ). -/
theorem exceptional_conormal_euler_difference (hA : BlowupRegularPointLiteral k)
    (hreg' : ∀ y : S'.Point, RegularPoint S'.toScheme y)
    (hstr : e.inv ≫ S.structureMorphism =
      PointBlowupGluing.projection j q hclosed ≫ S'.structureMorphism) :
    eulerCharacteristic (exceptionalInclusion j q hclosed e ≫ S.structureMorphism)
        (conormalLine (exceptionalInclusion j q hclosed e)
          (exceptionalInclusion_kernel_isInvertible j q hclosed e)).obj -
      eulerCharacteristic (exceptionalInclusion j q hclosed e ≫ S.structureMorphism)
        (_root_.SheafOfModules.unit
          (PointBlowupGluing.globalCenterFiber j q hclosed).ringCatSheaf) = 1 := by
  obtain ⟨eF, hstructF, hdeg⟩ := hA.exceptional_projectiveLine S' R j q hclosed hreg'
  have hfg : eF.hom ≫ projectiveSpaceToSpec k 1 =
      exceptionalInclusion j q hclosed e ≫ S.structureMorphism := by
    rw [exceptionalInclusion_structure j q hclosed e hstr]
    exact hstructF
  rw [conormalLine_obj, eulerCharacteristic_eq_pullback_inv eF _ (projectiveSpaceToSpec k 1) hfg,
    eulerCharacteristic_unit_eq eF _ (projectiveSpaceToSpec k 1) hfg,
    eulerCharacteristic_eq_of_iso (projectiveSpaceToSpec k 1)
      ((schemeModulePullback eF.inv).mapIso (exceptionalConormalIso j q hclosed e))]
  exact hdeg

/-- **The exceptional curve of the blowup is a `(−1)`-curve contracted to the centre.** -/
theorem exists_minusOne_of_chart (hA : BlowupRegularPointLiteral k)
    (hreg' : ∀ y : S'.Point, RegularPoint S'.toScheme y)
    (hreg : ∀ y : S.Point, RegularPoint S.toScheme y)
    (hstr : e.inv ≫ S.structureMorphism =
      PointBlowupGluing.projection j q hclosed ≫ S'.structureMorphism) :
    ∃ E : S.PrimeCurve, IsMinusOneCurve hreg E ∧
      (e.hom ≫ PointBlowupGluing.projection j q hclosed).base ''
        (E : Set S.toScheme) = {j.base q} := by
  obtain ⟨eF, hstructF, -⟩ := hA.exceptional_projectiveLine S' R j q hclosed hreg'
  letI : IsIntegral (PointBlowupGluing.globalCenterFiber j q hclosed) :=
    PrimeCurveOfClosedImmersion.isIntegral_of_iso_projectiveLine eF
  have hfg : eF.hom ≫ projectiveSpaceToSpec k 1 =
      exceptionalInclusion j q hclosed e ≫ S.structureMorphism := by
    rw [exceptionalInclusion_structure j q hclosed e hstr]
    exact hstructF
  refine ⟨PrimeCurveOfClosedImmersion.primeCurveOfIsoProjectiveLine S
    (exceptionalInclusion j q hclosed e) eF, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · refine ⟨(asIso (PrimeCurveInclusionLift.lift
      (PrimeCurveOfClosedImmersion.primeCurveOfIsoProjectiveLine S
        (exceptionalInclusion j q hclosed e) eF) (exceptionalInclusion j q hclosed e) rfl)).symm
      ≪≫ eF, ?_⟩
    rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, hfg, ← Category.assoc,
      ← PrimeCurveInclusionLift.inclusion_eq_inv_lift]
    rfl
  · refine selfIntersectionNumber_eq_neg_one_of_lineDegree_eq_one hreg _
      (exceptionalInclusion j q hclosed e) rfl
      (exceptionalInclusion_kernel_isInvertible j q hclosed e) ?_
    rw [lineDegree_curveConormalLine_eq_euler_difference]
    exact exceptional_conormal_euler_difference j q hclosed e hA hreg' hstr
  · have hinvhom : ∀ w : PointBlowupGluing.scheme j q hclosed, e.hom.base (e.inv.base w) = w := by
      intro w
      change (e.inv ≫ e.hom).base w = w
      rw [e.inv_hom_id]
      rfl
    have hmaps : ∀ z : PointBlowupGluing.globalCenterFiber j q hclosed,
        (e.hom ≫ PointBlowupGluing.projection j q hclosed).base
          ((exceptionalInclusion j q hclosed e).base z) = j.base q := by
      intro z
      have hz : (PointBlowupGluing.projection j q hclosed).base
          ((PointBlowupGluing.globalCenterFiberι j q hclosed).base z) = j.base q := by
        have hmem : (PointBlowupGluing.globalCenterFiberι j q hclosed).base z ∈
            (PointBlowupGluing.projection j q hclosed).base ⁻¹' {j.base q} := by
          rw [← PointBlowupGluing.range_globalCenterFiberι]
          exact ⟨z, rfl⟩
        exact hmem
      change (PointBlowupGluing.projection j q hclosed).base
        (e.hom.base (e.inv.base
          ((PointBlowupGluing.globalCenterFiberι j q hclosed).base z))) = j.base q
      rw [hinvhom]
      exact hz
    rw [Set.eq_singleton_iff_unique_mem]
    constructor
    · obtain ⟨p⟩ := projectiveSpace_nonempty k 1
      exact ⟨(exceptionalInclusion j q hclosed e).base (eF.inv.base p),
        ⟨eF.inv.base p, rfl⟩, hmaps (eF.inv.base p)⟩
    · rintro y ⟨z, ⟨w, rfl⟩, rfl⟩
      exact hmaps w

end Exceptional

section Discharge

variable [IsAlgClosed k]

/-- **The exceptional curve of any point blowup of a regular surface is a `(−1)`-curve**, from
Stacks 0AGQ. -/
theorem exists_minusOne_of_literal (hA : BlowupRegularPointLiteral k)
    {S S' : NormalProjectiveSurface k} (b : S.toScheme ⟶ S'.toScheme) (x' : S'.Point)
    (hb : IsPointBlowupAt S S' b x') (hreg' : ∀ y : S'.Point, RegularPoint S'.toScheme y)
    (hreg : ∀ y : S.Point, RegularPoint S.toScheme y) :
    ∃ E : S.PrimeCurve, IsMinusOneCurve hreg E ∧ b.base '' (E : Set S.toScheme) = {x'} := by
  obtain ⟨c, e, hce⟩ := hb.blowup
  letI := c.instCommRing
  letI := c.instOpenImmersion
  letI := c.instMaximal
  have hproj : c.projection = PointBlowupGluing.projection c.j c.q c.isClosed := rfl
  have hstr : e.inv ≫ S.structureMorphism =
      PointBlowupGluing.projection c.j c.q c.isClosed ≫ S'.structureMorphism := by
    rw [← hproj, ← hb.over_base, ← hce, Category.assoc, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  obtain ⟨E, hminus, himg⟩ :=
    exists_minusOne_of_chart c.j c.q c.isClosed e hA hreg' hreg hstr
  refine ⟨E, hminus, ?_⟩
  rw [← hproj, hce, c.base_eq] at himg
  exact himg

/-- **The E2 named hypothesis `BlowupExceptionalMinusOne` is a consequence of Stacks 0AGQ.** -/
theorem blowupExceptionalMinusOne_of_literal (hA : BlowupRegularPointLiteral k) :
    BlowupExceptionalMinusOne k :=
  ⟨fun _ _ b x' hb hreg' hreg => exists_minusOne_of_literal hA b x' hb hreg' hreg⟩

/-- **Uniqueness of the minimal resolution without the named `(−1)`-curve hypothesis**: the E2
theorem `minimalResolution_unique` with Stacks 0AGQ in place of `BlowupExceptionalMinusOne`. The
remaining non-literature hypothesis is `MinimalResolutionDominationHypothesis` (no Stacks statement;
see `laneE/F10_LITERALS.md`). -/
theorem minimalResolution_unique' (hF : BirationalFactorizationLiteral k)
    (hR : BlowupRegularLiteral k) (hA : BlowupRegularPointLiteral k)
    (hDom : MinimalResolutionDominationHypothesis k)
    {S₁ S₂ X : NormalProjectiveSurface k} {π₁ : S₁.toScheme ⟶ X.toScheme}
    {π₂ : S₂.toScheme ⟶ X.toScheme} (h₁ : IsMinimalResolution S₁ X π₁)
    (h₂ : IsMinimalResolution S₂ X π₂) :
    ∃ e : S₂.toScheme ≅ S₁.toScheme, e.hom ≫ π₁ = π₂ :=
  minimalResolution_unique hF hR (blowupExceptionalMinusOne_of_literal hA) hDom h₁ h₂

end Discharge

end KltDP.Geometry.BlowupExceptional
