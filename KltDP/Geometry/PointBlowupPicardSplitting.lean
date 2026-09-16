import KltDP.Geometry.ExceptionalKernelInfiniteOrder
import KltDP.Geometry.BlowupExceptionalCurve
import KltDP.Geometry.PointBlowupPicardDecomposition

/-!
# `Pic T ≃ Pic S × ℤ` for the glued point blowup of a regular surface

BRIEF33, task 1 (F09, the Picard formula for a point blowup). This is the composition recorded at the
end of BRIEF32: everything below is assembled from accepted results, lane E's queued
`Geometry/BlowupExceptionalCurve` (copied byte-identically), and lane A1's own BRIEF29/31/32 modules.
No new mathematics.

Let `S` be a regular normal projective surface over an algebraically closed field, `x = j.base q` a
closed point of an affine chart, and `T = PointBlowupGluing.scheme j q hclosed` the accepted glued
blowup. Lane E's `blowupSurface` packages `T` as a `NormalProjectiveSurface` (regular by Stacks 0AGR,
projective by 0C5P) and its `exists_minusOne_of_chart` produces the exceptional `(−1)`-curve from
Stacks 0AGQ.

* `exceptionalCurve`: the centre fibre as a prime curve of the blowup surface, built from the `P¹`
  identification supplied by 0AGQ. Its underlying set is `Set.range (globalCenterFiberι).base`, which
  the accepted `range_globalCenterFiberι` identifies with `σ⁻¹{x}`; hence
  **`complementOpen_exceptionalCurve : complementOpen (exceptionalCurve …) = exceptionalComplementOpen j q hclosed`**,
  the compatibility that lets BRIEF32's kernel computation be read off the accepted
  `PointBlowupPicard.restrictComplement`.
* `exceptionalCurve_eq` (inside the main proof): lane E's `(−1)`-curve **is** that curve — it is
  contained in `σ⁻¹{x}` because it is contracted to `x`, and two prime curves one of which contains
  the generic point of the other coincide (BRIEF32's `eq_of_genericPoint_mem`). This transports
  `E · E = −1` to `exceptionalCurve`.
* **`picardDecomposition'' : Nonempty (Pic T ≃* Pic S × Multiplicative ℤ)`** — BRIEF29's `splitEquiv`
  (via BRIEF32's `picardEquivProdInt`) with `s := pullbackHom`, `ρ := retraction`,
  `hρ := retraction_pullback`, `hres` discharged by BRIEF31's `restrictPuncture_bijective`, and `hker`
  the accepted `ker_retraction` transported along `complementOpen_exceptionalCurve`.

The statement is `Nonempty (… ≃* …)` because the exceptional curve is produced by an existential
(Stacks 0AGQ supplies the `P¹` identification only up to choice); the equivalence itself is
constructed, not assumed. The only hypotheses beyond regularity of `S` are lane E's three literals,
named explicitly in the statement: `BlowupChartRegularLiteral` (0AGR),
`RegularProperProjectiveLiteral` (0C5P) and `BlowupRegularPointLiteral` (0AGQ).

Also here: `infiniteOrder_of_degreeHom`, the degree-homomorphism form of BRIEF32's infinite-order
criterion, for use by instantiations whose `(−1)` datum is a pairing rather than an
`intersectionNumber`.

The splitting itself is BRIEF32's `picardEquivProdInt`, whose `H` was corrected in BRIEF34 to live in
its own universe (a Picard group is in `Type (u+1)`, so the original `{H : Type u}` could never be
instantiated at one).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupSplitting

open KltDP.Geometry.PrimeCurveComplementKernel KltDP.Geometry.NormalProjectiveSurface
open KltDP.Literature.Stacks

/-! ## Infinite order from an arbitrary integral pairing -/

/-- If some additive map `Pic X → ℤ` takes the value `-1` on `c`, then `c` has infinite order. This is
BRIEF32's criterion with the accepted `picardRestrictionDegreeHom` replaced by an arbitrary pairing. -/
theorem infiniteOrder_of_degreeHom {k : Type u} [Field k] {X : NormalProjectiveSurface k}
    (φ : Additive X.toScheme.Pic →+ ℤ) (c : X.toScheme.Pic) (hc : φ (Additive.ofMul c) = -1) :
    InfiniteOrder c := by
  intro n hn
  have h1 : φ (Additive.ofMul (c ^ n)) = n • φ (Additive.ofMul c) := by
    rw [ofMul_zpow, map_zsmul]
  rw [hn, show Additive.ofMul (1 : X.toScheme.Pic) = 0 from rfl, map_zero, hc] at h1
  simp only [zsmul_eq_mul, smul_eq_mul, mul_neg_one, mul_one] at h1
  omega

/-! ## The exceptional curve of the glued blowup -/

section Blowup

variable {k : Type u} [Field k] [IsAlgClosed k] {R : Type u} [CommRing R]
  (S : NormalProjectiveSurface k) (j : Spec (CommRingCat.of R) ⟶ S.toScheme) [IsOpenImmersion j]
  (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
  (hclosed : IsClosed ({j.base q} : Set S.toScheme))
  (hR : BlowupChartRegularLiteral k) (hP : RegularProperProjectiveLiteral k)
  (hreg : ∀ x : S.Point, RegularPoint S.toScheme x)

/-- The blowup, as a normal projective surface (lane E). -/
abbrev blowupSurf : NormalProjectiveSurface k :=
  BlowupExceptional.blowupSurface S j q hclosed hR hP hreg

/-- The blowup surface is regular (Stacks 0AGR). -/
theorem blowupSurf_regular :
    ∀ y : (blowupSurf S j q hclosed hR hP hreg).Point,
      RegularPoint (blowupSurf S j q hclosed hR hP hreg).toScheme y :=
  hR.regular S R j q hclosed hreg

/-- **The exceptional curve as a prime curve of the blowup surface**, from the `P¹` identification of
Stacks 0AGQ. Its underlying set is the range of the accepted centre-fibre immersion. -/
def exceptionalCurve
    (eF : PointBlowupGluing.globalCenterFiber j q hclosed ≅ projectiveSpace k 1) :
    (blowupSurf S j q hclosed hR hP hreg).PrimeCurve :=
  PrimeCurveOfClosedImmersion.primeCurveOfIsoProjectiveLine
    (blowupSurf S j q hclosed hR hP hreg)
    (PointBlowupGluing.globalCenterFiberι j q hclosed) eF

/-- Its underlying set is the fibre over the centre (accepted `range_globalCenterFiberι`). -/
theorem coe_exceptionalCurve
    (eF : PointBlowupGluing.globalCenterFiber j q hclosed ≅ projectiveSpace k 1) :
    ((exceptionalCurve S j q hclosed hR hP hreg eF :
        (blowupSurf S j q hclosed hR hP hreg).PrimeCurve) :
        Set (blowupSurf S j q hclosed hR hP hreg).toScheme) =
      (PointBlowupGluing.projection j q hclosed).base ⁻¹' {j.base q} :=
  PointBlowupGluing.range_globalCenterFiberι j q hclosed

/-- **The complement of the exceptional curve is the accepted `exceptionalComplementOpen`.** -/
theorem complementOpen_exceptionalCurve
    (eF : PointBlowupGluing.globalCenterFiber j q hclosed ≅ projectiveSpace k 1) :
    complementOpen (exceptionalCurve S j q hclosed hR hP hreg eF) =
      PointBlowupGluing.exceptionalComplementOpen j q hclosed := by
  apply TopologicalSpace.Opens.ext
  show ((exceptionalCurve S j q hclosed hR hP hreg eF :
      (blowupSurf S j q hclosed hR hP hreg).PrimeCurve) :
      Set (blowupSurf S j q hclosed hR hP hreg).toScheme)ᶜ = _
  rw [coe_exceptionalCurve S j q hclosed hR hP hreg eF]
  rfl

end Blowup

/-! ## The splitting -/

section Splitting

variable {k : Type u} [Field k] [IsAlgClosed k] {R : Type u} [CommRing R]
  (S : NormalProjectiveSurface k) (j : Spec (CommRingCat.of R) ⟶ S.toScheme) [IsOpenImmersion j]
  (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
  (hclosed : IsClosed ({j.base q} : Set S.toScheme))

set_option maxHeartbeats 1000000 in
/-- **`Pic T ≃* Pic S × ℤ` for the accepted glued point blowup of a regular surface at a closed
point**, conditional only on the three Stacks literals of lane E, named explicitly. -/
theorem picardDecomposition'' (hR : BlowupChartRegularLiteral k)
    (hP : RegularProperProjectiveLiteral k) (hA : BlowupRegularPointLiteral k)
    (hreg : ∀ x : S.Point, RegularPoint S.toScheme x) :
    Nonempty ((PointBlowupGluing.scheme j q hclosed).Pic ≃*
      S.toScheme.Pic × Multiplicative ℤ) := by
  haveI := S.stalks_uniqueFactorizationMonoid_of_regular hreg
  have hregT := blowupSurf_regular S j q hclosed hR hP hreg
  haveI := (blowupSurf S j q hclosed hR hP hreg).stalks_uniqueFactorizationMonoid_of_regular hregT
  obtain ⟨eF, hstrF, hdegF⟩ := hA.exceptional_projectiveLine S R j q hclosed hreg
  let E₀ : (blowupSurf S j q hclosed hR hP hreg).PrimeCurve :=
    exceptionalCurve S j q hclosed hR hP hreg eF
  have hE₀coe : ((E₀ : (blowupSurf S j q hclosed hR hP hreg).PrimeCurve) :
      Set (blowupSurf S j q hclosed hR hP hreg).toScheme) =
      (PointBlowupGluing.projection j q hclosed).base ⁻¹' {j.base q} :=
    coe_exceptionalCurve S j q hclosed hR hP hreg eF
  have hcompl : complementOpen E₀ =
      PointBlowupGluing.exceptionalComplementOpen j q hclosed :=
    complementOpen_exceptionalCurve S j q hclosed hR hP hreg eF
  have hstr : (Iso.refl (PointBlowupGluing.scheme j q hclosed)).inv ≫
      (blowupSurf S j q hclosed hR hP hreg).structureMorphism =
      PointBlowupGluing.projection j q hclosed ≫ S.structureMorphism := by
    rw [Iso.refl_inv, Category.id_comp]
    exact BlowupExceptional.blowupSurface_structureMorphism S j q hclosed hR hP hreg
  obtain ⟨E, hminus, himg⟩ :=
    BlowupExceptional.exists_minusOne_of_chart j q hclosed
      (Iso.refl (PointBlowupGluing.scheme j q hclosed)) hA hreg hregT hstr
  have hsub : (E : Set (blowupSurf S j q hclosed hR hP hreg).toScheme) ⊆
      ((E₀ : (blowupSurf S j q hclosed hR hP hreg).PrimeCurve) :
        Set (blowupSurf S j q hclosed hR hP hreg).toScheme) := by
    rw [hE₀coe]
    intro y hy
    have hmem : ((Iso.refl (PointBlowupGluing.scheme j q hclosed)).hom ≫
        PointBlowupGluing.projection j q hclosed).base y ∈
        ({j.base q} : Set S.toScheme) := by
      rw [← himg]
      exact ⟨y, hy, rfl⟩
    simpa using hmem
  have hEE₀ : E = E₀ := eq_of_genericPoint_mem E E₀ (hsub E.genericPoint_mem)
  have hself' : E₀.intersectionNumber
      ((blowupSurf S j q hclosed hR hP hreg).cartierWeilEquiv.symm
        (Finsupp.single E₀ 1)) = -1 := by
    have h := hminus.selfIntersection
    rw [hEE₀] at h
    exact h
  have hinf : InfiniteOrder (primeCurveClass E₀) :=
    infiniteOrder_of_intersectionNumber_neg_one E₀ hself'
  have hV : ∀ C : (blowupSurf S j q hclosed hR hP hreg).PrimeCurve,
      C.genericPoint ∈ complementOpen E₀ ↔ C ≠ E₀ :=
    genericPoint_mem_complementOpen_iff E₀
  have hres := CartierExtension.restrictPuncture_bijective j q hclosed
  have hker : (PointBlowupPicard.retraction j q hclosed hres).ker =
      (schemePicardPullbackHom (complementOpen E₀).ι).ker := by
    rw [PointBlowupPicard.ker_retraction]
    show (schemePicardPullbackHom
      (PointBlowupGluing.exceptionalComplementOpen j q hclosed).ι).ker = _
    rw [hcompl]
  -- state the goal on the blowup *surface*, whose `toScheme` is the glued blowup by `rfl`
  show Nonempty ((blowupSurf S j q hclosed hR hP hreg).toScheme.Pic ≃*
    S.toScheme.Pic × Multiplicative ℤ)
  exact ⟨picardEquivProdInt E₀ hV hinf (PointBlowupPicard.pullbackHom j q hclosed)
    (PointBlowupPicard.retraction j q hclosed hres)
    (PointBlowupPicard.retraction_pullback j q hclosed hres) hker⟩

end Splitting

end KltDP.Geometry.PointBlowupSplitting
