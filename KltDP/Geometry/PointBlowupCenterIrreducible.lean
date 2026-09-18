import KltDP.Geometry.Resolution
import KltDP.Geometry.LocalizedBlowupCenterFiber
import KltDP.Geometry.RegularLocalBlowupFiberIrreducible
import KltDP.Geometry.PointBlowupCenterFiber
import KltDP.Geometry.SurfaceRegularCharts
import KltDP.Geometry.RegularLocalEquiv

/-!
# Irreducibility of the actual point-blowup fiber at a regular surface point

The original local ring supplies the irreducible localized fiber. Its
proved full image gives the original affine fiber, and the original affine
blowup inclusion gives the whole glued fiber. The final theorem transports
this through the actual isomorphism in IsPointBlowupAt.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- The entire actual affine Rees point fiber is irreducible when the
original local ring of that point is regular of dimension two. -/
theorem affineBlowup_pointFiber_isIrreducible
    {R : Type u} [CommRing R] (m : PrimeSpectrum R)
    (hregular : RegularLocal (Localization.AtPrime m.asIdeal))
    (hdim : ringKrullDim (Localization.AtPrime m.asIdeal) = 2) :
    IsIrreducible ((AffineBlowup.toSpec m.asIdeal).base ⁻¹' {m}) := by
  let J := m.asIdeal.map (algebraMap R (Localization.AtPrime m.asIdeal))
  letI : IrreducibleSpace (AffineBlowup.centerFiber J) := by
    change IrreducibleSpace (AffineBlowup.centerFiber
      (m.asIdeal.map (algebraMap R (Localization.AtPrime m.asIdeal))))
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact RegularLocalBlowupFiber.centerFiber_irreducible _ hregular hdim
  have h := (IrreducibleSpace.isIrreducible_univ (AffineBlowup.centerFiber J)).image
    (LocalizedBlowupCenterFiber.toOriginal m).base
    (LocalizedBlowupCenterFiber.toOriginal m).continuous.continuousOn
  rw [← LocalizedBlowupCenterFiber.range_toOriginal m]
  simpa only [Set.image_univ] using h

namespace PointBlowupGluing

/-- The whole actual center fiber is irreducible from regularity and
dimension of the original target stalk, without a chosen curve model. -/
theorem pointFiber_isIrreducible
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X))
    (hregular : RegularPoint X (j.base q))
    (hdim : ringKrullDim (X.presheaf.stalk (j.base q)) = 2) :
    IsIrreducible ((projection j q hclosed).base ⁻¹' {j.base q}) := by
  let e := openImmersionStalkLocalizationEquiv j q
  have hreg := regularLocal_of_ringEquiv e hregular
  have hdim' : ringKrullDim (Localization.AtPrime q.asIdeal) = 2 :=
    (ringKrullDim_eq_of_ringEquiv e).symm.trans hdim
  have h := (affineBlowup_pointFiber_isIrreducible q hreg hdim').image
    (affineBlowupι j q hclosed).base (affineBlowupι j q hclosed).continuous.continuousOn
  have heq : (affineBlowupι j q hclosed).base ''
      ((AffineBlowup.toSpec q.asIdeal).base ⁻¹' {q}) =
        (projection j q hclosed).base ⁻¹' {j.base q} := by
    apply Set.Subset.antisymm
    · rintro x ⟨a, ha, rfl⟩
      change (projection j q hclosed).base ((affineBlowupι j q hclosed).base a) = j.base q
      have hmap := congrArg (fun f : AffineBlowup.scheme q.asIdeal ⟶ X => f.base a)
        (affineBlowupι_projection j q hclosed)
      exact hmap.trans (congrArg j.base ha)
    · intro x hx
      have hmem : x ∈ Set.range (affineBlowupι j q hclosed).base := by
        rw [range_affineBlowupι]
        change (projection j q hclosed).base x ∈ Set.range j.base
        exact ⟨q, hx.symm⟩
      obtain ⟨a, ha⟩ := hmem
      refine ⟨a, ?_, ha⟩
      apply j.isOpenEmbedding.injective
      have hmap := congrArg (fun f : AffineBlowup.scheme q.asIdeal ⟶ X => f.base a)
        (affineBlowupι_projection j q hclosed)
      exact hmap.symm.trans ((congrArg (projection j q hclosed).base ha).trans hx)
  exact heq ▸ h

end PointBlowupGluing

/-- The full point fiber of the original IsPointBlowupAt morphism is
irreducible at a regular dimension-two original target point. -/
theorem IsPointBlowupAt.pointFiber_isIrreducible
    {k : Type u} [Field k] {S T : NormalProjectiveSurface k}
    {b : S.toScheme ⟶ T.toScheme} {z : T.Point}
    (hb : IsPointBlowupAt S T b z) (hregular : RegularPoint T.toScheme z)
    (hdim : ringKrullDim (T.toScheme.presheaf.stalk z) = 2) :
    IsIrreducible (b.base ⁻¹' {z}) := by
  obtain ⟨c, e, he⟩ := hb.blowup
  letI : CommRing c.R := c.instCommRing
  letI : IsOpenImmersion c.j := c.instOpenImmersion
  letI : c.q.asIdeal.IsMaximal := c.instMaximal
  have hdim' := (congrArg (fun p : T.Point =>
    ringKrullDim (T.toScheme.presheaf.stalk p)) c.base_eq).trans hdim
  have h := PointBlowupGluing.pointFiber_isIrreducible c.j c.q c.isClosed
    (by simpa only [c.base_eq] using hregular) hdim'
  have hpre : b.base ⁻¹' {z} = e.hom.base ⁻¹'
      ((PointBlowupGluing.projection c.j c.q c.isClosed).base ⁻¹' {c.j.base c.q}) := by
    ext x
    change b.base x = z ↔
      (PointBlowupGluing.projection c.j c.q c.isClosed).base (e.hom.base x) = c.j.base c.q
    have hx := congrArg (fun f : S.toScheme ⟶ T.toScheme => f.base x) he
    change (PointBlowupGluing.projection c.j c.q c.isClosed).base
      (e.hom.base x) = b.base x at hx
    rw [hx, c.base_eq]
  rw [hpre]
  refine ⟨?_, h.2.preimage e.hom.isOpenEmbedding⟩
  obtain ⟨x, hx⟩ := h.1
  obtain ⟨y, rfl⟩ := e.hom.surjective x
  exact ⟨y, hx⟩

end KltDP.Geometry

#print axioms KltDP.Geometry.IsPointBlowupAt.pointFiber_isIrreducible
