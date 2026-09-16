import KltDP.Geometry.InvertibleSheafFiniteAffineExtension
import KltDP.Geometry.InvertibleSheafAdvanceFrame
import KltDP.Geometry.InvertibleSheafAdvancePullback

/-!
# Further-power equality on original ambient overlaps

On a quasi-compact subopen of an actual affine frame, two original
ambient twisted sections which agree on the original nonvanishing open
agree after all sufficiently many further powers. The frame, coefficient,
chart module, and comparison with the original sections are constructed
from the original invertible sheaf. No overlap exponent is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafOriginalOverlapEquality

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance originalOverlapMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open InvertibleSheafSectionPowers InvertibleSheafSectionAdvance
open InvertibleSectionNonvanishingOpen InvertibleSheafFiniteAffineExtension
open InvertibleSheafOpenTwistSections InvertibleSheafAdvancePullback

variable {X : Scheme.{u}}

private theorem image_preimage_of_le (U : X.Opens) {W : X.Opens} (hWU : W ≤ U) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inter,
    Scheme.Opens.opensRange_ι, inf_eq_right.mpr hWU]

/-- Eventual equality of actual ambient twists on a compact original
subopen of one of the constructed affine charts. -/
theorem eventually_rightAdvance_eq_on_chart (L : InvertibleSheaf X) (M : X.Modules)
    [M.IsQuasicoherent] (s : L.obj.sections) (a : Chart L)
    {W : X.Opens} (hWa : W ≤ chartOpen L a) (hW : IsCompact (W : Set X)) (n : ℕ)
    (t v : (M ⊗ (power L n).obj).val.obj (op W))
    (heq : (M ⊗ (power L n).obj).val.map
        (homOfLE (show W ⊓ nonvanishingOpen X L s ≤ W from inf_le_left)).op t =
      (M ⊗ (power L n).obj).val.map
        (homOfLE (show W ⊓ nonvanishingOpen X L s ≤ W from inf_le_left)).op v) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (rightAdvance L s M n k).val.app (op W) t =
        (rightAdvance L s M n k).val.app (op W) v := by
  let U := chartOpen L a
  let f := U.ι
  let Y := U.toScheme
  let V := f ⁻¹ᵁ W
  let D := nonvanishingOpen X L s
  let b : Γ(Y, V) := Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
    (InvertibleSheafFiniteAffineExtension.chartCoefficient L s a)
  have hV : f ''ᵁ V = W := image_preimage_of_le U hWa
  have hB : Y.basicOpen b = f ⁻¹ᵁ (W ⊓ D) := by
    dsimp only [b]
    rw [Scheme.basicOpen_res, chartBasicOpen_eq]
    rfl
  have hBi : f ''ᵁ Y.basicOpen b = W ⊓ D :=
    (congrArg (fun V' : Y.Opens => f ''ᵁ V') hB).trans
      (image_preimage_of_le U (inf_le_left.trans hWa))
  have hVc : IsCompact (V : Set Y) := by
    apply f.isOpenEmbedding.isEmbedding.isCompact_iff.mpr
    change IsCompact (f ''ᵁ V : Set X)
    rw [hV]
    exact hW
  let eV := twistSectionsEquiv f M L n V W hV
  let eB := twistSectionsEquiv f M L n (Y.basicOpen b) (W ⊓ D) hBi
  let tY := eV.symm t
  let vY := eV.symm v
  have heqY : (chartModule L M a ⊗ (power (chartLine L a) n).obj).val.map
      (homOfLE (Y.basicOpen_le b)).op tY =
    (chartModule L M a ⊗ (power (chartLine L a) n).obj).val.map
      (homOfLE (Y.basicOpen_le b)).op vY := by
    apply eB.injective
    calc
      _ = (M ⊗ (power L n).obj).val.map (homOfLE inf_le_left).op (eV tY) :=
        twistSectionsEquiv_naturality f M L n hV hBi (Y.basicOpen_le b) inf_le_left tY
      _ = (M ⊗ (power L n).obj).val.map (homOfLE inf_le_left).op t := by
        rw [AddEquiv.apply_symm_apply]
      _ = (M ⊗ (power L n).obj).val.map (homOfLE inf_le_left).op v := heq
      _ = (M ⊗ (power L n).obj).val.map (homOfLE inf_le_left).op (eV vY) := by
        rw [AddEquiv.apply_symm_apply]
      _ = _ := (twistSectionsEquiv_naturality f M L n hV hBi
        (Y.basicOpen_le b) inf_le_left vY).symm
  letI : (chartModule L M a).IsQuasicoherent :=
    _root_.SheafOfModules.isQuasicoherent_of_isIso
      (R := Y.ringCatSheaf)
      (M := (SchemeModuleRestriction.restriction f).obj M)
      (N := chartModule L M a)
      ((SchemeModuleRestriction.restrictionIsoPullback f).hom.app M)
  obtain ⟨K, hK⟩ := InvertibleSheafAdvanceFrame.eventually_rightAdvance_eq_of_restrict_eq
    (chartLine L a) (chartFrame L a) (chartSection L s a) (chartModule L M a)
    hVc n tY vY heqY
  refine ⟨K, fun k hk => ?_⟩
  have ht := twistSectionsEquiv_rightAdvance f L s M n k V W hV tY
  have hv := twistSectionsEquiv_rightAdvance f L s M n k V W hV vY
  have he := congrArg (twistSectionsEquiv f M L (n + k) V W hV) (hK k hk)
  have h := ht.symm.trans (he.trans hv)
  simpa only [tY, vY, eV, AddEquiv.apply_symm_apply] using h

end KltDP.Geometry.InvertibleSheafOriginalOverlapEquality
