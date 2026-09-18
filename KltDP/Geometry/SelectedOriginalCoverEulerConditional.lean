import KltDP.Geometry.OriginalQuadraticCoverEulerConditional
import KltDP.Geometry.OriginalEvenSelectionFourDivisibility
import KltDP.Geometry.OriginalCartierQuadraticIntegral
import KltDP.Geometry.SchemeKernelIdealIsoTransport
import KltDP.Geometry.AmpleSerreDegreeBound

/-!
# The actual selected-branch cover has Euler value 2 chi minus one quarter the count

The original square-root isomorphism supplies the integral Picard
equality. Rational adjunction supplies the canonical degrees. The
already constructed same-cover splitting and original-surface RR then
give the manuscript's numerical cover formula for the original branch.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.InvertibleSheafTensor

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (hAffine : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsAffineHom f] (n : ℕ),
    ∃ e : ∀ (M : X.Modules), M.IsQuasicoherent →
      H ((schemeModulePushforward f).obj M) n ≃+ H M n,
      ∀ (M N : X.Modules) (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
        (φ : M ⟶ N) (x : H ((schemeModulePushforward f).obj M) n),
        e N hN ((zariskiFunctor Y n).map ((schemeModulePushforward f).map φ) x) =
          (zariskiFunctor X n).map φ (e M hM x))

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
  [IsSmoothOfRelativeDimension 2 S.structureMorphism]

local instance selectedEulerSmooth : IsSmooth S.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism

local instance selectedEulerSeparated : S.toScheme.IsSeparated := surfaceSeparated S

local instance selectedEulerMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

include hAffine

/-- The literal original Cartier cover of the selected rational minus-two
curves has the precise count correction, without supplied Picard or degree equations. -/
theorem selected_original_cover_euler
    (N : Finset S.PrimeCurve) (E : CartierDivisor S.toScheme)
    (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E)
    (hweil : S.cartierToWeilHom E = S.selectedPrimeWeil N)
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hP1 : ∀ C ∈ N, ∃ η : C.toScheme ≅ projectiveSpace k 1,
      η.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec)
    (hself : ∀ C ∈ N, C.selfIntersectionNumber S.regularPoints_of_isSmooth = -2) :
    let A := effectiveCartierQuadraticAtlas S.toScheme E hE L e
    (eulerCharacteristic (A.morphism ≫ S.structureMorphism)
        (_root_.SheafOfModules.unit A.scheme.ringCatSheaf) : ℚ) =
      2 * (eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) : ℚ) - (N.card : ℚ) / 4 := by
  let D := S.picardRepresentative L.toPic
  have hD : cartierPicardClass S.toScheme D = L.toPic :=
    S.cartierPicardClass_picardRepresentative L.toPic
  have heven : cartierPicardClass S.toScheme E =
      cartierPicardClass S.toScheme (D + D) := by
    have h := SchemeKernelIdealIsoTransport.toPic_eq_of_iso
      (tensorInvertibleSheaf L L) (cartierDivisorInvertibleSheaf S.toScheme E) e
    rw [AmpleSerreDegreeBound.tensorInvertibleSheaf_toPic] at h
    change L.toPic * L.toPic = cartierPicardClass S.toScheme E at h
    rw [cartierPicardClass_add, hD]
    exact h.symm
  let K := SmoothCanonicalCartierRepresentative.cartierRepresentative S.structureMorphism
  let eK : cartierDivisorModule S.toScheme K ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2 :=
    SmoothCanonicalCartierExterior.representativeIsoExterior S.structureMorphism
  have hK : ∀ C ∈ N, C.intersectionNumber K = 0 := by
    intro C hC
    obtain ⟨η, hη⟩ := hP1 C hC
    have h := CompatibleRationalAdjunctionDegree.canonical_intersection_eq S
      S.regularPoints_of_isSmooth K eK C η hη
    rw [hself C hC] at h
    omega
  have hcount := S.even_disjoint_selection_euler_difference S.regularPoints_of_isSmooth
    N E D K hweil heven hdisj hself hK eK
  have hsplit := original_squareRoot_euler_split hAffine S L
    (cartierDivisorModule S.toScheme E) e (effectiveCartierSection S.toScheme E hE)
  rw [S.dual_euler_eq_inverseCartier L D hD] at hsplit
  have hcountQ := congrArg (fun z : ℤ => (z : ℚ)) hcount
  have hsplitQ := congrArg (fun z : ℤ => (z : ℚ)) hsplit
  push_cast at hcountQ hsplitQ
  dsimp only [effectiveCartierQuadraticAtlas]
  linarith only [hcountQ, hsplitQ]

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.selected_original_cover_euler
#print axioms KltDP.Geometry.NormalProjectiveSurface.selected_original_cover_euler
