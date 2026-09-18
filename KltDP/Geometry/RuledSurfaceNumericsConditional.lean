import KltDP.Geometry.HartshorneRuledConditional
import KltDP.Geometry.RuledNumericalBasis
import KltDP.Geometry.RuledSurfaceSourceGeometry
import KltDP.Geometry.CurveCanonicalRational

/-!
# Original ruled-surface numerical invariants, conditionally on the full sources

The complete reviewed V.2.3 and V.2.5 statements remain explicit parameters.
The actual section and an actual closed scheme fibre provide the original
prime curves. Their original over-field isomorphisms give the two genera,
and arithmetic adjunction with the integral numerical quotient gives the
canonical square and Picard rank on this same surface.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u

namespace KltDP.Geometry.RuledSurfaceNumericsConditional

variable (hPicard :
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
    (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
    (hCdim : topologicalKrullDim C = 1)
    (hCreg : ∀ y : C, RegularPoint C y)
    (π : X.toScheme ⟶ C)
    (hbase : π ≫ c = X.structureMorphism)
    (hsurj : Function.Surjective π.base)
    (hfib : ∀ y : C, IsClosed ({y} : Set C) →
      ∃ e : π.fiber y ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 =
          π.fiberι y ≫ X.structureMorphism)
    (σ : C ⟶ X.toScheme) (hσ : σ ≫ π = 𝟙 C)
    (S₀ : X.PrimeCurve) (e₀ : S₀.toScheme ≅ C)
    (he₀ : e₀.inv ≫ S₀.inclusion = σ)
    (y : C) (hy : IsClosed ({y} : Set C))
    (F : X.PrimeCurve) (eF : F.toScheme ≅ π.fiber y)
    (heF : eF.hom ≫ π.fiberι y = F.inclusion),
    let DS := X.primeCurveCartier hX S₀
    let DF := X.primeCurveCartier hX F
    let PS := cartierPicardHom X.toScheme DS
    let PF := cartierPicardHom X.toScheme DF
    ∃ ePic : (ℤ × Additive C.Pic) ≃+ Additive X.toScheme.Pic,
      ∃ eNum : (ℤ × ℤ) ≃+ X.IntegralNumericalClassGroup,
        (∀ (n : ℤ) (L : Additive C.Pic),
          ePic (n, L) = n • PS + (schemePicardPullbackHom π).toAdditive L) ∧
        (∀ n m : ℤ,
          eNum (n, m) =
            n • X.picardIntegralNumericalMap PS +
            m • X.picardIntegralNumericalMap PF) ∧
        X.intersectionPairing hX DS DF = 1 ∧
        X.intersectionPairing hX DF DF = 0
)

variable (hGenus :
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
    (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
    (hCdim : topologicalKrullDim C = 1)
    (hCreg : ∀ y : C, RegularPoint C y)
    (π : X.toScheme ⟶ C)
    (hbase : π ≫ c = X.structureMorphism)
    (hsurj : Function.Surjective π.base)
    (hfib : ∀ y : C, IsClosed ({y} : Set C) →
      ∃ e : π.fiber y ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 =
          π.fiberι y ≫ X.structureMorphism)
    (σ : C ⟶ X.toScheme) (hσ : σ ≫ π = 𝟙 C),
    (eulerCharacteristic X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) - 1 =
      -(CurveCanonical.genus c : ℤ)) ∧
    (cohomologyDimension X.structureMorphism
        (relativeDifferentialExterior X.structureMorphism 2) 0 = 0) ∧
    (cohomologyDimension X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 1 =
      CurveCanonical.genus c)
)

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k))
  [IsIntegral C] [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
  (hCdim : topologicalKrullDim C = 1)
  (hCreg : ∀ y : C, RegularPoint C y)
  (π : X.toScheme ⟶ C)
  (hbase : π ≫ c = X.structureMorphism)
  (hsurj : Function.Surjective π.base)
  (hfib : ∀ y : C, IsClosed ({y} : Set C) →
    ∃ e : π.fiber y ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 =
        π.fiberι y ≫ X.structureMorphism)
  (σ : C ⟶ X.toScheme) (hσ : σ ≫ π = 𝟙 C)

include hPicard hGenus hCdim hCreg hbase hsurj hfib hσ in
/-- The same original ruled surface has rank two and its canonical square
and Noether sum expressed using its actual scalar H1 dimension. -/
theorem invariants
    (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2) :
    X.picardRank = 2 ∧
      X.intersectionPairing hX K K =
        8 * (1 - (cohomologyDimension X.structureMorphism
          (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 1 : ℤ)) ∧
      X.intersectionPairing hX K K + (X.picardRank : ℤ) =
        10 - 8 * (cohomologyDimension X.structureMorphism
          (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 1 : ℤ) := by
  obtain ⟨S₀, e₀, he₀, he₀base, _⟩ :=
    RuledSurfaceSourceGeometry.exists_sectionPrimeCurve X c π hbase hCdim σ hσ
  letI : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  obtain ⟨y, _, hy⟩ := nonempty_inter_closedPoints
    (show (Set.univ : Set C).Nonempty from ⟨genericPoint C, Set.mem_univ _⟩)
    isOpen_univ.isLocallyClosed
  obtain ⟨e, he⟩ := hfib y hy
  obtain ⟨F, eF, heF, heFbase, _⟩ :=
    RuledSurfaceSourceGeometry.exists_fiberPrimeCurve X π y hy e he
  obtain ⟨ePic, eNum, hePic, heNum, hSF, hFF⟩ :=
    HartshorneRuledConditional.decomposition_at hPicard X hX C c hCdim hCreg
      π hbase hsurj hfib σ hσ S₀ e₀ he₀ y hy F eF heF
  have hSgenus : CurveCanonical.genus S₀.toSpec = CurveCanonical.genus c :=
    CurveCanonical.genus_eq_of_schemeIso e₀ S₀.toSpec c he₀base
  have hFgenus : CurveCanonical.genus F.toSpec = 0 :=
    CurveCanonical.genus_eq_zero_of_projectiveLineIso F.toSpec (eF ≪≫ e) heFbase
  have hnum := X.ruled_invariants_of_integralNumericalBasis hX
    S₀ F eNum heNum hSF hFF K eK hFgenus
  have hcoh := (HartshorneRuledConditional.genera_at hGenus X hX C c
    hCdim hCreg π hbase hsurj hfib σ hσ).2.2
  rw [hSgenus, ← hcoh] at hnum
  exact hnum

end KltDP.Geometry.RuledSurfaceNumericsConditional

#check @KltDP.Geometry.RuledSurfaceNumericsConditional.invariants
#print axioms KltDP.Geometry.RuledSurfaceNumericsConditional.invariants
