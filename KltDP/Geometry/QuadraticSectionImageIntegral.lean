import KltDP.Geometry.QuadraticSectionImage
import KltDP.Geometry.InvertibleQuadraticSectionNonzero
import Mathlib.CategoryTheory.Sites.LocallyInjective

/-!
# The actual section image on an integral base

For an original nonzero square section on an integral scheme, the already
derived nonzero coefficients make evaluation injective on every nonempty
original affine refinement chart. The affine basis and separatedness of
the actual dual sheaf give injectivity on all opens, including empty ones.
Thus the original evaluation morphism is mono and its canonical image
factor is an isomorphism. Evaluating that actual inverse proves equality
between image-sheaf sections and component images without an assumed
section-lifting or image-preservation property.

The result identifies the genuine image ideal with the original branch
principal ideal on every existing affine chart and derives invertibility
of the original image ideal subsheaf. It retains the literal integral-base
and nonzero-global-section hypotheses. Identification with a prescribed
effective Cartier divisor and its reducedness remain separate geometry.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
  TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleQuadraticAtlas

open KltDP.SheafOfModules TransitionUnitGluing QuadraticCover

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]

local instance imageIntegralCommRing (W : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj W) :=
  inferInstanceAs (CommRing (X.presheaf.obj W))

local instance : ∀ W, IsMulCommutative (X.ringCatSheaf.val.obj W) :=
  fun _ => ⟨⟨fun a b => mul_comm a b⟩⟩

local instance imageIntegralMonoidal : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (N : X.Modules) (b : N.val.obj (op (⊤ : X.Opens)))

/-- Actual evaluation is injective on each nonempty original affine chart;
its coefficient is proved nonzero from the original global section. -/
theorem sectionEvaluationMorphism_chart_injective
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ N) (hb : b ≠ 0)
    (i : AffineOpenRefinement.Index X L.localTrivializations.X)
    [Nonempty (AffineOpenRefinement.opens X L.localTrivializations.X i)] :
    Function.Injective ((sectionEvaluationMorphism X N b).val.app
      (op (AffineOpenRefinement.opens X L.localTrivializations.X i))) := by
  intro φ ψ h
  apply (cancel_epi (squareRootSheafFrame X N L e i).inv).mp
  apply (dualUnitSectionsEquiv X.ringCatSheaf
    (AffineOpenRefinement.opens X L.localTrivializations.X i)).injective
  apply mul_right_cancel₀
    (M₀ := Γ(X, AffineOpenRefinement.opens X L.localTrivializations.X i))
    (fromSquareRoot_coefficient_ne_zero X L N e b hb i)
  exact (sectionEvaluationMorphism_app_squareRoot X N b L e i φ).symm.trans
    (h.trans (sectionEvaluationMorphism_app_squareRoot X N b L e i ψ))

/-- Original affine neighborhoods and the actual dual sheaf condition
prove injectivity on every open; empty opens need no nonempty assumption. -/
theorem sectionEvaluationMorphism_open_injective
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ N) (hb : b ≠ 0)
    (W : X.Opens) :
    Function.Injective ((sectionEvaluationMorphism X N b).val.app (op W)) := by
  intro φ ψ h
  apply TopCat.Presheaf.IsSheaf.section_ext
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj
      (dual X.ringCatSheaf N)).cond
  intro x hx
  have hxU : x ∈ ⨆ j, L.localTrivializations.X j := by
    rw [TransitionUnitExtraction.invertibleSheafUnits_cover X L]
    trivial
  obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hxU
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hsub⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open
      (show x ∈ W ⊓ L.localTrivializations.X j from ⟨hx, hxj⟩)
      (W ⊓ L.localTrivializations.X j).isOpen
  let i : AffineOpenRefinement.Index X L.localTrivializations.X :=
    ⟨j, ⟨V, hV, hsub.trans inf_le_right⟩⟩
  let hVW : V ≤ W := hsub.trans inf_le_left
  letI : Nonempty (AffineOpenRefinement.opens X L.localTrivializations.X i) :=
    ⟨⟨x, hxV⟩⟩
  refine ⟨V, hVW, hxV, ?_⟩
  apply sectionEvaluationMorphism_chart_injective X N b L e hb i
  change (sectionEvaluationMorphism X N b).val.app (op V)
      ((dual X.ringCatSheaf N).val.map (homOfLE hVW).op φ) =
    (sectionEvaluationMorphism X N b).val.app (op V)
      ((dual X.ringCatSheaf N).val.map (homOfLE hVW).op ψ)
  rw [_root_.PresheafOfModules.naturality_apply,
    _root_.PresheafOfModules.naturality_apply, h]

/-- The original global dual-evaluation morphism is a monomorphism. -/
theorem sectionEvaluationMorphism_mono
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ N) (hb : b ≠ 0) :
    Mono (sectionEvaluationMorphism X N b) := by
  have h : Mono ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map
      (sectionEvaluationMorphism X N b)) :=
    CategoryTheory.Sheaf.mono_of_injective _
      (fun W => sectionEvaluationMorphism_open_injective X N b L e hb W.unop)
  exact (_root_.SheafOfModules.toSheaf X.ringCatSheaf).mono_of_mono_map h

/-- The actual canonical image factor is an isomorphism, derived from
the original nonzero global section and the integral base. -/
def sectionDualImageIso
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ N) (hb : b ≠ 0) :
    dual X.ringCatSheaf N ≅ sectionImage X N b := by
  letI := sectionEvaluationMorphism_mono X N b L e hb
  exact asIso (Abelian.factorThruImage (sectionEvaluationMorphism X N b))

/-- The isomorphism retains the original evaluation map into O. -/
@[reassoc]
theorem sectionDualImageIso_hom_ι
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ N) (hb : b ≠ 0) :
    (sectionDualImageIso X N b L e hb).hom ≫ sectionImageι X N b =
      sectionEvaluationMorphism X N b :=
  sectionImage_factorization X N b

/-- The actual inverse image factor supplies the reverse section-image
inclusion on every original open. No local lifting is assumed. -/
theorem sectionImageIdeal_eq_componentRange_of_nonzero
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ N) (hb : b ≠ 0)
    (W : X.Opens) :
    sectionImageIdeal X N b W =
      LinearMap.range ((sectionEvaluationMorphism X N b).val.app (op W)).hom := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    let η := sectionDualImageIso X N b L e hb
    have hfac : η.inv ≫ sectionEvaluationMorphism X N b = sectionImageι X N b :=
      (congrArg (fun f : dual X.ringCatSheaf N ⟶
          _root_.SheafOfModules.unit X.ringCatSheaf => η.inv ≫ f)
        (sectionImage_factorization X N b).symm).trans
          (η.inv_hom_id_assoc (sectionImageι X N b))
    refine ⟨η.inv.val.app (op W) t, ?_⟩
    exact congrArg (fun f : sectionImage X N b ⟶
      _root_.SheafOfModules.unit X.ringCatSheaf => f.val.app (op W) t) hfac
  · exact sectionEvaluation_range_le_imageIdeal X N b W

/-- The genuine global image ideal has precisely the original branch
coefficient ideal on every existing affine refinement chart. -/
theorem sectionImageIdeal_eq_branchIdeal_of_nonzero
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ N) (hb : b ≠ 0)
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    sectionImageIdeal X N b (AffineOpenRefinement.opens X L.localTrivializations.X i) =
      branchIdeal ((fromSquareRoot X L N e b).sections i) := by
  rw [sectionImageIdeal_eq_componentRange_of_nonzero X N b L e hb,
    sectionEvaluationMorphism_range_eq_branchIdeal X N b L e i]

/-- The actual section-zero image ideal subsheaf is invertible, using the
original dual and its actual image isomorphism. -/
theorem sectionImageSubmodule_isInvertible_of_nonzero
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ N) (hb : b ≠ 0) :
    KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf)
      (sectionImageSubmodule X N b).toSheafOfModules := by
  letI := squareRoot_dual_isInvertible X N L e
  exact KltDP.SheafOfModules.IsInvertible.of_iso
    (R := X.ringCatSheaf)
    (M := dual X.ringCatSheaf N)
    (N := (sectionImageSubmodule X N b).toSheafOfModules)
    (sectionDualImageIso X N b L e hb ≪≫ sectionImageIsoSubmodule X N b)

end KltDP.Geometry.InvertibleQuadraticAtlas
