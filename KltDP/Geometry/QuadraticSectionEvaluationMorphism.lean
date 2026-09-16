import KltDP.Geometry.QuadraticSectionEvaluationIdeal
import KltDP.Compatibility.SheafEvaluationTrivialization

/-!
# Evaluation of the original square section by the genuine dual sheaf

The existing `KltDP.SheafOfModules.dual` has actual local module-sheaf
functionals as its sections, with proved restriction maps and sheaf condition.
The existing `evalSection` is defined using the original section/unit-section
correspondences and is natural under those restrictions. Fixing the actual
global section therefore gives a genuine morphism from this dual sheaf to O.

The original square-root isomorphism and original matching-coordinate chart
isomorphisms produce a sheaf frame on each existing affine chart. Evaluation
in that frame is exactly the original quadratic coefficient. Thus the range
of the actual sheaf morphism component equals the previously defined local
module-dual evaluation ideal and the literal principal branch ideal.

No global image-sheaf coherence, Cartier-divisor identification, reducedness,
nonzero section, integral base or characteristic hypothesis is assumed.
The original separatedness assumption is retained only for the existing
quadratic atlas. This does not construct its global branch closed subscheme.

Reuse: the actual dual/evaluation and frame factorization already exist in
the project's reviewed AINTLIB adapters (Apache-2.0). Pinned and newer official
Mathlib sheaf/module APIs were checked; no new dual or tensor port is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.Geometry

open KltDP.SheafOfModules

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u})

local instance evaluationMorphismCommRing (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

local instance : ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun _ => ⟨⟨fun a b => mul_comm a b⟩⟩

variable (N : X.Modules) (b : N.val.obj (op (⊤ : X.Opens)))

private theorem restrictedSection_comp {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    N.val.map f (N.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op b) =
      N.val.map (homOfLE (le_top : V.unop ≤ ⊤)).op b := by
  calc
    _ = N.val.map ((homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f) b :=
      (CategoryTheory.congr_fun
        (N.val.presheaf.map_comp (homOfLE (le_top : U.unop ≤ ⊤)).op f) b).symm
    _ = _ := congrArg (fun g : op (⊤ : X.Opens) ⟶ V => N.val.map g b)
      (Subsingleton.elim
        ((homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f)
        (homOfLE (le_top : V.unop ≤ ⊤)).op)

/-- Evaluate genuine local sheaf functionals on the actual restrictions
of the original global section. Naturality is proved, not supplied. -/
def sectionEvaluationMorphism :
    dual X.ringCatSheaf N ⟶ _root_.SheafOfModules.unit X.ringCatSheaf where
  val :=
    { app := fun U => by
        letI : Module (X.ringCatSheaf.val.obj U)
            ((dualPresheafAb X.ringCatSheaf N).obj U) :=
          dualSectionsModule X.ringCatSheaf N U.unop
        exact ModuleCat.ofHom
          { toFun := fun φ => evalSection X.ringCatSheaf N U.unop φ
              (N.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op b)
            map_add' := fun φ ψ => evalSection_add_left X.ringCatSheaf N U.unop φ ψ _
            map_smul' := fun r φ => evalSection_smul_left X.ringCatSheaf N U.unop φ r _ }
      naturality := fun {U V} f => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        change evalSection X.ringCatSheaf N V.unop
            (dualRestrict X.ringCatSheaf N f φ)
            (N.val.map (homOfLE (le_top : V.unop ≤ ⊤)).op b) =
          X.ringCatSheaf.val.map f
            (evalSection X.ringCatSheaf N U.unop φ
              (N.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op b))
        rw [← restrictedSection_comp X N b f]
        exact evalSection_naturality X.ringCatSheaf N f φ _ }

/-- The component of the constructed morphism uses the original local
functional and the original restriction of b. -/
@[simp]
theorem sectionEvaluationMorphism_app (W : X.Opens)
    (φ : (dual X.ringCatSheaf N).val.obj (op W)) :
    (sectionEvaluationMorphism X N b).val.app (op W) φ =
      evalSection X.ringCatSheaf N W φ
        (N.val.map (homOfLE (le_top : W ≤ ⊤)).op b) := rfl

/-- An actual sheaf frame computes the actual component image ideal. -/
theorem sectionEvaluationMorphism_range_eq_span (W : X.Opens)
    (ψ : N.over W ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over W)) :
    LinearMap.range ((sectionEvaluationMorphism X N b).val.app (op W)).hom =
      Ideal.span ({evalSection X.ringCatSheaf N W ψ.hom
        (N.val.map (homOfLE (le_top : W ≤ ⊤)).op b)} : Set Γ(X, W)) := by
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩
    apply (Ideal.mem_span_singleton (α := Γ(X, W))).mpr
    refine ⟨dualUnitSectionsEquiv X.ringCatSheaf W (ψ.inv ≫ φ), ?_⟩
    change evalSection X.ringCatSheaf N W φ _ = _
    exact (evalSection_factor X.ringCatSheaf N W ψ φ _).trans (mul_comm _ _)
  · apply Ideal.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨ψ.hom, rfl⟩

namespace InvertibleQuadraticAtlas

open TransitionUnitGluing TransitionUnitExtraction QuadraticCover

local instance evaluationMorphismMonoidal : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ N)

/-- The original square-root and matching-coordinate sheaf isomorphisms
give a genuine frame on each original affine refinement chart. -/
def squareRootSheafFrame
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    N.over (AffineOpenRefinement.opens X L.localTrivializations.X i) ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over
        (AffineOpenRefinement.opens X L.localTrivializations.X i)) :=
  (_root_.SheafOfModules.overFunctor X.ringCatSheaf
      (AffineOpenRefinement.opens X L.localTrivializations.X i)).mapIso
      (e.symm ≪≫ squareCoordinatesIso X L) ≪≫
    chartIsoOn X L.localTrivializations.X
      (productUnits X L.localTrivializations.X (invertibleSheafUnits X L)
        (invertibleSheafUnits X L))
      (productUnits_isCocycle X L.localTrivializations.X
        (invertibleSheafUnits X L) (invertibleSheafUnits X L)
        (invertibleSheafUnits_isCocycle X L) (invertibleSheafUnits_isCocycle X L))
      (AffineOpenRefinement.original X L.localTrivializations.X i)
      (AffineOpenRefinement.subordinate X L.localTrivializations.X i)

/-- Evaluation by the genuine sheaf frame equals the existing original
linear coordinate map on the same section module. -/
theorem squareRootSheafFrame_eval
    (i : AffineOpenRefinement.Index X L.localTrivializations.X)
    (m : N.val.obj (op (AffineOpenRefinement.opens X L.localTrivializations.X i))) :
    evalSection X.ringCatSheaf N
        (AffineOpenRefinement.opens X L.localTrivializations.X i)
        (squareRootSheafFrame X N L e i).hom m =
      squareRootCoordinateEquiv X L N e i m := by
  change squareRootCoordinateEquiv X L N e i
      (N.val.map (𝟙 (AffineOpenRefinement.opens X L.localTrivializations.X i)).op m) = _
  exact congrArg (squareRootCoordinateEquiv X L N e i)
    (CategoryTheory.congr_fun (N.val.presheaf.map_id
      (op (AffineOpenRefinement.opens X L.localTrivializations.X i))) m)

variable [X.IsSeparated]

/-- On the existing affine atlas the actual global dual-evaluation map
is multiplication by the original branch coefficient in the dual frame. -/
theorem sectionEvaluationMorphism_app_squareRoot
    (i : AffineOpenRefinement.Index X L.localTrivializations.X)
    (φ : (dual X.ringCatSheaf N).val.obj
      (op (AffineOpenRefinement.opens X L.localTrivializations.X i))) :
    (sectionEvaluationMorphism X N b).val.app
        (op (AffineOpenRefinement.opens X L.localTrivializations.X i)) φ =
      @Mul.mul (Γ(X, AffineOpenRefinement.opens X L.localTrivializations.X i))
        inferInstance
        (dualUnitSectionsEquiv X.ringCatSheaf
          (AffineOpenRefinement.opens X L.localTrivializations.X i)
          ((squareRootSheafFrame X N L e i).inv ≫ φ))
        ((fromSquareRoot X L N e b).sections i) := by
  let W := AffineOpenRefinement.opens X L.localTrivializations.X i
  let m : N.val.obj (op W) :=
    N.val.map (homOfLE (le_top : W ≤ ⊤)).op b
  have hc : evalSection X.ringCatSheaf N W (squareRootSheafFrame X N L e i).hom m =
      (fromSquareRoot X L N e b).sections i :=
    (squareRootSheafFrame_eval X N L e i m).trans
      (squareRootCoordinateEquiv_restrictedSection X L N e b i)
  exact (sectionEvaluationMorphism_app X N b W φ).trans
    ((evalSection_factor X.ringCatSheaf N W (squareRootSheafFrame X N L e i) φ m).trans
      (congrArg (@Mul.mul (Γ(X, W)) inferInstance
        (dualUnitSectionsEquiv X.ringCatSheaf W
          ((squareRootSheafFrame X N L e i).inv ≫ φ))) hc))

/-- The image of the actual sheaf morphism component is the original
quadratic branch coefficient ideal; no image equality is assumed. -/
theorem sectionEvaluationMorphism_range_eq_branchIdeal
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    LinearMap.range ((sectionEvaluationMorphism X N b).val.app
      (op (AffineOpenRefinement.opens X L.localTrivializations.X i))).hom =
        branchIdeal ((fromSquareRoot X L N e b).sections i) := by
  rw [sectionEvaluationMorphism_range_eq_span X N b _ (squareRootSheafFrame X N L e i),
    squareRootSheafFrame_eval, squareRootCoordinateEquiv_restrictedSection, branchIdeal]

include e in
/-- The genuine sheaf-morphism component image recovers the preceding
local module-dual evaluation ideal on every original affine chart. -/
theorem sectionEvaluationMorphism_range_eq_evaluationIdeal
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    LinearMap.range ((sectionEvaluationMorphism X N b).val.app
      (op (AffineOpenRefinement.opens X L.localTrivializations.X i))).hom =
        sectionEvaluationIdeal X N b
          (AffineOpenRefinement.opens X L.localTrivializations.X i) := by
  rw [sectionEvaluationMorphism_range_eq_branchIdeal X N b L e i,
    sectionEvaluationIdeal_eq_branchIdeal X L N e b i]

end InvertibleQuadraticAtlas

end KltDP.Geometry
