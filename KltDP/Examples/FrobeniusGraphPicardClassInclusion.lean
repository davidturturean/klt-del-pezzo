import KltDP.Examples.FrobeniusGraphPicardClassCartier

/-!
# Rational normalization of the original graph-kernel inclusion

The original inclusion into the structure sheaf factors through the
fixed first-frame rational coordinate by the actual value of that
frame's generator. The proof uses its true section restriction,
linearity and the original generic-point germ.

The remaining normalization identifies the actual first-generator
value with the original polynomial equation y-x^p. That equality is
not included as an assumption here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassInclusion

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassIntegral
open FrobeniusGraphPicardClassRational FrobeniusGraphPicardClassCartier

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

def firstGraphChart (p : ℕ) : LineBundleTrivializationChart (projectiveProduct k)
    (schemeKernelIdeal (projectiveGraphMorphism p)) where
  openSet := diagonalOpen 0
  nonempty := inferInstance
  trivialization := firstGraphTrivialization p

/-- The actual global-kernel section supplied by the fixed first frame. -/
def firstGraphGenerator (p : ℕ) :
    (schemeKernelIdeal (projectiveGraphMorphism (k := k) p)).val.obj (op (diagonalOpen 0)) :=
  lineBundleChartGenerator (projectiveProduct k)
    (schemeKernelIdeal (projectiveGraphMorphism p)) (firstGraphChart p)

/-- Its value through the original ideal inclusion and original function-field germ. -/
def firstGraphGeneratorValue (p : ℕ) : (projectiveProduct k).functionField :=
  (projectiveProduct k).germToFunctionField (diagonalOpen 0)
    ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op (diagonalOpen 0))
      (firstGraphGenerator p))

/-- The original inclusion and the first-frame rational coordinate differ by this actual value. -/
theorem graphInclusion_generic_factor (p : ℕ) (V : (projectiveProduct k).Opens)
    [Nonempty V]
    (s : (schemeKernelIdeal (projectiveGraphMorphism (k := k) p)).val.obj (op V)) :
    (projectiveProduct k).germToFunctionField V
        ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op V) s) =
      firstGraphGeneratorValue p *
        lineBundleGenericCoordinate (projectiveProduct k)
          (schemeKernelIdeal (projectiveGraphMorphism p)) (diagonalOpen 0)
          (firstGraphTrivialization p) V s := by
  let X := projectiveProduct k
  let M := schemeKernelIdeal (projectiveGraphMorphism (k := k) p)
  let W : X.Opens := V ⊓ diagonalOpen 0
  letI : Nonempty W := ⟨⟨genericPoint X,
    genericPoint_mem_nonempty_open X V,
    genericPoint_mem_nonempty_open X (diagonalOpen 0)⟩⟩
  let j : W ⟶ V := homOfLE inf_le_left
  let i : W ⟶ diagonalOpen 0 := homOfLE inf_le_right
  let θ := overTrivializationSectionEquiv X M (diagonalOpen 0)
    (firstGraphTrivialization p) i
  let g : M.val.obj (op W) := M.val.map i.op (firstGraphGenerator p)
  let sW : M.val.obj (op W) := M.val.map j.op s
  have hg : θ g = 1 := by
    have hrestrict : g = θ.symm (1 : Γ(X, W)) :=
      lineBundleChartGenerator_restrict X M (firstGraphChart (k := k) p) i
    exact (congrArg θ hrestrict).trans (θ.apply_symm_apply 1)
  have hs : sW = θ sW • g := by
    apply θ.injective
    rw [θ.map_smul, hg, smul_eq_mul, mul_one]
  have hι (U₁ U₂ : X.Opens) (a : U₂ ⟶ U₁) (t : M.val.obj (op U₁)) :
      (schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op U₂) (M.val.map a.op t) =
        X.presheaf.map a.op
          ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op U₁) t) :=
    PresheafOfModules.naturality_apply (schemeKernelIdealι (projectiveGraphMorphism p)).val a.op t
  have hgen : X.germToFunctionField W
      ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op W) g) =
        firstGraphGeneratorValue p := by
    change X.germToFunctionField W
      ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op W)
        (M.val.map i.op (firstGraphGenerator p))) = _
    rw [hι, X.presheaf.germ_res_apply]
    rfl
  calc
    _ = X.germToFunctionField W
        ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op W) sW) := by
          change _ = X.germToFunctionField W
            ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op W) (M.val.map j.op s))
          rw [hι, X.presheaf.germ_res_apply]
    _ = X.germToFunctionField W
        ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op W) (θ sW • g)) :=
          congrArg (fun t => X.germToFunctionField W
            ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op W) t)) hs
    _ = X.germToFunctionField W (θ sW) *
        X.germToFunctionField W
          ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op W) g) := by
          rw [map_smul]
          exact (X.germToFunctionField W).hom.map_mul _ _
    _ = X.germToFunctionField W (θ sW) * firstGraphGeneratorValue p := by rw [hgen]
    _ = _ := mul_comm _ _

end KltDP.Examples.FrobeniusGraphPicardClassInclusion
