import KltDP.Geometry.QuadraticGlobalRootCoordinates
import KltDP.Geometry.UnbranchedRationalBranchRoot
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Actual coherent quadratic roots on a branch-disjoint rational curve

The original branch-disjoint rational-curve construction supplies its
half-line frame and its global unit root. The original pulled square
isomorphism then identifies the pulled canonical branch section with
the tensor square of that original section. This derives unit roots of
the literal fromSquareRoot atlas coefficients without adding a frame,
coefficient nonvanishing, root, or splitting hypothesis.

Identifying this newly pulled line atlas with the scheme-theoretic
pullback of the ambient glued cover remains a separate obligation.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
universe u

namespace KltDP.Geometry.UnbranchedRationalQuadraticCoordinates

attribute [local instance] Types.instFunLike Types.instConcreteCategory
local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open SchemeModuleTensorSections QuadraticTensorSectionCoordinates
open QuadraticGlobalRootCoordinates InvertibleQuadraticAtlas

/-- The actual tensor comparison followed by the original pulled square isomorphism. -/
def pulledSquareIso {X C : Scheme.{u}} (f : C ⟶ X) (L : InvertibleSheaf X)
    (N : X.Modules) (e : L.obj ⊗ L.obj ≅ N) :
    (pullbackInvertibleSheaf f L).obj ⊗ (pullbackInvertibleSheaf f L).obj ≅
      (schemeModulePullback f).obj N :=
  (schemeModulePullbackTensorIso f L.obj L.obj).symm ≪≫
    (schemeModulePullback f).mapIso e

private theorem abstract_square_unit_hom {A : Type*} [Category A] [MonoidalCategory A]
    {O : A} (e : 𝟙_ A ≅ O) :
    (tensorIso e.symm e.symm ≪≫ λ_ (𝟙_ A) ≪≫ e).hom =
      ((tensorLeft O).mapIso e.symm ≪≫ ρ_ O).hom := by
  simp only [Iso.trans_hom, tensorIso_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [unitors_equal]
  simp only [tensorHom_def', Category.assoc, rightUnitor_naturality_assoc,
    e.inv_hom_id, Category.comp_id]
  rfl

/-- The literal unit convention in the branch frame is original multiplication. -/
theorem square_unit_hom (C : Scheme.{u}) :
    (tensorIso (SchemeModuleStructureUnit.iso C) (SchemeModuleStructureUnit.iso C) ≪≫
      λ_ (𝟙_ C.Modules) ≪≫ (SchemeModuleStructureUnit.iso C).symm).hom =
      (schemeStructureTensorRightIso (_root_.SheafOfModules.unit C.ringCatSheaf)).hom := by
  exact @abstract_square_unit_hom C.Modules inferInstance (moduleTensor C)
    (_root_.SheafOfModules.unit C.ringCatSheaf)
    (PresheafOfModules.sheafTensorUnitIso C.sheaf.val C.ringCatSheaf.cond)

/-- The square of the original section has the square of its literal frame coefficient. -/
theorem rootSection_square_frame (C : Scheme.{u}) (L : InvertibleSheaf C)
    (t : L.obj ≅ _root_.SheafOfModules.unit C.ringCatSheaf) (b : Γ(C, ⊤)ˣ) :
    (tensorIso t t ≪≫
      schemeStructureTensorRightIso (_root_.SheafOfModules.unit C.ringCatSheaf)).hom.val.app
        (op (⊤ : C.Opens))
        (tensorSection L.obj L.obj ⊤ (rootSection C L t b) (rootSection C L t b)) =
      (b : Γ(C, ⊤)) ^ 2 := by
  have ht : t.hom.val.app (op (⊤ : C.Opens)) (rootSection C L t b) =
      (b : Γ(C, ⊤)) :=
    congrArg (fun z : _root_.SheafOfModules.unit C.ringCatSheaf ⟶
      _root_.SheafOfModules.unit C.ringCatSheaf => z.val.app (op ⊤) (b : Γ(C, ⊤)))
        t.inv_hom_id
  change (schemeStructureTensorRightIso
    (_root_.SheafOfModules.unit C.ringCatSheaf)).hom.val.app (op ⊤)
      ((t.hom ⊗ t.hom).val.app (op ⊤)
        (tensorSection L.obj L.obj ⊤ (rootSection C L t b) (rootSection C L t b))) = _
  rw [tensorSection_natural, ht, structure_tensorSection, pow_two]

/-- The supplied root equality in the original branch frame identifies the
literal pulled square section; no new tensor compatibility is assumed. -/
theorem pulled_square_section_eq {X C : Scheme.{u}} (f : C ⟶ X) (L : InvertibleSheaf X)
    (N : X.Modules) (e : L.obj ⊗ L.obj ≅ N)
    (s : ((schemeModulePullback f).obj N).val.obj (op (⊤ : C.Opens)))
    (t : (pullbackInvertibleSheaf f L).obj ≅ _root_.SheafOfModules.unit C.ringCatSheaf)
    (b : Γ(C, ⊤)ˣ)
    (hb : (b : Γ(C, ⊤)) ^ 2 =
      (UnbranchedRationalBranchRoot.squareFrame f L N e t).hom.val.app (op ⊤) s) :
    (pulledSquareIso f L N e).inv.val.app (op ⊤) s =
      tensorSection (pullbackInvertibleSheaf f L).obj (pullbackInvertibleSheaf f L).obj ⊤
        (rootSection C (pullbackInvertibleSheaf f L) t b)
        (rootSection C (pullbackInvertibleSheaf f L) t b) := by
  let F := tensorIso t t ≪≫
    schemeStructureTensorRightIso (_root_.SheafOfModules.unit C.ringCatSheaf)
  let eF := ((_root_.SheafOfModules.evaluation C.ringCatSheaf (op (⊤ : C.Opens))).mapIso F).toLinearEquiv
  apply eF.injective
  have hf : (pulledSquareIso f L N e).inv ≫ F.hom =
      (UnbranchedRationalBranchRoot.squareFrame f L N e t).hom := by
    simp only [pulledSquareIso, F, UnbranchedRationalBranchRoot.squareFrame,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Category.assoc]
    rw [← square_unit_hom C]
    simp only [Iso.trans_hom, Category.assoc]
    rfl
  change ((pulledSquareIso f L N e).inv ≫ F.hom).val.app (op ⊤) s = _
  rw [hf]
  exact hb.symm.trans (rootSection_square_frame C (pullbackInvertibleSheaf f L) t b).symm

/-- Branch disjointness on an actual rational curve supplies coherent unit
roots of the original pulled-line quadratic atlas's actual coefficients. -/
theorem exists_roots (k : Type u) [Field k] [IsAlgClosed k]
    {X C : Scheme.{u}} [IsIntegral X] [C.IsSeparated]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)
    (f : C ⟶ X) (eC : C ≅ projectiveSpace k 1)
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base)) :
    ∃ (t : (pullbackInvertibleSheaf f L).obj ≅ _root_.SheafOfModules.unit C.ringCatSheaf)
      (b : Γ(C, ⊤)ˣ), ∀ i,
      (rootUnit C (pullbackInvertibleSheaf f L) t b i :
        Γ(C, AffineOpenRefinement.opens C (pullbackInvertibleSheaf f L).localTrivializations.X i)) ^ 2 =
        (fromSquareRoot C (pullbackInvertibleSheaf f L)
          ((schemeModulePullback f).obj (cartierDivisorModule X E))
          (pulledSquareIso f L (cartierDivisorModule X E) e)
          (RationalTreePicard.pulledSection f (cartierDivisorModule X E) ⊤
            (effectiveCartierSection X E hE))).sections i := by
  obtain ⟨t, b, hb⟩ := UnbranchedRationalBranchRoot.exists_frame_and_root
    k E hE L e f eC hdisj
  have heq := pulled_square_section_eq f L (cartierDivisorModule X E) e
    (RationalTreePicard.pulledSection f (cartierDivisorModule X E) ⊤
      (effectiveCartierSection X E hE)) t b hb
  refine ⟨t, b, ?_⟩
  intro i
  change _ = (fromSquareSection C (pullbackInvertibleSheaf f L) _).sections i
  rw [heq]
  exact rootUnit_sq C (pullbackInvertibleSheaf f L) t b i

end KltDP.Geometry.UnbranchedRationalQuadraticCoordinates

#print axioms KltDP.Geometry.UnbranchedRationalQuadraticCoordinates.exists_roots
