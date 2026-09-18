import KltDP.Geometry.PullbackTransitionUnitGluing
import KltDP.Geometry.InvertibleSheafSectionPowersPullback

/-!
# Original sections under the constructed cocycle pullback isomorphism

Read the actual pulled section in the actual pulled frame. Linearity and
the proved frame coordinate one identify its coefficient with the original
ring pullback. Recovery and the equality of the original cocycles preserve
these coordinates under the specific `pullbackGluedIso`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitExtraction RationalTreePicard

private theorem moduleSheaf_eqToIso_hom_app_val
    (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    {g g' : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ} (hg : g = g')
    (h : moduleSheaf X U g = moduleSheaf X U g')
    (W : X.Opensᵒᵖ) (x : sections X U g W.unop) (i : ι) :
    ((eqToIso h).hom.val.app W x).val i = x.val i := by
  cases hg
  rfl

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {ι : Type u}
  (U : ι → X.Opens) (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ)
  (hc : IsCocycle X U g) (hU : (⨆ i, U i) = ⊤)

/-- On its original chart every section is its original coefficient times
the original glued frame. -/
theorem section_eq_trivialization_smul_chartFrame (i : ι)
    (x : sections X U g (U i)) :
    x = trivialization X U g hc i le_rfl x • chartFrame U g hc i := by
  apply (trivialization X U g hc i le_rfl).injective
  rw [map_smul, trivialization_chartFrame]
  exact ((smul_eq_mul _ _).trans (mul_one _)).symm

/-- The actual pulled frame reads the original pullback of the coefficient. -/
theorem chartEquiv_pulledSection (i : ι) (x : sections X U g (U i)) :
    chartEquiv Y _ (pulledAtlas U g hc f hU) i le_rfl
        (pulledSection f (moduleSheaf X U g) (U i) x) =
      f.app (U i) (trivialization X U g hc i le_rfl x) := by
  let e : ((schemeModulePullback f).obj (moduleSheaf X U g)).val.obj
      (op (f ⁻¹ᵁ U i)) ≃ₗ[Γ(Y, f ⁻¹ᵁ U i)] Γ(Y, f ⁻¹ᵁ U i) :=
    chartEquiv Y _ (pulledAtlas U g hc f hU) i (W := f ⁻¹ᵁ U i) le_rfl
  let a : Γ(X, U i) := trivialization X U g hc i le_rfl x
  let b : Γ(Y, f ⁻¹ᵁ U i) := f.app (U i) a
  have hx : x = a • chartFrame U g hc i :=
    section_eq_trivialization_smul_chartFrame U g hc i x
  have hframe : e
      (pulledSection f (moduleSheaf X U g) (U i) (chartFrame U g hc i)) = 1 :=
    pulledFrameCoordinate f U g hc hU i
  change e (pulledSection f (moduleSheaf X U g) (U i) x) = b
  calc
    _ = e (pulledSection f (moduleSheaf X U g) (U i)
        (a • chartFrame U g hc i)) :=
      congrArg (fun z => e (pulledSection f (moduleSheaf X U g) (U i) z)) hx
    _ = e (b • pulledSection f (moduleSheaf X U g) (U i) (chartFrame U g hc i)) :=
      congrArg e (pulledSection_smul f (moduleSheaf X U g) (U i) a (chartFrame U g hc i))
    _ = b * e (pulledSection f (moduleSheaf X U g) (U i) (chartFrame U g hc i)) :=
      e.map_smul b _
    _ = b := (congrArg (fun z : Γ(Y, f ⁻¹ᵁ U i) => b * z) hframe).trans (mul_one b)

/-- The same coordinate formula holds on every original subopen of the
inverse-image chart for the literal compatible pulled section family. -/
theorem chartEquiv_pullbackSection (s : (moduleSheaf X U g).sections)
    (i : ι) {W : Y.Opens} (hWi : W ≤ f ⁻¹ᵁ U i) :
    chartEquiv Y _ (pulledAtlas U g hc f hU) i hWi
        ((InvertibleSheafSectionPowersPullback.pullbackSection f
          (moduleSheaf X U g) s).val (op W)) =
      res Y hWi (f.app (U i) (trivialization X U g hc i le_rfl (s.val (op (U i))))) := by
  let t := InvertibleSheafSectionPowersPullback.pullbackSection f (moduleSheaf X U g) s
  have hs := t.property (homOfLE hWi).op
  rw [← hs, InvertibleSheafSectionPowersPullback.pullbackSection_val]
  exact (chartEquiv_restrict Y _ (pulledAtlas U g hc f hU) i hWi le_rfl _).trans
    (congrArg (res Y hWi) (chartEquiv_pulledSection f U g hc hU i (s.val (op (U i)))))

/-- Coordinate evaluation of the specific original glued pullback isomorphism. -/
theorem pullbackGluedIso_hom_app_val (W : Y.Opensᵒᵖ)
    (x : ((schemeModulePullback f).obj (moduleSheaf X U g)).val.obj W) (i : ι) :
    ((pullbackGluedIso f U g hc hU).hom.val.app W x).val i =
      chartEquiv Y _ (pulledAtlas U g hc f hU) i
        (inf_le_right : W.unop ⊓ (f ⁻¹ᵁ U i) ≤ f ⁻¹ᵁ U i)
        (((schemeModulePullback f).obj (moduleSheaf X U g)).val.map
          (homOfLE (inf_le_left : W.unop ⊓ (f ⁻¹ᵁ U i) ≤ W.unop)).op x) := by
  have hu : transitionUnits Y ((schemeModulePullback f).obj (moduleSheaf X U g))
      (pulledAtlas U g hc f hU) = pullbackUnits f U g := by
    funext a b
    exact transitionUnits_pulledAtlas U g hc f hU
      (fun a => pulledFrameCoordinate f U g hc hU a) a b
  unfold pullbackGluedIso
  simp only [Iso.trans_hom, pulledHom_comp_val_app]
  exact (moduleSheaf_eqToIso_hom_app_val Y (fun i => f ⁻¹ᵁ U i) hu _ W _ i).trans
    (recoveryIso_hom_app_val Y ((schemeModulePullback f).obj (moduleSheaf X U g))
      (pulledAtlas U g hc f hU) W x i)

/-- The specific glued pullback isomorphism preserves every original
section's coordinate, on every open and every original chart. -/
theorem pullbackGluedIso_hom_app_val_pullbackSection
    (s : (moduleSheaf X U g).sections) (W : Y.Opens) (i : ι) :
    ((pullbackGluedIso f U g hc hU).hom.val.app (op W)
      ((InvertibleSheafSectionPowersPullback.pullbackSection f
        (moduleSheaf X U g) s).val (op W))).val i =
      res Y (inf_le_right : W ⊓ (f ⁻¹ᵁ U i) ≤ f ⁻¹ᵁ U i)
        (f.app (U i) (trivialization X U g hc i le_rfl (s.val (op (U i))))) := by
  rw [pullbackGluedIso_hom_app_val]
  let M := (schemeModulePullback f).obj (moduleSheaf X U g)
  let t := InvertibleSheafSectionPowersPullback.pullbackSection f (moduleSheaf X U g) s
  have hs : M.val.map (homOfLE (inf_le_left : W ⊓ (f ⁻¹ᵁ U i) ≤ W)).op
      (t.val (op W)) = t.val (op (W ⊓ (f ⁻¹ᵁ U i))) :=
    t.property (homOfLE (inf_le_left : W ⊓ (f ⁻¹ᵁ U i) ≤ W)).op
  exact (congrArg
    (fun z : M.val.obj (op (W ⊓ (f ⁻¹ᵁ U i))) =>
      chartEquiv Y M (pulledAtlas U g hc f hU) i inf_le_right z) hs).trans
    (chartEquiv_pullbackSection f U g hc hU s i inf_le_right)

end KltDP.Geometry.TransitionUnitGluing
