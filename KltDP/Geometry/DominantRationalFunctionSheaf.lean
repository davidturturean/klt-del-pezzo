import KltDP.Geometry.CartierDivisorPullback
import KltDP.Geometry.OpenImmersionRationalSheaf

/-!
The original generic-point-preserving morphism induces a map of the
existing rational-function sheaves. On nonempty inverse-image opens it
uses the original functionFieldMap homomorphism; on empty opens it uses
the actual terminal section ring. The original germ identity proves the
structure-sheaf square. This adapts the existing open-immersion proof
without assuming a function-field isomorphism or effective equations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.DominantCartierPullback

variable {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
variable (π : X ⟶ Y) [GenericPointPreserving π]

/-- An original preimage point gives an original target-open point. -/
private theorem targetOpen_nonempty (U : Y.Opens) [Nonempty (π ⁻¹ᵁ U)] : Nonempty U := by
  obtain ⟨⟨x, hx⟩⟩ := (inferInstance : Nonempty (π ⁻¹ᵁ U))
  exact ⟨⟨π.base x, hx⟩⟩

/-- Actual rational transport on sections, including the empty case. -/
def rationalPullbackApp (U : Y.Opens) :
    (rationalFunctionSheaf Y).val.obj (op U) ⟶
      (rationalFunctionSheaf X).val.obj (op (π ⁻¹ᵁ U)) := by
  classical
  by_cases hU : Nonempty (π ⁻¹ᵁ U)
  · letI := hU
    letI := targetOpen_nonempty π U
    exact (rationalFunctionSectionsIso Y U).hom ≫
      functionFieldMap π ≫ (rationalFunctionSectionsIso X (π ⁻¹ᵁ U)).inv
  · exact (OpenImmersionRational.rationalSectionsTerminal (π ⁻¹ᵁ U) hU).from _

/-- On nonempty inverse-image opens this is exactly the original
function-field map under the actual rational section identifications. -/
theorem rationalPullbackApp_comp_sectionsIso (U : Y.Opens)
    [Nonempty U] :
    rationalPullbackApp π U ≫ (rationalFunctionSectionsIso X (π ⁻¹ᵁ U)).hom =
      (rationalFunctionSectionsIso Y U).hom ≫ functionFieldMap π := by
  classical
  simp only [rationalPullbackApp, dif_pos (inferInstance : Nonempty (π ⁻¹ᵁ U)),
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual component maps commute with restriction on all opens. -/
theorem rationalPullbackApp_naturality {U V : Y.Opens} (i : V ⟶ U) :
    (rationalFunctionSheaf Y).val.map i.op ≫ rationalPullbackApp π V =
      rationalPullbackApp π U ≫
        (rationalFunctionSheaf X).val.map ((Opens.map π.base).map i).op := by
  classical
  by_cases hV : Nonempty (π ⁻¹ᵁ V)
  · letI := hV
    letI : Nonempty (π ⁻¹ᵁ U) := by
      obtain ⟨⟨y, hy⟩⟩ := hV
      exact ⟨⟨y, i.le hy⟩⟩
    letI := targetOpen_nonempty π V
    letI := targetOpen_nonempty π U
    apply (cancel_mono (rationalFunctionSectionsIso X (π ⁻¹ᵁ V)).hom).1
    rw [Category.assoc, rationalPullbackApp_comp_sectionsIso,
      ← Category.assoc]
    have hX := rationalFunctionSectionsIso_naturality Y i.le
    have hY := rationalFunctionSectionsIso_naturality X
      (show π ⁻¹ᵁ V ≤ π ⁻¹ᵁ U from fun _ hy => i.le hy)
    change (rationalFunctionSheaf Y).val.map i.op ≫
        (rationalFunctionSectionsIso Y V).hom = _ at hX
    change (rationalFunctionSheaf X).val.map ((Opens.map π.base).map i).op ≫
        (rationalFunctionSectionsIso X (π ⁻¹ᵁ V)).hom = _ at hY
    rw [hX, Category.assoc, hY, rationalPullbackApp_comp_sectionsIso]
  · exact (OpenImmersionRational.rationalSectionsTerminal (π ⁻¹ᵁ V) hV).hom_ext _ _

/-- The actual sheaf map on rational functions induced by the original
dominant morphism, into the actual sheaf pushforward. -/
def rationalPullback : rationalFunctionSheaf Y ⟶
    (TopCat.Sheaf.pushforward CommRingCat π.base).obj (rationalFunctionSheaf X) :=
  ⟨{ app U := rationalPullbackApp π U.unop
     naturality {_ _} i := rationalPullbackApp_naturality π i.unop }⟩

/-- The existing scheme structure morphism as a map of ring sheaves. -/
def structurePullback : Y.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat π.base).obj X.sheaf :=
  CategoryTheory.Sheaf.Hom.mk π.c

/-- Regular functions transport into rational functions through the
same actual map. This is the square needed for the Cartier quotient. -/
theorem structureToRationalFunctions_pullback :
    structureToRationalFunctions Y ≫ rationalPullback π =
      structurePullback π ≫
        (TopCat.Sheaf.pushforward CommRingCat π.base).map
          (structureToRationalFunctions X) := by
  apply CategoryTheory.Sheaf.Hom.ext
  apply NatTrans.ext
  funext U
  change (structureToRationalFunctions Y).val.app U ≫ rationalPullbackApp π U.unop =
    π.app U.unop ≫ (structureToRationalFunctions X).val.app (op (π ⁻¹ᵁ U.unop))
  classical
  by_cases hU : Nonempty (π ⁻¹ᵁ U.unop)
  · letI := hU
    letI := targetOpen_nonempty π U.unop
    apply (cancel_mono (rationalFunctionSectionsIso X (π ⁻¹ᵁ U.unop)).hom).1
    rw [Category.assoc, rationalPullbackApp_comp_sectionsIso,
      ← Category.assoc, structureToRationalFunctions_app_comp_sectionsIso,
      Category.assoc, structureToRationalFunctions_app_comp_sectionsIso]
    ext s
    exact functionFieldMap_germ π U.unop s
  · exact (OpenImmersionRational.rationalSectionsTerminal (π ⁻¹ᵁ U.unop) hU).hom_ext _ _

end KltDP.Geometry.DominantCartierPullback
