import KltDP.Geometry.OpenImmersionFunctionField

/-!
# Actual rational-function sheaf map for an open immersion

The map is the proved function-field isomorphism on every nonempty
inverse-image open. An empty inverse image uses the actual terminal
section ring of the rational-function sheaf. The resulting components
are natural and commute with the actual structure-sheaf map.

This constructs a morphism into the actual topological sheaf pushforward.
No pointwise quotient or claim about global rational representatives of
Cartier divisors is used. The next quotient construction can therefore
apply the actual cokernel universal property to these actual sheaf maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : Y ⟶ X) [IsOpenImmersion f]

/-- The section ring over an empty open is terminal, as supplied by
the actual sheaf condition. -/
def rationalSectionsTerminal (V : Y.Opens) (hV : ¬ Nonempty V) :
    IsTerminal ((rationalFunctionSheaf Y).val.obj (op V)) := by
  have hbot : V = ⊥ := by
    apply SetLike.ext
    intro y
    exact ⟨fun hy => (hV ⟨⟨y, hy⟩⟩).elim, fun hy => hy.elim⟩
  subst V
  exact (rationalFunctionSheaf Y).isTerminalOfEmpty

/-- Actual rational transport on sections, including the empty case. -/
def rationalPullbackApp (U : X.Opens) :
    (rationalFunctionSheaf X).val.obj (op U) ⟶
      (rationalFunctionSheaf Y).val.obj (op (f ⁻¹ᵁ U)) := by
  classical
  by_cases hU : Nonempty (f ⁻¹ᵁ U)
  · letI := hU
    letI := nonempty_of_preimage f U
    exact (rationalFunctionSectionsIso X U).hom ≫
      (functionFieldIso f).hom ≫ (rationalFunctionSectionsIso Y (f ⁻¹ᵁ U)).inv
  · exact (rationalSectionsTerminal (f ⁻¹ᵁ U) hU).from _

/-- On nonempty inverse-image opens this is exactly the original
function-field map under the actual rational section identifications. -/
theorem rationalPullbackApp_comp_sectionsIso (U : X.Opens)
    [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    rationalPullbackApp f U ≫ (rationalFunctionSectionsIso Y (f ⁻¹ᵁ U)).hom =
      (rationalFunctionSectionsIso X U).hom ≫ (functionFieldIso f).hom := by
  classical
  simp only [rationalPullbackApp, dif_pos (inferInstance : Nonempty (f ⁻¹ᵁ U)),
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual component maps commute with restriction on all opens. -/
theorem rationalPullbackApp_naturality {U V : X.Opens} (i : V ⟶ U) :
    (rationalFunctionSheaf X).val.map i.op ≫ rationalPullbackApp f V =
      rationalPullbackApp f U ≫
        (rationalFunctionSheaf Y).val.map ((Opens.map f.base).map i).op := by
  classical
  by_cases hV : Nonempty (f ⁻¹ᵁ V)
  · letI := hV
    letI : Nonempty (f ⁻¹ᵁ U) := by
      obtain ⟨⟨y, hy⟩⟩ := hV
      exact ⟨⟨y, i.le hy⟩⟩
    letI := nonempty_of_preimage f V
    letI := nonempty_of_preimage f U
    apply (cancel_mono (rationalFunctionSectionsIso Y (f ⁻¹ᵁ V)).hom).1
    rw [Category.assoc, rationalPullbackApp_comp_sectionsIso,
      ← Category.assoc]
    have hX := rationalFunctionSectionsIso_naturality X i.le
    have hY := rationalFunctionSectionsIso_naturality Y
      (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hy => i.le hy)
    change (rationalFunctionSheaf X).val.map i.op ≫
        (rationalFunctionSectionsIso X V).hom = _ at hX
    change (rationalFunctionSheaf Y).val.map ((Opens.map f.base).map i).op ≫
        (rationalFunctionSectionsIso Y (f ⁻¹ᵁ V)).hom = _ at hY
    rw [hX, Category.assoc, hY, rationalPullbackApp_comp_sectionsIso]
  · exact (rationalSectionsTerminal (f ⁻¹ᵁ V) hV).hom_ext _ _

/-- The actual sheaf map on rational functions induced by the open
immersion, into the actual sheaf pushforward. -/
def rationalPullback : rationalFunctionSheaf X ⟶
    (TopCat.Sheaf.pushforward CommRingCat f.base).obj (rationalFunctionSheaf Y) :=
  ⟨{ app U := rationalPullbackApp f U.unop
     naturality {_ _} i := rationalPullbackApp_naturality f i.unop }⟩

/-- The existing scheme structure morphism as a map of ring sheaves. -/
def structurePullback : X.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat f.base).obj Y.sheaf :=
  CategoryTheory.Sheaf.Hom.mk f.c

/-- Regular functions transport into rational functions through the
same actual map. This is the square needed for the Cartier quotient. -/
theorem structureToRationalFunctions_pullback :
    structureToRationalFunctions X ≫ rationalPullback f =
      structurePullback f ≫
        (TopCat.Sheaf.pushforward CommRingCat f.base).map
          (structureToRationalFunctions Y) := by
  apply CategoryTheory.Sheaf.Hom.ext
  apply NatTrans.ext
  funext U
  change (structureToRationalFunctions X).val.app U ≫ rationalPullbackApp f U.unop =
    f.app U.unop ≫ (structureToRationalFunctions Y).val.app (op (f ⁻¹ᵁ U.unop))
  classical
  by_cases hU : Nonempty (f ⁻¹ᵁ U.unop)
  · letI := hU
    letI := nonempty_of_preimage f U.unop
    apply (cancel_mono (rationalFunctionSectionsIso Y (f ⁻¹ᵁ U.unop)).hom).1
    rw [Category.assoc, rationalPullbackApp_comp_sectionsIso,
      ← Category.assoc, structureToRationalFunctions_app_comp_sectionsIso,
      Category.assoc, structureToRationalFunctions_app_comp_sectionsIso]
    exact germ_comp_functionFieldIso f U.unop
  · exact (rationalSectionsTerminal (f ⁻¹ᵁ U.unop) hU).hom_ext _ _

end KltDP.Geometry.OpenImmersionRational
