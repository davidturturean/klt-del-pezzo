import KltDP.Geometry.GloballyGeneratedUnitCoefficient

/-!
# A nonvanishing image section with its original preimage retained

A globally generated sheaf need not be invertible. If an actual morphism
from its restriction onto the local unit sheaf is an epimorphism, some
original global generator has unit image germ at the chosen point.

For a morphism into a line bundle which is an epimorphism on a neighbourhood,
this supplies a nonzero global image section together with its original
preimage. Applied to the inclusion of an ideal twist, the preimage retains
membership in the actual ideal twist. Coherence of point ideals and the
tensor-inclusion comparison are separate geometric adapters.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.GloballyGeneratedImageSection

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Local epimorphisms onto the unit select an original global generator
whose actual image germ is a unit. The source sheaf need not be invertible. -/
theorem exists_generator_unit_image (G : M.GeneratingSections)
    (U : X.Opens) (x : X) (hx : x ∈ U)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) [Epi φ] :
    ∃ i : G.I, IsUnit (X.presheaf.germ U x hx
      (φ.val.app (op (Over.mk (𝟙 U))) ((G.s i).val (op U)))) := by
  let G' := G.map (_root_.SheafOfModules.overFunctor X.ringCatSheaf U)
    (_root_.SheafOfModules.unitOverIso (R := X.ringCatSheaf) U).symm
  obtain ⟨i, hi⟩ := GeneratingUnitGerm.exists_generator_isUnit_germ X U x hx
    (G'.ofEpi φ)
  refine ⟨i, ?_⟩
  change IsUnit (X.presheaf.germ U x hx
    (φ.val.app (op (Over.mk (𝟙 U))) ((G'.s i).val (op (Over.mk (𝟙 U)))))) at hi
  have hval : (G'.s i).val (op (Over.mk (𝟙 U))) = (G.s i).val (op U) :=
    KltDP.SheafGeneratingSectionsRestriction.generatorsOver_section_val
      (R := X.ringCatSheaf) (M := M) G U i (op (Over.mk (𝟙 U)))
  exact (congrArg (fun a : M.val.obj (op U) =>
    IsUnit (X.presheaf.germ U x hx (φ.val.app (op (Over.mk (𝟙 U))) a))) hval).mp hi

/-- The selected unit image germ comes from an actual original global section. -/
theorem exists_section_unit_image (hM : Positivity.IsGloballyGenerated M)
    (U : X.Opens) (x : X) (hx : x ∈ U)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) [Epi φ] :
    ∃ s : M.val.obj (op (⊤ : X.Opens)),
      IsUnit (X.presheaf.germ U x hx (φ.val.app (op (Over.mk (𝟙 U)))
        (M.val.map (homOfLE (le_top : U ≤ ⊤)).op s))) := by
  obtain ⟨I, f, hf⟩ := hM
  letI := hf
  let G := (_root_.SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I).ofEpi f
  obtain ⟨i, hi⟩ := exists_generator_unit_image G U x hx φ
  let s := (G.s i).val (op (⊤ : X.Opens))
  have hres : M.val.map (homOfLE (le_top : U ≤ ⊤)).op s = (G.s i).val (op U) :=
    (G.s i).property (homOfLE (le_top : U ≤ ⊤)).op
  exact ⟨s, by rwa [hres]⟩

/-- A locally surjective original morphism to a framed line has a nonzero
global image section; the original preimage section is part of the conclusion. -/
theorem exists_nonzero_image_section (hM : Positivity.IsGloballyGenerated M)
    (φ : M ⟶ N) (U : X.Opens) (x : X) (hx : x ∈ U)
    [Epi ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U).map φ)]
    (e : N.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ∃ s : M.val.obj (op (⊤ : X.Opens)),
      φ.val.app (op (⊤ : X.Opens)) s ≠ 0 ∧
      IsUnit (X.presheaf.germ U x hx (e.hom.val.app (op (Over.mk (𝟙 U)))
        (N.val.map (homOfLE (le_top : U ≤ ⊤)).op
          (φ.val.app (op (⊤ : X.Opens)) s)))) := by
  let ψ := (_root_.SheafOfModules.overFunctor X.ringCatSheaf U).map φ ≫ e.hom
  obtain ⟨s, hs⟩ := exists_section_unit_image hM U x hx ψ
  have hres : N.val.map (homOfLE (le_top : U ≤ ⊤)).op
        (φ.val.app (op (⊤ : X.Opens)) s) =
      φ.val.app (op U) (M.val.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
    exact (_root_.PresheafOfModules.naturality_apply φ.val
      (homOfLE (le_top : U ≤ ⊤)).op s).symm
  change IsUnit (X.presheaf.germ U x hx (e.hom.val.app (op (Over.mk (𝟙 U)))
    (φ.val.app (op U) (M.val.map (homOfLE (le_top : U ≤ ⊤)).op s)))) at hs
  rw [← hres] at hs
  refine ⟨s, ?_, hs⟩
  intro hzero
  rw [hzero, map_zero, map_zero, map_zero] at hs
  exact not_isUnit_zero hs

end KltDP.Geometry.GloballyGeneratedImageSection
