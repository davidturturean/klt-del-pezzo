import KltDP.Geometry.GeneratingUnitGerm
import KltDP.Compatibility.SheafGeneratingSectionsRestriction
import KltDP.Geometry.Positivity
import KltDP.Compatibility.InvertibleTensorUnit

/-!
# A globally generated invertible sheaf has a nonvanishing original section

Restrict the original free presentation to a trivializing open, transport it
through its actual frame, and apply the unit-germ generator theorem.  The
restriction comparison identifies the selected local generator with an
original global section.  Its coefficient is a unit in the original local
ring, and the original section is consequently nonzero.

This supplies the section required to construct an effective Cartier
representative avoiding a chosen prime curve's generic point.  The final
Cartier-support comparison is a separate consumer.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.GloballyGeneratedUnitCoefficient

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} {M : X.Modules}

/-- Localizing the actual presentation and taking actual frame coordinates
selects one of the original generating sections with a unit coefficient. -/
theorem exists_generator_unit_coefficient (G : M.GeneratingSections)
    (U : X.Opens) (x : X) (hx : x ∈ U)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ∃ i : G.I, IsUnit (X.presheaf.germ U x hx
      (e.hom.val.app (op (Over.mk (𝟙 U))) ((G.s i).val (op U)))) := by
  let G' := G.map (_root_.SheafOfModules.overFunctor X.ringCatSheaf U)
    (_root_.SheafOfModules.unitOverIso (R := X.ringCatSheaf) U).symm
  obtain ⟨i, hi⟩ := GeneratingUnitGerm.exists_generator_isUnit_germ X U x hx
    (G'.ofEpi e.hom)
  refine ⟨i, ?_⟩
  change IsUnit (X.presheaf.germ U x hx
    (e.hom.val.app (op (Over.mk (𝟙 U))) ((G'.s i).val (op (Over.mk (𝟙 U)))))) at hi
  have hval : (G'.s i).val (op (Over.mk (𝟙 U))) = (G.s i).val (op U) :=
    KltDP.SheafGeneratingSectionsRestriction.generatorsOver_section_val
      (R := X.ringCatSheaf) (M := M) G U i (op (Over.mk (𝟙 U)))
  exact (congrArg (fun a : M.val.obj (op U) =>
    IsUnit (X.presheaf.germ U x hx (e.hom.val.app (op (Over.mk (𝟙 U))) a))) hval).mp hi

/-- Global generation supplies a nonzero original global section whose
coefficient in a specified actual local frame is a unit at the point. -/
theorem exists_section_unit_coefficient (hM : Positivity.IsGloballyGenerated M)
    (U : X.Opens) (x : X) (hx : x ∈ U)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ∃ s : M.val.obj (op (⊤ : X.Opens)), s ≠ 0 ∧
      IsUnit (X.presheaf.germ U x hx (e.hom.val.app (op (Over.mk (𝟙 U)))
        (M.val.map (homOfLE (le_top : U ≤ ⊤)).op s))) := by
  obtain ⟨I, f, hf⟩ := hM
  letI := hf
  let G := (_root_.SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I).ofEpi f
  obtain ⟨i, hi⟩ := exists_generator_unit_coefficient G U x hx e
  let s := (G.s i).val (op (⊤ : X.Opens))
  have hres : M.val.map (homOfLE (le_top : U ≤ ⊤)).op s = (G.s i).val (op U) :=
    (G.s i).property (homOfLE (le_top : U ≤ ⊤)).op
  refine ⟨s, ?_, by rwa [hres]⟩
  intro hs
  have hzero : (G.s i).val (op U) = 0 := by
    rw [← hres, hs]
    exact map_zero _
  rw [hzero, map_zero, map_zero] at hi
  exact not_isUnit_zero hi

/-- Every point of a globally generated invertible sheaf admits a local
frame and an original section nonvanishing there. -/
theorem exists_frame_and_section (L : InvertibleSheaf X)
    (hL : Positivity.IsGloballyGenerated L.obj) (x : X) :
    ∃ (U : X.Opens) (hx : x ∈ U)
      (e : L.obj.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
      (s : L.obj.val.obj (op (⊤ : X.Opens))), s ≠ 0 ∧
      IsUnit (X.presheaf.germ U x hx (e.hom.val.app (op (Over.mk (𝟙 U)))
        (L.obj.val.map (homOfLE (le_top : U ≤ ⊤)).op s))) := by
  let t := L.localTrivializations
  obtain ⟨V, f, ⟨i, ⟨g⟩⟩, hxV⟩ := t.coversTop ⊤ x trivial
  let hx : x ∈ t.X i := g.le hxV
  obtain ⟨s, hs, hunit⟩ := exists_section_unit_coefficient hL (t.X i) x hx (t.unitIso i)
  exact ⟨t.X i, hx, t.unitIso i, s, hs, hunit⟩

end KltDP.Geometry.GloballyGeneratedUnitCoefficient
