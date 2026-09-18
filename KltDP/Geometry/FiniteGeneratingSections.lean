import KltDP.Geometry.FiniteNonvanishingGenerators
import KltDP.Geometry.FramedGlobalGeneration
import KltDP.Compatibility.SheafUnitAutomorphisms

/-!
# Finite original global generators on a quasi-compact scheme

A section nonvanishing at a point becomes the unit of an actual frame on
a smaller neighborhood. The accepted local-to-global epimorphism theorem
therefore applies to any family whose intrinsic nonvanishing opens cover.
Compactness selects a finite subset of any original generating family,
and the same sections give the resulting finite free epimorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.FiniteGeneratingSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen TransitionUnitExtraction

variable {X : Scheme.{u}}

local instance sectionCommRing (V : (X.Opens)ᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj V) :=
  inferInstanceAs (CommRing (X.presheaf.obj V))

local instance : ∀ V, IsMulCommutative (X.ringCatSheaf.val.obj V) :=
  fun _ => ⟨⟨fun a b => mul_comm a b⟩⟩

/-- An original nonvanishing section is the unit in an actual normalized
frame on a neighborhood of the given point. -/
theorem exists_unit_frame (L : InvertibleSheaf X) (s : L.obj.sections)
    (x : X) (hx : x ∈ nonvanishingOpen X L s) :
    ∃ (V : X.Opens), x ∈ V ∧
      ∃ e : L.obj.over V ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over V),
        e.hom.val.app (op (Over.mk (𝟙 V))) (s.val (op V)) = (1 : Γ(X, V)) := by
  let t := L.localTrivializations
  have hxt : x ∈ (⨆ a, t.X a) := by
    rw [chartOpens_cover X L.obj t]
    trivial
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hxt
  let c : Γ(X, t.X a) := chartCoefficient X L.obj t s a
  have hc : IsUnit (X.presheaf.germ (t.X a) x ha c) :=
    (mem_nonvanishingOpen_iff_isUnit_germ X L s t a x ha).mp hx
  obtain ⟨V, r, hxV, hV⟩ :=
    X.toRingedSpace.isUnit_res_of_isUnit_germ (t.X a) c x ha hc
  obtain ⟨v, hv⟩ := hV
  let eV := t.unitIsoOver a r
  have heV : eV.hom.val.app (op (Over.mk (𝟙 V))) (s.val (op V)) =
      X.presheaf.map r.op c := by
    change chartEquiv X L.obj t a r.le (s.val (op V)) = _
    exact (chartCoefficient_restrict X L.obj t s a r.le).symm
  let e := eV ≪≫ KltDP.SheafOfModules.overUnitSectionUnitsEquivAut
    X.ringCatSheaf V v⁻¹
  refine ⟨V, hxV, e, ?_⟩
  change (KltDP.SheafOfModules.overUnitSectionUnitsEquivAut X.ringCatSheaf V v⁻¹).hom.val.app
    (op (Over.mk (𝟙 V))) (eV.hom.val.app (op (Over.mk (𝟙 V))) (s.val (op V))) = _
  rw [KltDP.SheafOfModules.overUnitSectionUnitsEquivAut_hom_app_apply]
  change (show Γ(X, V) from eV.hom.val.app (op (Over.mk (𝟙 V))) (s.val (op V))) *
    X.presheaf.map (𝟙 V).op (↑(v⁻¹)) = (1 : Γ(X, V))
  rw [op_id, X.presheaf.map_id]
  change (show Γ(X, V) from eV.hom.val.app (op (Over.mk (𝟙 V))) (s.val (op V))) * ↑(v⁻¹) = (1 : Γ(X, V))
  rw [heV, ← hv]
  simp

/-- The original free map is epic whenever the intrinsic nonvanishing
opens of its given original sections cover the scheme. -/
theorem epi_of_nonvanishing_cover (L : InvertibleSheaf X)
    {I : Type u} (s : I → L.obj.sections)
    (hcover : (⨆ a, nonvanishingOpen X L (s a)) = ⊤) :
    Epi (L.obj.freeHomEquiv.symm s) := by
  classical
  have hlocal (x : X) : ∃ (V : X.Opens), x ∈ V ∧
      ∃ e : L.obj.over V ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over V),
        ∃ a : I, e.hom.val.app (op (Over.mk (𝟙 V)))
          ((s a).val (op V)) = (1 : Γ(X, V)) := by
    have hx : x ∈ (⨆ a, nonvanishingOpen X L (s a)) := by rw [hcover]; trivial
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx
    obtain ⟨V, hxV, e, he⟩ := exists_unit_frame L (s a) x ha
    exact ⟨V, hxV, e, a, he⟩
  choose V hxV e a he using hlocal
  have hV : (⊤ : X.Opens) ≤ ⨆ x, V x := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hxV x⟩
  exact FramedGlobalGeneration.epi_of_unit_coefficients L.obj V hV e s
    (fun x => ⟨a x, he x⟩)

/-- A finite subset of the supplied original generating family still
generates the original invertible sheaf. -/
theorem exists_finite_subfamily (L : InvertibleSheaf X)
    (hX : IsCompact (Set.univ : Set X)) (G : L.obj.GeneratingSections) :
    ∃ S : Finset G.I, Epi (L.obj.freeHomEquiv.symm (fun a : S => G.s a.val)) := by
  obtain ⟨S, hS⟩ := FiniteNonvanishingGenerators.exists_finite_nonvanishing_subcover L hX G
  exact ⟨S, epi_of_nonvanishing_cover L (fun a : S => G.s a.val) hS⟩

/-- Quasi-compact global generation of an invertible sheaf has an actual
finite generating family. -/
theorem exists_finite_generatingSections (L : InvertibleSheaf X)
    (hX : IsCompact (Set.univ : Set X)) (hL : Positivity.IsGloballyGenerated L.obj) :
    ∃ H : L.obj.GeneratingSections, Finite H.I := by
  obtain ⟨I, f, hf⟩ := hL
  letI := hf
  let G := (_root_.SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I).ofEpi f
  obtain ⟨S, hS⟩ := exists_finite_subfamily L hX G
  let H : L.obj.GeneratingSections := { I := S, s := fun a => G.s a.val, epi := hS }
  exact ⟨H, inferInstanceAs (Finite S)⟩

/-- The finite free epimorphism is the original free presentation attached
to the constructed finite family of original global sections. -/
theorem exists_finite_free_epi (L : InvertibleSheaf X)
    (hX : IsCompact (Set.univ : Set X)) (hL : Positivity.IsGloballyGenerated L.obj) :
    ∃ (I : Type u) (_ : Finite I)
      (f : _root_.SheafOfModules.free (R := X.ringCatSheaf) I ⟶ L.obj), Epi f := by
  obtain ⟨H, hH⟩ := exists_finite_generatingSections L hX hL
  exact ⟨H.I, hH, H.π, inferInstance⟩

end KltDP.Geometry.FiniteGeneratingSections
