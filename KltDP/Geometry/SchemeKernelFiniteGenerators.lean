import KltDP.Compatibility.SheafEpiOnBasis
import KltDP.Compatibility.SheafGeneratingSectionsMap
import KltDP.Geometry.PrincipalKernelSheaf
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Actual finite generators of a scheme morphism's kernel ideal sheaf

The accepted single-equation kernel map extends to an arbitrary family
of actual global equations. When those equations generate the literal
global section kernel on an affine target, the resulting free
map is an epimorphism: the accepted kernel-localization theorem supplies
generation on every basic open, and the sectionwise linear range proves
surjectivity there.

Consequently a quasi-compact scheme morphism into a locally Noetherian
affine scheme has an actual finite-free epimorphism onto its original
categorical kernel ideal sheaf. Finite generation is derived from the
Noetherian section ring; it is not a sheaf-generation hypothesis.

This is an original adapter from the pinned ideal-localization theorem
and accepted project kernel maps. The modern Apache-2.0 Mazur source at
9327963d4ec14fba49c7b14b004fd00707ffc2e9 supplies the broader comparison
route recorded in POINT_IDEAL_REUSE.md; no newer API is imported or ported.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {I : Type u}
  (d : I → Γ(Y, ⊤)) (hd : ∀ i, f.appTop (d i) = 0)

/-- The original equations, lifted through the original categorical
kernel, give the canonical map from the original coproduct free sheaf. -/
def schemeKernelGeneratorsMap :
    _root_.SheafOfModules.free (R := Y.ringCatSheaf) I ⟶ schemeKernelIdeal f :=
  Sigma.desc (fun i => schemeKernelGenerator f (d i) (hd i))

/-- Each summand still acts by multiplication by its original equation
after the actual kernel inclusion. -/
@[simp]
theorem schemeKernelGeneratorsMap_comp_ι (i : I) :
    Sigma.ι (fun _ : I => _root_.SheafOfModules.unit Y.ringCatSheaf) i ≫
        schemeKernelGeneratorsMap f d hd ≫ schemeKernelIdealι f =
      schemeScalarEnd (d i) := by
  rw [← Category.assoc, schemeKernelGeneratorsMap, Sigma.ι_desc,
    schemeKernelGenerator_comp_ι]

/-- Literal generation of the original section kernel makes the
constructed map surjective on those original sections. -/
theorem schemeKernelGeneratorsMap_app_surjective (U : Y.Opens)
    (hker : RingHom.ker (f.app U).hom =
      Ideal.span (Set.range (fun i =>
        Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (d i)))) :
    Function.Surjective ((schemeKernelGeneratorsMap f d hd).val.app (op U)) := by
  let α := ((schemeKernelGeneratorsMap f d hd ≫ schemeKernelIdealι f).val.app
    (op U)).hom
  have hspan : Ideal.span (Set.range (fun i =>
      Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (d i))) ≤
      LinearMap.range α := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨(Sigma.ι (fun _ : I => _root_.SheafOfModules.unit Y.ringCatSheaf)
      i).val.app (op U) (1 : Γ(Y, U)), ?_⟩
    exact (congrArg
      (fun q : End (_root_.SheafOfModules.unit Y.ringCatSheaf) =>
        q.val.app (op U) (1 : Γ(Y, U)))
      (schemeKernelGeneratorsMap_comp_ι f d hd i)).trans
        (by simp only [schemeScalarEnd_app, one_mul])
  have hι : Function.Injective ((schemeKernelIdealι f).val.app (op U)) := by
    apply (ModuleCat.mono_iff_injective _).mp
    change Mono ((_root_.SheafOfModules.evaluation Y.ringCatSheaf (op U)).map
      (kernel.ι (structureToPushforwardUnit f)))
    infer_instance
  intro t
  have ht : (schemeKernelIdealι f).val.app (op U) t ∈ RingHom.ker (f.app U).hom := by
    change ((schemeKernelIdealι f ≫ structureToPushforwardUnit f).val.app (op U)) t = 0
    rw [schemeKernelIdealι_comp]
    rfl
  rw [hker] at ht
  obtain ⟨a, ha⟩ := hspan ht
  exact ⟨a, hι ha⟩

variable [IsAffine Y] [QuasiCompact f]

/-- Generation of the literal affine global kernel gives an actual
epimorphism, using localization on every original basic open. -/
theorem schemeKernelGeneratorsMap_epi
    (hgen : Ideal.span (Set.range d) = RingHom.ker f.appTop.hom) :
    Epi (schemeKernelGeneratorsMap f d hd) := by
  apply KltDP.SheafOfModules.epi_of_surjective_on_basis
    (schemeKernelGeneratorsMap f d hd) (isBasis_basicOpen Y)
  intro r
  apply schemeKernelGeneratorsMap_app_surjective f d hd (Y.basicOpen r)
  rw [schemeKernel_basicOpen f r, ← hgen, Ideal.map_span]
  congr 1
  ext a
  constructor
  · rintro ⟨b, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨d i, ⟨i, rfl⟩, rfl⟩

/-- A finitely generated literal affine section kernel produces an
actual finite-free epimorphism onto the original ideal sheaf. -/
theorem exists_finite_free_epi_schemeKernelIdeal_of_fg
    (hfg : (RingHom.ker f.appTop.hom).FG) :
    ∃ (I : Type u) (_ : Finite I)
      (p : _root_.SheafOfModules.free (R := Y.ringCatSheaf) I ⟶
        schemeKernelIdeal f), Epi p := by
  obtain ⟨I, hI, d, hgen⟩ :
      ∃ (I : Type u) (_ : Finite I) (d : I → Γ(Y, ⊤)),
        Ideal.span (Set.range d) = RingHom.ker f.appTop.hom :=
    Submodule.fg_iff_exists_finite_generating_family.mp hfg
  letI := hI
  have hd : ∀ i, f.appTop (d i) = 0 := by
    intro i
    apply RingHom.mem_ker.mp
    rw [← hgen]
    exact Ideal.subset_span (Set.mem_range_self i)
  exact ⟨I, hI, schemeKernelGeneratorsMap f d hd,
    schemeKernelGeneratorsMap_epi f d hd hgen⟩

/-- On a locally Noetherian affine target the finite equations are
derived from Noetherianity of the actual global section ring. -/
theorem exists_finite_free_epi_schemeKernelIdeal [IsLocallyNoetherian Y] :
    ∃ (I : Type u) (_ : Finite I)
      (p : _root_.SheafOfModules.free (R := Y.ringCatSheaf) I ⟶
        schemeKernelIdeal f), Epi p := by
  letI : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  exact exists_finite_free_epi_schemeKernelIdeal_of_fg f
    (IsNoetherian.noetherian (RingHom.ker f.appTop.hom))

end KltDP.Geometry
