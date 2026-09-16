import KltDP.Geometry.SchemeConormal
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The actual ideal sequence of a rational point

For a section whose source has at most one point, the original structural
map is surjective on every open. The section identity first supplies a
right inverse on global functions. Every section on an open of the source
extends globally, since that open is either empty or the whole source.
Naturality then gives surjectivity on the original target open.

The resulting short exact sequence uses the previously defined categorical
kernel and its original inclusion. No replacement ideal, quotient, scalar
action, or exactness hypothesis is introduced. In particular the construction
applies to an actual rational point with source `Spec k`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalPointIdeal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- On a scheme with at most one point, every section on an open extends
to a global section of the original structure sheaf. -/
theorem topRestriction_surjective (S : Scheme.{u}) [Subsingleton S] (U : S.Opens) :
    Function.Surjective
      (S.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  classical
  by_cases hU : Nonempty U
  · obtain ⟨x⟩ := hU
    have htop : U = ⊤ := by
      apply top_unique
      intro y _
      have hy : y = x.1 := Subsingleton.elim _ _
      simpa only [hy] using x.2
    subst U
    have hid : (homOfLE (show (⊤ : S.Opens) ≤ ⊤ from le_top)).op =
        𝟙 (op (⊤ : S.Opens)) := Subsingleton.elim _ _
    rw [hid, S.presheaf.map_id]
    exact Function.surjective_id
  · have hbot : U = ⊥ := by
      apply SetLike.ext
      intro x
      exact ⟨fun hx => (hU ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    subst U
    exact fun s => ⟨0, Subsingleton.elim _ _⟩

variable {S X : Scheme.{u}} (i : S ⟶ X) (f : X ⟶ S) (hi : i ≫ f = 𝟙 S)

include f hi in
/-- The actual section identity supplies a right inverse on global sections. -/
theorem appTop_surjective : Function.Surjective i.appTop := by
  have h : f.appTop ≫ i.appTop = 𝟙 (Γ(S, ⊤)) := by
    rw [← Scheme.comp_appTop, hi, Scheme.id_appTop]
  intro s
  exact ⟨f.appTop s, ConcreteCategory.congr_hom h s⟩

include f hi in
/-- Naturality extends the global surjectivity to every original target open. -/
theorem app_surjective [Subsingleton S] (U : X.Opens) :
    Function.Surjective (i.app U) := by
  intro s
  obtain ⟨t, ht⟩ := topRestriction_surjective S (i ⁻¹ᵁ U) s
  obtain ⟨r, hr⟩ := appTop_surjective i f hi t
  refine ⟨X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r, ?_⟩
  calc
    i.app U (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) =
        S.presheaf.map (homOfLE (show i ⁻¹ᵁ U ≤ ⊤ from le_top)).op (i.appTop r) :=
      ConcreteCategory.congr_hom
        (i.naturality (homOfLE (show U ≤ ⊤ from le_top)).op) r
    _ = s := by rw [hr, ht]

include f hi in
/-- The structural morphism of the original module sheaves is an epimorphism. -/
theorem structureToPushforwardUnit_epi [Subsingleton S] :
    Epi (structureToPushforwardUnit i) := by
  constructor
  intro M g h hcomp
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  obtain ⟨r, hr⟩ := app_surjective i f hi U.unop s
  subst s
  exact congrArg
    (fun q : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ M => q.val.app U r) hcomp

/-- The literal kernel/inclusion/structural-map sequence attached to `i`. -/
def idealSequence : ShortComplex X.Modules :=
  ShortComplex.mk (schemeKernelIdealι i) (structureToPushforwardUnit i)
    (schemeKernelIdealι_comp i)

/-- Exactness is the existing categorical-kernel theorem for the same map. -/
theorem idealSequence_exact : (idealSequence i).Exact :=
  ShortComplex.exact_kernel (structureToPushforwardUnit i)

include f hi in
/-- A section with one-point source gives the actual ideal short exact sequence. -/
theorem idealSequence_shortExact [Subsingleton S] : (idealSequence i).ShortExact := by
  letI := structureToPushforwardUnit_epi i f hi
  exact
    { exact := idealSequence_exact i
      mono_f := inferInstanceAs (Mono (kernel.ι (structureToPushforwardUnit i)))
      epi_g := inferInstanceAs (Epi (structureToPushforwardUnit i)) }

end KltDP.Geometry.RationalPointIdeal
