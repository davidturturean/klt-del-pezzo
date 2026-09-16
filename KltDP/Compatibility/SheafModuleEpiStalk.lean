import KltDP.Compatibility.SheafModuleExactness
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Epimorphisms of actual module sheaves are locally and stalkwise surjective

The accepted `KltDP.Sheaf.toSheaf_preservesFiniteColimits` already supplies the
forgetful step from module sheaves to additive sheaves.  Composing it with the
pinned site's epimorphism criterion proves local lifting, and the pinned
topological stalk criterion then proves surjectivity on the actual additive
stalks.  No pointwise-surjectivity hypothesis or new mathematical axiom is used.

This file also records colimit preservation of the additive-stalk functor.  It
is the composition of the accepted forgetful colimit theorem with the pinned
stalk/skyscraper adjunction; in particular it applies to the actual coproduct
used by `SheafOfModules.free`.

For global generation of an invertible sheaf, the next adapter must show that
one generating section has a *unit coefficient* at a specified point.  A
merely nonzero germ in a local ring does not prove that assertion.
-/

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace KltDP.SheafModuleEpiStalk

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  {M N : _root_.SheafOfModules.{u} R}

/-- The underlying additive-sheaf map of a module-sheaf epimorphism is epi.
The preservation instance comes from actual finite-colimit preservation. -/
theorem toSheaf_map_epi (f : M ⟶ N) [Epi f] :
    Epi ((_root_.SheafOfModules.toSheaf R).map f) := by
  infer_instance

/-- An epimorphism of module sheaves is locally surjective on its original
presheaf sections, after forgetting only their scalar action. -/
theorem locallySurjective_of_epi (f : M ⟶ N) [Epi f] :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f.val := by
  letI := toSheaf_map_epi f
  exact (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrp.{u})
    ((_root_.SheafOfModules.toSheaf R).map f)).2 inferInstance

/-- A section of the target of a module-sheaf epimorphism has an actual
source-section representative on a neighbourhood of every point. -/
theorem exists_local_lift_of_epi (f : M ⟶ N) [Epi f]
    (U : Opens X) (s : N.val.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (i : V ⟶ U) (t : M.val.obj (op V)),
      x ∈ V ∧ f.val.app (op V) t = N.val.map i.op s := by
  letI := locallySurjective_of_epi f
  obtain ⟨V, i, ⟨t, ht⟩, hxV⟩ :=
    (CategoryTheory.Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
      ((_root_.PresheafOfModules.toPresheaf R.val).map f.val) s) x hx
  exact ⟨V, i, t, hxV, ht⟩

/-- An epimorphism of module sheaves is surjective on every actual additive
stalk, with local representatives supplied by the preceding theorem. -/
theorem stalkMap_surjective_of_epi (f : M ⟶ N) [Epi f] (x : X) :
    Function.Surjective ((TopCat.Presheaf.stalkFunctor AddCommGrp.{u} x).map
      ((_root_.PresheafOfModules.toPresheaf R.val).map f.val)) := by
  exact (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).1
    (locallySurjective_of_epi f) x

/-- Taking the underlying additive stalk of an actual module sheaf. -/
def additiveStalkFunctor (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X) :
    _root_.SheafOfModules.{u} R ⥤ AddCommGrp.{u} :=
  _root_.SheafOfModules.toSheaf R ⋙
    (TopCat.Sheaf.forget AddCommGrp.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrp.{u} x)

/-- Additive stalks preserve arbitrary small colimits of actual module
sheaves, including their free coproducts. -/
theorem additiveStalkFunctor_preservesColimits (x : X) :
    PreservesColimitsOfSize.{u, u} (additiveStalkFunctor R x) := by
  classical
  letI : PreservesColimitsOfSize.{u, u} (_root_.SheafOfModules.toSheaf R) :=
    { preservesColimitsOfShape := by
        intro K hK
        exact KltDP.Sheaf.toSheaf_preservesColimitsOfShape R K }
  letI : PreservesColimitsOfSize.{u, u}
      (TopCat.Sheaf.forget AddCommGrp.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrp.{u} x) :=
    (_root_.stalkSkyscraperSheafAdjunction (C := AddCommGrp.{u}) x).leftAdjoint_preservesColimits
  unfold additiveStalkFunctor
  infer_instance

/-- Every stalk of an identity module-sheaf epimorphism is surjective;
this supplies a witness without any assumptions on point dimensions. -/
theorem identity_stalk_surjective (M : _root_.SheafOfModules.{u} R) (x : X) :
    Function.Surjective ((additiveStalkFunctor R x).map (𝟙 M)) := by
  rw [CategoryTheory.Functor.map_id]
  exact Function.surjective_id

end KltDP.SheafModuleEpiStalk
