import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.Topology.Sheaves.Sheaf

/-!
# The actual quotient sheaf and its local representatives

For a morphism of sheaves of abelian groups on a topological space, the
quotient sheaf is the categorical cokernel. This adapter reuses pinned
Mathlib's abelian sheaf category, `cokernel.π`, and
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`. The latter theorem
turns the cokernel projection's epimorphism into local surjectivity.

The neighborhood statement is obtained from `Presheaf.imageSieve_mem`
and the actual open-set Grothendieck topology. In particular, it does not
identify sections of a quotient sheaf with pointwise quotient groups or
assume that quotient sections have global representatives.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace KltDP.Sheaf

/-- The pinned topological sheaf category is a definition of the actual
site sheaf category. Expose its existing abelian structure across that
definition so that its zero morphisms, kernels and cokernels are available. -/
instance topCatSheafAddCommGrpAbelian (X : TopCat.{u}) :
    Abelian (TopCat.Sheaf AddCommGrp.{u} X) :=
  inferInstanceAs (Abelian
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}))

variable {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrp.{u} X} (φ : F ⟶ G)

/-- The categorical cokernel in the actual category of sheaves. -/
abbrev quotientSheaf : TopCat.Sheaf AddCommGrp.{u} X :=
  cokernel φ

/-- The canonical morphism from the target sheaf to its quotient. -/
abbrev toQuotientSheaf : G ⟶ quotientSheaf φ :=
  cokernel.π φ

/-- The defining relation of the actual sheaf cokernel. -/
@[simp]
theorem toQuotientSheaf_condition : φ ≫ toQuotientSheaf φ = 0 :=
  cokernel.condition φ

instance toQuotientSheaf_epi : Epi (toQuotientSheaf φ) := by
  dsimp only [toQuotientSheaf]
  infer_instance

/-- Every section of the cokernel is locally represented by a section of `G`. -/
theorem toQuotientSheaf_isLocallySurjective :
    CategoryTheory.Sheaf.IsLocallySurjective (toQuotientSheaf φ) :=
  (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrp.{u})
    (toQuotientSheaf φ)).2 inferInstance

/-- A quotient section has an actual representative near each point of its domain. -/
theorem exists_local_quotient_representative (U : Opens X)
    (s : (quotientSheaf φ).val.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (i : V ⟶ U) (r : G.val.obj (op V)),
      x ∈ V ∧ (toQuotientSheaf φ).val.app (op V) r =
        (quotientSheaf φ).val.map i.op s := by
  letI : CategoryTheory.Sheaf.IsLocallySurjective (toQuotientSheaf φ) :=
    toQuotientSheaf_isLocallySurjective φ
  obtain ⟨V, i, ⟨r, hr⟩, hxV⟩ :=
    (CategoryTheory.Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
      (toQuotientSheaf φ).val s) x hx
  exact ⟨V, i, r, hxV, hr⟩

end KltDP.Sheaf
