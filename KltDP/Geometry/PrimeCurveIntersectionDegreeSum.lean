import KltDP.Geometry.PrimeCurveCartierRestriction
import KltDP.Geometry.SchemeDisjointCoverSections
import KltDP.Geometry.SurfaceEulerSections

/-!
# The intersection degree as a sum over a disjoint open cover

`intersectionDegree` is the `k`-dimension of `H⁰(C ∩ D, O)`; by the accepted `H⁰`
comparison this is the `k`-dimension of `Γ(C ∩ D, ⊤)` for the action through the
structure morphism. For a finite family of pairwise disjoint opens covering the
intersection subscheme, the disjoint-cover decomposition gives
`intersectionDegree = Σ_i dim_k Γ(C ∩ D, V i)`.

Choosing such a cover separating the finitely many intersection points, and the
identification of each `Γ(C ∩ D, V i)` with the local contribution
`O_{C,y} ⧸ (d|_C)`, are recorded as remaining steps in `F03_RESTRICTION_ADAPTERS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of k))

/-- Global sections of the structure module are the global sections of the structure
sheaf, `k`-linearly for the actions through the structure morphism. -/
def sectionsUnitLinearEquiv :
    letI := ModuleCohomology.baseSectionsModule f (_root_.SheafOfModules.unit Z.ringCatSheaf)
    letI := Module.compHom Γ(Z, ⊤) (baseFieldToGlobalSections f)
    ModuleCohomology.sections (_root_.SheafOfModules.unit Z.ringCatSheaf) ≃ₗ[k] Γ(Z, ⊤) := by
  letI := ModuleCohomology.baseSectionsModule f (_root_.SheafOfModules.unit Z.ringCatSheaf)
  letI := Module.compHom Γ(Z, ⊤) (baseFieldToGlobalSections f)
  exact
    { toFun := fun s => s
      invFun := fun s => s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- `dim_k H⁰(Z, O) = dim_k Γ(Z, ⊤)` for the action through the structure morphism. -/
theorem cohomologyDimension_zero_unit_eq_finrank :
    letI := Module.compHom Γ(Z, ⊤) (baseFieldToGlobalSections f)
    ModuleCohomology.cohomologyDimension f (_root_.SheafOfModules.unit Z.ringCatSheaf) 0 =
      Module.finrank k Γ(Z, ⊤) := by
  letI := ModuleCohomology.baseSectionsModule f (_root_.SheafOfModules.unit Z.ringCatSheaf)
  letI := Module.compHom Γ(Z, ⊤) (baseFieldToGlobalSections f)
  exact (ModuleCohomology.cohomologyDimension_zero_eq_finrank_sections f _).trans
    (sectionsUnitLinearEquiv f).finrank_eq

/-- Finite-dimensional `H⁰` gives finite-dimensional global sections of the structure sheaf. -/
theorem finite_sections_of_hZero
    (hfin : FiniteDimensional k ((ModuleCohomology.baseFunctor f 0).obj
      (_root_.SheafOfModules.unit Z.ringCatSheaf))) :
    letI := Module.compHom Γ(Z, ⊤) (baseFieldToGlobalSections f)
    Module.Finite k Γ(Z, ⊤) := by
  letI := ModuleCohomology.baseSectionsModule f (_root_.SheafOfModules.unit Z.ringCatSheaf)
  letI := Module.compHom Γ(Z, ⊤) (baseFieldToGlobalSections f)
  haveI := ModuleCohomology.sections_finiteDimensional_of_hZero f
    (_root_.SheafOfModules.unit Z.ringCatSheaf) hfin
  exact Module.Finite.equiv (sectionsUnitLinearEquiv f)

/-- `dim_k H⁰(Z, O)` is the sum of the `k`-dimensions of the sections over a finite
pairwise disjoint open cover. -/
theorem cohomologyDimension_zero_unit_eq_sum {ι : Type u} [Fintype ι] (V : ι → Z.Opens)
    (hcover : (⨆ i, V i) = ⊤) (hdisj : Pairwise fun i j => V i ⊓ V j = ⊥)
    (hfin : FiniteDimensional k ((ModuleCohomology.baseFunctor f 0).obj
      (_root_.SheafOfModules.unit Z.ringCatSheaf))) :
    letI : ∀ i, Module k Γ(Z, V i) := fun i => sectionsBaseModule Z (baseFieldToGlobalSections f) (V i)
    ModuleCohomology.cohomologyDimension f (_root_.SheafOfModules.unit Z.ringCatSheaf) 0 =
      ∑ i, Module.finrank k Γ(Z, V i) := by
  letI := Module.compHom Γ(Z, ⊤) (baseFieldToGlobalSections f)
  letI : ∀ i, Module k Γ(Z, V i) := fun i => sectionsBaseModule Z (baseFieldToGlobalSections f) (V i)
  exact (cohomologyDimension_zero_unit_eq_finrank f).trans
    (finrank_sections_eq_sum Z V (baseFieldToGlobalSections f) hcover hdisj
      (finite_sections_of_hZero f hfin))

end KltDP.Geometry

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
  (hC : C.NotInSupport D hD)

/-- The structure morphism of the intersection subscheme over the base field. -/
def intersectionToSpec : C.intersectionScheme D hD hC ⟶ Spec (CommRingCat.of k) :=
  effectiveCartierToSpec C.toScheme (C.restrictCartier D hD hC)
    (C.restrictCartier_hasRegularEquations D hD hC) C.toSpec

/-- `intersectionDegree = dim_k Γ(C ∩ D, ⊤)` for the action through the structure morphism. -/
theorem intersectionDegree_eq_finrank_sections :
    letI := Module.compHom Γ(C.intersectionScheme D hD hC, ⊤)
      (baseFieldToGlobalSections (C.intersectionToSpec D hD hC))
    C.intersectionDegree D hD hC = Module.finrank k Γ(C.intersectionScheme D hD hC, ⊤) :=
  cohomologyDimension_zero_unit_eq_finrank (C.intersectionToSpec D hD hC)

/-- The sum formula over a finite pairwise disjoint open cover of the intersection subscheme:
`intersectionDegree = Σ_i dim_k Γ(C ∩ D, V i)`. -/
theorem intersectionDegree_eq_sum_of_disjoint_cover {ι : Type u} [Fintype ι]
    (V : ι → (C.intersectionScheme D hD hC).Opens)
    (hcover : (⨆ i, V i) = ⊤) (hdisj : Pairwise fun i j => V i ⊓ V j = ⊥) :
    letI : ∀ i, Module k Γ(C.intersectionScheme D hD hC, V i) := fun i =>
      sectionsBaseModule (C.intersectionScheme D hD hC)
        (baseFieldToGlobalSections (C.intersectionToSpec D hD hC)) (V i)
    C.intersectionDegree D hD hC = ∑ i, Module.finrank k Γ(C.intersectionScheme D hD hC, V i) :=
  cohomologyDimension_zero_unit_eq_sum (C.intersectionToSpec D hD hC) V hcover hdisj
    (C.intersectionDegree_finiteDimensional D hD hC)

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
