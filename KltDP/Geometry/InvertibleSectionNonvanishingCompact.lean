import KltDP.Geometry.InvertibleSectionNonvanishingOpen
import KltDP.Geometry.AffineOpenRefinement
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Finite actual affine frames and quasi-compact nonvanishing opens

The accepted affine refinement of the original rank-one atlas has an
actual finite subcover on a quasi-compact scheme. Every selected open
retains its original restricted frame. On each such affine open the
intrinsic nonvanishing open is the basic open of the literal restricted
coefficient. Its finite union is consequently quasi-compact.

All covers and frames are constructed from the original local triviality.
No affine triviality of the original charts, separatedness, integrality,
or nonzero-section hypothesis is imposed. These are cover prerequisites
for twisted section extension; they do not yet glue those extensions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSectionNonvanishingCompact

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitExtraction InvertibleSectionNonvanishingOpen

variable (X : Scheme.{u}) (M : X.Modules)
  (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)

/-- A finite subcover of the already constructed actual affine refinement. -/
theorem exists_finite_affine_refinement (hX : IsCompact (Set.univ : Set X)) :
    ∃ S : Finset (AffineOpenRefinement.Index X t.X),
      (⨆ a : S, AffineOpenRefinement.opens X t.X a.val) = ⊤ := by
  classical
  have hc : (Set.univ : Set X) ⊆
      ⋃ a : AffineOpenRefinement.Index X t.X,
        (AffineOpenRefinement.opens X t.X a : Set X) := by
    intro x hx
    have hx' : x ∈ ⨆ a, AffineOpenRefinement.opens X t.X a := by
      rw [AffineOpenRefinement.covers X t.X (chartOpens_cover X M t)]
      exact hx
    exact Set.mem_iUnion.mpr (Opens.mem_iSup.mp hx')
  obtain ⟨S, hS⟩ := hX.elim_finite_subcover
    (fun a : AffineOpenRefinement.Index X t.X =>
      (AffineOpenRefinement.opens X t.X a : Set X))
    (fun a => (AffineOpenRefinement.opens X t.X a).2) hc
  refine ⟨S, top_unique ?_⟩
  intro x hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hS hx)
  exact Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hxa⟩

/-- Every actual subordinate affine open carries the original restricted frame. -/
def refinementFrame (a : AffineOpenRefinement.Index X t.X) :
    M.over (AffineOpenRefinement.opens X t.X a) ≅
      _root_.SheafOfModules.unit
        (X.ringCatSheaf.over (AffineOpenRefinement.opens X t.X a)) :=
  t.unitIsoOver (AffineOpenRefinement.original X t.X a)
    (homOfLE (AffineOpenRefinement.subordinate X t.X a))

variable (L : InvertibleSheaf X) (s : L.obj.sections)

/-- On any actual subopen of an original chart, the intrinsic nonvanishing
open is the basic open of the original restricted coefficient. -/
theorem subopen_inf_nonvanishingOpen
    (d : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) L.obj)
    (i : d.I) {V : X.Opens} (hVi : V ≤ d.X i) :
    V ⊓ nonvanishingOpen X L s =
      X.basicOpen (X.presheaf.map (homOfLE hVi).op (chartCoefficient X L.obj d s i)) := by
  calc
    V ⊓ nonvanishingOpen X L s = (V ⊓ d.X i) ⊓ nonvanishingOpen X L s := by
      rw [inf_eq_left.mpr hVi]
    _ = V ⊓ X.basicOpen (chartCoefficient X L.obj d s i) := by
      rw [inf_assoc, chart_inf_nonvanishingOpen X L s d i]
    _ = _ := (X.basicOpen_res (chartCoefficient X L.obj d s i) (homOfLE hVi).op).symm

/-- The actual nonvanishing open of an invertible-sheaf section on a
quasi-compact scheme is quasi-compact, without a separatedness assumption. -/
theorem isCompact_nonvanishingOpen (hX : IsCompact (Set.univ : Set X)) :
    IsCompact (nonvanishingOpen X L s : Set X) := by
  classical
  let d := L.localTrivializations
  obtain ⟨S, hS⟩ := exists_finite_affine_refinement X L.obj d hX
  have heq : (nonvanishingOpen X L s : Set X) =
      ⋃ a : S,
        (AffineOpenRefinement.opens X d.X a.val ⊓ nonvanishingOpen X L s : Set X) := by
    ext x
    constructor
    · intro hx
      have hxc : x ∈ ⨆ a : S, AffineOpenRefinement.opens X d.X a.val := by
        rw [hS]
        trivial
      obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hxc
      exact Set.mem_iUnion.mpr ⟨a, ha, hx⟩
    · intro hx
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
      exact ha.2
  rw [heq]
  apply isCompact_iUnion
  intro a
  exact (congrArg (fun V : X.Opens => IsCompact (V : Set X))
    (subopen_inf_nonvanishingOpen X L s d
      (AffineOpenRefinement.original X d.X a.val)
      (AffineOpenRefinement.subordinate X d.X a.val))).mpr
    ((AffineOpenRefinement.affine X d.X a.val).basicOpen _).isCompact

end KltDP.Geometry.InvertibleSectionNonvanishingCompact
