import KltDP.Geometry.LinearSystemRationalMap
import Mathlib.AlgebraicGeometry.Properties

/-!
# A nonzero original section has a nonempty nonvanishing open

On a reduced scheme, an empty basic open forces its original coefficient
to vanish. Applying this in the existing local frames and using sheaf
uniqueness shows that an original section with empty nonvanishing open
has zero top value. Thus an actual nonzero coordinate of a finite tuple
makes its original non-base open nonempty. No properness, degree or
global-generation hypothesis is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitExtraction InvertibleSectionNonvanishingOpen

namespace InvertibleSectionNonvanishingOpen

private theorem chartCoefficient_eq_zero_of_open_eq_bot
    (X : Scheme.{u}) [IsReduced X] (L : InvertibleSheaf X)
    (s : L.obj.sections)
    (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) L.obj)
    (i : t.I) (hbot : nonvanishingOpen X L s = ⊥) :
    chartCoefficient X L.obj t s i = 0 := by
  apply eq_zero_of_basicOpen_eq_bot
  rw [← chart_inf_nonvanishingOpen X L s t i, hbot, inf_bot_eq]

private theorem chart_value_eq_zero_of_coefficient_eq_zero
    (X : Scheme.{u}) (M : X.Modules)
    (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)
    (s : M.sections) (i : t.I) (hi : chartCoefficient X M t s i = 0) :
    (show M.val.obj (op (t.X i)) from s.val (op (t.X i))) = 0 := by
  apply (chartEquiv X M t i le_rfl).injective
  exact hi.trans (map_zero (chartEquiv X M t i le_rfl)).symm

private theorem top_value_eq_zero_of_chart_values_eq_zero
    (X : Scheme.{u}) (M : X.Modules)
    (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)
    (s : M.sections)
    (hs : ∀ i : t.I, (show M.val.obj (op (t.X i)) from s.val (op (t.X i))) = 0) :
    (show M.val.obj (op (⊤ : X.Opens)) from s.val (op ⊤)) = 0 := by
  apply TopCat.Sheaf.eq_of_locally_eq' (X := (X : TopCat)) (C := AddCommGrp.{u})
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    t.X ⊤ (fun _ => homOfLE le_top) (chartOpens_cover X M t).ge
  intro i
  change M.val.map (homOfLE (le_top : t.X i ≤ ⊤)).op (s.val (op ⊤)) =
    M.val.map (homOfLE (le_top : t.X i ≤ ⊤)).op 0
  have hsres : M.val.map (homOfLE (le_top : t.X i ≤ ⊤)).op (s.val (op ⊤)) =
      s.val (op (t.X i)) := s.property (homOfLE (le_top : t.X i ≤ ⊤)).op
  exact hsres.trans ((hs i).trans (map_zero
    (M.val.map (homOfLE (le_top : t.X i ≤ ⊤)).op).hom).symm)

/-- A nonzero original top section has a nonempty intrinsic nonvanishing
open on any reduced scheme. -/
theorem nonvanishingOpen_nonempty_of_top_ne_zero (X : Scheme.{u}) [IsReduced X]
    (L : InvertibleSheaf X) (s : L.obj.sections)
    (hs : s.val (op (⊤ : X.Opens)) ≠ 0) :
    (nonvanishingOpen X L s : Set X).Nonempty := by
  classical
  by_contra h
  have hbot := (Opens.not_nonempty_iff_eq_bot (nonvanishingOpen X L s)).mp h
  apply hs
  apply top_value_eq_zero_of_chart_values_eq_zero X L.obj L.localTrivializations s
  intro i
  exact chart_value_eq_zero_of_coefficient_eq_zero X L.obj L.localTrivializations s i
    (chartCoefficient_eq_zero_of_open_eq_bot X L s L.localTrivializations i hbot)

end InvertibleSectionNonvanishingOpen

namespace LinearSystemRationalMap

/-- An actual nonzero top coordinate makes the original finite system's
non-base open nonempty, including without generation on the source. -/
theorem nonBaseOpen_nonempty_of_top_ne_zero {X : Scheme.{u}} [IsReduced X]
    (L : InvertibleSheaf X) {n : ℕ} (s : Fin (n + 1) → L.obj.sections)
    (i : Fin (n + 1)) (hi : (s i).val (op (⊤ : X.Opens)) ≠ 0) :
    (nonBaseOpen L s : Set X).Nonempty := by
  obtain ⟨x, hx⟩ := nonvanishingOpen_nonempty_of_top_ne_zero X L (s i) hi
  exact ⟨x, Opens.mem_iSup.mpr ⟨i, hx⟩⟩

end LinearSystemRationalMap

end KltDP.Geometry
