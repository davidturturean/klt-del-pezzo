import KltDP.Geometry.TransitionUnitExtraction

/-!
# The nonvanishing open of an original invertible-sheaf section

The original local rank-one coordinates define basic opens that agree on
every overlap, including between different actual atlases. Their union is
therefore independent of the atlas. Its intersection with any original
chart is exactly the basic open of that section's original coefficient.

The transition units and restriction equations are the accepted actual
coordinate constructions. No transition, open-compatibility, nonzero-section,
integrality, coherence or ampleness hypothesis is imposed. This constructs
the open needed for twisted section extension; global extension and an
actual Serre-ample witness are separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSectionNonvanishingOpen

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitExtraction TransitionUnitGluing

variable (X : Scheme.{u}) (M : X.Modules)

local instance originalSectionModule (V : X.Opens) :
    Module Γ(X, V) (M.val.obj (op V)) := (M.val.obj (op V)).isModule

variable (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)

/-- The literal original section coefficient in the chosen original chart. -/
def chartCoefficient (s : M.sections) (i : t.I) : Γ(X, t.X i) :=
  chartEquiv X M t i (le_refl (t.X i)) (s.val (op (t.X i)))

/-- On every subopen, the chart coefficient restricts to the coordinate
of the original compatible section there. -/
theorem chartCoefficient_restrict (s : M.sections) (i : t.I)
    {V : X.Opens} (hVi : V ≤ t.X i) :
    res X hVi (chartCoefficient X M t s i) =
      chartEquiv X M t i hVi (s.val (op V)) := by
  have h := chartEquiv_restrict X M t i hVi (le_refl (t.X i))
    (s.val (op (t.X i)))
  have hs : M.val.map (homOfLE hVi).op (s.val (op (t.X i))) = s.val (op V) :=
    s.property (homOfLE hVi).op
  exact h.symm.trans (congrArg (chartEquiv X M t i hVi) hs)

set_option maxHeartbeats 800000 in
/-- The coefficient basic opens agree on overlaps of any two original
rank-one atlases. The coordinate-change unit is constructed from their
actual linear equivalences. -/
theorem basicOpen_overlap
    (d : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)
    (s : M.sections) (i : t.I) (j : d.I) :
    (t.X i ⊓ d.X j) ⊓ X.basicOpen (chartCoefficient X M t s i) =
      (t.X i ⊓ d.X j) ⊓ X.basicOpen (chartCoefficient X M d s j) := by
  let W : X.Opens := t.X i ⊓ d.X j
  let ei := chartEquiv X M t i (inf_le_left : W ≤ t.X i)
  let ej := chartEquiv X M d j (inf_le_right : W ≤ d.X j)
  let a : Γ(X, W)ˣ := KltDP.Module.transitionUnit ej ei
  have hc : res X (inf_le_left : W ≤ t.X i) (chartCoefficient X M t s i) =
      (a : Γ(X, W)) *
        res X (inf_le_right : W ≤ d.X j) (chartCoefficient X M d s j) := by
    rw [chartCoefficient_restrict, chartCoefficient_restrict]
    exact (KltDP.Module.transitionUnit_mul_apply ej ei (s.val (op W))).symm
  have hi : X.basicOpen
      (res X (inf_le_left : W ≤ t.X i) (chartCoefficient X M t s i)) =
      W ⊓ X.basicOpen (chartCoefficient X M t s i) :=
    X.basicOpen_res (chartCoefficient X M t s i)
      (homOfLE (inf_le_left : W ≤ t.X i)).op
  have hj : X.basicOpen
      (res X (inf_le_right : W ≤ d.X j) (chartCoefficient X M d s j)) =
      W ⊓ X.basicOpen (chartCoefficient X M d s j) :=
    X.basicOpen_res (chartCoefficient X M d s j)
      (homOfLE (inf_le_right : W ≤ d.X j)).op
  have h := congrArg (fun b : Γ(X, W) => X.basicOpen b) hc
  dsimp only at h
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit X a.isUnit, hi, hj] at h
  simpa only [inf_left_idem] using h

/-- Union of the actual nonvanishing coefficient opens in an original atlas. -/
def nonvanishingOpenOfAtlas (s : M.sections) : X.Opens :=
  ⨆ i, X.basicOpen (chartCoefficient X M t s i)

/-- The union restricts on each original chart to its literal coefficient
basic open; the compatibility is proved, not supplied. -/
theorem chart_inf_nonvanishingOpenOfAtlas (s : M.sections) (i : t.I) :
    t.X i ⊓ nonvanishingOpenOfAtlas X M t s =
      X.basicOpen (chartCoefficient X M t s i) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx.2
    have hmem : x ∈ (t.X i ⊓ t.X j) ⊓
        X.basicOpen (chartCoefficient X M t s j) :=
      ⟨⟨hx.1, X.basicOpen_le _ hj⟩, hj⟩
    rw [← basicOpen_overlap X M t t s i j] at hmem
    exact hmem.2
  · intro x hx
    exact ⟨X.basicOpen_le _ hx, Opens.mem_iSup.mpr ⟨i, hx⟩⟩

private theorem nonvanishingOpenOfAtlas_le
    (d : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)
    (s : M.sections) :
    nonvanishingOpenOfAtlas X M t s ≤ nonvanishingOpenOfAtlas X M d s := by
  intro x hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  have hxcover : x ∈ (⨆ j, d.X j) := by
    rw [chartOpens_cover X M d]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxcover
  have hmem : x ∈ (t.X i ⊓ d.X j) ⊓
      X.basicOpen (chartCoefficient X M t s i) :=
    ⟨⟨X.basicOpen_le _ hi, hj⟩, hi⟩
  rw [basicOpen_overlap X M t d s i j] at hmem
  exact Opens.mem_iSup.mpr ⟨j, hmem.2⟩

/-- Any two actual atlases yield the same nonvanishing open of the
original section. -/
theorem nonvanishingOpenOfAtlas_eq
    (d : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)
    (s : M.sections) :
    nonvanishingOpenOfAtlas X M t s = nonvanishingOpenOfAtlas X M d s :=
  le_antisymm (nonvanishingOpenOfAtlas_le X M t d s)
    (nonvanishingOpenOfAtlas_le X M d t s)

/-- The nonvanishing open of an actual invertible-sheaf section, using
its already constructed local rank-one atlas. -/
def nonvanishingOpen (L : InvertibleSheaf X) (s : L.obj.sections) : X.Opens :=
  nonvanishingOpenOfAtlas X L.obj L.localTrivializations s

/-- In any actual local atlas of the original invertible sheaf, the
intrinsic open has exactly the original coefficient's basic open. -/
theorem chart_inf_nonvanishingOpen (L : InvertibleSheaf X) (s : L.obj.sections)
    (d : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) L.obj)
    (i : d.I) :
    d.X i ⊓ nonvanishingOpen X L s = X.basicOpen (chartCoefficient X L.obj d s i) := by
  rw [nonvanishingOpen, nonvanishingOpenOfAtlas_eq X L.obj L.localTrivializations d s]
  exact chart_inf_nonvanishingOpenOfAtlas X L.obj d s i

/-- On every actual chart, membership means that the original coefficient
germ is a unit in the original local ring. -/
theorem mem_nonvanishingOpen_iff_isUnit_germ (L : InvertibleSheaf X) (s : L.obj.sections)
    (d : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) L.obj)
    (i : d.I) (x : X) (hx : x ∈ d.X i) :
    x ∈ nonvanishingOpen X L s ↔
      IsUnit (X.presheaf.germ (d.X i) x hx (chartCoefficient X L.obj d s i)) := by
  have h : x ∈ nonvanishingOpen X L s ↔ x ∈ d.X i ⊓ nonvanishingOpen X L s :=
    ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  rw [chart_inf_nonvanishingOpen X L s d i] at h
  exact h.trans (X.mem_basicOpen (chartCoefficient X L.obj d s i) x hx)

end KltDP.Geometry.InvertibleSectionNonvanishingOpen
