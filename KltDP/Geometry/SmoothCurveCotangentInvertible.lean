import KltDP.Geometry.SmoothCurveCanonicalDegree
import KltDP.Geometry.SmoothFieldCharts
import KltDP.Compatibility.SheafLocalBasis
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Smooth of relative dimension one over a field ⇒ the cotangent sheaf is invertible

For `f : C ⟶ Spec k` smooth of relative dimension `1` (`IsSmoothOfRelativeDimension 1 f`), every
point has an affine open `V` whose section ring `A = Γ(C, V)` is standard smooth of relative
dimension `1` over `k` through the accepted `baseToAffineSectionsMap` (the pinned
`exists_isStandardSmoothOfRelativeDimension`, transported exactly as the accepted
`SmoothFieldCharts.standardSmooth_baseToAffineSectionsMap`). The pinned
`IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` gives `rank_A Ω[A/k] = 1` (`A` is
nontrivial because `V` is nonempty), so the chosen Kähler basis has a singleton index, the accepted
`affineFreeIsoOfBasis` trivialises `Ω` on `Spec A`, and the accepted transport of
`SmoothKaehlerLocallyFree.exists_standardSmooth_open_freeIso` carries the trivialisation to `V`.
Hence

  **`cotangentSheaf_isInvertible : IsInvertible (Ω_{C/k})`**, so `canonicalSheaf`, `canonicalClass`
  and the canonical degree of `SmoothCurveCanonicalDegree` are available for every curve smooth of
  relative dimension one over `k` without an invertibility hypothesis
  (`canonicalSheafOfSmooth`, `canonicalClassOfSmooth`).

Hypotheses: `k : Type u`, `[Field k]`, `f : C ⟶ Spec (CommRingCat.of k)`, `[IsSmoothOfRelativeDimension 1 f]`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open KltDP.Geometry.SchemeKaehlerSheaf KltDP.Geometry.SchemeKaehlerOpenRestriction
open KltDP.Geometry.SchemeModuleRestriction KltDP.Geometry.SmoothKaehlerLocallyFree

universe u

namespace KltDP.Geometry.SmoothCurveCotangent

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Bridge

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The accepted global-sections bridge, at fixed relative dimension. -/
theorem standardSmoothOfRelativeDimension_baseToAffineSectionsMap {V : X.Opens}
    (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ ⊤) (n : ℕ)
    (hsmooth : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE ⊤ V e).hom) :
    RingHom.IsStandardSmoothOfRelativeDimension n (baseToAffineSectionsMap f hV).hom := by
  let eR : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  have heR : RingHom.IsStandardSmoothOfRelativeDimension 0 eR.toRingHom :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv (R := R) eR
  have hcomp := hsmooth.comp heR
  rw [Nat.add_zero] at hcomp
  change RingHom.IsStandardSmoothOfRelativeDimension n
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ V e).hom) at hcomp
  rw [affineBaseSections_appLE_eq_baseToAffineSectionsMap f hV e] at hcomp
  exact hcomp

end Bridge

section Field

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (CommRingCat.of k))

/-- Around every point, an affine chart standard smooth of the given relative dimension over the
field (the base neighbourhood is all of `Spec k`, which has one point). -/
theorem exists_affine_standardSmoothOfRelativeDimension (n : ℕ)
    [IsSmoothOfRelativeDimension n f] (x : C) :
    ∃ (V : C.Opens) (hV : IsAffineOpen V), x ∈ V ∧
      RingHom.IsStandardSmoothOfRelativeDimension n (baseToAffineSectionsMap f hV).hom := by
  obtain ⟨⟨U, hU⟩, ⟨V, hV⟩, hx, e, hsmooth⟩ :=
    IsSmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (f := f) (n := n) x
  have htop : U = ⊤ := by
    apply le_antisymm le_top
    intro y _
    have hy : y = f.base x := Subsingleton.elim _ _
    simpa only [hy] using e hx
  subst U
  exact ⟨V, hV, hx, standardSmoothOfRelativeDimension_baseToAffineSectionsMap f hV e n hsmooth⟩

/-- The section ring of a nonempty affine open is nontrivial. -/
theorem nontrivial_sections_of_mem {V : C.Opens} (hV : IsAffineOpen V) {x : C} (hx : x ∈ V) :
    Nontrivial Γ(C, V) := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have hrange : x ∈ Set.range hV.fromSpec.base := by
    rw [hV.range_fromSpec]
    exact hx
  obtain ⟨p, -⟩ := hrange
  haveI : Subsingleton Γ(C, V) := hn
  exact ((inferInstance : IsEmpty (PrimeSpectrum Γ(C, V))).false p).elim

/-- On a standard-smooth chart of relative dimension one the differential sheaf is trivial. -/
theorem exists_unit_iso_of_standardSmoothOfRelativeDimension_one {V : C.Opens}
    (hV : IsAffineOpen V) {x : C} (hx : x ∈ V)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension 1 (baseToAffineSectionsMap f hV).hom) :
    Nonempty (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf ≅
      (restriction V.ι).obj (baseRingSheaf f)) := by
  let A := Γ(C, V)
  letI : Algebra k A := (baseToAffineSectionsMap f hV).hom.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 k A := hs.toAlgebra
  haveI : Algebra.IsStandardSmooth k A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := k) (S := A) 1
  haveI : Nontrivial A := nontrivial_sections_of_mem hV hx
  have hrank : Module.rank A (KaehlerDifferential k A) = 1 := by
    have h := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := A) 1
    simpa using h
  have hcard : Cardinal.mk (Module.Free.ChooseBasisIndex A (KaehlerDifferential k A)) = 1 := by
    rw [← Module.Free.rank_eq_card_chooseBasisIndex A (KaehlerDifferential k A)]
    exact hrank
  obtain ⟨hsub, hne⟩ := Cardinal.eq_one_iff_unique.mp hcard
  haveI := hsub
  haveI := hne
  let j := hV.isoSpec.hom
  let g := Spec.map (CommRingCat.ofHom (algebraMap k A))
  have hj : j ≫ g = V.ι ≫ f := by
    change hV.isoSpec.hom ≫ Spec.map (baseToAffineSectionsMap f hV) = V.ι ≫ f
    rw [Spec_map_baseToAffineSectionsMap f hV, ← Category.assoc,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec]
  let u₀ : _root_.SheafOfModules.unit (Spec (.of A)).ringCatSheaf ≅ baseRingSheaf g :=
    (_root_.SheafOfModules.freeUniqueIsoUnit (R := (Spec (.of A)).ringCatSheaf)
      (Module.Free.ChooseBasisIndex A (KaehlerDifferential k A))).symm ≪≫
      affineFreeIsoOfBasis k A (Module.Free.chooseBasis A (KaehlerDifferential k A))
  let u₁ : _root_.SheafOfModules.unit V.toScheme.ringCatSheaf ≅ (restriction j).obj (baseRingSheaf g) :=
    (restrictionUnitIso j).symm ≪≫ (restriction j).mapIso u₀
  let e₂ : baseRingSheaf (j ≫ g) ≅ baseRingSheaf (V.ι ≫ f) :=
    eqToIso (congrArg (fun h => SchemeKaehlerSheaf.baseRingSheaf h) hj)
  exact ⟨u₁ ≪≫ restrictionIso g j ≪≫ e₂ ≪≫ (restrictionIso f V.ι).symm⟩

variable [IsSmoothOfRelativeDimension 1 f]

/-- Every point has an affine open on which `Ω_{C/k}` is trivial. -/
theorem exists_affine_open_unitIso (x : C) :
    ∃ V : C.Opens, x ∈ V ∧
      Nonempty (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf ≅
        (restriction V.ι).obj (baseRingSheaf f)) := by
  obtain ⟨V, hV, hx, hs⟩ := exists_affine_standardSmoothOfRelativeDimension f 1 x
  exact ⟨V, hx, exists_unit_iso_of_standardSmoothOfRelativeDimension_one f hV hx hs⟩

/-- Local trivialisations of `Ω_{C/k}` indexed by the points of `C`. -/
def localTrivializations :
    KltDP.SheafOfModules.LocalTrivializations (R := C.ringCatSheaf) (baseRingSheaf f) := by
  classical
  choose V hx e using exists_affine_open_unitIso f
  exact localTrivializationsOfOpenCharts (baseRingSheaf f) V (fun x => ⟨x, hx x⟩)
    (fun x => Classical.choice (e x))

/-- **The cotangent sheaf of a curve smooth of relative dimension one over a field is invertible.** -/
theorem cotangentSheaf_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := C.ringCatSheaf) (CurveCanonical.cotangentSheaf f) :=
  (localTrivializations f).isInvertible

/-- The canonical sheaf `ω_C = Ω_C` of a curve smooth of relative dimension one. -/
def canonicalSheafOfSmooth : InvertibleSheaf C :=
  CurveCanonical.canonicalSheaf f (cotangentSheaf_isInvertible f)

/-- The canonical class `K_C ∈ Pic C` of a curve smooth of relative dimension one. -/
def canonicalClassOfSmooth : C.Pic :=
  CurveCanonical.canonicalClass f (cotangentSheaf_isInvertible f)

theorem canonicalDegree_eq_picardEulerValue_of_smooth :
    CurveCanonical.canonicalDegree f =
      picardEulerValue f (canonicalClassOfSmooth f) - picardEulerValue f 1 :=
  CurveCanonical.canonicalDegree_eq_picardEulerValue f (cotangentSheaf_isInvertible f)

end Field

end KltDP.Geometry.SmoothCurveCotangent
