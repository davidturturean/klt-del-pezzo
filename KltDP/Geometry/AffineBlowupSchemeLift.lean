import KltDP.Geometry.AffineBlowupGlobalUniqueness
import Mathlib.AlgebraicGeometry.IdealSheaf

/-!
# Blowup lifts from schemes with locally principal regular extended center

The test scheme is arbitrary. On an actual affine open cover, the actual
ring map to each chart extends the center to a principal ideal with a
nonzerodivisor generator. These are local geometric hypotheses only.

Local lifts come from the proved affine construction. Their agreement is
proved on the actual scheme-theoretic intersections, using affine covers
and preservation of regularity by open immersions. Mathlib's scheme gluing
then constructs the global morphism; arbitrary candidates agree with it.

`LocallyPrincipalRegular` records these literal local ideal equations.
The existing `IdealSheafData.ofIdealTop` constructs the actual extended
ideal sheaf. Its local affine equations are compared with the chart maps,
and pointwise affine neighborhoods derive a suitable covering family.
No equivalence with a separate invertible-ideal definition is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace KltDP.Geometry.AffineBlowup

universe u v w

/-- Extension of a principal ideal along a further actual ring map. -/
theorem map_comp_eq_span_singleton
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    (I : Ideal R) (φ : R →+* S) (d : S)
    (hcenter : Ideal.map φ I = Ideal.span {d}) (ρ : S →+* T) :
    Ideal.map (ρ.comp φ) I = Ideal.span {ρ d} := by
  rw [← Ideal.map_map, hcenter, Ideal.map_span, Set.image_singleton]

section OpenTest

variable {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (φ : R →+* S) (d : S)
    (hcenter : Ideal.map φ I = Ideal.span {d})
    (hregular : d ∈ nonZeroDivisors S)

include d hcenter hregular in
/-- Arbitrary candidates agree on any open subscheme of an admissible
affine test scheme. The source need not itself be affine. -/
theorem hom_ext_of_openImmersion_principal_regular
    {Z : Scheme.{u}} (α : Z ⟶ Spec (CommRingCat.of S)) [IsOpenImmersion α]
    (g h : Z ⟶ scheme I)
    (hg : g ≫ toSpec I = α ≫ Spec.map (CommRingCat.ofHom φ))
    (hh : h ≫ toSpec I = α ≫ Spec.map (CommRingCat.ofHom φ)) : g = h := by
  let 𝒰 := Z.affineOpenCover
  apply 𝒰.openCover.hom_ext
  intro i
  change 𝒰.map i ≫ g = 𝒰.map i ≫ h
  let β := 𝒰.map i ≫ α
  let ρ := (Spec.preimage β).hom
  have hmap : Ideal.map (ρ.comp φ) I = Ideal.span {ρ d} :=
    map_comp_eq_span_singleton I φ d hcenter ρ
  have hreg : ρ d ∈ nonZeroDivisors (𝒰.obj i) :=
    openImmersionSpecPreimage_mem_nonZeroDivisors β hregular
  have hbase : Spec.map (CommRingCat.ofHom (ρ.comp φ)) =
      β ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact congrArg (fun j => j ≫ Spec.map (CommRingCat.ofHom φ))
      (Spec.map_preimage β)
  have hg' : (𝒰.map i ≫ g) ≫ toSpec I =
      Spec.map (CommRingCat.ofHom (ρ.comp φ)) := by
    rw [Category.assoc, hg, ← Category.assoc]
    exact hbase.symm
  have hh' : (𝒰.map i ≫ h) ≫ toSpec I =
      Spec.map (CommRingCat.ofHom (ρ.comp φ)) := by
    rw [Category.assoc, hh, ← Category.assoc]
    exact hbase.symm
  exact (principalTargetLift_unique I (ρ.comp φ) (ρ d) hmap hreg _ hg').trans
    (principalTargetLift_unique I (ρ.comp φ) (ρ d) hmap hreg _ hh').symm

end OpenTest

section SchemeTest

variable {R : Type u} [CommRing R] (I : Ideal R)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (𝒰 : Scheme.AffineOpenCover.{u} Y)

/-- The actual ring map of the test morphism on a specified affine chart. -/
def testChartMap (i : 𝒰.J) : R →+* 𝒰.obj i :=
  (Spec.preimage (𝒰.map i ≫ f)).hom

/-- The chart ring map corresponds to the actual restricted test morphism. -/
@[simp]
theorem testChartMap_toSpec (i : 𝒰.J) :
    Spec.map (CommRingCat.ofHom (testChartMap f 𝒰 i)) = 𝒰.map i ≫ f :=
  Spec.map_preimage _

variable (d : ∀ i : 𝒰.J, 𝒰.obj i)
    (hcenter : ∀ i, Ideal.map (testChartMap f 𝒰 i) I = Ideal.span {d i})
    (hregular : ∀ i, d i ∈ nonZeroDivisors (𝒰.obj i))

/-- The actual lift on each member of the affine cover. -/
def schemeLocalLift (i : 𝒰.J) : Spec (𝒰.obj i) ⟶ scheme I :=
  principalTargetLift I (testChartMap f 𝒰 i) (d i) (hcenter i) (hregular i)

/-- Each local lift is over the given restricted test morphism. -/
@[simp]
theorem schemeLocalLift_toSpec (i : 𝒰.J) :
    schemeLocalLift I f 𝒰 d hcenter hregular i ≫ toSpec I = 𝒰.map i ≫ f :=
  (principalTargetLift_toSpec I (testChartMap f 𝒰 i) (d i)
    (hcenter i) (hregular i)).trans (testChartMap_toSpec f 𝒰 i)

/-- Compatibility on the actual categorical intersections is a theorem.
No transition or local-lift agreement is part of the input data. -/
theorem schemeLocalLift_overlap (i j : 𝒰.J) :
    pullback.fst (𝒰.map i) (𝒰.map j) ≫ schemeLocalLift I f 𝒰 d hcenter hregular i =
      pullback.snd (𝒰.map i) (𝒰.map j) ≫
        schemeLocalLift I f 𝒰 d hcenter hregular j := by
  apply hom_ext_of_openImmersion_principal_regular I
    (testChartMap f 𝒰 i) (d i) (hcenter i) (hregular i)
    (pullback.fst (𝒰.map i) (𝒰.map j))
  · rw [Category.assoc, schemeLocalLift_toSpec, testChartMap_toSpec]
  · rw [Category.assoc, schemeLocalLift_toSpec, testChartMap_toSpec,
      ← Category.assoc, ← Category.assoc, pullback.condition]

/-- The actual global lift, glued from the derived compatible local lifts. -/
def schemeLift : Y ⟶ scheme I :=
  𝒰.openCover.glueMorphisms (schemeLocalLift I f 𝒰 d hcenter hregular)
    (schemeLocalLift_overlap I f 𝒰 d hcenter hregular)

/-- Restriction of the glued lift is the constructed affine lift. -/
theorem schemeLift_restrict (i : 𝒰.J) :
    𝒰.map i ≫ schemeLift I f 𝒰 d hcenter hregular =
      schemeLocalLift I f 𝒰 d hcenter hregular i :=
  𝒰.openCover.ι_glueMorphisms _ _ i

/-- The glued lift is over exactly the original test morphism. -/
@[simp]
theorem schemeLift_toSpec : schemeLift I f 𝒰 d hcenter hregular ≫ toSpec I = f := by
  apply 𝒰.openCover.hom_ext
  intro i
  change 𝒰.map i ≫ (schemeLift I f 𝒰 d hcenter hregular ≫ toSpec I) = 𝒰.map i ≫ f
  rw [← Category.assoc, schemeLift_restrict, schemeLocalLift_toSpec]

/-- Every global candidate agrees with the constructed lift. -/
theorem schemeLift_unique (g : Y ⟶ scheme I) (hg : g ≫ toSpec I = f) :
    g = schemeLift I f 𝒰 d hcenter hregular := by
  apply 𝒰.openCover.hom_ext
  intro i
  change 𝒰.map i ≫ g = 𝒰.map i ≫ schemeLift I f 𝒰 d hcenter hregular
  rw [schemeLift_restrict]
  apply principalTargetLift_unique I (testChartMap f 𝒰 i) (d i)
    (hcenter i) (hregular i)
  rw [Category.assoc, hg, testChartMap_toSpec]

/-- A literal local condition on the actual extended ideal. It contains
neither a lift nor a gluing or uniqueness conclusion. -/
def LocallyPrincipalRegular : Prop :=
  ∃ 𝒱 : Scheme.AffineOpenCover.{u} Y, ∀ i : 𝒱.J, ∃ e : 𝒱.obj i,
    Ideal.map (testChartMap f 𝒱 i) I = Ideal.span {e} ∧
      e ∈ nonZeroDivisors (𝒱.obj i)

/-- Existence and uniqueness for arbitrary test schemes whose actual
extended center has principal regular equations on an affine open cover. -/
theorem existsUnique_lift_of_locally_principal_regular
    (hloc : LocallyPrincipalRegular I f) :
    ∃! g : Y ⟶ scheme I, g ≫ toSpec I = f := by
  obtain ⟨𝒱, h𝒱⟩ := hloc
  choose e he hreg using h𝒱
  exact ⟨schemeLift I f 𝒱 e he hreg, schemeLift_toSpec I f 𝒱 e he hreg,
    fun g hg => schemeLift_unique I f 𝒱 e he hreg g hg⟩

end SchemeTest

section IntrinsicIdeal

variable {R : Type u} [CommRing R] (I : Ideal R)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))

/-- The actual map from the affine base ring to global test-scheme sections. -/
def testGlobalRingMap : R →+* Γ(Y, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/-- The actual ideal sheaf generated by the image of the affine center,
using Mathlib's existing localization-compatible ideal-sheaf carrier. -/
def extendedCenter : Y.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.map (testGlobalRingMap f) I)

/-- The canonical affine chart map is the restriction of the actual map
to global sections. Both sides use the pinned `ΓSpecIso` normalization. -/
theorem testAffinePreimage_eq (U : Y.affineOpens) :
    Spec.preimage (U.2.fromSpec ≫ f) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫
        Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op := by
  have hfrom : U.2.fromSpec.appTop =
      Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op ≫
        (Scheme.ΓSpecIso Γ(Y, U.1)).inv := by
    simpa only [Scheme.Hom.appTop, homOfLE_refl, op_id,
      Functor.map_id, Category.comp_id] using U.2.fromSpec_app_of_le ⊤ le_top
  apply (cancel_mono (Scheme.ΓSpecIso Γ(Y, U.1)).inv).mp
  rw [Scheme.ΓSpecIso_inv_naturality, Spec.map_preimage,
    Scheme.comp_appTop, hfrom]
  simp only [Category.assoc]

/-- On every actual affine open, the existing ideal sheaf is exactly the
extension along the canonical ring map of that affine chart. -/
theorem extendedCenter_ideal (U : Y.affineOpens) :
    (extendedCenter I f).ideal U =
      Ideal.map (Spec.preimage (U.2.fromSpec ≫ f)).hom I := by
  change Ideal.map (Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op).hom
      (Ideal.map (testGlobalRingMap f) I) = _
  rw [Ideal.map_map, testAffinePreimage_eq]
  rfl

/-- Intrinsic local equations for the actual extended ideal sheaf: every
point lies in an actual affine open on which that ideal has a regular
principal generator. This makes no merely stalkwise spreading assertion. -/
def ExtendedCenterLocallyPrincipalRegular : Prop :=
  ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧ ∃ e : Γ(Y, U.1),
    (extendedCenter I f).ideal U = Ideal.span {e} ∧
      e ∈ nonZeroDivisors Γ(Y, U.1)

/-- Pointwise affine neighborhoods and their literal ideal equations
derive an actual affine cover carrying the required regular generators. -/
theorem locallyPrincipalRegular_of_extendedCenter
    (hlocal : ExtendedCenterLocallyPrincipalRegular I f) :
    LocallyPrincipalRegular I f := by
  choose U hmem e hideal hreg using hlocal
  let 𝒰 : Scheme.AffineOpenCover.{u} Y :=
    { J := Y
      obj := fun y => Γ(Y, (U y).1)
      map := fun y => (U y).2.fromSpec
      f := id
      covers := fun y => by
        change y ∈ Set.range (U y).2.fromSpec.base
        rw [(U y).2.range_fromSpec]
        exact hmem y }
  refine ⟨𝒰, fun y => ⟨e y, ?_, hreg y⟩⟩
  change Ideal.map (Spec.preimage ((U y).2.fromSpec ≫ f)).hom I = Ideal.span {e y}
  rw [← extendedCenter_ideal I f (U y)]
  exact hideal y

/-- The actual unique global factorization for arbitrary test schemes
whose extended ideal sheaf has local regular principal equations. -/
theorem existsUnique_lift_of_extendedCenter_locally_principal_regular
    (hlocal : ExtendedCenterLocallyPrincipalRegular I f) :
    ∃! g : Y ⟶ scheme I, g ≫ toSpec I = f :=
  existsUnique_lift_of_locally_principal_regular I f
    (locallyPrincipalRegular_of_extendedCenter I f hlocal)

end IntrinsicIdeal

end KltDP.Geometry.AffineBlowup
