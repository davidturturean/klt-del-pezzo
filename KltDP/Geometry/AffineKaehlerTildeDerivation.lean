import KltDP.Geometry.SchemeKaehlerSheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Etale.Kaehler

/-!
# An actual derivation into the affine differential tilde sheaf

The canonical differential-localization theorem identifies the ordinary
Kähler module at each original prime with the localization of the
original affine Kähler module. Transporting the ordinary local-ring
derivation through this canonical equivalence gives a pointwise map.

For an original local fraction `z * b = a`, the product rule proves
`b^2 • dz = b • da - a • db`. Thus this pointwise map preserves the
original locally-fractional section predicates and defines a derivation
into the existing affine tilde sheaf, compatible with every restriction.

The representing property of `SchemeKaehlerSheaf` then gives the actual
comparison from the constructed global differential sheaf to that tilde.
Its bijectivity, and the later top differential line, are separate proofs.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineKaehlerTildeDerivation

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- The original affine module of relative Kähler differentials. -/
abbrev differentialModule : ModuleCat A := ModuleCat.of A (KaehlerDifferential k A)

/-- The canonical localization comparison at the original prime. -/
def fiberEquiv (p : PrimeSpectrum A) :
    LocalizedModule p.asIdeal.primeCompl (differentialModule k A) ≃ₗ[A]
      KaehlerDifferential k (Localization.AtPrime p.asIdeal) :=
  IsLocalizedModule.iso p.asIdeal.primeCompl
    (KaehlerDifferential.map k k A (Localization.AtPrime p.asIdeal))

/-- The local-ring derivation, transported into the original tilde fiber. -/
def fiberD (p : PrimeSpectrum A) :
    Localization.AtPrime p.asIdeal →+
      LocalizedModule p.asIdeal.primeCompl (differentialModule k A) :=
  (fiberEquiv k A p).symm.toLinearMap.toAddMonoidHom.comp
    (KaehlerDifferential.D k (Localization.AtPrime p.asIdeal)).toLinearMap.toAddMonoidHom

/-- The transported derivation retains the actual local scalar action. -/
theorem fiberD_mul (p : PrimeSpectrum A) (a b : Localization.AtPrime p.asIdeal) :
    fiberD k A p (a * b) = a • fiberD k A p b + b • fiberD k A p a := by
  change (fiberEquiv k A p).symm
      (KaehlerDifferential.D k (Localization.AtPrime p.asIdeal) (a * b)) = _
  rw [Derivation.leibniz, map_add]
  exact congrArg₂ (fun x y : LocalizedModule p.asIdeal.primeCompl
      (differentialModule k A) => x + y)
    ((IsLocalization.linearMap_compatibleSMul p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal)
      (KaehlerDifferential k (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl (differentialModule k A))).map_smul
        (fiberEquiv k A p).symm.toLinearMap a
        (KaehlerDifferential.D k (Localization.AtPrime p.asIdeal) b))
    ((IsLocalization.linearMap_compatibleSMul p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal)
      (KaehlerDifferential k (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl (differentialModule k A))).map_smul
        (fiberEquiv k A p).symm.toLinearMap b
        (KaehlerDifferential.D k (Localization.AtPrime p.asIdeal) a))

/-- An original affine differential becomes its canonical localized element. -/
theorem fiberD_algebraMap (p : PrimeSpectrum A) (a : A) :
    fiberD k A p (algebraMap A (Localization.AtPrime p.asIdeal) a) =
      LocalizedModule.mkLinearMap p.asIdeal.primeCompl (differentialModule k A)
        (KaehlerDifferential.D k A a) := by
  change (fiberEquiv k A p).symm
      (KaehlerDifferential.D k (Localization.AtPrime p.asIdeal)
        (algebraMap A (Localization.AtPrime p.asIdeal) a)) = _
  rw [← KaehlerDifferential.map_D k k A (Localization.AtPrime p.asIdeal)]
  exact IsLocalizedModule.iso_symm_apply p.asIdeal.primeCompl
    (KaehlerDifferential.map k k A (Localization.AtPrime p.asIdeal)) _

/-- Differentiating the actual fraction equation gives a uniform square
denominator, without choosing unrelated local representatives. -/
theorem fiberD_fraction (p : PrimeSpectrum A) (z : Localization.AtPrime p.asIdeal)
    (a b : A) (hz : z * algebraMap A (Localization.AtPrime p.asIdeal) b =
      algebraMap A (Localization.AtPrime p.asIdeal) a) :
    b ^ 2 • fiberD k A p z =
      LocalizedModule.mkLinearMap p.asIdeal.primeCompl (differentialModule k A)
        (b • KaehlerDifferential.D k A a - a • KaehlerDifferential.D k A b) := by
  let m := LocalizedModule.mkLinearMap p.asIdeal.primeCompl (differentialModule k A)
  have hd : z • m (KaehlerDifferential.D k A b) + b • fiberD k A p z =
      m (KaehlerDifferential.D k A a) := by
    have h := congrArg (fiberD k A p) hz
    rw [fiberD_mul, fiberD_algebraMap, fiberD_algebraMap] at h
    simpa only [algebraMap_smul] using h
  have hclear (w : LocalizedModule p.asIdeal.primeCompl (differentialModule k A)) :
      b • (z • w) = a • w := by
    calc
      b • (z • w) =
          (algebraMap A (Localization.AtPrime p.asIdeal) b) • (z • w) :=
        (IsScalarTower.algebraMap_smul
          (R := A) (Localization.AtPrime p.asIdeal) b (z • w)).symm
      _ = ((algebraMap A (Localization.AtPrime p.asIdeal) b) * z) • w :=
        (mul_smul _ _ _).symm
      _ = (z * algebraMap A (Localization.AtPrime p.asIdeal) b) • w := by
        rw [mul_comm]
      _ = (algebraMap A (Localization.AtPrime p.asIdeal) a) • w := by rw [hz]
      _ = a • w := IsScalarTower.algebraMap_smul
        (R := A) (Localization.AtPrime p.asIdeal) a w
  have hsolve : b • fiberD k A p z =
      m (KaehlerDifferential.D k A a) - z • m (KaehlerDifferential.D k A b) :=
    (eq_sub_iff_add_eq).mpr ((add_comm _ _).trans hd)
  calc
    b ^ 2 • fiberD k A p z = b • (b • fiberD k A p z) := by
      rw [pow_two, mul_smul]
    _ = b • (m (KaehlerDifferential.D k A a) -
        z • m (KaehlerDifferential.D k A b)) := by rw [hsolve]
    _ = b • m (KaehlerDifferential.D k A a) -
        a • m (KaehlerDifferential.D k A b) := by rw [smul_sub, hclear]
    _ = m (b • KaehlerDifferential.D k A a - a • KaehlerDifferential.D k A b) := by
      rw [map_sub, map_smul, map_smul]

/-- Differentiation preserves the original local-fraction section condition. -/
theorem sectionD_isLocallyFraction (U : Opens (PrimeSpectrum A))
    (s : Γ(Spec (CommRingCat.of A), U)) :
    (ModuleCat.Tilde.isLocallyFraction (differentialModule k A)).pred
      (fun x : U => fiberD k A x.val (s.val x)) := by
  intro x
  obtain ⟨V, hxV, i, a, b, h⟩ := s.property x
  refine ⟨V, hxV, i,
    b • KaehlerDifferential.D k A a - a • KaehlerDifferential.D k A b, b ^ 2, ?_⟩
  intro y
  refine ⟨?_, fiberD_fraction k A y.val (s.val (i y)) a b (h y).2⟩
  simpa only [pow_two] using y.val.asIdeal.primeCompl.mul_mem (h y).1 (h y).1

/-- The original structure sections map to actual differential tilde sections. -/
def sectionD (U : Opens (PrimeSpectrum A)) :
    Γ(Spec (CommRingCat.of A), U) →+
      (differentialModule k A).tilde.val.obj (op U) where
  toFun s := ⟨fun x => fiberD k A x.val (s.val x), sectionD_isLocallyFraction k A U s⟩
  map_zero' := by
    apply Subtype.ext
    funext x
    exact (fiberD k A x.val).map_zero
  map_add' s t := by
    apply Subtype.ext
    funext x
    exact (fiberD k A x.val).map_add (s.val x) (t.val x)

/-- The actual structure-sheaf multiplication satisfies the product rule. -/
theorem sectionD_mul (U : Opens (PrimeSpectrum A))
    (s t : Γ(Spec (CommRingCat.of A), U)) :
    sectionD k A U (s * t) = s • sectionD k A U t + t • sectionD k A U s := by
  apply Subtype.ext
  funext x
  exact fiberD_mul k A x.val (s.val x) (t.val x)

/-- The original affine functions have their original canonical differential sections. -/
theorem sectionD_toOpen (U : Opens (PrimeSpectrum A)) (a : A) :
    sectionD k A U (StructureSheaf.toOpen A U a) =
      ModuleCat.Tilde.toOpen (differentialModule k A) U (KaehlerDifferential.D k A a) := by
  apply Subtype.ext
  funext x
  exact fiberD_algebraMap k A x.val a

/-- On an affine scheme the original base-scalar map is the original
algebra map followed by the original canonical section map. -/
theorem scalarPresheafHom_app (U : Opens (PrimeSpectrum A)) :
    (SchemeKaehlerSheaf.scalarPresheafHom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).app (op U) =
        CommRingCat.ofHom (algebraMap k A) ≫ StructureSheaf.toOpen A U := by
  change (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap k A))).appTop ≫
      (Spec (CommRingCat.of A)).presheaf.map (homOfLE le_top).op = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rfl

/-- The actual differential tilde sheaf carries the original base-ring
derivation, with all open restrictions and scalar images verified. -/
def tildeDerivation :
    (differentialModule k A).tilde.val.Derivation'
      (SchemeKaehlerSheaf.scalarPresheafHom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))) where
  d {U} := sectionD k A U.unop
  d_mul {U} := sectionD_mul k A U.unop
  d_map {U V} i s := by
    apply Subtype.ext
    funext x
    rfl
  d_app {U} a := by
    change sectionD k A U.unop
      ((SchemeKaehlerSheaf.scalarPresheafHom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).app (op U.unop) a) = 0
    rw [scalarPresheafHom_app]
    change sectionD k A U.unop (StructureSheaf.toOpen A U.unop (algebraMap k A a)) = 0
    rw [sectionD_toOpen, Derivation.map_algebraMap, map_zero]

/-- The actual comparison from the constructed global differential sheaf
to the existing affine tilde sheaf; its map is determined by differentiation. -/
def comparison :
    SchemeKaehlerSheaf.baseRingSheaf
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ (differentialModule k A).tilde :=
  SchemeKaehlerSheaf.desc _ (tildeDerivation k A)

/-- The comparison preserves the derivative of every original section,
including sections on arbitrary opens rather than only affine generators. -/
theorem comparison_d (U : Opens (PrimeSpectrum A))
    (s : Γ(Spec (CommRingCat.of A), U)) :
    (comparison k A).val.app (op U)
      ((SchemeKaehlerSheaf.baseRingDerivation
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d s) = sectionD k A U s :=
  _root_.PresheafOfModules.Derivation.congr_d
    (SchemeKaehlerSheaf.derivation_postcomp_desc _ (tildeDerivation k A)) s

end KltDP.Geometry.AffineKaehlerTildeDerivation
