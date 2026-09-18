import KltDP.Geometry.CompleteLinearSystemMap
import KltDP.Geometry.FiniteNonvanishingGenerators

/-! A complete original basis generates whenever the original invertible sheaf does.
The proof uses the existing H0 comparison and basis extensionality over the
original field. Its exact complete-basis nonvanishing opens then cover X. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.CompleteLinearSystemGlobalGeneration

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open ModuleCohomology CompleteLinearSystemSections

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
  [hproper : IsProper f] (hpos : 0 < dimension f L)

include hproper in
/-- The whole original H0 basis yields an actual free-sheaf epimorphism. -/
theorem positiveBasisSections_epi (hL : Positivity.IsGloballyGenerated L.obj) :
    Epi (L.obj.freeHomEquiv.symm
      (fun j : ULift.{u} (Fin ((dimension f L - 1) + 1)) =>
        positiveBasisSections f L hpos j.down)) := by
  obtain ⟨I, π, hπ⟩ := hL
  letI := hπ
  constructor
  intro M a b hab
  have hcoordinates (j : Fin ((dimension f L - 1) + 1)) :
      a.val.app (op ⊤) ((positiveBasisSections f L hpos j).val (op ⊤)) =
        b.val.app (op ⊤) ((positiveBasisSections f L hpos j).val (op ⊤)) := by
    have h := congrArg (fun q => M.freeHomEquiv q (ULift.up j)) hab
    have hs : _root_.SheafOfModules.sectionsMap a (positiveBasisSections f L hpos j) =
        _root_.SheafOfModules.sectionsMap b (positiveBasisSections f L hpos j) := by
      simpa only [_root_.SheafOfModules.freeHomEquiv_comp_apply,
        Equiv.apply_symm_apply] using h
    exact congrArg (fun s : M.sections => s.val (op ⊤)) hs
  letI := baseModule f L.obj 0
  letI := baseModule f M 0
  letI := baseSectionsModule f L.obj
  let e := hZeroBaseLinearEquivSections f L.obj
  let β := (positiveTopSectionBasis f L hpos).map e.symm
  have hmaps : (baseFunctor f 0).map a = (baseFunctor f 0).map b := by
    apply ModuleCat.hom_ext
    apply β.ext
    intro j
    apply (hZeroEquivGlobalSections M).injective
    change hZeroEquivGlobalSections M ((zariskiFunctor X 0).map a (β j)) =
      hZeroEquivGlobalSections M ((zariskiFunctor X 0).map b (β j))
    rw [← hZeroEquivGlobalSections_naturality, ← hZeroEquivGlobalSections_naturality]
    change a.val.app (op ⊤) (e (e.symm (positiveTopSectionBasis f L hpos j))) =
      b.val.app (op ⊤) (e (e.symm (positiveTopSectionBasis f L hpos j)))
    rw [LinearEquiv.apply_symm_apply]
    simpa only [positiveBasisSections_top] using hcoordinates j
  have hsections (s : L.obj.sections) :
      _root_.SheafOfModules.sectionsMap a s = _root_.SheafOfModules.sectionsMap b s := by
    apply (schemeModuleSectionsEquivTop M).injective
    obtain ⟨v, hv⟩ := (hZeroEquivGlobalSections L.obj).surjective (s.val (op ⊤))
    change a.val.app (op ⊤) (s.val (op ⊤)) = b.val.app (op ⊤) (s.val (op ⊤))
    rw [← hv, hZeroEquivGlobalSections_naturality, hZeroEquivGlobalSections_naturality]
    exact congrArg (hZeroEquivGlobalSections M) (ConcreteCategory.congr_hom hmaps v)
  apply (cancel_epi π).mp
  apply M.freeHomEquiv.injective
  funext j
  simpa only [_root_.SheafOfModules.freeHomEquiv_comp_apply] using
    hsections (L.obj.freeHomEquiv π j)

/-- The actual complete tuple, without adding or deleting a basis vector. -/
def generatingSections (hL : Positivity.IsGloballyGenerated L.obj) : L.obj.GeneratingSections where
  I := ULift.{u} (Fin ((dimension f L - 1) + 1))
  s j := positiveBasisSections f L hpos j.down
  epi := positiveBasisSections_epi f L hpos hL

/-- The actual non-base open of the original complete linear system is the whole source. -/
theorem nonBaseOpen_eq_top (hL : Positivity.IsGloballyGenerated L.obj) :
    CompleteLinearSystemMap.nonBaseOpen f L hpos = ⊤ := by
  change (⨆ j, InvertibleSectionNonvanishingOpen.nonvanishingOpen X L
    (positiveBasisSections f L hpos j)) = ⊤
  have h := FiniteNonvanishingGenerators.iSup_nonvanishing_eq_top L
    (generatingSections f L hpos hL)
  change (⨆ j : ULift.{u} (Fin ((dimension f L - 1) + 1)),
    InvertibleSectionNonvanishingOpen.nonvanishingOpen X L
      (positiveBasisSections f L hpos j.down)) = ⊤ at h
  simpa only [iSup_ulift] using h

#print axioms positiveBasisSections_epi
#print axioms nonBaseOpen_eq_top

end KltDP.Geometry.CompleteLinearSystemGlobalGeneration
