import KltDP.Geometry.SchemeKernelOpenPullback
import KltDP.Geometry.PrincipalKernelSheaf
import KltDP.Geometry.SchemeModuleFunctorial
import KltDP.Geometry.SchemeModulePullbackUnit

/-!
# The kernel ideal line of a closed immersion is trivial off its range

For a closed immersion `g : X ⟶ Y`, the kernel ideal `schemeKernelIdeal g` restricted to the open
complement of `range g` is the unit (`kernelLine_complement_unitIso`: on the complement the restricted
morphism has empty source, so the generator `1` frames the kernel — the accepted argument of
`complementGlobalFrameIso`, made generic), hence its pullback along any morphism `f : Z ⟶ Y` whose
range misses `range g` is trivial (`kernelLine_pullback_unitIso`). This gives `C · [D] = 0` for a
curve `C` disjoint from a divisor `D` defined as the range of a closed immersion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.KernelLinePullbackOffRange

open KltDP.Geometry

/-- The generator `1` frames the kernel of a morphism with empty source (the accepted private
`emptyKernelGenerator_isIso`, restated). -/
theorem emptyKernelGenerator_isIso' {X Y : Scheme.{u}} (f : X ⟶ Y) [IsEmpty X] :
    IsIso (schemeKernelGenerator f 1 (Subsingleton.elim _ _)) := by
  apply KltDP.SheafOfModules.isIso_of_bijective_on_basis
    (B := fun U : Y.Opens => U) _
    (Opens.isBasis_iff_nbhd.mpr (fun {U x} hx => ⟨U, ⟨U, rfl⟩, hx, le_rfl⟩))
  intro U
  apply schemeKernelGenerator_app_bijective f 1 (Subsingleton.elim _ _) U
  · rw [map_one, Ideal.span_singleton_one]
    apply top_unique
    intro r _
    exact Subsingleton.elim _ _
  · rw [map_one]
    exact one_mem _

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsClosedImmersion g]

/-- The open complement of the range of a closed immersion. -/
def rangeComplement : Y.Opens :=
  ⟨(Set.range g.base)ᶜ, g.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The closed immersion has empty preimage over the complement of its range. -/
instance preimage_rangeComplement_isEmpty : IsEmpty (g ⁻¹ᵁ rangeComplement g).toScheme :=
  ⟨fun x => x.2 ⟨x.1, rfl⟩⟩

/-- **The kernel line is the unit on the complement of the range.** -/
def kernelLine_complement_unitIso :
    _root_.SheafOfModules.unit (rangeComplement g).toScheme.ringCatSheaf ≅
      (schemeModulePullback (rangeComplement g).ι).obj (schemeKernelIdeal g) :=
  haveI := emptyKernelGenerator_isIso' (g ∣_ rangeComplement g)
  asIso (schemeKernelGenerator (g ∣_ rangeComplement g) 1 (Subsingleton.elim _ _)) ≪≫
    localKernelToGlobalPullbackIso g (rangeComplement g)

/-- **The pullback of the kernel line along a morphism missing the range is trivial.** -/
def kernelLine_pullback_unitIso {Z : Scheme.{u}} (f : Z ⟶ Y)
    (hdisj : Disjoint (Set.range f.base) (Set.range g.base)) :
    (schemeModulePullback f).obj (schemeKernelIdeal g) ≅
      _root_.SheafOfModules.unit Z.ringCatSheaf := by
  have hsub : Set.range f.base ⊆ Set.range (rangeComplement g).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact Set.disjoint_left.mp hdisj
  have hf : IsOpenImmersion.lift (rangeComplement g).ι f hsub ≫ (rangeComplement g).ι = f :=
    IsOpenImmersion.lift_fac _ _ _
  rw [← hf]
  exact ((schemeModulePullbackCompIso (IsOpenImmersion.lift (rangeComplement g).ι f hsub)
      (rangeComplement g).ι).symm.app _) ≪≫
    (schemeModulePullback (IsOpenImmersion.lift (rangeComplement g).ι f hsub)).mapIso
      (kernelLine_complement_unitIso g).symm ≪≫
    schemeModulePullbackUnitIso (IsOpenImmersion.lift (rangeComplement g).ι f hsub)

end KltDP.Geometry.KernelLinePullbackOffRange
