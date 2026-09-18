import KltDP.Geometry.SpecPrincipalQuotientStalkKernel
import KltDP.Geometry.AffinePrincipalIdealTildeFrame

/-!
# The original principal ideal tilde is the original quotient kernel

The two original equation frames compare the actual ideal tilde with the
actual categorical kernel. Both inclusions are multiplication by the
same original equation, so the resulting isomorphism preserves them.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.SpecPrincipalQuotient

variable {R : Type u} [CommRing R] (r : R)

/-- The original global section map has the original principal kernel. -/
theorem appTop_kernel :
    RingHom.ker (inclusion r).appTop.hom = Ideal.span {sectionOf r} := by
  simpa only [Scheme.Hom.ker_apply] using ker_ideal_top r

/-- The original defining equation is killed by the original quotient. -/
theorem sectionOf_eq_zero : (inclusion r).appTop (sectionOf r) = 0 := by
  apply RingHom.mem_ker.mp
  rw [appTop_kernel]
  exact Ideal.mem_span_singleton_self _

/-- Regularity is carried through the actual global-section isomorphism. -/
theorem sectionOf_regular (hr : r ∈ nonZeroDivisors R) :
    sectionOf r ∈ nonZeroDivisors Γ(Spec (.of R), ⊤) := by
  let e := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  apply mem_nonZeroDivisors_of_injective (f := e) e.injective
  change e (e.symm r) ∈ nonZeroDivisors R
  simpa only [e.apply_symm_apply] using hr

/-- The same regular equation frames the actual kernel sheaf. -/
def kernelFrame (hr : r ∈ nonZeroDivisors R) :
    _root_.SheafOfModules.unit (Spec (.of R)).ringCatSheaf ≅
      schemeKernelIdeal (inclusion r) :=
  principalKernelSheafIso (inclusion r) (sectionOf r) (sectionOf_eq_zero r)
    (appTop_kernel r) (sectionOf_regular r hr)

theorem kernelFrame_inclusion (hr : r ∈ nonZeroDivisors R) :
    (kernelFrame r hr).hom ≫ schemeKernelIdealι (inclusion r) =
      schemeScalarEnd (sectionOf r) :=
  schemeKernelGenerator_comp_ι (inclusion r) (sectionOf r) (sectionOf_eq_zero r)

/-- The original principal ideal tilde is the actual quotient kernel. -/
def idealTildeKernelIso (hr : r ∈ nonZeroDivisors R) :
    (ModuleCat.of R (Ideal.span {r})).tilde ≅ schemeKernelIdeal (inclusion r) :=
  (AffinePrincipalIdealTildeFrame.frameIso (Ideal.span {r})
    ⟨r, Ideal.mem_span_singleton_self r⟩ rfl hr).symm ≪≫ kernelFrame r hr

/-- This comparison intertwines the two original ideal inclusions. -/
theorem idealTildeKernelIso_inclusion (hr : r ∈ nonZeroDivisors R) :
    (idealTildeKernelIso r hr).hom ≫ schemeKernelIdealι (inclusion r) =
      AffinePrincipalIdealTildeFrame.inclusion (Ideal.span {r}) := by
  rw [idealTildeKernelIso, Iso.trans_hom, Category.assoc, kernelFrame_inclusion]
  change (AffinePrincipalIdealTildeFrame.frameIso (Ideal.span {r})
    ⟨r, Ideal.mem_span_singleton_self r⟩ rfl hr).inv ≫
      schemeScalarEnd (StructureSheaf.toOpen R ⊤ r) = _
  rw [← AffinePrincipalIdealTildeFrame.frameIso_inclusion (Ideal.span {r})
    ⟨r, Ideal.mem_span_singleton_self r⟩ rfl hr, Iso.inv_hom_id_assoc]

end KltDP.Geometry.SpecPrincipalQuotient

#print axioms KltDP.Geometry.SpecPrincipalQuotient.idealTildeKernelIso_inclusion
