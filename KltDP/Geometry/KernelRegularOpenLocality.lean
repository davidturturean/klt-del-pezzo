import KltDP.Geometry.CartierPullbackKernelTransport
import KltDP.Geometry.SchemeKernelOpenBaseChange

/-!
# Regular principal equations for kernels on an open cover

The kernel of an actual open base change inherits regular principal local
equations from the original kernel on an integral scheme. The source open
need not be nonempty: at each point its integrality and generic-point map
follow from the open immersion, and the existing Cartier pullback comparison
supplies the equations.

Conversely, regular equations for the actual base changes along an open
cover give regular equations for the original kernel. The proof uses the
accepted restriction isomorphism and the pinned equality of section ideals;
it preserves the actual ideals, including their embeddings in section rings.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.KernelRegularOpenLocality

open KltDP.Geometry KltDP.Geometry.CartierPullbackKernelTransport
  KltDP.Geometry.CartierDivisorPullbackIdeal KltDP.Geometry.SchemeKernelOpenBaseChange

/-- Regular principal kernel equations pull back along an actual open
immersion square. Integrality of the source is derived pointwise. -/
theorem kernel_locallyPrincipalRegular_of_open_isPullback
    {X Y Z Z' : Scheme.{u}} [IsIntegral Y]
    (π : X ⟶ Y) [IsOpenImmersion π] (f : Z ⟶ Y) [QuasiCompact f]
    (f' : Z' ⟶ X) (j : Z' ⟶ Z) (H : IsPullback f' j π f)
    (hI : IdealLocallyPrincipalRegular f.ker) :
    IdealLocallyPrincipalRegular f'.ker := by
  intro x
  letI : Nonempty X := ⟨x⟩
  letI : IsIntegral X := isIntegral_of_isOpenImmersion π
  letI : GenericPointPreserving π := ⟨genericPoint_eq_of_isOpenImmersion π⟩
  have hk := pullbackIdealData_eq_kernel π (cartierDivisorOfIdeal Y f.ker hI)
    (cartierDivisorOfIdeal_hasRegularEquations Y f.ker hI) f f' j H
    (cartierDivisorOfIdeal_idealData Y f.ker hI)
  have hr := pullbackIdealData_locallyPrincipalRegular π (cartierDivisorOfIdeal Y f.ker hI)
    (cartierDivisorOfIdeal_hasRegularEquations Y f.ker hI)
  rw [hk] at hr
  exact hr x

/-- Regular principal equations for the actual kernels on an open cover
are regular principal equations for the original kernel. -/
theorem kernel_locallyPrincipalRegular_of_openCover {X Z : Scheme.{u}}
    (f : Z ⟶ X) [QuasiCompact f] {ι : Type*} (V : ι → X.Opens)
    (hcover : ∀ x : X, ∃ i, x ∈ V i)
    (hreg : ∀ i, IdealLocallyPrincipalRegular (pullback.fst (V i).ι f).ker) :
    IdealLocallyPrincipalRegular f.ker := by
  intro x
  obtain ⟨i, hxi⟩ := hcover x
  have hk : (pullback.fst (V i).ι f).ker = (f ∣_ V i).ker := by
    rw [← baseChangeRestrictIso_hom_restrict f (V i)]
    apply le_antisymm
    · have h := Scheme.Hom.le_ker_comp (baseChangeRestrictIso f (V i)).inv
        ((baseChangeRestrictIso f (V i)).hom ≫ (f ∣_ V i))
      simpa only [Iso.inv_hom_id_assoc] using h
    · exact Scheme.Hom.le_ker_comp _ _
  have hr := hreg i
  rw [hk] at hr
  obtain ⟨W, hxW, d, hd, hdr⟩ := hr ⟨x, hxi⟩
  exact ⟨⟨(V i).ι ''ᵁ W.1, W.2.image_of_isOpenImmersion _⟩,
    ⟨⟨x, hxi⟩, hxW, rfl⟩, d,
    (Scheme.ker_morphismRestrict_ideal f (V i) W).symm.trans hd, hdr⟩

end KltDP.Geometry.KernelRegularOpenLocality
