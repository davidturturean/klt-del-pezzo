import KltDP.Geometry.NormalCartierWeilInjective
import KltDP.Geometry.CartierRepresentativeWithPicardClass

/-!
The original Picard-to-Weil class homomorphism is injective on a normal
projective surface. The proved normal Cartier-to-Weil injectivity removes
the principal correction while retaining the actual sheaf Picard class.
The target need not be regular or locally factorial.
-/

noncomputable section

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- Original invertible sheaf classes embed in the actual Weil class
group of a normal projective surface. -/
theorem picardToWeilClassHom_injective : Function.Injective X.picardToWeilClassHom := by
  intro L M h
  obtain ⟨A, hA⟩ := cartierPicardHom_surjective X.toScheme L
  have hclass : X.weilClassMap (X.cartierToWeilHom A) =
      X.picardToWeilClassHom M :=
    (X.picardToWeilClassHom_cartierPicardHom A).symm.trans
      ((congrArg X.picardToWeilClassHom hA).trans h)
  obtain ⟨B, hB, hBM⟩ := X.exists_cartier_representative_of_picardWeilClass_eq
    (X.cartierToWeilHom A) M hclass
  have hBA : B = A := X.cartierToWeilHom_injective hB
  exact hA.symm.trans ((congrArg (cartierPicardHom X.toScheme) hBA.symm).trans hBM)

end KltDP.Geometry.NormalProjectiveSurface
