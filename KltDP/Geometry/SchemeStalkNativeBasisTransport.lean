import KltDP.Geometry.KaehlerBasisAlgEquiv
import KltDP.Geometry.SchemeStalkKaehlerMap

/-!
# Native bases through the original isomorphic stalk map

The actual over-base square makes the original stalk map a ground-algebra
map. Its actual invertibility gives the algebra equivalence used by the
already accepted native Kähler basis transport. Each original derivative
is carried to the derivative of its original stalk-map image.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

namespace KltDP.Geometry.SchemeStalkNativeBasisTransport

open IntrinsicNodal

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ X)
    (g : Y ⟶ Spec (CommRingCat.of k)) (h : q ≫ f = g) (s : Y)

/-- The forward map is the original stalk map with the actual ground scalars. -/
def hom :
    letI := stalkAlgebra f (q.base s)
    letI := stalkAlgebra g s
    X.presheaf.stalk (q.base s) →ₐ[k] Y.presheaf.stalk s := by
  letI := stalkAlgebra f (q.base s)
  letI := stalkAlgebra g s
  refine { (q.stalkMap s).hom with commutes' := ?_ }
  intro r
  exact congrArg (fun a : CommRingCat.of k ⟶ Y.presheaf.stalk s => a.hom r)
    (SchemeStalkKaehlerMap.scalar_triangle f q g h s).symm

/-- Invertibility of that same original stalk map supplies its algebra equivalence. -/
def equiv [IsIso (q.stalkMap s)] :
    letI := stalkAlgebra f (q.base s)
    letI := stalkAlgebra g s
    X.presheaf.stalk (q.base s) ≃ₐ[k] Y.presheaf.stalk s := by
  letI := stalkAlgebra f (q.base s)
  letI := stalkAlgebra g s
  exact AlgEquiv.ofBijective (hom f q g h s)
    (ConcreteCategory.bijective_of_isIso (q.stalkMap s))

/-- Transport the native basis through the original stalk algebra equivalence. -/
def basis [IsIso (q.stalkMap s)] {ι : Type v} :
    letI := stalkAlgebra f (q.base s)
    letI := stalkAlgebra g s
    Basis ι (X.presheaf.stalk (q.base s))
        (KaehlerDifferential k (X.presheaf.stalk (q.base s))) →
      Basis ι (Y.presheaf.stalk s) (KaehlerDifferential k (Y.presheaf.stalk s)) := by
  letI := stalkAlgebra f (q.base s)
  letI := stalkAlgebra g s
  exact KaehlerBasisAlgEquiv.basis (equiv f q g h s)

/-- Original differential vectors retain the exact original map on their arguments. -/
theorem basis_apply_of_eq_D [IsIso (q.stalkMap s)] {ι : Type v} :
    letI := stalkAlgebra f (q.base s)
    letI := stalkAlgebra g s
    ∀ (b : Basis ι (X.presheaf.stalk (q.base s))
        (KaehlerDifferential k (X.presheaf.stalk (q.base s))))
      (i : ι) (a : X.presheaf.stalk (q.base s)),
      b i = KaehlerDifferential.D k (X.presheaf.stalk (q.base s)) a →
        basis f q g h s b i =
          KaehlerDifferential.D k (Y.presheaf.stalk s) (q.stalkMap s a) := by
  letI := stalkAlgebra f (q.base s)
  letI := stalkAlgebra g s
  refine fun b i a ha => ?_
  exact KaehlerBasisAlgEquiv.basis_apply_of_eq_D (equiv f q g h s) b i a ha

end KltDP.Geometry.SchemeStalkNativeBasisTransport
