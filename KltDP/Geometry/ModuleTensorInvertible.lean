import KltDP.Geometry.InvertibleSheafTensor

/-!
# Twisting an arbitrary module sheaf by an invertible sheaf (F02/F03/F05 infrastructure)

The accepted tree can tensor an **invertible** sheaf by an invertible sheaf
(`InvertibleSheafTensor.tensorInvertibleSheaf`), but there is no plain operation twisting an
*arbitrary* `X.Modules` by an invertible sheaf. That operation is wanted independently of ampleness —
Riemann–Roch twists a coherent sheaf by `O(D)`, and the projection formula is stated for a general
`N : Y.Modules` twisted by an invertible `L` — so it is recorded here as a gap in its own right.

`tensorByInvertible F L` is `F ⊗ L.obj`, packaged so that a consumer needs no monoidal instance of its
own: the instance is declared locally here, exactly as the accepted
`KltDP/Geometry/InvertibleSheafTensor.lean:23` declares `invertibleSheafTensorMonoidal`. (A
`local instance` dies at the namespace `end`, so each module that tensors must declare its own; that
is the accepted convention, used 56 times for `MonoidalCategory` alone.)

* `tensorByInvertible_obj` — the defining equation;
* **`tensorByInvertible_invertible`** — on an invertible first argument this agrees with the accepted
  `tensorInvertibleSheaf`, so the new operation extends the existing one rather than competing with it;
* `tensorByInvertibleMapIso` — functoriality in the twisted sheaf, through `tensorRight`.

Nothing is admitted and no literal is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace KltDP.Geometry.ModuleTensorInvertible

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensorInvertibleMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {X : Scheme.{u}}

/-- **Twist of an arbitrary module sheaf by an invertible sheaf**: `F ⊗ L`. -/
def tensorByInvertible (F : X.Modules) (L : InvertibleSheaf X) : X.Modules :=
  F ⊗ L.obj

@[simp]
theorem tensorByInvertible_obj (F : X.Modules) (L : InvertibleSheaf X) :
    tensorByInvertible F L = F ⊗ L.obj := rfl

/-- **Agreement with the accepted invertible-by-invertible tensor.** On an invertible first argument
this is the underlying sheaf of `tensorInvertibleSheaf`, so the general operation extends the accepted
one. -/
theorem tensorByInvertible_invertible (L M : InvertibleSheaf X) :
    tensorByInvertible L.obj M = (InvertibleSheafTensor.tensorInvertibleSheaf L M).obj := by
  rw [tensorByInvertible_obj, InvertibleSheafTensor.tensorInvertibleSheaf_obj]

/-- **Functoriality in the twisted sheaf**: an isomorphism `F ≅ F'` induces `F ⊗ L ≅ F' ⊗ L`. -/
def tensorByInvertibleMapIso {F F' : X.Modules} (e : F ≅ F') (L : InvertibleSheaf X) :
    tensorByInvertible F L ≅ tensorByInvertible F' L :=
  (tensorRight L.obj).mapIso e

end KltDP.Geometry.ModuleTensorInvertible
