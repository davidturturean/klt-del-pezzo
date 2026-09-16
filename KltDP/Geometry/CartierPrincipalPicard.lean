import KltDP.Geometry.CartierDivisorTrivialization
import KltDP.Geometry.InvertibleSheafPicard
import KltDP.Compatibility.SheafOverTerminal

/-!
# Principal Cartier divisors and the actual Picard identity

A principal Cartier divisor has a global equation. Its existing actual
chart trivialization over the top open therefore descends to an actual
global module-sheaf isomorphism with the structure sheaf. The Picard class
is obtained from the proved locally free rank-one sheaf O(D), and principal
classes are one because of that actual isomorphism.

The monoidal unit is compared with the structure-sheaf module using the
proved sheafification counit; they are not identified definitionally.
Tensor-additivity of the Cartier assignment and the resulting group
homomorphism remain separate proofs.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual global trivialization of the module of a principal
Cartier divisor. Its forward inverse is locally the coordinate map `a/f`. -/
def principalCartierModuleIsoUnit (f : X.functionFieldˣ) :
    cartierDivisorModule X (principalCartierDivisorHom X (Additive.ofMul f)) ≅
      _root_.SheafOfModules.unit X.ringCatSheaf :=
  (KltDP.SheafOfModules.isoFromOverTerminal X.ringCatSheaf (⊤ : X.Opens) isTerminalTop
    (_root_.SheafOfModules.unitOverIso (R := X.ringCatSheaf) ⊤ ≪≫
      cartierEquationOverIso X (principalCartierDivisorHom X (Additive.ofMul f))
        ⊤ f (by
          simpa only [principalCartierDivisorHom] using
            (cartierEquationClassHom_restrict X
              (show (⊤ : X.Opens) ≤ ⊤ from le_rfl) f).symm))).symm

/-- The actual Picard class of the constructed invertible module O(D).
This is an object-level map; its additive law is not built into the definition. -/
def cartierPicardClass (D : CartierDivisor X) : X.Pic :=
  (cartierDivisorInvertibleSheaf X D).toPic

/-- The underlying tensor-monoid class is exactly that of the actual O(D). -/
@[simp]
theorem cartierPicardClass_val (D : CartierDivisor X) :
    letI := Scheme.Modules.monoidalCategory X
    (cartierPicardClass X D : Skeleton X.Modules) = toSkeleton (cartierDivisorModule X D) :=
  InvertibleSheaf.toPic_val (cartierDivisorInvertibleSheaf X D)

/-- Actual module-sheaf isomorphisms induce equality of the corresponding
Cartier Picard classes. -/
theorem cartierPicardClass_eq_of_iso (D E : CartierDivisor X)
    (e : cartierDivisorModule X D ≅ cartierDivisorModule X E) :
    cartierPicardClass X D = cartierPicardClass X E := by
  letI := Scheme.Modules.monoidalCategory X
  apply Units.ext
  rw [cartierPicardClass_val, cartierPicardClass_val]
  exact Quotient.sound ⟨e⟩

/-- Principal Cartier divisors represent the identity of the actual
scheme Picard group, by their proved global sheaf trivialization. -/
@[simp]
theorem cartierPicardClass_principal (f : X.functionFieldˣ) :
    cartierPicardClass X (principalCartierDivisorHom X (Additive.ofMul f)) = 1 := by
  letI := Scheme.Modules.monoidalCategory X
  apply Units.ext
  rw [cartierPicardClass_val]
  change toSkeleton (cartierDivisorModule X
    (principalCartierDivisorHom X (Additive.ofMul f))) = (1 : Skeleton X.Modules)
  rw [Skeleton.one_eq]
  exact Quotient.sound ⟨principalCartierModuleIsoUnit X f ≪≫
    (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).symm⟩

/-- The zero Cartier divisor also has the identity Picard class. -/
@[simp]
theorem cartierPicardClass_zero : cartierPicardClass X 0 = 1 := by
  simpa only [ofMul_one, map_zero] using cartierPicardClass_principal X (1 : X.functionFieldˣ)

end KltDP.Geometry
