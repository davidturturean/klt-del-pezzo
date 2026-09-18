import KltDP.Geometry.BaseFieldCohomology
import KltDP.Geometry.CoherentModule
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Dualizing sheaves through the original cohomology trace

This is the usual proper-curve universal property, expressed on actual coherent
scheme modules. The cohomology groups and their field actions are exactly those
of `ModuleCohomology.baseFunctor` for the given structure morphism. See Stacks
0BS2(5) and 0AWP for the coherent-module representation property.

The definition supplies no existence or invertibility theorem and contains no
genus, degree, conic, or smoothness conclusion. In particular it does not replace
the dualizing sheaf by the sheaf of relative differentials.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.CurveDualizing

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k))

/-- A coefficient morphism followed by the original cohomology trace. -/
def traceMap {ω : X.Modules}
    (trace : Module.Dual k ((baseFunctor f 1).obj ω)) (M : X.Modules) :
    (M ⟶ ω) → Module.Dual k ((baseFunctor f 1).obj M) :=
  fun a => trace.comp ((baseFunctor f 1).map a).hom

/-- Each native trace pairing is linear in the original cohomology class. -/
theorem traceMap_smul {ω M : X.Modules}
    (trace : Module.Dual k ((baseFunctor f 1).obj ω))
    (a : M ⟶ ω) (r : k) (x : (baseFunctor f 1).obj M) :
    traceMap f trace M a (r • x) = r • traceMap f trace M a x :=
  (traceMap f trace M a).map_smul r x

/-- The trace correspondence is contravariantly natural in the coefficient
module, using the same original cohomology map on both sides. -/
theorem traceMap_naturality {ω M N : X.Modules}
    (trace : Module.Dual k ((baseFunctor f 1).obj ω))
    (a : M ⟶ N) (b : N ⟶ ω) :
    traceMap f trace M (a ≫ b) =
      (traceMap f trace N b).comp ((baseFunctor f 1).map a).hom := by
  unfold traceMap
  rw [(baseFunctor f 1).map_comp a b]
  rfl

/-- The trace is recovered by evaluating the correspondence at the identity. -/
theorem traceMap_id {ω : X.Modules}
    (trace : Module.Dual k ((baseFunctor f 1).obj ω)) :
    traceMap f trace ω (𝟙 ω) = trace := by
  unfold traceMap
  rw [(baseFunctor f 1).map_id ω]
  rfl

/-- An actual coherent dualizing module with its original-field trace.
Only the standard representing property is bundled; inhabitation is not
assumed, and numerical or geometric conclusions are not fields of this data. -/
structure DualizingSheaf where
  sheaf : X.Modules
  coherent : IsCoherentModule sheaf
  trace : Module.Dual k ((baseFunctor f 1).obj sheaf)
  traceMap_bijective (M : X.Modules) (hM : IsCoherentModule M) :
    Function.Bijective (traceMap f trace M)

/-- The actual representing bijection, for a specified dualizing sheaf. -/
def DualizingSheaf.homEquiv (ω : DualizingSheaf f)
    (M : X.Modules) (hM : IsCoherentModule M) :
    (M ⟶ ω.sheaf) ≃ Module.Dual k ((baseFunctor f 1).obj M) :=
  Equiv.ofBijective (traceMap f ω.trace M) (ω.traceMap_bijective M hM)

end KltDP.Geometry.CurveDualizing

#print axioms KltDP.Geometry.CurveDualizing.traceMap_naturality
#print axioms KltDP.Geometry.CurveDualizing.traceMap_smul
