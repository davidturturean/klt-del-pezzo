import KltDP.Geometry.ModuleCohomologyEuler
import KltDP.Geometry.SurfaceCohomologyVanishing
import KltDP.Geometry.ProjectiveProper
import KltDP.Geometry.CoherentModule
import KltDP.AdmissionProbe.ProperCohomologyConsumers

/-!
# Euler characteristics are additive on a normal projective surface

On a normal projective surface `X` over a field `k` every coherent module has finite-dimensional
cohomology in all degrees (the accepted Stacks 02O6 consumer `proper_baseFunctor_finiteDimensional`,
properness of the structure morphism from the projective embedding) and cohomology vanishes above
degree two (accepted `normalProjectiveSurface_H_subsingleton`). Hence the accepted long-exact-sequence
Euler identity `eulerCharacteristic_additive` applies with vanishing bound `2` to every short exact
sequence of coherent modules on the surface: `χ(M₂) = χ(M₁) + χ(M₃)`
(`eulerCharacteristic_additive_of_coherent`). This is the F05 infrastructure statement; the Euler
pairing of Cartier divisors (`CartierEulerPairing`) is built on the same `χ`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology KltDP.AdmissionProbe.ProperCohomologyConsumers

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- All cohomology of a coherent module on the surface is finite-dimensional (accepted 02O6 consumer
with the properness of the structure morphism). -/
theorem coherent_cohomology_finiteDimensional (M : X.toScheme.Modules) [IsCoherentModule M]
    (n : ℕ) : FiniteDimensional k ((baseFunctor X.structureMorphism n).obj M) :=
  proper_baseFunctor_finiteDimensional X.structureMorphism M n

/-- **Euler characteristics are additive along short exact sequences of coherent modules on a normal
projective surface.** -/
theorem eulerCharacteristic_additive_of_coherent (S : ShortComplex X.toScheme.Modules)
    (hS : S.ShortExact) [IsCoherentModule S.X₁] [IsCoherentModule S.X₂] [IsCoherentModule S.X₃] :
    eulerCharacteristic X.structureMorphism S.X₂ =
      eulerCharacteristic X.structureMorphism S.X₁ + eulerCharacteristic X.structureMorphism S.X₃ :=
  eulerCharacteristic_additive X.structureMorphism S hS 2
    (X.coherent_cohomology_finiteDimensional S.X₁) (X.coherent_cohomology_finiteDimensional S.X₂)
    (X.coherent_cohomology_finiteDimensional S.X₃)
    (fun n hn => normalProjectiveSurface_H_subsingleton X S.X₁ n hn)
    (fun n hn => normalProjectiveSurface_H_subsingleton X S.X₂ n hn)
    (fun n hn => normalProjectiveSurface_H_subsingleton X S.X₃ n hn)

end KltDP.Geometry.NormalProjectiveSurface
