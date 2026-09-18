import KltDP.Geometry.RegularPairBlowupFiberIrreducible
import KltDP.Geometry.RegularLocalTwoParameters
import KltDP.Geometry.CotangentGenerators

/-!
# The original blowup center fiber over a regular local surface ring

Regularity supplies two actual generators of the original maximal ideal.
Their two actual orders satisfy the proved regular-pair conditions, so
irreducibility of the entire original fiber has no generator input.
-/

noncomputable section

open IsLocalRing

universe u

namespace KltDP.Geometry.RegularLocalBlowupFiber

/-- Blow up the original maximal ideal of an arbitrary actual regular
local ring of dimension two. Its whole original scheme-theoretic center
fiber is irreducible, with no supplied parameter pair or fiber model. -/
theorem centerFiber_irreducible (R : Type u) [CommRing R] [IsLocalRing R]
    (hR : RegularLocal R) (hdim : ringKrullDim R = 2) :
    IrreducibleSpace (AffineBlowup.centerFiber (maximalIdeal R)) := by
  letI : IsNoetherianRing R := hR.1
  have hrank := RationalTreePicard.finrank_cotangentSpace_eq_two_of_regularLocal hR hdim
  have hv := exists_maximal_generators_finrank R
  rw [hrank] at hv
  obtain ⟨v, hv⟩ := hv
  have hfun : (fun i => (v i : R)) = ![(v 0 : R), (v 1 : R)] := by
    funext i
    fin_cases i <;> rfl
  rw [hfun, Matrix.range_cons_cons_empty] at hv
  obtain ⟨ha, hb⟩ := RegularLocalTwoParameters.regular_pair hR hdim
    (v 0 : R) (v 1 : R) hv
  obtain ⟨hb', ha'⟩ := RegularLocalTwoParameters.regular_pair hR hdim
    (v 1 : R) (v 0 : R) (Ideal.span_pair_comm.trans hv)
  exact RegularPairBlowupFiber.centerFiber_irreducible (maximalIdeal R)
    (v 0) (v 1) ha hb hv.symm hb' ha'

end KltDP.Geometry.RegularLocalBlowupFiber

#print axioms KltDP.Geometry.RegularLocalBlowupFiber.centerFiber_irreducible
