import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic

/-!
# The integral section-fibre pairing is perfect

A cyclic base summand and a fibre pairing once with the section make the
actual section and fibre generate the full group. Their two integral
pairing rows then solve every integral functional without denominators.
-/

set_option autoImplicit false

namespace KltDP.LinearAlgebra.SectionFiberIntegralDual

variable {A G : Type*} [AddCommGroup A] [AddCommGroup G]

/-- An element pairing once with the section generates the cyclic base
summand, so the section and that element generate the entire actual group. -/
theorem generate_of_cyclic_base
    (B : LinearMap.BilinForm ℤ A) (a f : A) (j : G →+ A)
    (e : (ℤ × G) ≃+ A) (he : ∀ n l, e (n, l) = n • a + j l)
    (eG : G ≃+ ℤ) (l : G) (hf : f = j l) (haf : B a f = 1) :
    ∀ p : A, ∃ n m : ℤ, p = n • a + m • f := by
  let g := j (eG.symm 1)
  let d : ℤ := B a g
  have hcyclic (v : G) : v = eG v • eG.symm 1 := by
    apply eG.injective
    simp only [map_zsmul, AddEquiv.apply_symm_apply, zsmul_eq_mul, mul_one]
    rfl
  have hj (v : G) : j v = eG v • g := by
    simpa only [map_zsmul] using congrArg j (hcyclic v)
  have hfg : f = eG l • g := hf.trans (hj l)
  have hprod : eG l * d = 1 := by
    simpa only [hfg, map_zsmul, zsmul_eq_mul] using haf
  have hprod' : d * eG l = 1 := by simpa only [mul_comm] using hprod
  have hgf : g = d • f := by
    rw [hfg, smul_smul, hprod', one_smul]
  intro p
  obtain ⟨⟨n, v⟩, hp⟩ := e.surjective p
  refine ⟨n, eG v * d, ?_⟩
  calc
    p = e (n, v) := hp.symm
    _ = n • a + j v := he n v
    _ = n • a + (eG v * d) • f := by rw [hj v, hgf, smul_smul]

/-- Section self-intersection is arbitrary. The off-diagonal ones and
zero fibre square give a bijection with the actual additive integral dual. -/
theorem dual_bijective_of_section_fiber
    (B : LinearMap.BilinForm ℤ A) (a f : A)
    (hgen : ∀ p : A, ∃ n m : ℤ, p = n • a + m • f)
    (haf : B a f = 1) (hfa : B f a = 1) (hff : B f f = 0) :
    Function.Bijective (fun p => (B p).toAddMonoidHom) := by
  constructor
  · intro p q hpq
    obtain ⟨n, m, hp⟩ := hgen p
    obtain ⟨r, s, hq⟩ := hgen q
    have hn : n = r := by
      have h := congrArg (fun L : A →+ ℤ => L f) hpq
      change B p f = B q f at h
      simpa only [hp, hq, map_add, map_zsmul, LinearMap.add_apply,
        LinearMap.smul_apply, zsmul_eq_mul, haf, hff, mul_one, mul_zero, add_zero] using h
    have hm : m = s := by
      have h := congrArg (fun L : A →+ ℤ => L a) hpq
      change B p a = B q a at h
      simp only [hp, hq, map_add, map_zsmul, LinearMap.add_apply,
        LinearMap.smul_apply, zsmul_eq_mul, hfa, mul_one] at h
      change n * B a a + m = r * B a a + s at h
      rw [hn] at h
      exact add_left_cancel h
    rw [hp, hq, hn, hm]
  · intro L
    refine ⟨L f • a + (L a - L f * B a a) • f, ?_⟩
    apply AddMonoidHom.ext
    intro p
    obtain ⟨n, m, hp⟩ := hgen p
    change B (L f • a + (L a - L f * B a a) • f) p = L p
    rw [hp]
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply,
      zsmul_eq_mul, haf, hfa, hff]
    ring
    change n * L f * B a a + n * (-(B a a * L f) + L a) + L f * m =
      n * L a + L f * m
    ring

end KltDP.LinearAlgebra.SectionFiberIntegralDual

#print axioms KltDP.LinearAlgebra.SectionFiberIntegralDual.generate_of_cyclic_base
#print axioms KltDP.LinearAlgebra.SectionFiberIntegralDual.dual_bijective_of_section_fiber
