/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Cochains from complexes concentrated in one degree

Port of the single-cochain block of `HomComplex` and the from-single block
of `HomComplexSingle` at Mathlib 79d0395a1825a6264ad5d269e35e60537518955e.
The original cochain and differential are those of the pinned Mathlib.
Newer elaboration options and arithmetic tactics are replaced by explicit
pinned proofs; no cohomology-class or Ext comparison is assumed.
-/

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace CochainComplex.HomComplex.Cochain

variable {K L : CochainComplex C ℤ}

/-- The cochain in `Cochain K L n` that is given by a single
morphism `K.X p ⟶ L.X q` and is zero otherwise. (As we do not check
that `p + n = q`, this will be the zero cochain when `p + n ≠ q`.) -/
def single {p q : ℤ} (f : K.X p ⟶ L.X q) (n : ℤ) :
    Cochain K L n :=
  Cochain.mk (fun p' q' _ =>
    if h : p = p' ∧ q = q'
      then (K.XIsoOfEq h.1).inv ≫ f ≫ (L.XIsoOfEq h.2).hom
      else 0)

@[simp]
lemma single_v {p q : ℤ} (f : K.X p ⟶ L.X q) (n : ℤ) (hpq : p + n = q) :
    (single f n).v p q hpq = f := by
  dsimp [single]
  rw [if_pos, id_comp, comp_id]
  exact ⟨rfl, rfl⟩

lemma single_v_eq_zero {p q : ℤ} (f : K.X p ⟶ L.X q) (n : ℤ) (p' q' : ℤ) (hpq' : p' + n = q')
    (hp' : p' ≠ p) :
    (single f n).v p' q' hpq' = 0 := by
  dsimp [single]
  rw [dif_neg]
  intro h
  exact hp' (by omega)

/-- Variant of `single_v_eq_zero` where the assumption is `q' ≠ q` rather than `p' ≠ p`. -/
lemma single_v_eq_zero' {p q : ℤ} (f : K.X p ⟶ L.X q) (n : ℤ) (p' q' : ℤ) (hpq' : p' + n = q')
    (hq' : q' ≠ q) :
    (single f n).v p' q' hpq' = 0 := by
  dsimp [single]
  rw [dif_neg]
  intro h
  exact hq' h.2.symm

variable (K L) in
@[simp]
lemma single_zero (p q n : ℤ) :
    (single (p := p) (q := q) 0 n : Cochain K L n) = 0 := by
  ext p' q' hpq'
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq
      simp
    · simp [single_v_eq_zero' _ _ _ _ _ hq]
  · simp [single_v_eq_zero _ _ _ _ _ hp]

lemma δ_single {p q : ℤ} (f : K.X p ⟶ L.X q) (n m : ℤ) (hm : n + 1 = m)
    (p' q' : ℤ) (hp' : p' + 1 = p) (hq' : q + 1 = q') :
    δ n m (single f n) = single (f ≫ L.d q q') m + m.negOnePow • single (K.d p' p ≫ f) m := by
  ext p'' q'' hpq''
  rw [δ_v n m hm (single f n) p'' q'' (by omega) (q'' - 1) (p'' + 1) rfl (by omega),
    add_v, units_smul_v]
  congr 1
  · by_cases h : p'' = p
    · subst h
      by_cases h : q = q'' - 1
      · subst h
        obtain rfl : q' = q'' := by omega
        simp only [single_v]
      · rw [single_v_eq_zero', single_v_eq_zero', zero_comp]
        all_goals omega
    · rw [single_v_eq_zero _ _ _ _ _ h, single_v_eq_zero _ _ _ _ _ h, zero_comp]
  · subst hm
    by_cases h : q'' = q
    · subst h
      by_cases h : p'' = p'
      · subst h
        obtain rfl : p = p'' + 1 := by omega
        simp
      · rw [single_v_eq_zero _ _ _ _ _ h, single_v_eq_zero, comp_zero, smul_zero]
        omega
    · simp [single_v_eq_zero' _ _ _ _ _ h]

variable [HasZeroObject C] {X : C}

/-- Constructor for cochains from a single complex. -/
noncomputable def fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (_ : p + n = q) :
    Cochain ((singleFunctor C p).obj X) K n :=
  Cochain.single ((HomologicalComplex.singleObjXSelf (.up ℤ) p X).hom ≫ f) n

variable (X K) in
@[simp]
lemma fromSingleMk_zero (p q n : ℤ) (h : p + n = q) :
    fromSingleMk (X := X) (K := K) 0 h = 0 := by
  simp [fromSingleMk]

@[simp]
lemma fromSingleMk_v {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    (fromSingleMk f h).v p q h =
      (HomologicalComplex.singleObjXSelf (.up ℤ) p X).hom ≫ f := by
  simp [fromSingleMk]

lemma fromSingleMk_v_eq_zero {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (p' q' : ℤ) (hpq' : p' + n = q') (hp' : p' ≠ p) :
    (fromSingleMk f h).v p' q' hpq' = 0 :=
  single_v_eq_zero _ _ _ _ _ hp'

lemma δ_fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (n' q' : ℤ) (h' : p + n' = q') :
    δ n n' (fromSingleMk f h) = fromSingleMk (f ≫ K.d q q') h' := by
  by_cases hq : q + 1 = q'
  · dsimp only [fromSingleMk]
    rw [δ_single _ n n' (by omega) (p - 1) q' (by omega) hq]
    simp [singleFunctor, singleFunctors]
  · simp [δ_shape n n' (by omega), HomologicalComplex.shape K q q' (by simp; omega),
      fromSingleMk]

/-- Cochains of degree `n` from `(singleFunctor C p).obj X` to `K` identify
to `X ⟶ K.X q` when `p + n = q`. -/
noncomputable def fromSingleEquiv {p q n : ℤ} (h : p + n = q) :
    Cochain ((singleFunctor C p).obj X) K n ≃+ (X ⟶ K.X q) where
  toFun α := (HomologicalComplex.singleObjXSelf (.up ℤ) p X).inv ≫ α.v p q h
  invFun f := fromSingleMk f h
  left_inv α := by
    ext p' q' hpq'
    by_cases hp : p' = p
    · subst p'
      have hq : q' = q := hpq'.symm.trans h
      cases hq
      rw [fromSingleMk_v]
      simp only [Iso.hom_inv_id_assoc]
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _
  right_inv f := by simp
  map_add' := by simp

@[simp]
lemma fromSingleEquiv_fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleEquiv h (fromSingleMk f h) = f := by
  simp [fromSingleEquiv]

@[simp]
lemma fromSingleMk_add {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleMk (f + g) h = fromSingleMk f h + fromSingleMk g h :=
  (fromSingleEquiv h).symm.map_add _ _

@[simp]
lemma fromSingleMk_sub {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleMk (f - g) h = fromSingleMk f h - fromSingleMk g h :=
  (fromSingleEquiv h).symm.map_sub _ _

@[simp]
lemma fromSingleMk_neg {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleMk (-f) h = -fromSingleMk f h :=
  (fromSingleEquiv h).symm.map_neg _

lemma fromSingleMk_surjective {p n : ℤ} (α : Cochain ((singleFunctor C p).obj X) K n)
    (q : ℤ) (h : p + n = q) :
    ∃ (f : X ⟶ K.X q), fromSingleMk f h = α :=
  (fromSingleEquiv h).symm.surjective α

lemma fromSingleMk_precomp
    {X' : C} (g : X' ⟶ X) {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleMk (g ≫ f) h =
      (Cochain.ofHom ((singleFunctor C p).map g)).comp (fromSingleMk f h) (zero_add n) := by
  apply (fromSingleEquiv h).injective
  simp [fromSingleEquiv, singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self]

lemma fromSingleMk_postcomp {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    {L : CochainComplex C ℤ} (g : K ⟶ L) :
    fromSingleMk (f ≫ g.f q) h =
      (fromSingleMk f h).comp (.ofHom g) (add_zero n) :=
  (fromSingleEquiv h).injective (by simp [fromSingleEquiv, singleFunctor, singleFunctors])


end CochainComplex.HomComplex.Cochain
