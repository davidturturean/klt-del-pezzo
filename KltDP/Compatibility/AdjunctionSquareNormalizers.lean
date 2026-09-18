import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Transporting a square through two adjunctions

The proof uses the pinned adjunction naturality lemmas in arbitrary
categories. Concrete sheaf functors are supplied only after the proof is
complete. The two normalizer hypotheses are identities of actual maps;
consumers discharge them with their already proved adjunction formulas.
No geometry or replacement comparison is constructed here.
-/

noncomputable section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace KltDP.AdjunctionSquare

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    {F : C ⥤ D} {G : D ⥤ C} {L : D ⥤ E} {R : E ⥤ D}

/-- A square becomes the composite of its two actual adjoints. Keeping
the categories abstract avoids unfolding concrete module constructions. -/
theorem homEquiv_square (adjF : F ⊣ G) (adjL : L ⊣ R)
    {M : C} {N : D} {P : E}
    (a : F.obj M ⟶ N) (r : L.obj N ⟶ P)
    (s : L.obj (F.obj M) ⟶ P) (h : L.map a ≫ r = s) :
    adjF.homEquiv M N a ≫ G.map (adjL.homEquiv N P r) =
      adjF.homEquiv M (R.obj P) (adjL.homEquiv (F.obj M) P s) := by
  rw [← adjF.homEquiv_naturality_right,
    ← adjL.homEquiv_naturality_left, h]

/-- The same square after substituting two proved normal forms. The
formula retains the original functors, maps, and adjunctions literally. -/
theorem homEquiv_square_of_normalizers (adjF : F ⊣ G) (adjL : L ⊣ R)
    {M : C} {N : D} {P : E}
    (a : F.obj M ⟶ N) (r : L.obj N ⟶ P)
    (s : L.obj (F.obj M) ⟶ P)
    (η : N ⟶ R.obj P) (t : M ⟶ G.obj (R.obj P))
    (h : L.map a ≫ r = s)
    (hη : adjL.homEquiv N P r = η)
    (ht : adjF.homEquiv M (R.obj P)
      (adjL.homEquiv (F.obj M) P s) = t) :
    adjF.homEquiv M N a ≫ G.map η = t := by
  rw [← hη]
  exact (homEquiv_square adjF adjL a r s h).trans ht

end KltDP.AdjunctionSquare

#check @KltDP.AdjunctionSquare.homEquiv_square_of_normalizers
#print axioms KltDP.AdjunctionSquare.homEquiv_square_of_normalizers
