import KltDP.Geometry.SchemeModulePullbackMapEqFactorNative

/-!
# A dependent Boolean family of original pullback factors

The Boolean elimination is proved before any geometric objects or chosen
refinements are substituted. Every scheme, chart map and global module is
an explicit parameter. Both branches retain their original whole-map law.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchemeModulePullbackBoolFactor

/-- Assemble two original pullback-factor families over their actual dependent index. -/
def iso (Y : Scheme.{u}) (P : Bool → Type u)
    (Z : (b : Bool) → P b → Scheme.{u}) (l : (b : Bool) → (p : P b) → Z b p ⟶ Y)
    (M N : Y.Modules)
    (e0 : (p : P false) → (schemeModulePullback (l false p)).obj M ≅
      (schemeModulePullback (l false p)).obj N)
    (e1 : (p : P true) → (schemeModulePullback (l true p)).obj M ≅
      (schemeModulePullback (l true p)).obj N)
    (t : Σ b, P b) :
    (schemeModulePullback (l t.1 t.2)).obj M ≅
      (schemeModulePullback (l t.1 t.2)).obj N := by
  rcases t with ⟨b, p⟩
  cases b
  · exact e0 p
  · exact e1 p

/-- Assembly preserves the original normalized inclusion and differential. -/
theorem iso_comp (Y : Scheme.{u}) (P : Bool → Type u)
    (Z : (b : Bool) → P b → Scheme.{u}) (l : (b : Bool) → (p : P b) → Z b p ⟶ Y)
    (M N T : Y.Modules)
    (e0 : (p : P false) → (schemeModulePullback (l false p)).obj M ≅
      (schemeModulePullback (l false p)).obj N)
    (e1 : (p : P true) → (schemeModulePullback (l true p)).obj M ≅
      (schemeModulePullback (l true p)).obj N)
    (i : N ⟶ T) (m : M ⟶ T)
    (h0 : ∀ p, (e0 p).hom ≫ (schemeModulePullback (l false p)).map i =
      (schemeModulePullback (l false p)).map m)
    (h1 : ∀ p, (e1 p).hom ≫ (schemeModulePullback (l true p)).map i =
      (schemeModulePullback (l true p)).map m)
    (t : Σ b, P b) :
    (iso Y P Z l M N e0 e1 t).hom ≫ (schemeModulePullback (l t.1 t.2)).map i =
      (schemeModulePullback (l t.1 t.2)).map m := by
  rcases t with ⟨b, p⟩
  cases b
  · exact h0 p
  · exact h1 p

end KltDP.Geometry.SchemeModulePullbackBoolFactor
