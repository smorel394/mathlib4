/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Homology.FreydCategory.Quotient

/-!
# Cokernels in Freyd categories

-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex Arrow

variable {V : Type*} [Category* V] [Preadditive V]

namespace CategoryTheory.Preadditive

namespace RightFreyd

variable [HasFiniteProducts V]

local instance : HasBinaryBiproducts V := HasBinaryBiproducts.of_hasBinaryProducts

variable {u v : Arrow V} (f : u ⟶ v)

namespace CandidateCokernel

/-- If `f` is a morphism of `Arrow V`, this is a "candidate cokernel" of `f`, i.e. an object
in `Arrow V` whose image in `RightFreyd V` will be a cokernel of the image of `f`. -/
abbrev cokernel : Arrow V := Arrow.mk (biprod.desc v.hom f.right)

/-- For `f : u ⟶ v` a morphism in `Arrow V`, this is the morphism `v ⟶ cokernel f` from `v` to
the "candidate cokernel" of `f`, whose image in `RightFreyd V` will be the projection to
the cokernel of the image of `f`. -/
def π : v ⟶ cokernel f :=
  Arrow.homMk biprod.inl (𝟙 v.right) ((biprod.inl_desc _ _).trans (comp_id _).symm)

/-- The right homotopy expressing that `f ≫ π f` is sent to `0` in `RightFreyd V`. -/
def condition : RightHomotopy (f ≫ π f) 0 where
  hom := biprod.inr
  comm := by
    simp only [π, comp_right, homMk_right, Hom.zero_right]
    refine Eq.trans ?_ (biprod.inr_desc _ _).symm
    rw [sub_zero]
    exact comp_id _

set_option backward.isDefEq.respectTransparency false in
instance isEpi_π : Epi ((quotient V).map (π f)) :=
  have : IsIso ((π f).right) := by simp only [π, homMk_right]; infer_instance
  isEpi_of_right_iso _

variable {w : Arrow V} (g : v ⟶ w) (h : RightHomotopy (f ≫ g) 0)

/--
If `f : u ⟶ v` and `g : v ⟶ w` are morphisms in `Arrow V` such that `f ≫ g` is right homotopic
to `0`, this is the morphism from the "candidate cokernel" of `f` to `w` defined from the
right homotopy. -/
def desc : cokernel f ⟶ w := by
  refine Arrow.homMk (biprod.desc g.left h.hom) g.right ?_
  simp only [mk_hom]
  apply biprod.hom_ext'
  · convert (biprod.inl_desc_assoc _ _ _).trans
      (Eq.trans g.w (biprod.inl_desc_assoc _ _ _).symm) <;> rfl
  · convert (biprod.inr_desc_assoc g.left h.hom w.hom).trans
      (Eq.trans (by simp [h.comm.symm]) (biprod.inr_desc_assoc v.hom f.right g.right).symm) <;> rfl

@[reassoc]
lemma π_desc : π f ≫ desc f g h = g := by
  simp only [cokernel, π, desc]
  ext
  · simp only [comp_left, homMk_left]
    exact biprod.inl_desc _ _
  · simp only [comp_right, homMk_right]
    exact Category.id_comp _

end CandidateCokernel

variable {X : RightFreyd V} {a : (quotient V).obj v ⟶ X} (eq : (quotient V).map f ≫ a = 0)

/-- Let `f : u ⟶ v` be a morphism in `Arrow V`, and let `a : (quotient V).obj v ⟶ X` be
a morphism in `RightFreyd V` such that `(quotient V).map f ≫ a = 0`. This is the morphism
`(quotient V).obj (cokernel f) ⟶ X` that will serve as `cokernel.desc f`. -/
def desc' : (quotient V).obj (CandidateCokernel.cokernel f) ⟶ X := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  exact (quotient V).map (CandidateCokernel.desc _ _ (homotopyOfEq _ _ eq))

lemma π_desc' : (quotient V).map (CandidateCokernel.π f) ≫ desc' f eq = a := by
  rw [← ((quotient V).map_surjective a).choose_spec] at eq
  conv_rhs => rw [← ((quotient V).map_surjective a).choose_spec,
                      ← CandidateCokernel.π_desc _ _ (homotopyOfEq _ _ eq)]
  rfl

/-- For `f` a morphism in `Arrow V`, construct a cokernel cofork of `(quotient V).map f`. -/
def candidateCokernelCofork : Cocone (parallelPair ((quotient V).map f) 0) := by
  refine CokernelCofork.ofπ ((quotient V).map (CandidateCokernel.π f)) ?_
  rw [← (quotient V).map_comp]
  exact eq_of_rightHomotopy _ _ (CandidateCokernel.condition f)

/-- For `f` a morphism in `Arrow V`, the cokernel cofork of `(quotient V).map f` constructed
in `candidateCokernelCofork` is a colimit cofork. -/
def candidateCokernelCoforkIsCokernel : IsColimit (candidateCokernelCofork f) where
  desc s := desc' f (CokernelCofork.condition s)
  fac s j :=
    match j with
    | WalkingParallelPair.zero => by
      simp only [Cofork.app_zero_eq_comp_π_left, CokernelCofork.condition]
      exact zero_comp
    | WalkingParallelPair.one => π_desc' f (CokernelCofork.condition s)
  uniq s m eq :=
    (cancel_epi ((quotient V).map (CandidateCokernel.π f))).mp ((eq WalkingParallelPair.one).trans
    (π_desc' f (CokernelCofork.condition s)).symm)

/-- The category `RightFreyd V` has all cokernels if `V` has finite products. -/
instance : HasCokernels (RightFreyd V) where
  has_colimit {X Y} f := {
    exists_colimit := by
      obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
      exact Nonempty.intro {
        cocone := candidateCokernelCofork f
        isColimit := candidateCokernelCoforkIsCokernel f}}

end RightFreyd

end CategoryTheory.Preadditive
