/-
Copyright (c) 2022 Sam van Gool and Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam van Gool, Jake Levinson
-/
module

public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sets.OpenCover

/-!

# Locally surjective maps of presheaves.

Let `X` be a topological space, `ℱ` and `𝒢` presheaves on `X`, `T : ℱ ⟶ 𝒢` a map.

In this file we formulate two notions for what it means for
`T` to be locally surjective:

  1. For each open set `U`, each section `t : 𝒢(U)` is in the image of `T`
     after passing to some open cover of `U`.

  2. For each `x : X`, the map of *stalks* `Tₓ : ℱₓ ⟶ 𝒢ₓ` is surjective.

We prove that these are equivalent.

-/

@[expose] public section


universe v u

noncomputable section

open CategoryTheory

open TopologicalSpace

open Opposite

namespace TopCat.Presheaf

section LocallySurjective

open scoped AlgebraicGeometry

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] {X : TopCat.{v}}
variable {ℱ 𝒢 : X.Presheaf C}

/-- A map of presheaves `T : ℱ ⟶ 𝒢` is **locally surjective** if for any open set `U`,
section `t` over `U`, and `x ∈ U`, there exists an open set `x ∈ V ⊆ U` and a section `s` over `V`
such that `$T_*(s_V) = t|_V$`.

See `TopCat.Presheaf.isLocallySurjective_iff` below.
-/
def IsLocallySurjective (T : ℱ ⟶ 𝒢) :=
  CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) T

/--
A morphism `T : ℱ ⟶ 𝒢` of presheaves on `X` is locally surjective if and only if, for every open
`U` of `X`, every section `t` of `𝒢` on `U` and every `x ∈ U`, there exists an open `V ≤ U`
containing `x` and a section `s` of `ℱ` on `V` whose image by `T` is `t |_ V`.
-/
theorem isLocallySurjective_iff (T : ℱ ⟶ 𝒢) :
    IsLocallySurjective T ↔
      ∀ (U t), ∀ x ∈ U, ∃ (V : _) (_ : V ≤ U), (∃ s, (T.app _) s = t |_ V ) ∧ x ∈ V := by
  refine ⟨fun h _ t x hx ↦ ?_, fun h => ⟨fun s x hx ↦ ?_⟩⟩
  · obtain ⟨V, i, hi⟩ := h.imageSieve_mem t x hx
    exact ⟨V, leOfHom i, hi⟩
  · obtain ⟨V, Vle, hV⟩ := h _ s x hx
    exact ⟨V, homOfLE Vle, hV⟩

/--
Let `B` be a set of opens of `X` that is a basis of the topology.
A morphism `T : ℱ ⟶ 𝒢` of presheaves on `X` is locally surjective if and only if, for every open
`U` of `X`, every section `t` of `𝒢` on `U` and every `x ∈ U`, there exists an element `V` of `B`
such that `V ≤ U` and `x ∈ V`, and a section `s` of `ℱ` on `V` whose image by `T` is `t |_ V`.
-/
theorem isLocallySurjective_iff' (T : ℱ ⟶ 𝒢) {B : Set (Opens X)} (hB : Opens.IsBasis B) :
    IsLocallySurjective T ↔ ∀ (U t), ∀ x ∈ U,
    ∃ (V : _) (_ : V ∈ B) (_ : V ≤ U) (s : ToType (ℱ.obj (op V))),
    (T.app _) s = t |_ V  ∧ x ∈ V := by
  rw [isLocallySurjective_iff]
  refine ⟨fun h _ t x hx ↦ ?_, fun h _ t x hx ↦ ?_⟩
  · obtain ⟨V, i, ⟨⟨s, hs⟩, hV⟩⟩ := h _ t x hx
    obtain ⟨W, hW1, hW2, hW3⟩ := Opens.isBasis_iff_nbhd.mp hB hV
    refine ⟨W, hW1, le_trans hW3 i, s |_ W, ?_, hW2⟩
    rw [Presheaf.map_restrict, hs, Presheaf.restrict_restrict]
  · obtain ⟨V, _, le, s, hs, hV⟩ := h _ t x hx
    exact ⟨V, le, ⟨s, hs⟩, hV⟩

set_option backward.isDefEq.respectTransparency false in
/--
Let `T : ℱ ⟶ 𝒢` be a locally surjective morphism of presheaves on `X`, and let `B : Set (Opens X)`
be a basis of the topology. For every glocal section `s` of `𝒢`, there exists a open cover
`V : ι → Opens X` by elements of `B` and sections `t i` of `ℱ` on the `V i` such that
`s |_ (V i) = t i` for every `i : ι`.
-/
theorem exists_lift_cover_basis_of_isLocallySurjective {T : ℱ ⟶ 𝒢} (hT : IsLocallySurjective T)
    {B : Set (Opens X)} (hB : Opens.IsBasis B) (s : ToType (𝒢.obj (op ⊤))) :
    ∃ (ι : Type v) (V : ι → Opens X) (_ : IsOpenCover V) (t : (i : ι) → ToType (ℱ.obj (op (V i)))),
    ∀ (i : ι), V i ∈ B ∧ (T.app _) (t i) = s |_ (V i) := by
  choose! V BV Vle t ht hV using ((isLocallySurjective_iff' T hB).mp hT ⊤ s)
  exact ⟨X, V, IsOpenCover.mk (eq_top_iff.mpr (fun x hx ↦ Opens.mem_iSup.mpr ⟨x, hV x hx⟩)),
    fun x ↦ t x (Opens.mem_top _), fun x ↦ ⟨BV x (Opens.mem_top x), ht x (Opens.mem_top _)⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
Let `T : ℱ ⟶ 𝒢` be a locally surjective morphism of presheaves on `X`. For every glocal section
`s` of `𝒢`, there exists a open cover `V : ι → Opens X` and sections `t i` of `ℱ` on the `V i`
such that `s |_ (V i) = t i` for every `i : ι`.
-/
theorem exists_lift_cover_of_isLocallySurjective {T : ℱ ⟶ 𝒢} (hT : IsLocallySurjective T)
    (s : ToType (𝒢.obj (op ⊤))) :
    ∃ (ι : Type v) (u : ι → Opens X) (_ : IsOpenCover u) (t : (i : ι) → ToType (ℱ.obj (op (u i)))),
    ∀ (i : ι), (T.app _) (t i) = s |_ (u i) := by
  obtain ⟨ι, u, hu, t, ht⟩ := exists_lift_cover_basis_of_isLocallySurjective hT (B := ⊤)
    (Opens.isBasis_iff_nbhd.mpr (fun {U _} hx ↦ ⟨U, by simp, hx, le_refl _⟩)) s
  exact ⟨ι, u, hu, t, fun i ↦ (ht i).2⟩

section SurjectiveOnStalks

variable [Limits.HasColimits C] [Limits.PreservesFilteredColimits (forget C)]

set_option backward.isDefEq.respectTransparency false in
/-- An equivalent condition for a map of presheaves to be locally surjective
is for all the induced maps on stalks to be surjective. -/
theorem locally_surjective_iff_surjective_on_stalks (T : ℱ ⟶ 𝒢) :
    IsLocallySurjective T ↔ ∀ x : X, Function.Surjective ((stalkFunctor C x).map T) := by
  constructor <;> intro hT
  · /- human proof:
        Let g ∈ Γₛₜ 𝒢 x be a germ. Represent it on an open set U ⊆ X
        as ⟨t, U⟩. By local surjectivity, pass to a smaller open set V
        on which there exists s ∈ Γ_ ℱ V mapping to t |_ V.
        Then the germ of s maps to g -/
    -- Let g ∈ Γₛₜ 𝒢 x be a germ.
    intro x g
    -- Represent it on an open set U ⊆ X as ⟨t, U⟩.
    obtain ⟨U, hxU, t, rfl⟩ := 𝒢.germ_exist x g
    -- By local surjectivity, pass to a smaller open set V
    -- on which there exists s ∈ Γ_ ℱ V mapping to t |_ V.
    rcases hT.imageSieve_mem t x hxU with ⟨V, ι, ⟨s, h_eq⟩, hxV⟩
    -- Then the germ of s maps to g.
    use ℱ.germ _ x hxV s
    simp [h_eq, germ_res_apply]
  · /- human proof:
        Let U be an open set, t ∈ Γ ℱ U a section, x ∈ U a point.
        By surjectivity on stalks, the germ of t is the image of
        some germ f ∈ Γₛₜ ℱ x. Represent f on some open set V ⊆ X as ⟨s, V⟩.
        Then there is some possibly smaller open set x ∈ W ⊆ V ∩ U on which
        we have T(s) |_ W = t |_ W. -/
    constructor
    intro U t x hxU
    set t_x := 𝒢.germ _ x hxU t with ht_x
    obtain ⟨s_x, hs_x : ((stalkFunctor C x).map T) s_x = t_x⟩ := hT x t_x
    obtain ⟨V, hxV, s, rfl⟩ := ℱ.germ_exist x s_x
    -- rfl : ℱ.germ x s = s_x
    have key_W := 𝒢.germ_eq x hxV hxU (T.app _ s) t <| by
      convert hs_x using 1
      symm
      convert stalkFunctor_map_germ_apply _ _ _ _ s
    obtain ⟨W, hxW, hWV, hWU, h_eq⟩ := key_W
    refine ⟨W, hWU, ⟨ℱ.map hWV.op s, ?_⟩, hxW⟩
    convert h_eq using 1
    simp only [← ConcreteCategory.comp_apply, T.naturality]

end SurjectiveOnStalks

end LocallySurjective

end TopCat.Presheaf
