/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesForMathlib.NumberTheory.Hecke.Basic
public import Mathlib.RepresentationTheory.Invariants

@[expose] public section

/-!
# Hecke operators

For a Hecke pair `(G, K)` and a representation `ρ` of `G`, the Hecke operator attached to
`g : G` sends a `K`-invariant vector `v` to the sum of `ρ x v` over the finitely many left
cosets `x K` contained in the double coset `K g K`.

Unlike the corresponding construction in the FLT project, no finiteness hypothesis is carried:
for a Hecke pair it is supplied by `Subgroup.IsHeckePair.finite_image_mk`.

*References:*
 - [The FLT project](https://github.com/ImperialCollegeLondon/FLT),
   `FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Abstract.lean`
-/

open scoped Pointwise

namespace Representation

variable {R G V : Type*} [CommRing R] [Group G] [AddCommGroup V] [Module R V]
variable (ρ : Representation R G V) (K : Subgroup G)

/-- The `K`-invariants of `ρ`. -/
noncomputable abbrev subgroupInvariants : Submodule R V :=
  Representation.invariants (ρ.comp K.subtype)

variable {ρ K}

theorem mem_subgroupInvariants {v : V} :
    v ∈ ρ.subgroupInvariants K ↔ ∀ k ∈ K, ρ k v = v :=
  ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k k.2⟩

/-- A `K`-invariant vector may be translated by a coset representative: `ρ x v` depends only on
`x K`. This is the function on `G ⧸ K` that the Hecke operator sums. -/
noncomputable def translateOn (v : ρ.subgroupInvariants K) : G ⧸ K → V :=
  Quotient.lift (fun x : G => ρ x (v : V)) <| by
    intro a b hab
    have hK : a⁻¹ * b ∈ K := by simpa [QuotientGroup.leftRel_apply] using hab
    have := (mem_subgroupInvariants.mp v.2) _ hK
    calc ρ a (v : V) = ρ a (ρ (a⁻¹ * b) (v : V)) := by rw [this]
      _ = ρ b (v : V) := by rw [← Module.End.mul_apply, ← map_mul]; group

@[simp]
theorem translateOn_mk (v : ρ.subgroupInvariants K) (x : G) :
    translateOn v (QuotientGroup.mk x) = ρ x (v : V) := rfl

theorem translateOn_smul (v : ρ.subgroupInvariants K) (k : K) (c : G ⧸ K) :
    translateOn v (k • c) = ρ k (translateOn v (c : G ⧸ K)) := by
  induction c using QuotientGroup.induction_on with
  | _ x =>
    show translateOn v (QuotientGroup.mk ((k : G) * x)) = _
    simp [map_mul]

theorem smul_mem_orbit_of_mem {x : G ⧸ K} {c : G ⧸ K} (hc : c ∈ MulAction.orbit K x) (k : K) :
    k • c ∈ MulAction.orbit K x := by
  obtain ⟨k', rfl⟩ := hc
  exact ⟨k * k', mul_smul k k' x⟩

variable (ρ K)

/-- **The Hecke operator** attached to `g : G`, acting on the `K`-invariants of `ρ`: it sends a
`K`-invariant vector `v` to the sum of `ρ x v` over the left cosets `x K` making up the double
coset `K g K`.

No finiteness hypothesis is needed: it comes from `Subgroup.IsHeckePair.finite_image_mk`. -/
noncomputable def heckeOperator (hK : K.IsHeckePair) (g : G) :
    ρ.subgroupInvariants K →ₗ[R] ρ.subgroupInvariants K where
  toFun v := ⟨∑ c ∈ (hK.finite_image_mk g).toFinset, translateOn v c, by
    rw [mem_subgroupInvariants]
    intro k hk
    rw [map_sum]
    refine Finset.sum_nbij' (i := fun c => (⟨k, hk⟩ : K) • c)
      (j := fun c => (⟨k, hk⟩ : K)⁻¹ • c) ?_ ?_ ?_ ?_ ?_
    · intro c hc
      simp only [Set.Finite.mem_toFinset, Subgroup.IsHeckePair.image_mk_eq_orbit] at hc ⊢
      exact smul_mem_orbit_of_mem hc _
    · intro c hc
      simp only [Set.Finite.mem_toFinset, Subgroup.IsHeckePair.image_mk_eq_orbit] at hc ⊢
      exact smul_mem_orbit_of_mem hc _
    · intro c _; simp
    · intro c _; simp
    · intro c _; rw [translateOn_smul]⟩
  map_add' v w := by
    ext
    simp only [Submodule.coe_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    induction c using QuotientGroup.induction_on with
    | _ x => simp [translateOn]
  map_smul' r v := by
    ext
    simp only [RingHom.id_apply, SetLike.val_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    induction c using QuotientGroup.induction_on with
    | _ x => simp [translateOn]

/-- The Hecke operator at the identity is the identity: the double coset `K 1 K` is a single
left coset. -/
@[simp]
theorem heckeOperator_one (hK : K.IsHeckePair) :
    heckeOperator ρ K hK 1 = LinearMap.id := by
  ext v
  have hsingleton : (hK.finite_image_mk 1).toFinset = {(QuotientGroup.mk 1 : G ⧸ K)} := by
    ext x
    simp only [Set.Finite.mem_toFinset, Set.mul_singleton, Set.image_image, mul_one,
      Set.mem_image, Finset.mem_singleton, SetLike.mem_coe]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact QuotientGroup.eq.mpr (by simpa using inv_mem hk)
    · rintro rfl
      exact ⟨1, one_mem K, rfl⟩
  simp only [heckeOperator, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id_eq,
    Submodule.coe_mk, hsingleton, Finset.sum_singleton]
  show translateOn v (QuotientGroup.mk 1) = (v : V)
  simp

end Representation
