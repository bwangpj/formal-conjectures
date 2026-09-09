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

public import Mathlib.GroupTheory.Commensurable
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

@[expose] public section

/-!
# Hecke pairs

A *Hecke pair* is a group `G` together with a subgroup `K` commensurable with all of its
conjugates. This is exactly the condition under which the double cosets `K \ G / K` carry a
convolution algebra, the Hecke algebra of the pair, which is built on top of this file.

The point of the definition is the finiteness in `IsHeckePair.finite_leftCosets`: for a Hecke
pair, each double coset `K g K` is a *finite* union of left cosets `x K`. That is what makes the
structure constants of the convolution well defined, and it is the only input the construction
of the Hecke algebra needs. In particular no topology and no Haar measure are involved: the
convolution is defined by counting cosets, following Shimura, rather than by integrating
against a Haar measure on a locally profinite group.

The motivating example is `G = GL n F` for `F` a nonarchimedean local field and
`K = GL n 𝒪` its maximal compact; there the resulting algebra is the spherical Hecke algebra
whose Satake parameters describe unramified representations.

## Main declarations

* `IsHeckePair`: every conjugate of `K` is commensurable with `K`; equivalently the
  commensurator of `K` is all of `G`.
* `Subgroup.IsHeckePair.finite_image_mk`: a right coset `K g` meets only finitely many left
  cosets, so `K g K` is a finite union of left cosets.

## Relation to the FLT project

The FLT project has abstract Hecke operators in
`FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Abstract.lean`: for `U V : Subgroup G`
acting on the `U`-invariants of a module, `AbstractHeckeOperator.heckeOperator` is the operator
attached to a double coset, together with a criterion for two such operators to commute. That
development takes the finiteness
`(QuotientGroup.mk '' (U * {g}) : Set (G ⧸ V)).Finite`
as a *hypothesis* on each operator, and constructs individual operators rather than an algebra.

This file supplies that hypothesis rather than assuming it: `finite_image_mk` is stated in
exactly the above form, and derives it from commensurability, so that for a Hecke pair every
abstract Hecke operator exists unconditionally. The ring structure on the span of the double
cosets is built on top, and is what the spherical Hecke algebra of `GL n` needs.

*References:*
 - G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, Chapter 3
 - [The FLT project](https://github.com/ImperialCollegeLondon/FLT),
   `FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Abstract.lean`
-/

open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G]

/-- `K` is a **Hecke subgroup** of `G` when every conjugate of `K` is commensurable with `K`;
equivalently, when the commensurator of `K` is all of `G`.

For such a `K` the double cosets `K \ G / K` carry a convolution product, defined by counting
left cosets; `finite_leftCosets` is the finiteness that makes the count well defined. -/
def IsHeckePair (K : Subgroup G) : Prop :=
  Commensurable.commensurator K = ⊤

theorem isHeckePair_iff {K : Subgroup G} :
    IsHeckePair K ↔ ∀ g : G, Commensurable (ConjAct.toConjAct g • K) K := by
  simp [IsHeckePair, Subgroup.eq_top_iff']

alias ⟨IsHeckePair.commensurable, isHeckePair_of_commensurable⟩ := isHeckePair_iff

/-- To check that `K` is a Hecke subgroup it is enough to bound one of the two relative
indices: the other follows by conjugating by `g⁻¹`. -/
theorem isHeckePair_of_relIndex {K : Subgroup G}
    (hrel : ∀ g : G, (ConjAct.toConjAct g • K).relIndex K ≠ 0) : IsHeckePair K := by
  refine isHeckePair_of_commensurable fun g => ⟨hrel g, ?_⟩
  have key := Subgroup.relIndex_pointwise_smul (h := ConjAct.toConjAct g)
    ((ConjAct.toConjAct g)⁻¹ • K) K
  rw [smul_inv_smul] at key
  rw [key, ← map_inv]
  exact hrel g⁻¹

/-- A normal subgroup is a Hecke subgroup: it is its own conjugates. -/
theorem isHeckePair_of_normal (K : Subgroup G) [K.Normal] : IsHeckePair K :=
  isHeckePair_of_commensurable fun g => by
    rw [(‹K.Normal›).conjAct (ConjAct.toConjAct g)]


namespace IsHeckePair

variable {K : Subgroup G}

/-- For a Hecke pair, the stabiliser in `K` of the coset `g K` is `K ∩ g K g⁻¹`. -/
theorem stabilizer_eq (g : G) :
    MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K) =
      (ConjAct.toConjAct g • K).subgroupOf K := by
  ext ⟨k, hk⟩
  have key : ((⟨k, hk⟩ : K) • (QuotientGroup.mk g : G ⧸ K)) = QuotientGroup.mk (k * g) := rfl
  simp only [MulAction.mem_stabilizer_iff, key, QuotientGroup.eq, Subgroup.mem_subgroupOf,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
    ConjAct.ofConjAct_toConjAct, inv_inv]
  rw [show (k * g)⁻¹ * g = (g⁻¹ * k * g)⁻¹ by group]
  exact K.inv_mem_iff

/-- The left cosets met by the right coset `K g` are exactly the `K`-orbit of `g K` in
`G ⧸ K`. -/
theorem image_mk_eq_orbit (g : G) :
    ((QuotientGroup.mk : G → G ⧸ K) '' ((K : Set G) * {g}))
      = MulAction.orbit K (QuotientGroup.mk g : G ⧸ K) := by
  rw [Set.mul_singleton, Set.image_image]
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    exact ⟨k, hk, rfl⟩

/-- **The finiteness underlying the Hecke algebra.** For a Hecke pair, the right coset `K g`
meets only finitely many left cosets of `K`; equivalently `K g K` is a finite union of left
cosets.

This is stated in the form in which the FLT project's `AbstractHeckeOperator.heckeOperator`
takes it as a hypothesis, so that for a Hecke pair that hypothesis is always available. -/
theorem finite_image_mk (hK : IsHeckePair K) (g : G) :
    ((QuotientGroup.mk : G → G ⧸ K) '' ((K : Set G) * {g})).Finite := by
  have himg := image_mk_eq_orbit (K := K) g
  have hfi : (MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K)).FiniteIndex := by
    rw [stabilizer_eq]
    exact ⟨(hK.commensurable g).1⟩
  have : Finite (K ⧸ MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K)) :=
    Subgroup.finite_quotient_of_finiteIndex
  rw [himg]
  exact Set.finite_coe_iff.mp
    (Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer K
      (QuotientGroup.mk g : G ⧸ K)).symm)

end IsHeckePair

end Subgroup
