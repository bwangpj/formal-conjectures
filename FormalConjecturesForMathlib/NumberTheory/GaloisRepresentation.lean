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

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

/-!
# Frobenius elements and unramified Galois representations

The vocabulary needed to say that a representation of an absolute Galois group is unramified
at a place and to name its Frobenius characteristic polynomial there, for an arbitrary, in
particular infinite, Galois extension.

A place of `L` over `K` is a valuation subring `A` of `L`, and Mathlib already provides its
decomposition subgroup `A.decompositionSubgroup K`, the stabiliser of `A` in `L ≃ₐ[K] L`, and
its inertia subgroup `A.inertiaSubgroup K`, the kernel of the action of the decomposition
subgroup on the residue field of `A`. Both are stated for an arbitrary extension, so with
`L = AlgebraicClosure ℚ` they are subgroups of the absolute Galois group
`Field.absoluteGaloisGroup ℚ`, and no finiteness is needed anywhere below.

The residue field action that cuts out inertia is also what names a Frobenius: at a place with
residue field of cardinality `q`, an element of the decomposition subgroup is a Frobenius
exactly when it acts on the residue field as `x ↦ x ^ q`. So `IsFrobeniusAt` needs no theory
beyond the action Mathlib already has, and in particular no choice of Frobenius element.

## Main declarations

* `ValuationSubring.residueAut`: the action of the decomposition subgroup on the residue
  field, as a homomorphism to its ring automorphisms. Its kernel is `inertiaSubgroup`.
* `ValuationSubring.IsFrobeniusAt`: an element of `L ≃ₐ[K] L` lies in the decomposition
  subgroup at `A` and acts on the residue field by `x ↦ x ^ q`.
* `ValuationSubring.IsUnramifiedAt`: a homomorphism out of `L ≃ₐ[K] L` kills inertia at `A`.
* `ValuationSubring.IsFrobeniusAt.isConj_of_isUnramifiedAt`: at an unramified place, any two
  Frobenius elements have the same image, so the characteristic polynomial of the image is well
  defined without choosing one.

## Implementation notes

A Frobenius is characterised by its action rather than constructed, which is what keeps this
elementary. Existence of a Frobenius at a place, and conjugacy of the Frobenii at the places
over a fixed place of `K`, are theorems that are not proved here; Mathlib has both at finite
level, in `Mathlib.RingTheory.Frobenius`. Statements below quantify over Frobenius elements
rather than picking one, so neither is needed.
-/

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

/-- The action of the decomposition subgroup at `A` on the residue field of `A`, as a
homomorphism to the ring automorphisms of the residue field. By definition
`A.inertiaSubgroup K` is its kernel. -/
noncomputable def residueAut (A : ValuationSubring L) :
    A.decompositionSubgroup K →* RingAut (IsLocalRing.ResidueField A) :=
  MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)

theorem inertiaSubgroup_eq_ker (A : ValuationSubring L) :
    A.inertiaSubgroup K = MonoidHom.ker (residueAut K A) := rfl

theorem mem_inertiaSubgroup_iff {A : ValuationSubring L} {σ : A.decompositionSubgroup K} :
    σ ∈ A.inertiaSubgroup K ↔ residueAut K A σ = 1 := Iff.rfl

/-- `σ` is a **Frobenius at `A`** for residue cardinality `q`: it stabilises `A`, and the
automorphism it induces on the residue field of `A` is `x ↦ x ^ q`.

At a place whose residue field is finite of cardinality `q`, or more generally whose residue
field is an algebraic closure of `𝔽_q`, this pins down the Frobenius up to inertia, which is
all that a characteristic polynomial sees (`IsFrobeniusAt.isConj_of_isUnramifiedAt`). -/
def IsFrobeniusAt (A : ValuationSubring L) (q : ℕ) (σ : L ≃ₐ[K] L) : Prop :=
  ∃ hσ : σ ∈ A.decompositionSubgroup K,
    ∀ x : IsLocalRing.ResidueField A, residueAut K A ⟨σ, hσ⟩ x = x ^ q

theorem IsFrobeniusAt.mem_decompositionSubgroup {A : ValuationSubring L} {q : ℕ}
    {σ : L ≃ₐ[K] L} (h : IsFrobeniusAt K A q σ) : σ ∈ A.decompositionSubgroup K :=
  h.1

/-- A homomorphism out of `L ≃ₐ[K] L` is **unramified at `A`** when it kills the inertia
subgroup at `A`. For a Galois representation this is the usual condition, and it is what makes
the image of a Frobenius independent of the choice of Frobenius. -/
def IsUnramifiedAt (A : ValuationSubring L) {G : Type*} [Group G]
    (ρ : (L ≃ₐ[K] L) →* G) : Prop :=
  ∀ σ ∈ A.inertiaSubgroup K, ρ (σ : L ≃ₐ[K] L) = 1

/-- At an unramified place any two Frobenius elements have the same image, so a Frobenius
characteristic polynomial is well defined even though a Frobenius element is not. -/
theorem IsFrobeniusAt.eq_of_isUnramifiedAt {A : ValuationSubring L} {q : ℕ}
    {G : Type*} [Group G] {ρ : (L ≃ₐ[K] L) →* G} (hρ : IsUnramifiedAt K A ρ)
    {σ τ : L ≃ₐ[K] L} (hσ : IsFrobeniusAt K A q σ) (hτ : IsFrobeniusAt K A q τ) :
    ρ σ = ρ τ := by
  obtain ⟨hσd, hσf⟩ := hσ
  obtain ⟨hτd, hτf⟩ := hτ
  -- `τ⁻¹ * σ` lies in the decomposition subgroup and acts trivially on the residue field
  have hmem : (⟨τ, hτd⟩ : A.decompositionSubgroup K)⁻¹ * ⟨σ, hσd⟩ ∈ A.inertiaSubgroup K := by
    rw [mem_inertiaSubgroup_iff, map_mul, map_inv]
    have h1 : residueAut K A ⟨σ, hσd⟩ = residueAut K A ⟨τ, hτd⟩ := by
      ext x
      rw [hσf x, hτf x]
    rw [h1, inv_mul_cancel]
  have := hρ _ hmem
  rw [Subgroup.coe_mul, InvMemClass.coe_inv, map_mul, map_inv] at this
  rw [← mul_one (ρ τ), ← this, mul_inv_cancel_left]

end ValuationSubring
