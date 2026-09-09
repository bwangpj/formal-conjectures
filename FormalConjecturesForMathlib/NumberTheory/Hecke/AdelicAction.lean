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

public import FormalConjecturesForMathlib.NumberTheory.AutomorphicForm.BorelJacquet
public import FormalConjecturesForMathlib.NumberTheory.Hecke.LocalEmbedding
public import FormalConjecturesForMathlib.NumberTheory.Hecke.Padic
public import FormalConjecturesForMathlib.NumberTheory.Hecke.Spherical
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

@[expose] public section

/-!
# The spherical Hecke operators at `p` acting on automorphic forms

The group homomorphism `GL n ℚ_[p] →* GL n 𝔸ᶠ[ℤ, ℚ]` placing a `p`-adic matrix at the place
`p` and the identity matrix at every other place, and the action of the spherical Hecke
algebra at `p` on automorphic forms that it induces.

Pulling back the right translation representation of `G(𝔸_f)` on the automorphic forms along
this embedding gives a representation of `GL n ℚ_[p]`, where `GL n ℤ_[p]` *is* a Hecke pair
(`Matrix.GeneralLinearGroup.isHeckePair_integralSubgroup_padic`); so the spherical Hecke
operators of `FormalConjecturesForMathlib.NumberTheory.Hecke.Spherical` act on the
`GL n ℤ_[p]`-invariant automorphic forms directly, and no Hecke pair inside `GL n 𝔸ᶠ` is
needed.

## Main declarations

* `padicToFiniteAdeles`: the embedding `GL n ℚ_[p] →* GL n 𝔸ᶠ[ℤ, ℚ]`, the composite of
  Mathlib's identification of `ℚ_[p]` with the completion of `ℚ` at the height-one prime
  `(p)` of `ℤ` (`Padic.adicCompletionEquiv`) with the local embedding
  `IsDedekindDomain.FiniteAdeleRing.localGL` at that place.
* `localRepresentation`: right translation on the automorphic forms, restricted to
  `GL n ℚ_[p]` along this embedding.
* `IsUnramifiedAt`: an automorphic form is unramified at `p` when it is fixed by right
  translation by (the image of) `GL n ℤ_[p]`.
* `adelicHeckeT p i`: the spherical Hecke operator `T_{p,i}`, at the double coset of
  `diag (p, …, p, 1, …, 1)` with `i` entries `p`, acting on the unramified-at-`p`
  automorphic forms.
-/

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing Rat.HeightOneSpectrum

open scoped IsDedekindDomain.FiniteAdeleRing

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- The height-one prime of `ℤ` attached to a prime number `p`. -/
noncomputable def placeOfPrime (p : Nat.Primes) : HeightOneSpectrum ℤ :=
  (primesEquiv (R := ℤ)).symm p

/-- **The `p`-adic points inside the finite-adelic points**: the group homomorphism
`GL n ℚ_[p] →* GL n 𝔸ᶠ[ℤ, ℚ]` identifying `ℚ_[p]` with the completion of `ℚ` at the place
`(p)`, then placing the matrix there and the identity matrix at every other place. -/
noncomputable def padicToFiniteAdeles (p : Nat.Primes) : GL n ℚ_[p] →* GL n 𝔸ᶠ[ℤ, ℚ] :=
  (localGL (placeOfPrime p)).comp
    (Matrix.GeneralLinearGroup.map
      (Padic.adicCompletionEquiv ℤ p).toAlgEquiv.toRingEquiv.toRingHom)

/-! ### The local action on automorphic forms -/

section LocalAction

variable [Nonempty n]

/-- Right translation on the automorphic forms, restricted to `GL n ℚ_[p]` along
`padicToFiniteAdeles`: the representation of `GL n ℚ_[p]` through which the spherical Hecke
algebra at `p` acts on the global object. -/
noncomputable def localRepresentation (p : Nat.Primes) :
    Representation ℂ (GL n ℚ_[p]) (automorphicForms n) :=
  (rightTranslation n).comp (padicToFiniteAdeles p)

/-- An automorphic form is **unramified at `p`** when it is fixed by right translation by
(the image of) `GL n ℤ_[p]`. This is the condition under which the spherical Hecke operators
at `p` act on it. -/
def IsUnramifiedAt (p : Nat.Primes) (f : automorphicForms n) : Prop :=
  f ∈ (localRepresentation p).subgroupInvariants (integralSubgroup n ℤ_[p] ℚ_[p])

theorem isUnramifiedAt_iff {p : Nat.Primes} {f : automorphicForms n} :
    IsUnramifiedAt p f ↔ ∀ g ∈ integralSubgroup n ℤ_[p] ℚ_[p],
      rightTranslation n (padicToFiniteAdeles p g) f = f :=
  Representation.mem_subgroupInvariants

end LocalAction

/-! ### The Hecke operators `T_{p,i}` -/

section HeckeOperator

/-- `p` as a unit of `ℚ_[p]`: the uniformizer at which the spherical Hecke operators sit. -/
noncomputable def padicUnit (p : Nat.Primes) : ℚ_[p]ˣ :=
  Units.mk0 ((p : ℕ) : ℚ_[p]) (Nat.cast_ne_zero.mpr p.2.ne_zero)

@[simp]
theorem val_padicUnit (p : Nat.Primes) : (padicUnit p : ℚ_[p]) = ((p : ℕ) : ℚ_[p]) := rfl

variable {m : ℕ} [NeZero m]

/-- **The spherical Hecke operator `T_{p,i}` on automorphic forms**: the Hecke operator at
the double coset of `diag (p, …, p, 1, …, 1)`, with `i` entries `p`, acting on the
`GL m ℤ_[p]`-invariant (i.e. unramified-at-`p`) automorphic forms. It exists with no further
hypotheses because `GL m ℤ_[p]` is a Hecke subgroup of `GL m ℚ_[p]`. -/
noncomputable def adelicHeckeT (p : Nat.Primes) (i : ℕ) :
    (localRepresentation (n := Fin m) p).subgroupInvariants
        (integralSubgroup (Fin m) ℤ_[p] ℚ_[p]) →ₗ[ℂ]
      (localRepresentation (n := Fin m) p).subgroupInvariants
        (integralSubgroup (Fin m) ℤ_[p] ℚ_[p]) :=
  T (localRepresentation p) (fun _ ha => PadicInt.finite_quotient_span_singleton ha)
    (padicUnit p) i

/-- `T_{p,0}` is the identity. -/
@[simp]
theorem adelicHeckeT_zero (p : Nat.Primes) :
    adelicHeckeT (m := m) p 0 = LinearMap.id :=
  T_zero _ _ _

end HeckeOperator

end Matrix.GeneralLinearGroup
