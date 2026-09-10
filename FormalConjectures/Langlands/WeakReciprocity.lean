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

import FormalConjecturesUtil

/-!
# Weak reciprocity for `GL m` over `ℚ`

An algebraic automorphic eigenform should have an attached `p`-adic Galois representation whose
Frobenius characteristic polynomials are its Hecke polynomials. This is the reciprocity half of
the Langlands correspondence, in the weakest form that can be stated faithfully today.

Precisely: let `f` be a C-algebraic automorphic eigenform for `GL m / ℚ`, unramified outside a
finite set `S` of primes, with Hecke eigensystems taking values in `ℚ̄` through a fixed
embedding `j : ℚ̄ → ℂ`. Then for every prime `p` and every embedding `ι : ℚ̄ → ℚ̄_p` there should
be a continuous representation `ρ` of the absolute Galois group of `ℚ` into `GL m ℚ̄_p`,
unramified at every place of residue characteristic outside `S ∪ {p}`, whose Frobenius
characteristic polynomial at such a place of residue characteristic `ℓ` is `ι` applied to the
Hecke polynomial of the eigensystem at `ℓ`.

## Why the eigenvalues are taken in `ℚ̄`

Buzzard-Gee state their conjecture relative to a fixed isomorphism of fields `ℂ ≅ ℚ̄_p`, which
exists but only by choice and is not constructible. The hypothesis here instead takes the
eigensystems in `ℚ̄` and uses an embedding `ℚ̄ → ℚ̄_p`, of which there provably are some. That
replacement is exactly what Clozel's algebraicity conjecture licenses: it says the eigenvalues
of a C-algebraic eigenform are algebraic, which is what lets them be named in `ℚ̄` in the first
place. So this statement consumes
`FormalConjectures.Langlands.ClozelAlgebraicity.clozel_algebraicity` as an input rather than
repeating it, and the factoring of the eigensystems through `ℚ̄` appears here as a hypothesis.

## Normalisation

This is where such a statement is most easily made silently false, so the conventions are
pinned down explicitly.

* **The Hecke polynomial is arithmetically normalised.** Buzzard-Gee normalise the Satake
  isomorphism in the standard way, twisted by half the sum of the positive roots, and observe
  that a square root of the residue characteristic then appears, so that the normalisation is
  not defined over `ℚ`; they note that Clozel and Gross avoid this by renormalising, and
  deliberately do not. `Satake.heckePolynomialOver` is that renormalisation, with only
  nonnegative integer powers of `ℓ`, which is why it transports along a ring homomorphism at
  all. Consequently the hypothesis here is `IsCAlgebraic` rather than `IsLAlgebraic`: the
  arithmetic normalisation pairs with C-algebraicity, and the two conventions differ by the
  twist `f ↦ f * |det| ^ ((m - 1) / 2)`, which is half-integral exactly when `m` is even.
* **Frobenius is arithmetic.** `ValuationSubring.IsFrobeniusAt` asks that the element act on
  the residue field by `x ↦ x ^ ℓ`, so it is the arithmetic Frobenius. Buzzard-Gee take a
  geometric Frobenius; the two statements differ by inverting, which on characteristic
  polynomials reverses the coefficients.
* **Sanity check.** For `m = 2` the Hecke polynomial is `X ^ 2 - a 1 * X + ℓ * a 2`. For a
  holomorphic eigenform of weight `k`, where `a 1 = a_ℓ` and `a 2 = ε ℓ * ℓ ^ (k - 2)`, this is
  `X ^ 2 - a_ℓ * X + ε ℓ * ℓ ^ (k - 1)`, which is Deligne's Galois representation, and for
  `k = 2` it is `X ^ 2 - a_ℓ * X + ℓ`, the characteristic polynomial of arithmetic Frobenius on
  the Tate module of an elliptic curve. Weight `k` holomorphic forms are C-algebraic for `k`
  even, so the hypothesis and the conclusion are consistent in the one case where both sides
  are classical.

## What "weak" leaves out

Buzzard-Gee's Conjecture 3.2.1 has four clauses. Only the second, unramified local-global
compatibility, is stated here. Dropped are:

* **de Rham at `p`, with the Hodge-Tate cocharacter read off from the weight**, and
  crystallinity when `p` is unramified. This is the clause carrying the arithmetic content, and
  it is not statable: Mathlib has the de Rham period ring only as a bare definition, with no
  Galois action, no filtration, and no notion of a de Rham representation.
* **The clause at the real place**, that the image of a complex conjugation is conjugate to an
  explicit element built from the archimedean parameter.
* **Local-global compatibility at the ramified primes**, which needs local Langlands.
* **Uniqueness and irreducibility of `ρ`.** Uniqueness up to isomorphism follows from
  Brauer-Nesbitt and Chebotarev, neither of which is in Mathlib, so only existence is asserted
  and no semisimplicity is imposed.

Nor is cuspidality imposed, condition (e) of the Borel-Jacquet definition not being formalised.

## References

- [BG14] K. Buzzard, T. Gee, *The conjectural connections between automorphic representations
  and Galois representations*, in Automorphic Forms and Galois Representations I, LMS Lecture
  Note Series 414 (2014), 135-187; Conjecture 3.2.1, and §2.2 for the Satake normalisation and
  the square root of `q`. https://arxiv.org/abs/1009.0785
- [Cl90] L. Clozel, *Motifs et formes automorphes: applications du principe de fonctorialité*,
  in Automorphic Forms, Shimura Varieties, and `L`-functions I, Perspect. Math. 10 (1990),
  77-159, where the Satake isomorphism is renormalised to be defined over `ℚ`.
- [Wikipedia](https://en.wikipedia.org/wiki/Langlands_program)
-/

namespace WeakReciprocity

open Matrix.GeneralLinearGroup ValuationSubring

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- The absolute Galois group of `ℚ`, as the automorphisms of a fixed algebraic closure. This
is `Field.absoluteGaloisGroup ℚ`, written out so that the Krull topology and Mathlib's
decomposition and inertia subgroups apply to it directly. -/
abbrev GaloisGroupRat := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- **Weak reciprocity** for `GL m` over `ℚ`: a C-algebraic automorphic eigenform with
algebraic Hecke eigensystems has, for each `p` and each embedding of `ℚ̄` into `ℚ̄_p`, an
attached continuous `p`-adic Galois representation which is unramified outside `S ∪ {p}` and
whose arithmetic Frobenius characteristic polynomials are the Hecke polynomials.

This is the unramified local-global compatibility clause of Buzzard-Gee's Conjecture 3.2.1,
with the de Rham condition at `p`, the condition at the real place, and uniqueness all omitted;
see the module documentation for the conventions and for what is left out. -/
@[category research open, AMS 11]
theorem weak_reciprocity (m : ℕ) [NeZero m] (f : automorphicForms (Fin m))
    (hf : IsAutomorphicEigenform f) (hC : IsCAlgebraic f) (S : Finset Nat.Primes)
    (j : AlgebraicClosure ℚ →+* ℂ) (a : Nat.Primes → Fin (m + 1) → AlgebraicClosure ℚ)
    (ha : ∀ ℓ ∉ S, HasHeckeEigensystemAt ℓ f fun i => j (a ℓ i))
    (p : Nat.Primes) (ι : AlgebraicClosure ℚ →+* PadicAlgCl p) :
    ∃ ρ : GaloisGroupRat →* GL (Fin m) (PadicAlgCl p), Continuous ρ ∧
      ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : Nat.Primes),
        ℓ ∉ S → ℓ ≠ p → CharP (IsLocalRing.ResidueField A) (ℓ : ℕ) →
          IsUnramifiedAt ℚ A ρ ∧
            ∀ σ : GaloisGroupRat, IsFrobeniusAt ℚ A (ℓ : ℕ) σ →
              Matrix.charpoly (↑(ρ σ) : Matrix (Fin m) (Fin m) (PadicAlgCl p))
                = (Satake.heckePolynomialOver (ℓ : ℕ) (a ℓ)).map ι := by
  sorry

end WeakReciprocity
