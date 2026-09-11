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

A **C-algebraic** automorphic eigenform should have attached `p`-adic Galois representations
whose Frobenius characteristic polynomials are its Hecke polynomials. This is the unramified
local-global compatibility clause of Buzzard-Gee's Conjecture 3.2.1 — the reciprocity half of
the Langlands correspondence — in the weakest form that can be stated faithfully today.

Precisely: let `f` be a C-algebraic automorphic eigenform for `GL m / ℚ`, unramified outside a
finite set `S`, whose Hecke eigensystems are algebraic, given in `ℚ̄` through a fixed embedding
`j : ℚ̄ → ℂ`. Then for every prime `p` and embedding `ι : ℚ̄ → ℚ̄_p` there should be a
continuous representation of `Gal(ℚ̄/ℚ)` on `GL m ℚ̄_p`, unramified at each place of residue
characteristic `ℓ ∉ S ∪ {p}`, where the characteristic polynomial of arithmetic Frobenius is
`ι` of the Hecke polynomial at `ℓ`.

## Eigenvalues in `ℚ̄`

Buzzard-Gee fix an isomorphism `ℂ ≅ ℚ̄_p`, which exists only by choice. Taking the eigensystems
in `ℚ̄` instead, moved around by the embeddings `j` and `ι` — of which there provably are some —
is licensed exactly by the algebraicity of the eigenvalues, which is Clozel's conjecture
(`FormalConjectures.Langlands.ClozelAlgebraicity.clozel_algebraicity`). Algebraicity is
therefore consumed as a hypothesis rather than restated, and the two conjectures stay modular.

## Normalisation: C-algebraic hypothesis, with the twist to L inside the Hecke polynomial

A `GL m ℚ̄_p`-valued representation can match Satake parameters on the nose only in the
L-normalisation, which is why Buzzard-Gee assume `π` L-algebraic — at the price of the `√ℓ` in
their normalised Satake isomorphism. Here the hypothesis is `IsCAlgebraic`, and the
compensating half-integral twist (the one carrying C-algebraic forms to L-algebraic ones, as
in the classical `rec (π_ℓ ⊗ |det| ^ ((1 - m) / 2))` statements) is encoded in
`Satake.heckePolynomialOver` itself: in terms of the unitary Satake parameters `α` of `f` at
`ℓ`, the coset operator eigenvalues are `a i = ℓ ^ (i * (m - i) / 2) * eᵢ α`, the twisted
Frobenius eigenvalues are `α j * ℓ ^ ((m - 1) / 2)`, and their elementary symmetric functions
are `ℓ ^ (i * (m - 1) / 2 - i * (m - i) / 2) * a i = ℓ ^ (i * (i - 1) / 2) * a i` — the
coefficients of the Hecke polynomial. The half-integral powers cancel, so the polynomial has
integer powers of `ℓ` only, is defined over `ℚ̄` with no choice of `√ℓ`, and transports along
`ι` at all. This is the renormalisation Buzzard-Gee attribute to Clozel and Gross.

Frobenius is **arithmetic**: `ValuationSubring.IsFrobeniusAt` asks for `x ↦ x ^ ℓ` on the
residue field. Buzzard-Gee use geometric Frobenius; the statements differ by inverting, which
reverses characteristic polynomials.

Sanity check, `m = 2`: the polynomial is `X ^ 2 - a 1 * X + ℓ * a 2`, which for a weight `k`
eigenform is `X ^ 2 - a_ℓ * X + ε ℓ * ℓ ^ (k - 1)` — Deligne's representation — and for
`k = 2` is `X ^ 2 - a_ℓ * X + ℓ`, arithmetic Frobenius on the Tate module of an elliptic
curve. Weight `k` forms are C-algebraic for `k` even, so hypothesis and conclusion agree in
the one case where both sides are classical.

## What "weak" leaves out

Of the four clauses of Conjecture 3.2.1 only unramified local-global compatibility is stated.
Dropped: **de Rham at `p`** with Hodge-Tate weights read off from the archimedean parameter,
and crystallinity at unramified `p` — the clause carrying the arithmetic content, not statable
while Mathlib's `B_dR` has no Galois action, filtration, or notion of de Rham representation;
**the clause at the real place** (image of complex conjugation); **compatibility at the
ramified primes** (needs local Langlands); and **uniqueness, semisimplicity and irreducibility
of `ρ`** (Brauer-Nesbitt and Chebotarev are not in Mathlib, so only existence is asserted).
Cuspidality is not imposed, condition (e) of Borel-Jacquet not being formalised.

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

/-- At the place `A` of `ℚ̄` over `ℓ`, the representation `ρ` is unramified, and every
arithmetic Frobenius element at `A` has characteristic polynomial the Hecke polynomial of the
eigensystem `a`, moved into `ℚ̄_p` along `ι`. This is the local condition of weak
reciprocity, at one place. -/
def MatchesHeckeAt {m : ℕ} (p : Nat.Primes) (ι : AlgebraicClosure ℚ →+* PadicAlgCl p)
    (a : Fin (m + 1) → AlgebraicClosure ℚ) (ρ : GaloisGroupRat →* GL (Fin m) (PadicAlgCl p))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) : Prop :=
  IsUnramifiedAt ℚ A ρ ∧
    ∀ σ : GaloisGroupRat, IsFrobeniusAt ℚ A ℓ σ →
      Matrix.charpoly (↑(ρ σ) : Matrix (Fin m) (Fin m) (PadicAlgCl p))
        = (Satake.heckePolynomialOver ℓ a).map ι

/-- **Weak reciprocity** for `GL m` over `ℚ`: a C-algebraic automorphic eigenform with
algebraic Hecke eigensystems has, for each `p` and each embedding of `ℚ̄` into `ℚ̄_p`, an
attached continuous `p`-adic Galois representation which is unramified outside `S ∪ {p}` and
whose arithmetic Frobenius characteristic polynomials are the Hecke polynomials.

This is the unramified local-global compatibility clause of Buzzard-Gee's Conjecture 3.2.1,
with the de Rham condition at `p`, the condition at the real place, and uniqueness all omitted;
see the module documentation for the conventions and for what is left out. -/
@[category research open, AMS 11]
theorem weak_reciprocity (m : ℕ) [NeZero m]
    -- a C-algebraic automorphic eigenform for `GL m / ℚ`
    (f : automorphicForms (Fin m)) (hf : IsAutomorphicEigenform f) (hC : IsCAlgebraic f)
    -- whose Hecke eigensystems outside `S` are the algebraic numbers `a`, viewed in `ℂ`
    -- through the embedding `j`
    (S : Finset Nat.Primes) (j : AlgebraicClosure ℚ →+* ℂ)
    (a : Nat.Primes → Fin (m + 1) → AlgebraicClosure ℚ)
    (ha : ∀ ℓ ∉ S, HasHeckeEigensystemAt ℓ f fun i => j (a ℓ i))
    -- a coefficient prime `p`, with an embedding of `ℚ̄` into `ℚ̄_p`
    (p : Nat.Primes) (ι : AlgebraicClosure ℚ →+* PadicAlgCl p) :
    -- then some continuous `p`-adic Galois representation matches the Hecke data of `f`
    -- at every place over every prime `ℓ ∉ S ∪ {p}`
    ∃ ρ : GaloisGroupRat →* GL (Fin m) (PadicAlgCl p), Continuous ρ ∧
      ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : Nat.Primes),
        ℓ ∉ S → ℓ ≠ p → CharP (IsLocalRing.ResidueField A) (ℓ : ℕ) →
          MatchesHeckeAt p ι (a ℓ) ρ A ℓ := by
  sorry

end WeakReciprocity
