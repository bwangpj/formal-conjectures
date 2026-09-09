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

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

/-! # Smith normal form for matrices over a principal ideal domain

`Mathlib.LinearAlgebra.FreeModule.PID` provides the Smith normal form of a *submodule* of a free
module over a PID: a basis of the ambient module together with elements scaling it to a basis of
the submodule. This file deduces the classical statement for *matrices*: a square matrix with
nonzero determinant over a PID can be written `U * diagonal d * V` with `U` and `V` invertible.

## Main results

* `Matrix.exists_smith_normal_form`: a square matrix with nonzero determinant over a principal
  ideal domain is `U * diagonal d * V` for some invertible `U` and `V`.

## Implementation notes

The matrix is read as a linear endomorphism of `n → R`. Its determinant being nonzero makes it
injective, so its range has full rank, and `Submodule.smithNormalFormOfRankEq` applies to give a
basis `bM` of `n → R` and a basis `bN` of the range with `bN i = a i • bM (f i)`. Pulling `bN`
back along the injection gives a second basis `c` of `n → R` on which the map is diagonal, and
the two changes of basis are the invertible factors.

The embedding `f` produced by the submodule version is a bijection here, both index types having
the same cardinality, and `d` is `a` transported along it.

## Upstreaming

This file is written to Mathlib conventions and is intended for Mathlib, where it belongs at
`Mathlib/LinearAlgebra/Matrix/SmithNormalForm.lean`. Only the copyright header needs changing:
Mathlib wants `Copyright (c) 2026 <author>. All rights reserved.`, which this repository's
header check rejects.

## Tags

matrix, smith normal form, principal ideal domain, elementary divisors
-/

open Matrix Module

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Smith normal form** for a square matrix with nonzero determinant over a principal ideal
domain: it factors as `U * diagonal d * V` with `U` and `V` invertible. -/
theorem Matrix.exists_smith_normal_form (A : Matrix n n R) (hA : A.det ≠ 0) :
    ∃ (U V : Matrix n n R) (d : n → R),
      IsUnit U.det ∧ IsUnit V.det ∧ A = U * Matrix.diagonal d * V := by
  classical
  set b : Basis n R (n → R) := Pi.basisFun R n with hb
  set T : (n → R) →ₗ[R] (n → R) := Matrix.toLin b b A with hT
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv0
    refine hA (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, ?_⟩)
    simpa [hT, hb, Matrix.toLin_eq_toLin', Matrix.toLin'_apply] using hv
  have hrank : finrank R (LinearMap.range T) = finrank R (n → R) :=
    LinearMap.finrank_range_of_inj hTinj
  set snf := Submodule.smithNormalFormOfRankEq b hrank with hsnf
  -- the embedding is a bijection, both index types having cardinality `card n`
  have hbij : Function.Bijective snf.f :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨snf.f.injective, by simp⟩
  set ef : Fin (Fintype.card n) ≃ n := Equiv.ofBijective snf.f hbij with hef
  -- the basis of the source on which `T` is diagonal
  set e : (n → R) ≃ₗ[R] LinearMap.range T := LinearEquiv.ofInjective T hTinj with he
  set c : Basis n R (n → R) := (snf.bN.map e.symm).reindex ef with hc
  set d : n → R := fun j => snf.a (ef.symm j) with hd
  have hTc : ∀ j, T (c j) = d j • snf.bM j := by
    intro j
    have h1 : (c j : n → R) = e.symm (snf.bN (ef.symm j)) := by
      simp [hc, Basis.reindex_apply, Basis.map_apply]
    have h2 : T (e.symm (snf.bN (ef.symm j))) = (snf.bN (ef.symm j) : n → R) := by
      simp [he]
    have hf : snf.f (ef.symm j) = j := Equiv.ofBijective_apply_symm_apply snf.f hbij j
    rw [h1, h2, snf.snf (ef.symm j), hf, hd]
  have hdiag : LinearMap.toMatrix c snf.bM T = Matrix.diagonal d := by
    ext i j
    rw [LinearMap.toMatrix_apply, hTc j, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one, Finsupp.single_apply, Matrix.diagonal_apply]
    rcases eq_or_ne i j with rfl | hne
    · simp
    · simp [hne, Ne.symm hne]
  have hU : Invertible (b.toMatrix ⇑snf.bM) := b.invertibleToMatrix snf.bM
  have hV : Invertible (c.toMatrix ⇑b) := c.invertibleToMatrix b
  refine ⟨b.toMatrix snf.bM, c.toMatrix b, d, Matrix.isUnit_det_of_invertible _,
    Matrix.isUnit_det_of_invertible _, ?_⟩
  have h1 := linearMap_toMatrix_mul_basis_toMatrix b c snf.bM T
  have h2 := basis_toMatrix_mul_linearMap_toMatrix b b snf.bM T
  rw [hdiag] at h1
  have h3 : (LinearMap.toMatrix b b) T = A := by rw [hT, LinearMap.toMatrix_toLin]
  rw [← h1, ← Matrix.mul_assoc, h3] at h2
  exact h2.symm
