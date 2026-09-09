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

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

@[expose] public section

/-!
# The local factor of `GL n` of the finite adeles

The embedding `GL n K_v → GL n 𝔸ᶠ` placing a local matrix at the place `v` and the identity
matrix at every other place.

This is what lets the local Hecke operators act on a global object. There is no need for a
Hecke pair inside `GL n 𝔸ᶠ`: pulling back along this embedding makes any representation of
`GL n 𝔸ᶠ` into one of `GL n K_v`, where `GL n O_v` *is* a Hecke pair, so the coset sums of
`Representation.heckeOperator` apply directly.

Note that the map is not induced by a ring homomorphism `K_v → 𝔸ᶠ`; placing an element at one
place and zero elsewhere does not preserve `1`. It is multiplicative on matrices because the
off-`v` components are all the identity matrix, whose products are again the identity.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Classical in
/-- The adele equal to `x` at `v` and to the image of `y : K` at every other place. -/
noncomputable def singleAt (v : HeightOneSpectrum R) (x : v.adicCompletion K) (y : R) :
    𝔸ᶠ[R, K] :=
  RestrictedProduct.mk
    (Function.update (fun w : HeightOneSpectrum R => (algebraMap R (w.adicCompletion K)) y) v x)
    (by
      filter_upwards [Set.Finite.compl_mem_cofinite (Set.finite_singleton v)] with w hw
      have hwv : w ≠ v := by simpa using hw
      simp only [Function.update_of_ne hwv]
      exact coe_mem_adicCompletionIntegers w y)

@[simp]
theorem singleAt_apply_self (v : HeightOneSpectrum R) (x : v.adicCompletion K) (y : R) :
    singleAt v x y v = x := by
  classical
  show Function.update
    (fun w : HeightOneSpectrum R => (algebraMap R (w.adicCompletion K)) y) v x v = x
  simp

open scoped Classical in
@[simp]
theorem singleAt_apply_of_ne {v w : HeightOneSpectrum R} (hw : w ≠ v)
    (x : v.adicCompletion K) (y : R) :
    singleAt v x y w = (algebraMap R (w.adicCompletion K)) y := by
  show Function.update
    (fun u : HeightOneSpectrum R => (algebraMap R (u.adicCompletion K)) y) v x w = _
  simp [Function.update_of_ne hw]

@[simp] theorem mul_apply (a b : 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (a * b) v = a v * b v := rfl

@[simp] theorem one_apply (v : HeightOneSpectrum R) : (1 : 𝔸ᶠ[R, K]) v = 1 := rfl

@[simp] theorem zero_apply (v : HeightOneSpectrum R) : (0 : 𝔸ᶠ[R, K]) v = 0 := rfl

@[simp] theorem add_apply (a b : 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (a + b) v = a v + b v := rfl

variable (R K) in
/-- Evaluation of a finite adele at the place `v`, as a ring homomorphism. -/
def evalRingHom (v : HeightOneSpectrum R) : 𝔸ᶠ[R, K] →+* v.adicCompletion K where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v :=
  map_sum (evalRingHom R K v) f s

open scoped Classical in
/-- The matrix over `𝔸ᶠ` equal to `M` at `v` and to the identity matrix elsewhere. -/
noncomputable def localMatrix (v : HeightOneSpectrum R)
    (M : Matrix n n (v.adicCompletion K)) : Matrix n n 𝔸ᶠ[R, K] :=
  Matrix.of fun i j => singleAt v (M i j) (if i = j then 1 else 0)

omit [Fintype n] in
@[simp]
theorem localMatrix_apply_self (v : HeightOneSpectrum R) (M : Matrix n n (v.adicCompletion K))
    (i j : n) : (localMatrix v M i j) v = M i j := by
  simp [localMatrix]

omit [Fintype n] in
theorem localMatrix_apply_of_ne {v w : HeightOneSpectrum R} (hw : w ≠ v)
    (M : Matrix n n (v.adicCompletion K)) (i j : n) :
    (localMatrix v M i j) w = (1 : Matrix n n (w.adicCompletion K)) i j := by
  classical
  rw [localMatrix, Matrix.of_apply, singleAt_apply_of_ne hw, Matrix.one_apply]
  split <;> simp

omit [Fintype n] in
theorem localMatrix_one (v : HeightOneSpectrum R) :
    localMatrix v (1 : Matrix n n (v.adicCompletion K)) = 1 := by
  ext i j w
  rcases eq_or_ne w v with rfl | hw
  · rw [localMatrix_apply_self, Matrix.one_apply, Matrix.one_apply,
      apply_ite (fun x : 𝔸ᶠ[R, K] => x w), one_apply, zero_apply]
  · rw [localMatrix_apply_of_ne hw, Matrix.one_apply, Matrix.one_apply,
      apply_ite (fun x : 𝔸ᶠ[R, K] => x w), one_apply, zero_apply]

theorem localMatrix_mul (v : HeightOneSpectrum R)
    (M N : Matrix n n (v.adicCompletion K)) :
    localMatrix v (M * N) = localMatrix v M * localMatrix v N := by
  ext i j w
  rw [Matrix.mul_apply, sum_apply]
  rcases eq_or_ne w v with rfl | hw
  · rw [localMatrix_apply_self, Matrix.mul_apply]
    simp only [mul_apply, localMatrix_apply_self]
  · rw [localMatrix_apply_of_ne hw]
    simp only [mul_apply, localMatrix_apply_of_ne hw]
    rw [← Matrix.mul_apply, one_mul]

/-- **The local embedding of general linear groups**: the group homomorphism
`GL n K_v →* GL n 𝔸ᶠ` placing a local matrix at the place `v` and the identity matrix at
every other place. It is not induced by a ring homomorphism `K_v → 𝔸ᶠ`, but it is
multiplicative because the off-`v` components are all the identity matrix. -/
noncomputable def localGL (v : HeightOneSpectrum R) :
    GL n (v.adicCompletion K) →* GL n 𝔸ᶠ[R, K] where
  toFun g :=
    ⟨localMatrix v g.val, localMatrix v g.inv,
      by rw [← localMatrix_mul, g.val_inv, localMatrix_one],
      by rw [← localMatrix_mul, g.inv_val, localMatrix_one]⟩
  map_one' := Units.ext (localMatrix_one v)
  map_mul' g h := Units.ext (localMatrix_mul v g.val h.val)

@[simp]
theorem coe_localGL (v : HeightOneSpectrum R) (g : GL n (v.adicCompletion K)) :
    (localGL v g : Matrix n n 𝔸ᶠ[R, K]) = localMatrix v (g : Matrix n n (v.adicCompletion K)) :=
  rfl

end IsDedekindDomain.FiniteAdeleRing
