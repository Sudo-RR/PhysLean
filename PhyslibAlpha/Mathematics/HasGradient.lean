/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Physlib.Mathematics.Calculus.Gradient
/-!

# Calculus rules for `HasGradientAt`

## i. Overview

Mathlib defines `HasGradientAt f f' x`, that `f'` is the gradient of `f` at `x`, but records no
rules for building it from simpler functions. This file records the rules for sums, differences,
products, and composition with a real function, together with the basic gradients on a real inner
product space: those of `y ↦ ⟪a, y⟫`, `y ↦ ⟪y, a⟫`, `y ↦ ⟪y, y⟫` and `y ↦ ‖y‖`, and that of a
coordinate functional on Euclidean space.

Stating gradients as `HasGradientAt` rather than computing `gradient` directly establishes
differentiability and the value of the gradient together. This is how the gradients of the
conserved quantities of central-force systems, built from `⟪p, p⟫`, `⟪q, q⟫`, `⟪q, p⟫` and `‖q‖`,
are computed.

## ii. Key results

- `HasGradientAt.add`, `HasGradientAt.sub`, `HasGradientAt.mul`, `HasGradientAt.const_mul` : the
  algebraic rules.
- `HasDerivAt.comp_hasGradientAt` : the chain rule for a real function of a real-valued function.
- `hasGradientAt_inner_left`, `hasGradientAt_inner_right`, `hasGradientAt_inner_self`,
  `hasGradientAt_norm`, `hasGradientAt_coord` : the basic gradients.

## iii. Table of contents

- A. Algebraic rules
- B. The chain rule
- C. Basic gradients
  - C.1. Scalar products
  - C.2. The norm
  - C.3. Coordinate functionals on Euclidean space

## iv. References

* Mathlib, `Mathlib.Analysis.Calculus.Gradient.Basic`.
-/

@[expose] public section

open InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F}

/-!

## A. Algebraic rules

-/

/-- The gradient of a sum is the sum of the gradients. -/
lemma HasGradientAt.add (hf : HasGradientAt f f' x) (hg : HasGradientAt g g' x) :
    HasGradientAt (fun y => f y + g y) (f' + g') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  simp only [map_add]
  exact hf.add hg

/-- The gradient of a difference is the difference of the gradients. -/
lemma HasGradientAt.sub (hf : HasGradientAt f f' x) (hg : HasGradientAt g g' x) :
    HasGradientAt (fun y => f y - g y) (f' - g') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  simp only [map_sub]
  exact hf.sub hg

/-- The gradient of a product is given by the Leibniz rule. -/
lemma HasGradientAt.mul (hf : HasGradientAt f f' x) (hg : HasGradientAt g g' x) :
    HasGradientAt (fun y => f y * g y) (f x • g' + g x • f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  simp only [map_add, map_smul]
  exact hf.mul hg

/-- The gradient of a constant multiple is the constant multiple of the gradient. -/
lemma HasGradientAt.const_mul (c : ℝ) (hf : HasGradientAt f f' x) :
    HasGradientAt (fun y => c * f y) (c • f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  simp only [map_smul]
  exact hf.const_mul c

/-!

## B. The chain rule

-/

/-- The chain rule: the gradient of `y ↦ φ (f y)` is `φ'` times the gradient of `f`, for `φ'` the
derivative of `φ` at `f x`. -/
lemma HasDerivAt.comp_hasGradientAt {φ : ℝ → ℝ} {φ' : ℝ} (hf : HasGradientAt f f' x)
    (hφ : HasDerivAt φ φ' (f x)) : HasGradientAt (fun y => φ (f y)) (φ' • f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  simp only [map_smul]
  exact hφ.comp_hasFDerivAt x hf

/-!

## C. Basic gradients

-/

/-!

### C.1. Scalar products

-/

/-- The gradient of `y ↦ ⟪a, y⟫` is `a`. -/
lemma hasGradientAt_inner_left (a x : F) : HasGradientAt (fun y : F => ⟪a, y⟫_ℝ) a x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (toDual ℝ F a).hasFDerivAt

/-- The gradient of `y ↦ ⟪y, a⟫` is `a`. -/
lemma hasGradientAt_inner_right (a x : F) : HasGradientAt (fun y : F => ⟪y, a⟫_ℝ) a x := by
  simp_rw [real_inner_comm a]
  exact hasGradientAt_inner_left a x

/-- The gradient of `y ↦ ⟪y, y⟫` is `2 • y`. -/
lemma hasGradientAt_inner_self (x : F) : HasGradientAt (fun y : F => ⟪y, y⟫_ℝ) ((2 : ℝ) • x) x := by
  rw [← gradient_inner_self x]
  exact (differentiableAt_fun_id.inner ℝ differentiableAt_fun_id).hasGradientAt

/-!

### C.2. The norm

-/

/-- Away from the origin, the gradient of the norm is the unit vector `‖x‖⁻¹ • x`. -/
lemma hasGradientAt_norm (hx : x ≠ 0) : HasGradientAt (fun y : F => ‖y‖) (‖x‖⁻¹ • x) x := by
  have hs : ⟪x, x⟫_ℝ ≠ 0 := by simpa using hx
  have h := (Real.hasDerivAt_sqrt hs).comp_hasGradientAt (hasGradientAt_inner_self x)
  simp only [← norm_eq_sqrt_real_inner] at h
  convert h using 1
  rw [smul_smul]
  congr 1
  field_simp

/-!

### C.3. Coordinate functionals on Euclidean space

-/

/-- The gradient of the `i`-th coordinate functional on Euclidean space is the `i`-th basis
vector. -/
lemma hasGradientAt_coord {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (x : EuclideanSpace ℝ ι) :
    HasGradientAt (fun y : EuclideanSpace ℝ ι => y i) (EuclideanSpace.single i 1) x := by
  rw [← gradient_coord i x]
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.hasGradientAt
