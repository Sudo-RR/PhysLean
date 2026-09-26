/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.InnerProductSpace.PiL2
/-!

# Analytic functions are non-zero on a dense set

## i. Overview

By the identity principle, an analytic function on a connected normed space which vanishes on a
non-empty open set vanishes everywhere. Hence an analytic function which is non-zero at one point
is non-zero on a dense set.

This is how domains of phase space cut out by the non-vanishing of polynomial functions of the
coordinates are shown to be dense, for instance the domains on which Hamiltonian systems are shown
to be Liouville integrable. To make the analyticity of such polynomial functions automatic, the
coordinate functionals on Euclidean space are shown to be analytic and tagged for `fun_prop`.

## ii. Key results

- `AnalyticOnNhd.dense_setOf_ne_zero` : a function analytic on a connected space and non-zero at
  some point is non-zero on a dense set.
- `analyticAt_euclideanSpace_apply` : coordinate functionals on Euclidean space are analytic.

## iii. Table of contents

- A. Density of the non-vanishing set
- B. Analyticity of coordinate functionals
-/

@[expose] public section

open Filter Topology

/-!

## A. Density of the non-vanishing set

-/

/-- A function analytic on a connected space, and non-zero at some point, is non-zero on a dense
set. -/
lemma AnalyticOnNhd.dense_setOf_ne_zero {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [PreconnectedSpace E] {f : E → F} (hf : AnalyticOnNhd 𝕜 f Set.univ) {x₀ : E}
    (hx₀ : f x₀ ≠ 0) : Dense {x | f x ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro W hW ⟨z, hz⟩
  by_contra h
  have hzero : f =ᶠ[𝓝 z] 0 := by
    filter_upwards [hW.mem_nhds hz] with y hy
    by_contra hne
    exact h ⟨y, hy, hne⟩
  exact hx₀ (congrFun (hf.eq_of_eventuallyEq analyticOnNhd_const hzero) x₀)

/-!

## B. Analyticity of coordinate functionals

-/

/-- The coordinate functionals on Euclidean space are analytic. -/
@[fun_prop]
lemma analyticAt_euclideanSpace_apply {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] (i : ι)
    (z : EuclideanSpace 𝕜 ι) : AnalyticAt 𝕜 (fun x : EuclideanSpace 𝕜 ι => x i) z :=
  (EuclideanSpace.proj (𝕜 := 𝕜) i).analyticAt z
