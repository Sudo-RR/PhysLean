/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import Physlib.Mathematics.ForMathlib.Analytic
public import PhyslibAlpha.ClassicalMechanics.CentralForce.AngularMomentum
/-!

# An open dense domain for central-force integrability

An application of analytic non-vanishing to a domain in central-force phase space.

## i. Overview

We consider phase-space points with non-zero radial momentum and angular momentum not parallel
to the z-axis. These conditions define an open dense domain away from the centre of force,
used in the subsequent proof of independence of the observables `H`, `L²` and `L_z`.
Density follows by expressing the domain as the non-vanishing set of a polynomial that is
non-zero at an explicit point. No independence or integrability result is asserted here.

## ii. Key results

- `CentralForce.integrabilityDomain` : the chosen domain in phase space.
- `CentralForce.isOpen_integrabilityDomain`, `CentralForce.dense_integrabilityDomain` : it is
  open and dense.
- `CentralForce.snd_ne_zero_of_mem_integrabilityDomain` : it excludes the centre of force.

## iii. Table of contents

- A. The domain of integrability

## iv. References

The density argument uses the analytic identity principle in
`Mathlib.Analysis.Analytic.Uniqueness`. For the integrability framework, see
`PhyslibAlpha.ClassicalMechanics.LiouvilleIntegrable.Basic`.
-/

@[expose] public section

namespace ClassicalMechanics.CentralForce

open InnerProductSpace

attribute [local fun_prop] analyticAt_fst analyticAt_snd

/-!

## A. The domain of integrability

-/

/-- The phase-space domain where the radial momentum is non-zero and the angular momentum
is not parallel to the z-axis, used to establish central-force integrability. -/
def integrabilityDomain : Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  {x | ⟪x.2, x.1⟫_ℝ ≠ 0 ∧ angularMomentum x.1 x.2 0 ^ 2 + angularMomentum x.1 x.2 1 ^ 2 ≠ 0}

/-- The domain is the non-vanishing set of a polynomial in the phase-space coordinates. -/
lemma integrabilityDomain_eq : integrabilityDomain =
    {x | (x.1 0 * x.2 0 + x.1 1 * x.2 1 + x.1 2 * x.2 2) *
      ((x.2 1 * x.1 2 - x.2 2 * x.1 1) ^ 2 + (x.2 2 * x.1 0 - x.2 0 * x.1 2) ^ 2) ≠ 0} := by
  ext x
  simp only [integrabilityDomain, Set.mem_ofPred_eq, mul_ne_zero_iff, angularMomentum_apply_zero,
    angularMomentum_apply_one, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    conj_trivial]

/-- The chosen central-force domain is open. -/
lemma isOpen_integrabilityDomain : IsOpen integrabilityDomain := by
  rw [integrabilityDomain_eq]
  exact isOpen_ne_fun (by fun_prop) continuous_const

/-- The chosen central-force domain is dense. -/
lemma dense_integrabilityDomain : Dense integrabilityDomain := by
  rw [integrabilityDomain_eq]
  refine AnalyticOnNhd.dense_setOf_ne_zero (𝕜 := ℝ) (fun z _ => by fun_prop)
    (x₀ := (!₂[1, 0, 1], !₂[1, 0, 0])) ?_
  norm_num [Matrix.cons_val_two]

/-- The chosen domain excludes the centre of force. -/
lemma snd_ne_zero_of_mem_integrabilityDomain
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)} (hx : x ∈ integrabilityDomain) :
    x.2 ≠ 0 := by
  intro h
  exact hx.1 (by rw [h, inner_zero_left])

end ClassicalMechanics.CentralForce
