/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import PhyslibAlpha.ClassicalMechanics.LiouvilleIntegrable.Basic
public import Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Hamiltonian
/-!

# The simple pendulum is Liouville integrable

## i. Overview

The simple pendulum has one degree of freedom, so it is Liouville integrable wherever the gradient
of its Hamiltonian does not vanish, by `LiouvilleIntegrableOn.oneDegreeOfFreedom`. The gradient
`(p / I, m g ℓ sin θ)` vanishes exactly at the equilibria, where the momentum vanishes and the
pendulum hangs straight down or stands straight up (`sin θ = 0`). Integrability therefore holds on
the complement of the equilibria, which is open, and dense because it contains every point of
non-zero momentum.

## ii. Key results

- `SimplePendulum.liouvilleIntegrable` : the simple pendulum is Liouville integrable away from its
  equilibria.

## iii. Table of contents

- A. Integrability of the simple pendulum
-/

@[expose] public section

namespace ClassicalMechanics

namespace SimplePendulum

open Time
open scoped ContDiff

variable (S : SimplePendulum)

/-!

## A. Integrability of the simple pendulum

-/

/-- The simple pendulum, with its Hamiltonian as the single conserved quantity, is Liouville
integrable away from its equilibria, the points of phase space where the momentum and `sin θ`
both vanish. -/
noncomputable def liouvilleIntegrable (t : Time) :
    LiouvilleIntegrableOn {x : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) |
      x.1 ≠ 0 ∨ Real.sin (x.2 0) ≠ 0} (S.hamiltonian t) :=
  LiouvilleIntegrableOn.oneDegreeOfFreedom
    ((isOpen_ne_fun continuous_fst continuous_const).union
      (isOpen_ne_fun (by fun_prop) continuous_const))
    (Dense.mono (fun _ hx => Or.inl hx)
      ((dense_compl_singleton 0).preimage isOpenMap_fst))
    (by
      refine ContDiff.contDiffOn ?_
      rw [hamiltonian_eq]
      fun_prop)
    (fun x hx h => by
      simp only [gradient_hamiltonian_momentum_eq, gradient_hamiltonian_position_eq,
        gradient_potentialEnergy] at h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      simp only [smul_eq_zero, one_div, inv_eq_zero, S.inertia_ne_zero, false_or,
        PiLp.single_eq_zero_iff, mul_eq_zero, S.m_ne_zero, S.g_ne_zero, S.ℓ_ne_zero] at h1 h2
      exact hx.elim (· h1) (· (h2.resolve_right one_ne_zero)))

end SimplePendulum

end ClassicalMechanics
