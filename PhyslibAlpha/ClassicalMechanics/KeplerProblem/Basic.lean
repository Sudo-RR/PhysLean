/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import PhyslibAlpha.ClassicalMechanics.CentralForce.Basic
/-!

# The Kepler problem

## i. Overview

The Kepler problem is the motion of a particle of mass `m` attracted to a fixed centre by an
inverse-square force, derived from the potential `V r = -k / r` with coupling constant `k > 0`
(`k = G M m` for a planet of mass `m` orbiting a star of mass `M`). It is the central-force system
with this potential, so its Hamiltonian is

$$H(p, q) = \frac{\langle p, p\rangle}{2m} - \frac{k}{\|q\|}.$$

## ii. Key results

- `KeplerProblem` : the input data, a mass and a coupling constant.
- `KeplerProblem.toCentralForce` : the Kepler problem as a central-force system.
- `KeplerProblem.hamiltonian` : the Hamiltonian, and `KeplerProblem.hamiltonian_eq` its explicit
  form.

## iii. Table of contents

- A. The input data
- B. The Kepler problem as a central-force system

## iv. References

* H. Goldstein, C. Poole and J. Safko, *Classical Mechanics*, 3rd edition, Chapter 3.
-/

@[expose] public section

namespace ClassicalMechanics

open InnerProductSpace

/-!

## A. The input data

-/

/-- The Kepler problem: a particle of mass `m` attracted to a fixed centre by the inverse-square
force derived from the potential `-k / r`, for a coupling constant `k`. -/
structure KeplerProblem where
  /-- The mass of the particle. -/
  m : ℝ
  /-- The coupling constant of the inverse-square force. -/
  k : ℝ
  /-- The mass of the particle is positive. -/
  m_pos : 0 < m
  /-- The force is attractive. -/
  k_pos : 0 < k

namespace KeplerProblem

variable (S : KeplerProblem)

/-!

## B. The Kepler problem as a central-force system

-/

/-- The Kepler problem as a central-force system, with potential `V r = -k / r`. -/
noncomputable def toCentralForce : CentralForce where
  m := S.m
  V := fun r => -S.k / r
  m_pos := S.m_pos
  contDiffOn_V := contDiffOn_const.div contDiffOn_id fun _ hr => ne_of_gt hr

/-- The Hamiltonian of the Kepler problem, as a function of the momentum and the position. -/
noncomputable def hamiltonian (p q : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  S.toCentralForce.hamiltonian p q

/-- The Hamiltonian of the Kepler problem is `⟪p, p⟫ / (2 m) - k / ‖q‖`. -/
lemma hamiltonian_eq (p q : EuclideanSpace ℝ (Fin 3)) :
    S.hamiltonian p q = (1 / (2 * S.m)) * ⟪p, p⟫_ℝ - S.k / ‖q‖ := by
  simp only [hamiltonian, CentralForce.hamiltonian, toCentralForce, neg_div, sub_eq_add_neg]

end KeplerProblem

end ClassicalMechanics
