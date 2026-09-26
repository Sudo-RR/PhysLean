/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import PhyslibAlpha.ClassicalMechanics.LiouvilleIntegrable.Basic
public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
/-!

# The harmonic oscillator is Liouville integrable

## i. Overview

The one-dimensional harmonic oscillator has one degree of freedom, so it is Liouville integrable
wherever the gradient of its Hamiltonian does not vanish, by
`LiouvilleIntegrableOn.oneDegreeOfFreedom`. The gradient `(p / m, k q)` vanishes only at the
equilibrium `(p, q) = (0, 0)`, so integrability holds on the complement of the origin of phase
space, which is open and dense.

## ii. Key results

- `HarmonicOscillator.liouvilleIntegrable` : the harmonic oscillator is Liouville integrable on the
  complement of the origin of phase space.

## iii. Table of contents

- A. Integrability of the harmonic oscillator
-/

@[expose] public section

namespace ClassicalMechanics

namespace HarmonicOscillator

open Time
open scoped ContDiff

variable (S : HarmonicOscillator)

/-!

## A. Integrability of the harmonic oscillator

-/

/-- The harmonic oscillator, with its Hamiltonian as the single conserved quantity, is Liouville
integrable on the complement of the origin of phase space. -/
noncomputable def liouvilleIntegrable (t : Time) :
    LiouvilleIntegrableOn {x : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) | x ≠ 0}
      (S.hamiltonian t) :=
  LiouvilleIntegrableOn.oneDegreeOfFreedom isOpen_ne (dense_compl_singleton 0)
    (by
      refine ContDiff.contDiffOn ?_
      rw [hamiltonian_eq]
      fun_prop)
    (fun x hx h => by
      simp only [gradient_hamiltonian_momentum_eq, gradient_hamiltonian_position_eq] at h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      simp only [smul_eq_zero, one_div, inv_eq_zero, S.m_ne_zero, S.k_ne_zero, false_or] at h1 h2
      exact hx (Prod.ext h1 h2))

end HarmonicOscillator

end ClassicalMechanics
