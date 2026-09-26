/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import Physlib.ClassicalMechanics.PoissonBracket
/-!

# Computing Poisson brackets

## i. Overview

Further properties of `poissonBracket` from `Physlib.ClassicalMechanics.PoissonBracket`, used to
compute the brackets between the conserved quantities of Hamiltonian systems: the bracket of a
function with itself vanishes, and the bracket of two functions whose partial gradients are known,
in the form of `HasGradientAt` statements, is given explicitly by those gradients.

## ii. Key results

- `poissonBracket_self` : every phase-space function Poisson-commutes with itself.
- `poissonBracket_eq_of_hasGradientAt` : the Poisson bracket in terms of known partial gradients.

## iii. Table of contents

- A. The bracket of a function with itself
- B. The bracket from known gradients
-/

@[expose] public section

open InnerProductSpace

namespace ClassicalMechanics

variable {X} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-!

## A. The bracket of a function with itself

-/

/-- The Poisson bracket of a phase-space function with itself vanishes. -/
lemma poissonBracket_self (f : X → X → ℝ) (p q : X) : poissonBracket f f p q = 0 := by
  have h := poissonBracket_antisymm f f p q
  linarith

/-!

## B. The bracket from known gradients

-/

/-- The Poisson bracket of two phase-space functions whose partial gradients at `(p, q)` are
known. -/
lemma poissonBracket_eq_of_hasGradientAt {f g : X → X → ℝ} {p q fp fq gp gq : X}
    (hfp : HasGradientAt (fun p' => f p' q) fp p) (hfq : HasGradientAt (fun q' => f p q') fq q)
    (hgp : HasGradientAt (fun p' => g p' q) gp p) (hgq : HasGradientAt (fun q' => g p q') gq q) :
    poissonBracket f g p q = ⟪fq, gp⟫_ℝ - ⟪fp, gq⟫_ℝ := by
  rw [poissonBracket, hfq.gradient, hgp.gradient, hfp.gradient, hgq.gradient]

end ClassicalMechanics
