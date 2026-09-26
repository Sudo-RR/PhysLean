/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import PhyslibAlpha.ClassicalMechanics.KeplerProblem.Basic
public import PhyslibAlpha.ClassicalMechanics.LiouvilleIntegrable.CentralForce
/-!

# The Kepler problem is Liouville integrable

## i. Overview

The Kepler problem is a central-force system, so by `CentralForce.liouvilleIntegrable` it is
Liouville integrable, with the energy, the squared magnitude of the angular momentum and its
z-component as its three conserved quantities in involution. They are functionally independent on
the open dense domain `CentralForce.integrabilityDomain` of phase space, where the radial momentum
is non-zero and the angular momentum is not parallel to the z-axis.

## ii. Key results

- `KeplerProblem.liouvilleIntegrable` : the Kepler problem is Liouville integrable.

## iii. Table of contents

- A. Integrability of the Kepler problem
-/

@[expose] public section

namespace ClassicalMechanics

namespace KeplerProblem

variable (S : KeplerProblem)

/-!

## A. Integrability of the Kepler problem

-/

/-- The Kepler problem is Liouville integrable on the domain of phase space where the radial
momentum is non-zero and the angular momentum is not parallel to the z-axis, with the energy, the
squared magnitude of the angular momentum and its z-component as conserved quantities. -/
noncomputable def liouvilleIntegrable :
    LiouvilleIntegrableOn CentralForce.integrabilityDomain S.hamiltonian :=
  S.toCentralForce.liouvilleIntegrable

end KeplerProblem

end ClassicalMechanics
