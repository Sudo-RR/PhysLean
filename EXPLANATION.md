# Plain-English explanation of this PR

> **Note to reviewers/maintainers:** this file is a plain-language companion to the change, meant
> to make review easier for anyone skimming the PR. It is not part of the formal library and
> should be deleted before merging.

## What PhysLib is doing here

PhysLib states every physics result as a formal proof in the Lean theorem prover: no step is
taken on faith, and every algebraic manipulation, use of calculus, or appeal to an earlier result
is checked mechanically. Once something is proved, it becomes a permanent, reusable fact that
later results can build on, the same way a textbook theorem can be cited.

## What already existed for the simple pendulum

Before this PR, PhysLib already had, for the simple gravity pendulum of mass $m$, rod length
$\ell$, and gravitational acceleration $g$:

- its Lagrangian and equation of motion, $\ddot\theta + \dfrac{g}{\ell}\sin\theta = 0$;
- conservation of energy along any solution;
- the two equilibria (hanging and inverted) and the energy thresholds separating libration from
  rotation;
- existence and uniqueness of solutions given an initial angle and angular velocity, plus
  time-reversal symmetry;
- the small-angle limit, where the pendulum behaves as a harmonic oscillator with period
  $2\pi\sqrt{\ell/g}$;
- the classical **nonlinear** period formula,
  $$
  T(\theta_0) = 4\sqrt{\ell/g}\; K\!\left(\sin^2(\theta_0/2)\right),
  $$
  where $K$ is the complete elliptic integral of the first kind, together with all its properties
  as a function (it's even in $\theta_0$, continuous, strictly increasing in the amplitude,
  bounded, and reduces to $2\pi\sqrt{\ell/g}$ at $\theta_0 = 0$).

## The gap this PR starts to close

That last formula was, until now, only ever a statement about the elliptic integral $K$. Nobody
had connected it back to an actual solution of the pendulum's equation of motion. It had every
property a period *should* have, but it wasn't yet proved to *be* the period of anything moving.

Formally closing that gap needs several ingredients, each substantial on its own:

1. the motion released from rest at $\theta_0$ reaches the bottom of its swing ($\theta = 0$) in
   finite time, moving monotonically the whole way down;
2. that time-to-descend can be written as a specific integral;
3. a trigonometric substitution turns that integral into exactly $K(\sin^2(\theta_0/2))$;
4. all of this assembles into an actual periodicity statement, which additionally needs the
   motion to be shown to exist for *all* time (currently PhysLib only has existence over a short
   interval near the start).

None of that is done yet. This PR is a first, self-contained step underneath all of it.

## What this PR actually proves

The classical derivation of the period formula starts by multiplying the equation of motion by
the angular velocity $\dot\theta$ and integrating once. Physically, this is just conservation of
energy. For a pendulum **released from rest** at angle $\theta_0$ — meaning it starts at
$\theta_0$ with zero angular velocity, rather than being given a push — the kinetic energy is
zero and the potential energy is $mg\ell(1 - \cos\theta_0)$ at the moment of release. Since total
energy never changes, at any later instant

$$
\underbrace{\tfrac{1}{2} m\ell^2 \dot\theta^2}_{\text{kinetic energy}} +
\underbrace{mg\ell(1-\cos\theta)}_{\text{potential energy}}
= mg\ell(1-\cos\theta_0),
$$

which rearranges to the classical quadrature

$$
\dot\theta^{\,2} = \frac{2g}{\ell}\left(\cos\theta - \cos\theta_0\right).
$$

This PR adds a new file, `ReleasedFromRest.lean`, proving exactly this — formally, for any genuine
solution of the pendulum's equation of motion satisfying the "released from rest at $\theta_0$"
initial conditions. It's proved in three equivalent forms, from least to most simplified:

1. **Raw form**, with the moment of inertia and mass not yet cancelled:
   $$ I\dot\theta^{\,2} = 2mg\ell(\cos\theta - \cos\theta_0). $$
2. **Mass-cancelled form**, using the pendulum's natural frequency $\omega = \sqrt{g/\ell}$:
   $$ \dot\theta^{\,2} = 2\omega^2(\cos\theta - \cos\theta_0). $$
3. **Classical form**, matching Landau & Lifshitz, *Mechanics*, §11, Problem 1, verbatim:
   $$ \dot\theta^{\,2} = \frac{2g}{\ell}(\cos\theta - \cos\theta_0). $$

The proof needs no new machinery: it's a direct algebraic consequence of the
`energy_conservation_of_equationOfMotion'` lemma already in the library
(`SimplePendulum/Basic.lean`), specialized to the two boundary values of the energy at the release
instant.

This PR also updates the `TODO` note in `PeriodFormula.lean` to record that this piece is done,
and to point future contributors at the new file.

## What's still open

Everything listed above under "the gap" remains open: the monotonicity of the descent, turning
the pointwise relation above into an actual integral for the time of descent, the trigonometric
substitution (including handling the fact that the resulting integral is singular at one
endpoint), and the final assembly into a genuine periodicity theorem, which in turn needs a
global (not just local) existence result for the pendulum's solutions. This PR does not attempt
any of those; it only supplies the energy relation they will all build on.
