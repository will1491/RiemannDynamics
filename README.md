# Complex Dynamics, Teichmüller Theory & Hyperbolic Geometry in Lean 4

An ongoing formalization following McMullen's course notes *Riemann surfaces, dynamics and geometry*.

## Highlighted Theorems

Headline results formalized so far — click to jump to the Lean source. Each is
sorry-free and depends only on the three standard Lean axioms (`propext`,
`Classical.choice`, `Quot.sound`).

1. **Sullivan's No Wandering Domains theorem** — [`sullivan_no_wandering_domains`](RiemannDynamics/Dynamics/NoWanderingDomains.lean#L454): no Fatou component of a rational map of degree at least two wanders. Equivalently, in positive form, [`fatouComponent_isEventuallyPeriodic`](RiemannDynamics/Dynamics/NoWanderingDomains.lean#L477): every Fatou component is eventually periodic.
2. **Measurable Riemann Mapping theorem** — [`mrmt_exists`](RiemannDynamics/QC/MRMT/Existence.lean#L537): every Beltrami coefficient `‖μ‖∞ < 1` admits a quasiconformal solution of `∂̄f = μ ∂f`; [`mrmt_unique_normalized`](RiemannDynamics/QC/MRMT/Uniqueness.lean#L401): the solution normalized by `f 0 = 0`, `f 1 = 1` is unique; [`mrmt_holomorphic_dependence_principal`](RiemannDynamics/QC/MRMT/AnalyticDependence.lean#L64): the principal solution depends holomorphically on the coefficient.
3. **Uniformization theorem** — [`uniformization_trichotomy`](RiemannDynamics/Uniformization/Trichotomy.lean#L180): every simply connected Riemann surface is biholomorphic to the unit disc, the complex plane, or the Riemann sphere.
4. **Equivalence of the analytic and geometric definitions of quasiconformality** — [`qc_analytic_iff_geometric`](RiemannDynamics/QC/Equivalence.lean#L984): for `1 ≤ K`, a map carries an analytic-quasiconformal structure with Beltrami norm at most `(K−1)/(K+1)` if and only if it is `K`-quasiconformal in the geometric (modulus) sense.
5. **Montel–Carathéodory (strong Montel) theorem** — [`montel_caratheodory_sphere`](RiemannDynamics/NormalFamilies/StrongMontel/SphereMontel.lean#L37): a family of sphere-holomorphic maps omitting three fixed values is normal.
6. **Schwarz–Pick inequality** — [`schwarzPick`](RiemannDynamics/Hyperbolic/DiskModel/SchwarzPick.lean#L89): a holomorphic self-map of the open unit disk is non-expansive for the Poincaré hyperbolic distance.

## Foundations

Built on Mathlib, plus two vendored projects consumed directly rather than re-derived:

- **RMT4** (Beffara) — the Riemann mapping theorem and the normal-families / Montel / Hurwitz / Schwarz scaffolding the dynamics line builds on.
- **Carleson** (van Doorn et al., pinned at `v4.29.0`) — two-sided Calderón–Zygmund theory; the Beurling kernel `(z − ζ)⁻²` is registered as a two-sided CZ kernel, which is what gives the transform its `Lᵖ` bounds.

No new `axiom`, no `sorry`.

## Collaborators

- **Will (Ziang) Li** — primary maintainer; design and formalization.
- [**Yusheng Luo**](https://sites.google.com/view/yushengmath/home) (Cornell, Department of Mathematics) — mathematical advisor; domain expert in complex dynamics, Teichmüller theory, and hyperbolic geometry.
- [**Ziyang Qin**](https://qinziyang.com) — Lean 4 expert; technical guidance on tactic infrastructure, Mathlib idioms, and large-scale proof engineering. (See also Ziyang's [differential geometry library](https://github.com/qinz1yang/differential-geometry).)

## Installation

Ensure you have [Lean 4](https://lean-lang.org/lean4/doc/setup.html) installed.

```bash
# Clone the repository
git clone https://github.com/will1491/RiemannDynamics
cd RiemannDynamics

# Build the library
lake build
```

## References

The abstractions and formalizations in this library are heavily inspired by and built upon the following sources:

- McMullen, C. T. *Riemann surfaces, dynamics and geometry.* Course notes, Harvard University. [Available here.](https://people.math.harvard.edu/~ctm/papers/home/text/class/notes/rs/course.pdf) **(Primary reference.)**
- McMullen, C. T. *Complex Dynamics and Renormalization.* Annals of Mathematics Studies 135, Princeton University Press. (ISBN 978-0-691-02981-8)
- Ahlfors, L. V. *Lectures on Quasiconformal Mappings.* 2nd ed. AMS University Lecture Series 38. (ISBN 978-0-8218-3644-6)
- Hubbard, J. H. *Teichmüller Theory and Applications to Geometry, Topology, and Dynamics*, Vol. 1: Teichmüller Theory. Matrix Editions. (ISBN 978-0-9715766-2-9)
- Farb, B., & Margalit, D. *A Primer on Mapping Class Groups.* Princeton Mathematical Series 49. (ISBN 978-0-691-14794-9)

## AI Disclaimer

Generative AI (Claude) was used in the development of this codebase. The high-level architecture is human-designed; AI agents assisted with formalizing individual proofs and writing boilerplate. All definitions and core theorem statements were human-verified for correctness. Since all proofs are verified by Lean's type checker, AI-generated and human-written code are held to the same standard of correctness.
