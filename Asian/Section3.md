# §3 Fokker–Planck and Dufresne

Paper: Lyasoff pp. 1067–1071 (infinite-horizon flux, joint Fokker–Planck).

@import "Section3.svg" {code_block=false, caption="Subsection dependencies within §3"}

Subsections follow Lean import order; labels are mathematical English.

- [Fokker–Planck characterization of the joint law](Section3/FokkerPlanck.md)
- [Dufresne's inverse-gamma density for the infinite-horizon integral](Section3/Dufresne.md)
- [Diffusion generator L = ½σ²x² ∂ₓₓ + (1 + (ν + σ²/2)x) ∂ₓ](Section3/Generator.md)
- [Stationary process Z_t from two independent BMs](Section3/Zproc.md)
- [Time-reversed twin of `expInt` and basic measurability/continuity](Section3/ExpIntTwin.md)
- [Ito identities for product test functions along `(expInt, W)`, used by…](Section3/JointFokkerPlanckIto.md)
- [Paper (3.5) operator `jointA` and product-test identities](Section3/JointA.md)
- [Expanded formal Fokker–Planck adjoint](Section3/JointFokkerPlanckAdjoint.md)
- [Generator of `(expIntTwin, B)` on product test functions](Section3/TwinGenerator.md)
- [Probability flux in the `x` direction](Section3/JointFlux.md)
- [Second-order operator A_t from the Fokker–Planck argument](Section3/Aop.md)
- [Path functional: reciprocal power of the finite-horizon `Z`](Section3/ZpowPath.md)
- [Path-space reciprocal of the finite-horizon `Z` process](Section3/InvZFromPaths.md)
- [Path-space perpetuity functional](Section3/PerpetuityPath.md)
- [Distributional Fokker–Planck equation and inverse-argument Laplace transform for `(∫₀ᵗ…](Section3/DistFokkerPlanck.md)
- [Expected Itô formula for functionals of `(∫₀ᵗ a(B_s) ds, B_t)` and the](Section3/ExpectedIto.md)
- [Smooth cutoff `expInvCut u x = if 0 < x then exp(-u / x) else 0` and its…](Section3/ExpInvCut.md)
- [Analytic helpers for `fokker_planck_joint`: open joint domain and pointwise upgrade](Section3/JointFokkerPlanckHelpers.md)
