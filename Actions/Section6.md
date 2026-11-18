# §6 Asian options

Paper: Lyasoff pp. 1088–1095 (pricing identity (6.1), delta, Tables 1–4).

@import "Section6.svg" {code_block=false, caption="Subsection dependencies within §6"}

Subsections follow Lean import order; labels are mathematical English.

- [Upper incomplete Gamma `Γ(s, x)` used in Asian inner integrals](Section6/UpperGamma.md)
- [Real Asian inner integral `S_{k,p}(α)` and closed forms](Section6/Sfun.md)
- [Complex Asian inner integral `S_{k,p}(A)` for complex rate `A`](Section6/SfunC.md)
- [Strike-derivative kernel `S'_{k,p}(A)` for complex rate `A`](Section6/SfunDerivC.md)
- [Strike derivative of `SfunC`: `∂_k S_{k,p}(A) = S'_{k,p}(A)`](Section6/SfunCDeriv.md)
- [Complex rate factor `A(u,w)` in the Asian π/2 integrand](Section6/Afun.md)
- [Jacobian–Girsanov factor `B(w)` in the Asian integrand](Section6/Bfun.md)
- [Contour prefactor `C(u,w)` of the π/2-formula](Section6/Cfun.md)
- [Asian complex integrand `F_{t,σ,μ,k}(u,w)`](Section6/Ffun.md)
- [Strike-derivative Asian integrand `F'_{t,σ,μ,k}(u,w)`](Section6/FfunDeriv.md)
- [Density ingredients for the Asian pricing identity](Section6/AsianDensity.md)
- [Asian call price and strike delta](Section6/Asian.md)
- [Numerical table parameter regimes](Section6/TableParams.md)
- [Classical numerical certificates for Tables 1–4](Section6/TableClassical.md)
- [Interval enclosure claims for Tables 1–4](Section6/TableClaim.md)
