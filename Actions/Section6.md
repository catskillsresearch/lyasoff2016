# §6 Asian options

Paper: Lyasoff pp. 1088–1095 (pricing identity (6.1), delta, Tables 1–4).

The market price used in the table claims is $e^{-rT}(S_0/T)\,\mathbb{E}\bigl[(\int_0^T e^{\sigma W+(r-\sigma^2/2)s}\,ds-KT/S_0)_+\bigr]$ with $S_0=1$ (`asianMarketPrice`). Table enclosures are classical numerical certificates from the paper’s mpmath/spline quadratures (not IA re-proofs).

@import "../Lyasoff2016/UpperGamma.lean"
@import "../Lyasoff2016/Sfun.lean"
@import "../Lyasoff2016/SfunC.lean"
@import "../Lyasoff2016/SfunDerivC.lean"
@import "../Lyasoff2016/SfunCDeriv.lean"
@import "../Lyasoff2016/Afun.lean"
@import "../Lyasoff2016/Bfun.lean"
@import "../Lyasoff2016/Cfun.lean"
@import "../Lyasoff2016/Ffun.lean"
@import "../Lyasoff2016/FfunDeriv.lean"
@import "../Lyasoff2016/AsianDensity.lean"
@import "../Lyasoff2016/Asian.lean"
@import "../Lyasoff2016/TableParams.lean"
@import "../Lyasoff2016/TableClassical.lean"
@import "../Lyasoff2016/TableClaim.lean"
