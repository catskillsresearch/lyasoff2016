#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""Independent high-precision check of Lyasoff (2016) Tables 1-4.

Target quantity (Lean `asianMarketPrice`, Lyasoff2016/Asian.lean):
    e^{-rT} (1/T) E[(∫_0^T exp(σ W_s + (r - σ²/2) s) ds - K T)_+]
  = e^{-rT} E[(A_T - K)_+],   A_T = (1/T) ∫_0^T S_s ds,  S_0 = 1,
i.e. the standard continuously averaged arithmetic Asian call (no dividends).

Two representations, both independent of the paper's ∬ Re F quadrature:

  A. Geman–Yor (1993) Laplace transform in h = σ²T/4, written in closed form with
     Kummer's 1F1, inverted numerically with mpmath's Talbot contour (and optionally
     de Hoog) at high working precision:
       C = e^{-rT} (4 S0/(σ² T)) C^{(ν)}(h, q),  q = σ² K T/(4 S0),  ν = 2r/σ² - 1,
       ∫_0^∞ e^{-λh} C^{(ν)}(h,q) dh
         = c^α Γ(β) 1F1(α; μ+1; -c) / (Γ(μ+1) λ (λ - 2 - 2ν)),
       c = 1/(2q), μ = sqrt(2λ + ν²), α = (μ-ν)/2 - 1, β = (μ+ν)/2 + 2.

  B. Linetsky (2004, Oper. Res. 52(6), eq. (10)) spectral integral for the put
     (Whittaker W, continuous spectrum; the ν<0 incomplete-gamma term), then
     Asian put–call parity (eq. (4)).

Both are validated against Linetsky's 7 published 10-digit benchmarks (`--bench`).

Usage:
    python3 scripts/asian_tables_independent_check.py --bench
    python3 scripts/asian_tables_independent_check.py --tables [--dps 60] [--linetsky]
Requires: mpmath (pip install mpmath).
"""
from __future__ import annotations

import argparse
import sys
import time

import mpmath as mp

# --- representation A: Geman–Yor + Talbot ----------------------------------------------

def gy_call(r, sig, T, S0, K, method="talbot"):
    h = sig ** 2 * T / 4
    q = sig ** 2 * K * T / (4 * S0)
    nu = 2 * r / sig ** 2 - 1
    c = 1 / (2 * q)

    def F(lam):
        mu = mp.sqrt(2 * lam + nu ** 2)
        a = (mu - nu) / 2 - 1
        b = (mu + nu) / 2 + 2
        return c ** a * mp.gamma(b) * mp.hyp1f1(a, mu + 1, -c) / (
            mp.gamma(mu + 1) * lam * (lam - 2 - 2 * nu))

    Ch = mp.invertlaplace(F, h, method=method)
    return mp.exp(-r * T) * 4 * S0 / (sig ** 2 * T) * Ch

# --- representation B: Linetsky spectral integral ----------------------------------------

def linetsky_call(r, sig, T, S0, K, width=2, tail=mp.mpf(10) ** -45):
    tau = sig ** 2 * T / 4
    k = tau * K / S0
    nu = 2 * r / sig ** 2 - 1
    z = 1 / (2 * k)
    pref = (2 * k) ** ((nu + 3) / 2) * mp.exp(-1 / (4 * k))

    def f(p):
        if p == 0:
            return mp.mpf(0)
        return (mp.exp(-(nu ** 2 + p ** 2) * tau / 2) * pref
                * mp.re(mp.whitw(-(nu + 3) / 2, 1j * p / 2, z))
                * abs(mp.gamma((nu + 1j * p) / 2)) ** 2 * mp.sinh(mp.pi * p) * p)

    # integrate on [0, P] in panels of `width`, stopping once |f| has fallen below
    # `tail` times its running maximum (Gaussian factor e^{-p²τ/2} dominates the tail).
    total = mp.mpf(0)
    fmax = mp.mpf(0)
    a = mp.mpf(0)
    while True:
        b = a + width
        total += mp.quad(f, [a, (a + b) / 2, b])
        fb = abs(f(b))
        fmax = max(fmax, fb, abs(f((a + b) / 2)))
        a = b
        if a > 4 and fmax > 0 and fb < tail * fmax and a ** 2 * tau / 2 > 60:
            break
    P = total / (8 * mp.pi ** 2)
    an = abs(nu)
    if nu < 0:
        P += (2 * k * mp.gammainc(an, z) - mp.gammainc(an - 1, z)) / (2 * mp.gamma(an))
    if nu < -2:
        raise NotImplementedError("ν < -2 terms not needed for these tables")
    put = mp.exp(-r * T) * 4 * S0 / (sig ** 2 * T) * P
    if r == 0:
        fwd = S0 - K
    else:
        fwd = (1 - mp.exp(-r * T)) / (r * T) * S0 - mp.exp(-r * T) * K
    return put + fwd

# --- data -------------------------------------------------------------------------------

def bench_cases():
    F = mp.mpf
    return [  # (r, σ, T, S0, K, Linetsky 2004 Table 3 value)
        (F(2) / 100, F(1) / 10, F(1), F(2), F(2), "0.0559860415"),
        (F(18) / 100, F(3) / 10, F(1), F(2), F(2), "0.2183875466"),
        (F(125) / 10000, F(1) / 4, F(2), F(2), F(2), "0.1722687410"),
        (F(5) / 100, F(1) / 2, F(1), F(19) / 10, F(2), "0.1931737903"),
        (F(5) / 100, F(1) / 2, F(1), F(2), F(2), "0.2464156905"),
        (F(5) / 100, F(1) / 2, F(1), F(21) / 10, F(2), "0.3062203648"),
        (F(5) / 100, F(1) / 2, F(2), F(2), F(2), "0.3500952190"),
    ]


def table_data():
    F = mp.mpf
    strikes = [F(7) / 10, F(8) / 10, F(9) / 10, F(1), F(11) / 10, F(12) / 10]
    printed = {
        1: ["0.302471713826246", "0.203823272652937", "0.109134667336200",
            "0.038694821814008", "0.008127776133751", "0.001028464610034"],
        2: ["0.30256324113", "0.20574087443", "0.11939786084",
            "0.05691875027", "0.02222765943", "0.00727337085"],
        3: ["0.304923087645", "0.208572293433", "0.120806302805",
            "0.056156816264", "0.020689114929", "0.006174095598"],
        4: ["0.30620859092", "0.21565075810", "0.13878233268",
            "0.08160208509", "0.04425815874", "0.02244768617"],
    }
    params = {1: (F(1) / 2, F(22) / 100, F(10) ** -15),
              2: (F(1) / 2, F(1) / 3, F(10) ** -11),
              3: (F(1), F(22) / 100, F(10) ** -12),
              4: (F(1), F(1) / 3, F(10) ** -11)}
    return strikes, printed, params


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--bench", action="store_true")
    ap.add_argument("--tables", action="store_true")
    ap.add_argument("--dps", type=int, default=60)
    ap.add_argument("--linetsky", action="store_true", help="also run representation B")
    ap.add_argument("--dehoog", action="store_true", help="also invert GY with de Hoog")
    ap.add_argument("--only", type=int, default=0, help="restrict to one table")
    args = ap.parse_args(argv)
    mp.mp.dps = args.dps
    if args.bench:
        for (r, s, T, S0, K, ref) in bench_cases():
            t0 = time.time()
            a = gy_call(r, s, T, S0, K)
            line = f"bench r={mp.nstr(r,4)} σ={mp.nstr(s,4)} T={T} S0={mp.nstr(S0,3)} ref={ref} GY={mp.nstr(a,18)}"
            if args.linetsky:
                b = linetsky_call(r, s, T, S0, K)
                line += f" LIN={mp.nstr(b,18)} |GY-LIN|={mp.nstr(abs(a-b),3)}"
            print(line, f"({time.time()-t0:.1f}s)", flush=True)
    if args.tables:
        mp.mp.dps = args.dps
        strikes, printed, params = table_data()
        r = mp.mpf(5) / 200
        for tb in (1, 2, 3, 4):
            if args.only and tb != args.only:
                continue
            T, s, err0 = params[tb]
            for K, pr in zip(strikes, printed[tb]):
                t0 = time.time()
                a = gy_call(r, s, T, mp.mpf(1), K)
                d = abs(a - mp.mpf(pr))
                line = (f"T{tb} K={mp.nstr(K,3)} printed={pr} GY={mp.nstr(a,22)} "
                        f"|GY-printed|={mp.nstr(d,3)} err0={mp.nstr(err0,1)} "
                        f"{'PASS' if d <= err0 else 'FAIL'}")
                if args.dehoog:
                    c = gy_call(r, s, T, mp.mpf(1), K, method="dehoog")
                    line += f" deHoog={mp.nstr(c,22)} |GY-dH|={mp.nstr(abs(a-c),3)}"
                if args.linetsky:
                    b = linetsky_call(r, s, T, mp.mpf(1), K)
                    line += f" LIN={mp.nstr(b,22)} |GY-LIN|={mp.nstr(abs(a-b),3)}"
                print(line, f"({time.time()-t0:.1f}s)", flush=True)


if __name__ == "__main__":
    sys.exit(main())
