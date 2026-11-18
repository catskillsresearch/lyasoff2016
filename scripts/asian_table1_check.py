#!/usr/bin/env python3
"""Numeric check of Lyasoff Table 1 market prices via path Monte Carlo.

Paper market price (vision OCR p. 1093, S0=1):
  e^{-rT}/T * E[(∫₀ᵀ exp(σ W_s + μ s) ds − K T)_+]
with μ = r − σ²/2.

This verifies the *corrected Lean claim* (asianMarketPrice vs printed digits)
without relying on delicate complex cancellation in g₄.
"""

from __future__ import annotations

import math
import sys

import numpy as np

R = 0.025
SIGMA = 0.22
T = 0.5
MU = R - SIGMA**2 / 2
ERR0 = 1e-15

TABLE1 = [
    (0.7, 0.302471713826246),
    (0.8, 0.203823272652937),
    (0.9, 0.109134667336200),
    (1.0, 0.038694821814008),
    (1.1, 0.008127776133751),
    (1.2, 0.001028464610034),
]


def market_price_mc(K: float, n_paths: int = 200_000, n_steps: int = 2000, seed: int = 0) -> tuple[float, float]:
    """Estimate asianMarketPrice by simulating BM paths."""
    rng = np.random.default_rng(seed)
    dt = T / n_steps
    # Brownian increments
    dW = rng.normal(0.0, math.sqrt(dt), size=(n_paths, n_steps))
    W = np.cumsum(dW, axis=1)
    # times at midpoints / right endpoints of intervals
    s = np.linspace(dt, T, n_steps)
    # integrand exp(σ W_s + μ s); use right-endpoint Riemann sum
    integrand = np.exp(SIGMA * W + MU * s)
    exp_int = integrand.sum(axis=1) * dt
    k = K * T
    payoff = np.maximum(exp_int - k, 0.0)
    undisc = payoff.mean()
    se_undisc = payoff.std(ddof=1) / math.sqrt(n_paths)
    pref = math.exp(-R * T) / T
    mkt = pref * undisc
    se = pref * se_undisc
    return mkt, se


def k0_closed_form() -> float:
    return (1 - math.exp(-R * T)) / (R * T)


def main() -> int:
    print(f"σ={SIGMA}  T={T}  μ={MU}", flush=True)
    print(flush=True)

    print("=== K=0 benchmark (closed form vs MC) ===", flush=True)
    closed = k0_closed_form()
    mkt0, se0 = market_price_mc(0.0, n_paths=100_000, n_steps=4000, seed=1)
    print(f"closed: {closed:.15f}", flush=True)
    print(f"MC:     {mkt0:.15f}  ± {se0:.3e}", flush=True)
    print(f"|MC-closed|: {abs(mkt0 - closed):.3e}", flush=True)
    print(flush=True)

    print("=== Table 1 strikes (MC vs printed) ===", flush=True)
    print(
        f"{'K':>6} {'printed':>18} {'MC':>18} {'±SE':>10} {'|err|':>12} {'err/SE':>8}",
        flush=True,
    )
    ok = True
    max_err = 0.0
    for K, printed in TABLE1:
        mkt, se = market_price_mc(K, n_paths=400_000, n_steps=4000, seed=42 + int(10 * K))
        err = abs(mkt - printed)
        max_err = max(max_err, err)
        print(
            f"{K:6.1f} {printed:18.15f} {mkt:18.15f} {se:10.3e} {err:12.3e} {err/se:8.2f}",
            flush=True,
        )
        # Within a few MC SEs and in the ballpark of printed digits
        if err > max(5 * se, 5e-4):
            ok = False

    print(flush=True)
    print(f"max |MC − printed| = {max_err:.3e}  (paper err0={ERR0})", flush=True)
    if ok:
        print("OK: MC agrees with printed Table 1 digits within sampling noise.", flush=True)
        return 0
    print("WARN: MC disagrees with some printed digits beyond tolerance.", flush=True)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
