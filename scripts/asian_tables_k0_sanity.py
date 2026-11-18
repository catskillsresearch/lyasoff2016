#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""K -> 0 sanity check for the Geman–Yor/Talbot pricer in asian_tables_independent_check.py.

As K -> 0 the Asian call tends to the K = 0 closed form (Remark 6.1 / benchmark_k_zero)
    e^{-rT} E[A_T] = (1 - e^{-rT}) / (rT)      (S0 = 1),
and for small K > 0 the put is negligible, so call = (1 - e^{-rT})/(rT) - e^{-rT} K
up to the (exponentially small) put value.
"""
import mpmath as mp
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from asian_tables_independent_check import gy_call, table_data

mp.mp.dps = 60
strikes, printed, params = table_data()
r = mp.mpf(5) / 200
for tb in (1, 2, 3, 4):
    T, s, err0 = params[tb]
    for K in (mp.mpf(1) / 10, mp.mpf(1) / 100):
        v = gy_call(r, s, T, mp.mpf(1), K)
        fwd = (1 - mp.exp(-r * T)) / (r * T) - mp.exp(-r * T) * K
        print(f"T{tb} K={mp.nstr(K,2)} GY={mp.nstr(v,30)} forward={mp.nstr(fwd,30)} diff={mp.nstr(v-fwd,3)}")
    print(f"T{tb} K=0 closed form (1-e^(-rT))/(rT) = {mp.nstr((1-mp.exp(-r*T))/(r*T),30)}")
