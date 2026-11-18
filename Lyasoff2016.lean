/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license.

Formalization of
  A. Lyasoff, "Another look at the integral of exponential Brownian motion
  and the pricing of Asian options", Finance Stoch. 20 (2016) 1061–1096.

Dependencies: BrownianMotion as a path copy under `vendor/brownian-motion`
(upstream pin with a few unfinished declarations removed; see `vendor/SOURCES`);
formal-mathfin, kolmogorov_extension4 (transitive) and Mathlib as Lake Git pins.
-/
module

public import Lyasoff2016.Setting
public import Lyasoff2016.Auxiliary
public import Lyasoff2016.FokkerPlanck
public import Lyasoff2016.Foliation
public import Lyasoff2016.IntegralReps
public import Lyasoff2016.PiFormulaLaplace
public import Lyasoff2016.PiHalfIdentify
public import Lyasoff2016.Asian
public import Lyasoff2016.ContourBendFfun
public import Lyasoff2016.TableParams
public import Lyasoff2016.TableClaim

@[expose] public section

