/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Lyasoff2016

/-!
# Palomar Solution

Imports the `Lyasoff2016/` library. Comparator matches the compared
declarations named in `Challenge.lean` / `comparator.json` against these
proved definitions and theorems (scott_models / nowakowska1982 packaging).

There is no `sorry` in the compared `Lyasoff2016/` proof modules for the
Comparator family. Five proof-chart classical certificates
(`asian_delta`, `table1`–`table4_asian_enclosure`) depend on project axioms
and are outside Comparator; see `PROVENANCE.md`.
-/
