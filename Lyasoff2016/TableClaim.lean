/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# §6 Tables 1–4 — reported rows (legacy module name)

These are data, not enclosures of a mathematical price. The former price-enclosure
statements have been withdrawn, not proved. No proposition relating the printed
values to `asianMarketPrice` is asserted by this module.
-/
module

public import Lyasoff2016.TableClassical

@[expose] public section
noncomputable section
namespace Lyasoff2016

/-- A transcription of one row of the paper, with no correctness certificate. -/
structure ReportedTableRow where
  params : TableParams
  strike : ℚ
  printed : ℚ

/-- Table 1 rows, transcribed from the paper; not certified prices. -/
def table1Reported (i : Fin 6) : ReportedTableRow :=
  ⟨table1Params, tableStrikes i, table1 i⟩

/-- Table 2 rows, transcribed from the paper; not certified prices. -/
def table2Reported (i : Fin 6) : ReportedTableRow :=
  ⟨table2Params, tableStrikes i, table2 i⟩

/-- Table 3 rows, transcribed from the paper; not certified prices. -/
def table3Reported (i : Fin 6) : ReportedTableRow :=
  ⟨table3Params, tableStrikes i, table3 i⟩

/-- Table 4 rows, transcribed from the paper; not certified prices. -/
def table4Reported (i : Fin 6) : ReportedTableRow :=
  ⟨table4Params, tableStrikes i, table4 i⟩

end Lyasoff2016
