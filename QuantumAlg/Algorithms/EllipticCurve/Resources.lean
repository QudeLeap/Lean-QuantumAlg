/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Cost
public import QuantumAlg.Util.Nat

/-!
# Generic ECDLP resource-bound functions

This module records natural-number upper-bound functions for the
signed-windowed elliptic-curve discrete-logarithm resource route of
Haener--Jaques--Naehrig--Roetteler--Soeken.  The source presents fitted
asymptotic formulas for the full Shor ECDLP circuit with signed-windowed point
addition and three optimization targets: low width, low T-count, and low depth
[HJN+20, numerical-estimates.tex:43-48, appendix.tex:363-374].

The decimal coefficients are encoded as exact rational ceilings, while negative
constant terms in the fitted formulas are dropped to obtain conservative
natural-number upper bounds.
-/

@[expose] public section

namespace QuantumAlg
namespace EllipticCurve
namespace Haner2020

/-- Optimization target for the HJN 2020 signed-windowed ECDLP route. -/
inductive OptimizationTarget where
  | lowWidth
  | lowTGates
  | lowDepth
deriving DecidableEq

/-- Natural-number parameters for HJN-style fitted formulas.  `bitSize` is the
elliptic-curve field/order bit size, and `logBitSizeFloor` supplies the
source-side `floor(log_2 n)` term used in the fitted formulas. -/
structure FormulaParameters where
  /-- Elliptic-curve field or group-order bit size. -/
  bitSize : Nat
  /-- Source-side floor of the base-two logarithm of the bit size. -/
  logBitSizeFloor : Nat
deriving DecidableEq

namespace FormulaParameters

/-- Positive denominator used for formulas with a division by `log n`.  For the
cryptographic sizes modeled by the source this equals the supplied logarithmic
term; the `max` only keeps the total Lean function defined at tiny widths. -/
def logDivisor (params : FormulaParameters) : Nat :=
  max 1 params.logBitSizeFloor

@[simp] theorem logDivisor_pos (params : FormulaParameters) :
    0 < params.logDivisor := by
  simp [logDivisor]

end FormulaParameters

/-- Natural-number resource tuple for the HJN signed-windowed ECDLP route. -/
structure GenericResourceBounds where
  /-- Logical-qubit upper bound for the selected optimization target. -/
  logicalQubits : Nat
  /-- T-gate upper bound for the selected optimization target. -/
  tGates : Nat
  /-- T-depth upper bound for the selected optimization target. -/
  tDepth : Nat
  /-- All-gate depth upper bound for the selected optimization target. -/
  allGateDepth : Nat
  /-- Total-gate upper bound for the selected optimization target. -/
  totalGates : Nat
deriving DecidableEq

namespace GenericResourceBounds

/-- Fieldwise equality assertion for a generic ECDLP resource tuple. -/
def HasExactFields (profile : GenericResourceBounds)
    (logicalQubits tGates tDepth allGateDepth totalGates : Nat) : Prop :=
  profile.logicalQubits = logicalQubits ∧
    profile.tGates = tGates ∧
    profile.tDepth = tDepth ∧
    profile.allGateDepth = allGateDepth ∧
    profile.totalGates = totalGates

end GenericResourceBounds

/-- Ceiling of an exact rational coefficient `num / den` times a natural term. -/
def rationalCoefficientCeil (num den term : Nat) : Nat :=
  QuantumAlg.Nat.ceilDiv (num * term) den

@[simp] theorem rationalCoefficientCeil_eq (num den term : Nat) :
    rationalCoefficientCeil num den term =
      QuantumAlg.Nat.ceilDiv (num * term) den :=
  rfl

/-- Cubic bit-size monomial used by the fitted full-algorithm formulas. -/
def nCubed (params : FormulaParameters) : Nat :=
  params.bitSize ^ 3

/-- Square bit-size monomial used by the low-depth fitted formulas. -/
def nSquared (params : FormulaParameters) : Nat :=
  params.bitSize ^ 2

namespace LowWidth

/-- Low-width logical-qubit upper bound:
`8n + ceil(10.2 floor(log n))`, conservatively dropping the fitted `-1`.
-/
def logicalQubits (params : FormulaParameters) : Nat :=
  8 * params.bitSize + rationalCoefficientCeil 102 10 params.logBitSizeFloor

/-- Low-width T-gate upper bound, conservatively dropping the fitted negative
constant in `436 n^3 - 1.05 * 2^26`. -/
def tGates (params : FormulaParameters) : Nat :=
  436 * nCubed params

/-- Low-width T-depth upper bound, conservatively dropping the fitted negative
constant in `120 n^3 - 1.67 * 2^22`. -/
def tDepth (params : FormulaParameters) : Nat :=
  120 * nCubed params

/-- Low-width all-gate depth upper bound, conservatively dropping the fitted
negative constant in `509 n^3 - 1.84 * 2^27`. -/
def allGateDepth (params : FormulaParameters) : Nat :=
  509 * nCubed params

/-- Low-width total-gate upper bound.  The prose summary gives `2900 n^3`,
while the appendix table gives `2800 n^3`; this module keeps the larger source
coefficient as a conservative integer upper bound.
-/
def totalGates (params : FormulaParameters) : Nat :=
  2900 * nCubed params

/-- Low-width generic ECDLP resource tuple. -/
def bounds (params : FormulaParameters) : GenericResourceBounds where
  logicalQubits := logicalQubits params
  tGates := tGates params
  tDepth := tDepth params
  allGateDepth := allGateDepth params
  totalGates := totalGates params

@[simp] theorem bounds_fields (params : FormulaParameters) :
    (bounds params).HasExactFields
      (logicalQubits params) (tGates params) (tDepth params)
      (allGateDepth params) (totalGates params) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end LowWidth

namespace LowTGates

/-- Low-T logical-qubit upper bound:
`10n + ceil(7.4 floor(log n)) + ceil(1.3)`. -/
def logicalQubits (params : FormulaParameters) : Nat :=
  10 * params.bitSize +
    rationalCoefficientCeil 74 10 params.logBitSizeFloor + 2

/-- Low-T T-gate upper bound from `1115 n^3 / log n`, with the fitted negative
constant dropped. -/
def tGates (params : FormulaParameters) : Nat :=
  QuantumAlg.Nat.ceilDiv (1115 * nCubed params) params.logDivisor

/-- Low-T T-depth upper bound from `389 n^3 / log n`, with the fitted negative
constant dropped. -/
def tDepth (params : FormulaParameters) : Nat :=
  QuantumAlg.Nat.ceilDiv (389 * nCubed params) params.logDivisor

/-- Low-T all-gate depth upper bound from `1701 n^3 / log n`, with the fitted
negative constant dropped. -/
def allGateDepth (params : FormulaParameters) : Nat :=
  QuantumAlg.Nat.ceilDiv (1701 * nCubed params) params.logDivisor

/-- Low-T total-gate upper bound from `6262 n^3 / log n`, with the fitted
negative constant dropped. -/
def totalGates (params : FormulaParameters) : Nat :=
  QuantumAlg.Nat.ceilDiv (6262 * nCubed params) params.logDivisor

/-- Low-T generic ECDLP resource tuple. -/
def bounds (params : FormulaParameters) : GenericResourceBounds where
  logicalQubits := logicalQubits params
  tGates := tGates params
  tDepth := tDepth params
  allGateDepth := allGateDepth params
  totalGates := totalGates params

@[simp] theorem bounds_fields (params : FormulaParameters) :
    (bounds params).HasExactFields
      (logicalQubits params) (tGates params) (tDepth params)
      (allGateDepth params) (totalGates params) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end LowTGates

namespace LowDepth

/-- Low-depth logical-qubit upper bound:
`11n + ceil(3.9 floor(log n)) + ceil(16.5)`. -/
def logicalQubits (params : FormulaParameters) : Nat :=
  11 * params.bitSize +
    rationalCoefficientCeil 39 10 params.logBitSizeFloor + 17

/-- Low-depth T-gate upper bound from `3120 n^3 / log n`, with the fitted
negative constant dropped. -/
def tGates (params : FormulaParameters) : Nat :=
  QuantumAlg.Nat.ceilDiv (3120 * nCubed params) params.logDivisor

/-- Low-depth T-depth upper bound, conservatively dropping the fitted negative
constant in `285 n^2 - 1.54 * 2^17`. -/
def tDepth (params : FormulaParameters) : Nat :=
  285 * nSquared params

/-- Low-depth all-gate depth upper bound:
`2523 n^2 + ceil(1.10 * 2^20)`. -/
def allGateDepth (params : FormulaParameters) : Nat :=
  2523 * nSquared params + QuantumAlg.Nat.ceilDiv (110 * 2 ^ 20) 100

/-- Low-depth total-gate upper bound from `12478 n^3 / log n`, with the fitted
negative constant dropped. -/
def totalGates (params : FormulaParameters) : Nat :=
  QuantumAlg.Nat.ceilDiv (12478 * nCubed params) params.logDivisor

/-- Low-depth generic ECDLP resource tuple. -/
def bounds (params : FormulaParameters) : GenericResourceBounds where
  logicalQubits := logicalQubits params
  tGates := tGates params
  tDepth := tDepth params
  allGateDepth := allGateDepth params
  totalGates := totalGates params

@[simp] theorem bounds_fields (params : FormulaParameters) :
    (bounds params).HasExactFields
      (logicalQubits params) (tGates params) (tDepth params)
      (allGateDepth params) (totalGates params) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end LowDepth

/-- Select the HJN generic ECDLP resource tuple for one optimization target. -/
def bounds (target : OptimizationTarget) (params : FormulaParameters) :
    GenericResourceBounds :=
  match target with
  | .lowWidth => LowWidth.bounds params
  | .lowTGates => LowTGates.bounds params
  | .lowDepth => LowDepth.bounds params

@[simp] theorem bounds_lowWidth (params : FormulaParameters) :
    bounds .lowWidth params = LowWidth.bounds params :=
  rfl

@[simp] theorem bounds_lowTGates (params : FormulaParameters) :
    bounds .lowTGates params = LowTGates.bounds params :=
  rfl

@[simp] theorem bounds_lowDepth (params : FormulaParameters) :
    bounds .lowDepth params = LowDepth.bounds params :=
  rfl

end Haner2020
end EllipticCurve
end QuantumAlg
