/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters
import all QuantumAlg.Primitives.ShortDLP
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Owned.ClassicalInputs
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Preparation.Empty

/-!
# Actual original-width oracle bank and result storage

The physical bank has the two original exponent registers and one modulus-width
XOR target. Actual finite measurement cells and one packed result are retained
beside that bank. Earlier classical storage and its reference are unrestricted.
No compiled arithmetic workspace or second bank is introduced.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

open Execution

noncomputable section

/-- The original oracle uses one modulus-width target register. -/
def parameters (N : Nat) : ShortDLP.RegisterParameters where
  m := shortLogBits N
  ell := tradeoffBits N
  workspaceBits := modulusBits N

/-- The exact original physical bank, without compiled arithmetic auxiliaries. -/
def layout (N : Nat) : QuantumLayout (ShortDLP.totalQubits (parameters N)) :=
  (ShortDLP.layout (parameters N)).toQuantumLayout

/-- Actual preparation of the source's zero computational basis. -/
def preparation (N : Nat) : BasisPreparation (layout N) :=
  ⟨(ShortDLP.layout (parameters N)).binaryIndexEquiv.symm 0⟩

/-- The source exponent measurement width is unchanged by its target encoding. -/
theorem nativeOracle_measurementBits (N : Nat) :
    measurementBits N = ShortDLP.firstBits (parameters N) + (parameters N).ell := rfl

/-- The declared bank has the original same-bit oracle width. -/
theorem nativeOracle_qubitCount_sameBit {n : Nat} (pair : RSA.RSAKeyPairBits n)
    (positive : 1 ≤ n) :
    ShortDLP.totalQubits (parameters pair.modulus) =
      3 * n + 2 * ((n + 2) / 2) + 1 := by
  simp only [ShortDLP.totalQubits, ShortDLP.firstBits, parameters,
    shortLogBits_sameBit pair positive, tradeoffBits_sameBit pair positive,
    modulusBits_sameBit pair positive, RSA.GeneratorOrder.m, RSA.GeneratorOrder.ell]
  omega

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

include noQuantum in
private theorem allocationDisjoint : List.Disjoint (layout N).identities base.physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, noQuantum, List.map_nil]
  exact List.disjoint_nil_right _

/-- The actual preparation extends the caller by precisely one owned bank. -/
def bankContext : RuntimeCtx .quantum :=
  base.addOwnedLayout base.canonicalFreshKey (layout N) base.canonicalFreshKey_fresh
    (allocationDisjoint base noQuantum N)

/-- One retained finite cell records each actual exponent measurement. -/
def cellsContext : RuntimeCtx .quantum :=
  MeasurementCells.context (bankContext base noQuantum N) 2 (measurementBits N)

/-- The final packed result is a real retained cell beside the complete bank and cells. -/
def context : RuntimeCtx .quantum :=
  (cellsContext base noQuantum N).addRetained (cellsContext base noQuantum N).canonicalFreshKey
    (.bits (measurementBits N)) (cellsContext base noQuantum N).canonicalFreshKey_fresh

/-- Every prior operand still reads its original storage below the owned bank. -/
def bankInput {shape : CShape} (input : CInputRef base shape) :
    CInputRef (bankContext base noQuantum N) shape :=
  input.underOwnedLayout base.canonicalFreshKey (layout N) base.canonicalFreshKey_fresh
    (allocationDisjoint base noQuantum N)

/-- The final operand is the same structural read beneath all actual result allocations. -/
def liftInput {shape : CShape} (input : CInputRef base shape) :
    CInputRef (context base noQuantum N) shape :=
  (MeasurementCells.liftInput 2
    (bankInput base noQuantum N input) (measurementBits N)).underRetained
    (cellsContext base noQuantum N).canonicalFreshKey (.bits (measurementBits N))
    (cellsContext base noQuantum N).canonicalFreshKey_fresh

/-- Each exponent wire writes to its own retained finite cell. -/
def cells (index : Fin (measurementBits N)) : CWriteRef (context base noQuantum N) (.finite 2) :=
  CWriteRef.underRetained
    (MeasurementCells.reference (bankContext base noQuantum N) 2 (measurementBits N) index)
    (cellsContext base noQuantum N).canonicalFreshKey (.bits (measurementBits N))
    (cellsContext base noQuantum N).canonicalFreshKey_fresh

/-- Actual writable storage for the packed exponent outcome. -/
def resultRef : CWriteRef (context base noQuantum N) (.bits (measurementBits N)) :=
  CWriteRef.retainedHead (cellsContext base noQuantum N)
    (cellsContext base noQuantum N).canonicalFreshKey (.bits (measurementBits N))
    (cellsContext base noQuantum N).canonicalFreshKey_fresh

/-- Only the original bank contributes quantum wires after preparation. -/
theorem nativeOracle_bankContext_wires :
    (bankContext base noQuantum N).quantumWires = (layout N).wires := by
  change (layout N).wires ++ base.quantumWires = _
  rw [noQuantum, List.append_nil]

/-- Retained measurements and packing add no quantum systems. -/
theorem nativeOracle_context_wires :
    (context base noQuantum N).quantumWires = (layout N).wires := by
  rw [context, RuntimeCtx.quantumWires_addRetained, cellsContext,
    MeasurementCells.context_quantumWires]
  exact nativeOracle_bankContext_wires base noQuantum N

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native
