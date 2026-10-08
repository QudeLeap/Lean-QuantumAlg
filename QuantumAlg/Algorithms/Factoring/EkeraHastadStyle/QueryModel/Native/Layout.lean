/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
public import QuantumAlg.Primitives.ShortDLP.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters
import all QuantumAlg.Primitives.ShortDLP.Measurement
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
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
public def parameters (N : Nat) : ShortDLP.RegisterParameters where
  m := shortLogBits N
  ell := tradeoffBits N
  workspaceBits := modulusBits N

/-- The known modulus determines its original injective residue encoding. -/
public def encoding {N : Nat} (input : Input N) :
    ShortDLP.UnitEncoding N (parameters N).workspaceBits :=
  ShortDLP.UnitEncoding.ofResidueEncoding
    { modulus_pos := input.modulus_pos
      register_fits := input.samplerInput.register_fits }

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
theorem allocationDisjoint : List.Disjoint (layout N).identities base.physicalIdx := by
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

variable {ctx : RuntimeCtx .quantum} (N : Nat) (sameWires : ctx.quantumWires = (layout N).wires)

include sameWires in
private theorem layoutWires : (layout N).wires = ctx.quantumLayout.wires :=
  (ctx.quantumLayout_wires.trans sameWires).symm

/-- Corresponding positions preserve complete wire identities and dimensions. -/
def wireEquiv : Fin (ShortDLP.totalQubits (parameters N)) ≃ Fin ctx.systemCount :=
  Execution.positionsOfEqualWires (layout N) ctx.quantumLayout (layoutWires N sameWires)

/-- The actual wire at each source position retains its physical identity and dimension. -/
theorem nativeOracle_wire_preserved (wire : Fin (ShortDLP.totalQubits (parameters N))) :
    ctx.quantumLayout.wire (wireEquiv N sameWires wire) = (layout N).wire wire :=
  Execution.wireAtCorrespondingPosition (layout N) ctx.quantumLayout (layoutWires N sameWires) wire

include sameWires in
/-- Every actual bank wire has dimension two. -/
theorem nativeOracle_context_qubits (wire : Fin ctx.systemCount) :
    (ctx.quantumLayout.wire wire).dimension = 2 := by
  obtain ⟨original, rfl⟩ := (wireEquiv N sameWires).surjective wire
  exact congrArg QuantumWire.dimension (nativeOracle_wire_preserved N sameWires original)

/-- Binary source labels identify the same actual ordered physical wires. -/
def basisEquiv : ctx.register.Index ≃ (Qubits (ShortDLP.totalQubits (parameters N))).Index :=
  (Execution.basisOfEqualWires (layout N) ctx.quantumLayout (layoutWires N sameWires)).symm.trans
    (ShortDLP.layout (parameters N)).binaryIndexEquiv

include sameWires in
/-- The runtime bank has exactly the consecutive source identities. -/
theorem nativeOracle_physicalIdx :
    ctx.physicalIdx = List.range (ShortDLP.totalQubits (parameters N)) := by
  change ctx.quantumWires.map QuantumWire.identity = _
  rw [sameWires]
  exact (layout_identities_eq_map_wires (layout N)).symm.trans
    (ShortDLP.layout_systemIdx (parameters N))


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native
