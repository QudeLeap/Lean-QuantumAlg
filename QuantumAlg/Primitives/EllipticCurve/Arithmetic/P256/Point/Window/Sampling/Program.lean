/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Index
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Fourier
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Cleanup
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Record.Lift

/-!
# Actual chronological windows with the same measured five-table point driver

Each list node first really measures and corrects its active bank, then
executes H on those same systems, the real paid table
construction and measured point operation, then the real stored-feedback
inverse Fourier word with physical same-cell reset. The structural list
recursion retains every actual Path and the original writable result cells.
Its closed schedule uses the high four-bit tail followed by sixteen complete
windows, first for the generator stream and then the supplied second stream.

No source-character, good-branch cleanup or Born law is assumed by this
syntax. In particular, the second table base must be prepared as the inverse
target by the enclosing caller; the driver does not negate that input.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution ClassicalAlgorithms.Modular

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- All blocks retain the same caller bank and actual original feedback cells. -/
structure Parameters (ctx : RuntimeCtx .quantum) where
  sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires = ctx.quantumLayout.wires
  results : Fourier.Results ctx
  output : Fin 256 → CWriteRef ctx (.finite 2)
  mask : CWriteRef ctx (.bits 256)
  parity : Fin 256 → CWriteRef ctx .bit
  temporary : CWriteRef ctx .bit
  output_separate : ∀ bit position, (output bit).key ≠ (results.cells position).key
  mask_separate : ∀ position, mask.key ≠ (results.cells position).key
  parity_separate : ∀ bit position, (parity bit).key ≠ (results.cells position).key
  temporary_separate : ∀ position, temporary.key ≠ (results.cells position).key
  frame : ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame ctx 256
  modulus : ModulusSpec 256

namespace Parameters

variable (parameters : Parameters ctx)

/-- The same 854-bank positions are used directly in the caller's entire ordered context. -/
def wire (index : WindowIndex) (bit : Fin (index.lowerWidth + 1)) : Fin ctx.systemCount :=
  positionsOfEqualWires (QubitLayout.canonical encoding.width).toQuantum
    ctx.quantumLayout parameters.sameWires
      (Enable.digitBit index.stream index.lowerWidth index.lowerWidth_bound bit).wire

lemma wire_injective (index : WindowIndex) : Function.Injective (parameters.wire index) := by
  intro left right same
  exact Enable.digitBit_injective index.stream index.lowerWidth index.lowerWidth_bound
    ((positionsOfEqualWires _ _ parameters.sameWires).injective same)

lemma wire_record (index : WindowIndex) (bit : Fin (index.lowerWidth + 1)) :
    ctx.quantumLayout.wire (parameters.wire index bit) =
      ⟨(Enable.digitBit index.stream index.lowerWidth index.lowerWidth_bound bit).wire.val, 2⟩ :=
  (wireAtCorrespondingPosition _ _ parameters.sameWires
    (Enable.digitBit index.stream index.lowerWidth index.lowerWidth_bound bit).wire).trans
      (QubitLayout.toQuantum_wire _ _)

lemma wire_identity (index : WindowIndex) (bit : Fin (index.lowerWidth + 1)) :
    (ctx.quantumLayout.wire (parameters.wire index bit)).identity =
      if bit.val = 0 then (if index.stream.val = 0 then 836 else 838)
      else 839 + (bit.val - 1) := by
  rw [parameters.wire_record]
  exact Enable.digitBit_wire index.stream index.lowerWidth index.lowerWidth_bound bit

/-- Actual global chronological result positions, without output relabeling or extra cells. -/
def ports (index : WindowIndex) :
    QuantumFourierTransform.Semiclassical.Window.Ports ctx 260 (index.lowerWidth + 1) where
  stream := index.stream
  start := index.start
  within := index.within
  wires := ⟨parameters.wire index, parameters.wire_injective index⟩
  qubits := fun bit => congrArg QuantumWire.dimension (parameters.wire_record index bit)
  results := parameters.results.cells
  results_injective := parameters.results.distinct

/-- Every query and arithmetic call receives those same original caller references. -/
def pointParameters (index : WindowIndex) : Driver.Parameters ctx where
  stream := index.stream
  highRemaining := index.highRemaining
  lowWidth := index.lowWidth
  addressBound := index.addressBound
  lowBound := index.lowBound
  sameWires := parameters.sameWires
  output := parameters.output
  mask := parameters.mask
  parity := fun bit => parameters.parity (Fin.castLE index.lowCapacity bit)
  temporary := parameters.temporary

/-- Reset reuses an existing point outcome cell, disjoint from all retained Fourier results. -/
def resetParameters : Cleanup.Parameters ctx where
  sameWires := parameters.sameWires
  output := parameters.output 0

/-- Real pre-H MZ and same-result correction, using one existing point cell and no Fourier cell. -/
def reset (index : WindowIndex) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx true :=
  .embed (ContextEmbedding.identity ctx)
    (parameters.resetParameters.run (index.lowerWidth + 1) (parameters.wire index))

/-- Actual reset, existing-bank H, measured point middle and full corrected Fourier readout. -/
def block (index : WindowIndex) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx true :=
  (parameters.reset index).seq
    ((Circuit.unitary (QuantumFourierTransform.Semiclassical.Window.preparation
      (index.lowerWidth + 1) (parameters.ports index))).seq
        ((Driver.circuit (parameters.pointParameters index) parameters.frame parameters.modulus
          index.row).seq
            (QuantumFourierTransform.Semiclassical.Window.liftedInverse (parameters.ports index))))

/-- Structural list recursion, with all real table allocations, measurements and native resets. -/
def sequence (parameters : Parameters ctx) : List WindowIndex →
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx true
  | [] => Circuit.id (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (allowAllocation := true) ctx
  | index :: rest => (parameters.block index).seq (sequence parameters rest)

lemma sequence_nil :
    parameters.sequence (services := services) [] =
      Circuit.id (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (allowAllocation := true) ctx := rfl

lemma sequence_cons (index : WindowIndex) (rest : List WindowIndex) :
    parameters.sequence (services := services) (index :: rest) =
      (parameters.block index).seq (parameters.sequence rest) := rfl

end Parameters

/-- Same actual34 measured point/table middles, with literal recycled Fourier words around each. -/
def circuit (parameters : Parameters ctx) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx true :=
  parameters.sequence schedule

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
