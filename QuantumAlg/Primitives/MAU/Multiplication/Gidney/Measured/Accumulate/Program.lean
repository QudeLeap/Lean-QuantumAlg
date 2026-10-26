/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Layout.Reduction
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Program
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Accumulate

/-!
# Literal measured forward and explicit negative-coefficient multiply-accumulate words

Original source bits are scanned in increasing little-endian order. Each
row executes the same actual measured modular-addition program on its
selector-excluding dirty placement. Forward constants retain the existing
static residues `a*2^i mod N`. The inverse word explicitly emits modular
additions of their negative residues; it never reverses a measured word
[VBE95, 9511018.tex:333-367; G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution Addition.Gidney.Measured Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- The existing independently constructed static modular weight of one source bit. -/
def forwardConstant (modulus : BitVec width) (coefficient : Nat) (index : Fin width) :
    BitVec width :=
  BitVec.ofNat width
    (Nat.FixedWidth.ModularAccumulate.stageConstantResidue modulus.toNat coefficient index.val)

/-- The explicit static negative residue used by the measured inverse MAC row. -/
def inverseConstant (modulus : BitVec width) (coefficient : Nat) (index : Fin width) :
    BitVec width :=
  BitVec.ofNat width ((modulus.toNat -
    Nat.FixedWidth.ModularAccumulate.stageConstantResidue modulus.toNat coefficient index.val) %
      modulus.toNat)

/-- Actual increasing-source-bit prefix on the same original physical systems and record bank. -/
def accumulatePrefixWord (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (constants : Fin width → BitVec width) :
    (count : Nat) → count ≤ width → List (Instruction encoding (width - 2))
  | 0, _ => []
  | count + 1, bounded =>
      layout.accumulatePrefixWord wide modulus constants count (by omega) ++
        (layout.reductionLayout ⟨count, by omega⟩).modularWord wide modulus
          (constants ⟨count, by omega⟩)

/-- The complete actual source-bit scan, with no hidden preparation or extra physical systems. -/
def accumulateWord (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (constants : Fin width → BitVec width) :
    List (Instruction encoding (width - 2)) :=
  layout.accumulatePrefixWord wide modulus constants width le_rfl

/-- The forward measured MAC uses exactly the original static positive modular weights. -/
def forwardMACWord (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient : Nat) : List (Instruction encoding (width - 2)) :=
  layout.accumulateWord wide modulus (forwardConstant modulus coefficient)

/-- Explicit measured inverse MAC, in original source order with paid negative modular additions. -/
def inverseMACWord (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient : Nat) : List (Instruction encoding (width - 2)) :=
  layout.accumulateWord wide modulus (inverseConstant modulus coefficient)

/-- Compile the literal forward measured word on the existing complete physical frame. -/
def forwardMACCircuit (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient : Nat) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2)) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false :=
  wordCircuit physical sameWires output (layout.forwardMACWord wide modulus coefficient)

/-- Compile the separate explicit negative-residue measured word without a unitary inverse. -/
def inverseMACCircuit (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient : Nat) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2)) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false :=
  wordCircuit physical sameWires output (layout.inverseMACWord wide modulus coefficient)

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
