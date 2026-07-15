/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.BaseGateRealization

/-!
# Boolean base-gate realizations

This module packages the one-gate semantic actions of the NOT, CNOT, and
Toffoli primitives as `BaseGateProgram.Realizes` proofs. These are the smallest
reusable building blocks for replacing arithmetic endpoint gates by
gate-structured programs over encoded bits; VBE introduces the NOT, CNOT, and
Toffoli elementary gate family before building the reversible adder networks
[VBE95, 9511018.tex:202-215,218-264,591-604].
-/

@[expose] public section

namespace QuantumAlg

noncomputable section

namespace BinaryLabelEncoding

/-- Faithful encoding of two Boolean wires, packed big-endian. -/
def boolPair : BinaryLabelEncoding (Bool × Bool) :=
  prod bool bool

/-- Faithful encoding of three Boolean wires, packed big-endian. -/
def boolTriple : BinaryLabelEncoding (Bool × (Bool × Bool)) :=
  prod bool (prod bool bool)

@[simp] theorem boolPair_width : boolPair.width = 2 :=
  rfl

@[simp] theorem boolTriple_width : boolTriple.width = 3 :=
  rfl

end BinaryLabelEncoding

namespace BoolBaseGate

/-- Semantic action of an X/NOT gate on one Boolean wire. -/
def xStep (b : Bool) : Bool :=
  !b

/-- Semantic action of a CNOT gate with the first Boolean controlling the second. -/
def cnotStep (x : Bool × Bool) : Bool × Bool :=
  (x.1, x.1 ^^ x.2)

/-- Semantic action of a two-wire SWAP network. -/
def swapStep (x : Bool × Bool) : Bool × Bool :=
  (x.2, x.1)

/-- Semantic action of a Toffoli gate with the first two Booleans controlling
the third. -/
def toffoliStep (x : Bool × (Bool × Bool)) : Bool × (Bool × Bool) :=
  (x.1, (x.2.1, (x.1 && x.2.1) ^^ x.2.2))

/-- One addressed X/NOT atom over the canonical one-bit layout. -/
def xProgram : BaseGateProgram 1 :=
  BaseGateProgram.x ⟨0, by decide⟩

/-- One addressed CNOT atom over the canonical two-bit layout. -/
def cnotProgram : BaseGateProgram 2 :=
  BaseGateProgram.cnot ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)

/-- Three-CNOT SWAP network over the canonical two-bit layout. -/
def swapProgram : BaseGateProgram 2 :=
  BaseGateProgram.append
    (BaseGateProgram.cnot ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide))
    (BaseGateProgram.append
      (BaseGateProgram.cnot ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide))
      (BaseGateProgram.cnot ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)))

/-- One addressed Toffoli atom over the canonical three-bit layout. -/
def toffoliProgram : BaseGateProgram 3 :=
  BaseGateProgram.toffoli ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
    (by decide) (by decide) (by decide)

@[simp] theorem xProgram_applyLabel (b : Bool) :
    BaseGateProgram.applyLabel xProgram
        (BinaryLabelEncoding.bool.encode b) =
      BinaryLabelEncoding.bool.encode (xStep b) := by
  cases b <;> decide

@[simp] theorem cnotProgram_applyLabel (x : Bool × Bool) :
    BaseGateProgram.applyLabel cnotProgram
        (BinaryLabelEncoding.boolPair.encode x) =
      BinaryLabelEncoding.boolPair.encode (cnotStep x) := by
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> decide

@[simp] theorem swapProgram_applyLabel (x : Bool × Bool) :
    BaseGateProgram.applyLabel swapProgram
        (BinaryLabelEncoding.boolPair.encode x) =
      BinaryLabelEncoding.boolPair.encode (swapStep x) := by
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> decide

@[simp] theorem toffoliProgram_applyLabel (x : Bool × (Bool × Bool)) :
    BaseGateProgram.applyLabel toffoliProgram
        (BinaryLabelEncoding.boolTriple.encode x) =
      BinaryLabelEncoding.boolTriple.encode (toffoliStep x) := by
  rcases x with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

/-- The one-bit X/NOT program realizes Boolean negation. -/
theorem xProgram_realizes :
    BaseGateProgram.Realizes BinaryLabelEncoding.bool xProgram xStep where
  applyLabel_eq := xProgram_applyLabel

/-- The two-bit CNOT program realizes controlled Boolean xor. -/
theorem cnotProgram_realizes :
    BaseGateProgram.Realizes BinaryLabelEncoding.boolPair cnotProgram cnotStep where
  applyLabel_eq := cnotProgram_applyLabel

/-- The three-CNOT SWAP program realizes Boolean-pair exchange. -/
theorem swapProgram_realizes :
    BaseGateProgram.Realizes BinaryLabelEncoding.boolPair swapProgram swapStep where
  applyLabel_eq := swapProgram_applyLabel

/-- The three-bit Toffoli program realizes double-controlled Boolean xor. -/
theorem toffoliProgram_realizes :
    BaseGateProgram.Realizes BinaryLabelEncoding.boolTriple toffoliProgram
      toffoliStep where
  applyLabel_eq := toffoliProgram_applyLabel

/-- Same-Circuit witness for the canonical one-bit X/NOT atom. -/
def xWitness : BaseGateSameCircuitWitness Bool xStep where
  encoding := BinaryLabelEncoding.bool
  program := xProgram
  realizes := xProgram_realizes

/-- Same-Circuit witness for the canonical two-bit CNOT atom. -/
def cnotWitness : BaseGateSameCircuitWitness (Bool × Bool) cnotStep where
  encoding := BinaryLabelEncoding.boolPair
  program := cnotProgram
  realizes := cnotProgram_realizes

/-- Same-Circuit witness for the canonical three-CNOT SWAP network. -/
def swapWitness : BaseGateSameCircuitWitness (Bool × Bool) swapStep where
  encoding := BinaryLabelEncoding.boolPair
  program := swapProgram
  realizes := swapProgram_realizes

/-- Same-Circuit witness for the canonical three-bit Toffoli atom. -/
def toffoliWitness :
    BaseGateSameCircuitWitness (Bool × (Bool × Bool)) toffoliStep where
  encoding := BinaryLabelEncoding.boolTriple
  program := toffoliProgram
  realizes := toffoliProgram_realizes

end BoolBaseGate

end

end QuantumAlg
