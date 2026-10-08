/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Primitives.QFT.Primitive
public import QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Construction
public import QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement

/-!
# The recursive QFT construction in the algorithm native language

Each stage executes its leading Hadamard, its complete controlled-phase words,
and the recursively placed tail. The final bit-reversal network contains the
complete three-CNOT expansion of every symmetric swap.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

open QFTPrimitive (layout)

/-- Rotation angle at the supplied separation in one recursive QFT stage. -/
public def phaseAngle (offset : Nat) : Real :=
  2 * Real.pi / (2 : Real) ^ (offset + 2)

/-- One complete controlled-phase word on the leading qubit and selected tail qubit. -/
public def phaseStep (oracles : OracleModel) (n : Nat) (offset : Fin n) :
    UnitaryCircuit AlgorithmGate.model oracles (layout (n + 1)) :=
  (QFTPrimitive.controlledPhase 0 offset.succ (phaseAngle offset.val)
    (by intro same; have value := congrArg Fin.val same; simp at value)).circuit oracles

/-- The first supplied number of controlled phases, in their original order. -/
public def phasePrefix (oracles : OracleModel) (n : Nat) :
    (count : Nat) → count ≤ n → UnitaryCircuit AlgorithmGate.model oracles (layout (n + 1))
  | 0, _ => UnitaryCircuit.identity AlgorithmGate.model oracles (layout (n + 1))
  | count + 1, bounded =>
      (phasePrefix oracles n count (Nat.le_of_succ_le bounded)).seq
        (phaseStep oracles n ⟨count, Nat.lt_of_succ_le bounded⟩)

/-- The full controlled-phase layer of a recursive stage. -/
public def phaseLayer (oracles : OracleModel) (n : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles (layout (n + 1)) :=
  phasePrefix oracles n n le_rfl

/-- One actual native one-qubit operation on the leading register position. -/
public def leadingHadamard (oracles : OracleModel) (n : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles (layout (n + 1)) :=
  UnitaryCircuit.macroCall "hadamard"
    (Gate.singleQubitAt (layout (n + 1)) oracles Gate.HOp 0 rfl)

/-- Place an existing tail circuit after the leading qubit without allocating any system. -/
public def tailLayer (oracles : OracleModel) (n : Nat)
    (body : UnitaryCircuit AlgorithmGate.model oracles (layout n)) :
    UnitaryCircuit AlgorithmGate.model oracles (layout (n + 1)) :=
  UnitaryCircuit.placeAt (layout n) (layout (n + 1))
    ⟨Fin.succ, Fin.succ_injective n⟩ (fun _ => rfl) body

/-- Recursive construction before its final wire reversal. -/
public def noSwap (oracles : OracleModel) :
    (n : Nat) → UnitaryCircuit AlgorithmGate.model oracles (layout n)
  | 0 => UnitaryCircuit.identity AlgorithmGate.model oracles (layout 0)
  | n + 1 => (leadingHadamard oracles n).seq
      ((phaseLayer oracles n).seq (tailLayer oracles n (noSwap oracles n)))

/-- The lower position of a symmetric pair in the final wire reversal. -/
public def swapLeft (n : Nat) (index : Fin (n / 2)) : Fin n :=
  ⟨index.val, lt_of_lt_of_le index.isLt (Nat.div_le_self n 2)⟩

/-- The upper position of the same symmetric pair. -/
public def swapRight (n : Nat) (index : Fin (n / 2)) : Fin n :=
  ⟨n - 1 - index.val, by have bounded := index.isLt; omega⟩

private theorem swap_distinct (n : Nat) (index : Fin (n / 2)) :
    swapLeft n index ≠ swapRight n index := by
  intro same
  have value := congrArg Fin.val same
  have bounded := index.isLt
  simp only [swapLeft, swapRight] at value
  omega

/-- One three-CNOT word exchanging the selected symmetric pair. -/
public def swapStep (oracles : OracleModel) (n : Nat) (index : Fin (n / 2)) :
    UnitaryCircuit AlgorithmGate.model oracles (layout n) :=
  (QFTPrimitive.swap (swapLeft n index) (swapRight n index)
    (swap_distinct n index)).circuit oracles

/-- The first supplied number of actual symmetric swaps. -/
public def reversePrefix (oracles : OracleModel) (n : Nat) :
    (count : Nat) → count ≤ n / 2 → UnitaryCircuit AlgorithmGate.model oracles (layout n)
  | 0, _ => UnitaryCircuit.identity AlgorithmGate.model oracles (layout n)
  | count + 1, bounded =>
      (reversePrefix oracles n count (Nat.le_of_succ_le bounded)).seq
        (swapStep oracles n ⟨count, Nat.lt_of_succ_le bounded⟩)

/-- The complete symmetric wire-reversal network. -/
public def bitReverse (oracles : OracleModel) (n : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles (layout n) :=
  reversePrefix oracles n (n / 2) le_rfl

/-- The complete recursive native word, including the final wire reversal. -/
public def circuit (oracles : OracleModel) (n : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles (layout n) :=
  (noSwap oracles n).seq (bitReverse oracles n)

end

end QuantumAlg.QuantumFourierTransform.Native
