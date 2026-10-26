/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Model.BitWord.Placement
import all QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Paid classical mask parity on supplied existing cells

A static table word selects the measured input bits whose XOR is required.
The actual program clears one supplied parity bit by self-XOR, then executes
one native XOR per selected input. The result can be read by a subsequent
real circuit branch. No quantum system or classical cell is allocated here.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.MaskParity

open Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {services : ClassicalOracleModel}

/-- One existing input bit is XORed into the actual supplied parity cell. -/
def xorOp (parity : CWriteRef ctx .bit) (input : CInputRef ctx .bit) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .xor ctx (.product (.storage parity.toCStorageRef) input) parity

/-- A real self-XOR clears the parity cell for each new table row. -/
def clearOp (parity : CWriteRef ctx .bit) : ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  xorOp parity (.storage parity.toCStorageRef)

/-- Admit the actual built-in native instruction without allocation. -/
def instruction {input output : CShape} (op : ClassicalOp input output ctx ctx) :
    Circuit (.quantum AlgorithmGate.model oracles BitWord.model services) ctx ctx false :=
  .classical (BitWord.application op)

/-- Traverse exactly the statically selected measured bit references in order. -/
def foldProgram (parity : CWriteRef ctx .bit) : List (CInputRef ctx .bit) →
    Circuit (.quantum AlgorithmGate.model oracles BitWord.model services) ctx ctx false
  | [] => .id (model := .quantum AlgorithmGate.model oracles BitWord.model services) ctx
  | input :: rest => (instruction (xorOp parity input)).seq (foldProgram parity rest)

/-- A paid clear precedes the actual selected-bit XOR fold. -/
def program (parity : CWriteRef ctx .bit) (inputs : List (CInputRef ctx .bit)) :
    Circuit (.quantum AlgorithmGate.model oracles BitWord.model services) ctx ctx false :=
  (instruction (clearOp parity)).seq (foldProgram parity inputs)

/-- The actual chronological caller-store update of the selected-bit fold. -/
def foldStore (parity : CWriteRef ctx .bit) : List (CInputRef ctx .bit) → Store ctx → Store ctx
  | [], store => store
  | input :: rest, store => foldStore parity rest (store.applyOp (xorOp parity input))

/-- The same native clear and fold determine the final actual store. -/
def storeStep (parity : CWriteRef ctx .bit) (inputs : List (CInputRef ctx .bit))
    (store : Store ctx) : Store ctx :=
  foldStore parity inputs (store.applyOp (clearOp parity))

/-- XOR of the original measured bits selected by one static table entry. -/
def value (inputs : List (CInputRef ctx .bit)) (store : Store ctx) : Bool :=
  inputs.foldr (fun input tail => (store.read input).toBool ^^ tail) false

private lemma xorOp_read (parity : CWriteRef ctx .bit) (input : CInputRef ctx .bit)
    (store : Store ctx) :
    ((store.applyOp (xorOp parity input)).read (.storage parity.toCStorageRef)).toBool =
      ((store.read (.storage parity.toCStorageRef)).toBool ^^ (store.read input).toBool) := by
  have written := Store.read_applyOp_output store (xorOp parity input)
  change (store.applyOp (xorOp parity input)).read (.storage parity.toCStorageRef) = _ at written
  rw [written]
  change (Resource.BitOpcode.eval .xor
    (.product (store.read (.storage parity.toCStorageRef)) (store.read input))).toBool = _
  cases first : store.read (.storage parity.toCStorageRef)
  cases second : store.read input
  rfl

/-- The parity clear acts correctly for either incoming classical bit. -/
lemma clearOp_read (parity : CWriteRef ctx .bit) (store : Store ctx) :
    ((store.applyOp (clearOp parity)).read (.storage parity.toCStorageRef)).toBool = false := by
  rw [clearOp, xorOp_read, Bool.xor_self]

/-- Every structural read outside the actual written parity cell is retained by the fold. -/
lemma foldStore_read_other (parity : CWriteRef ctx .bit)
    (inputs : List (CInputRef ctx .bit)) {shape : CShape} (observed : CInputRef ctx shape)
    (separate : parity.key ∉ observed.storageKeys) (store : Store ctx) :
    (foldStore parity inputs store).read observed = store.read observed := by
  induction inputs generalizing store with
  | nil => rfl
  | cons input rest ih =>
      rw [foldStore, ih]
      exact Store.read_applyOp_of_not_mem_storageKeys store (xorOp parity input) observed separate

private lemma value_applyOp (parity : CWriteRef ctx .bit)
    (inputs : List (CInputRef ctx .bit))
    (separate : ∀ input ∈ inputs, parity.key ∉ input.storageKeys)
    (op : ClassicalOp (.product .bit .bit) .bit ctx ctx)
    (written : op.outputRef = parity) (store : Store ctx) :
    value inputs (store.applyOp op) = value inputs store := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      have headRead := Store.read_applyOp_of_not_mem_storageKeys store op input
        (by rw [written]; exact separate input (by simp))
      change (((store.applyOp op).read input).toBool ^^ value rest (store.applyOp op)) = _
      rw [headRead, ih (fun other member => separate other (by simp [member]))]
      rfl

/-- The fold computes the exact XOR and preserves its arbitrary incoming accumulator. -/
lemma foldStore_read (parity : CWriteRef ctx .bit) (inputs : List (CInputRef ctx .bit))
    (separate : ∀ input ∈ inputs, parity.key ∉ input.storageKeys) (store : Store ctx) :
    ((foldStore parity inputs store).read (.storage parity.toCStorageRef)).toBool =
      ((store.read (.storage parity.toCStorageRef)).toBool ^^ value inputs store) := by
  induction inputs generalizing store with
  | nil => simp only [foldStore, value, List.foldr_nil, Bool.xor_false]
  | cons input rest ih =>
      rw [foldStore, ih (fun other member => separate other (by simp [member])), xorOp_read,
        value_applyOp parity rest (fun other member => separate other (by simp [member]))
          (xorOp parity input) rfl store]
      exact Bool.xor_assoc _ _ _

/-- The actual cleared parity cell contains precisely the original selected mask parity. -/
lemma storeStep_read (parity : CWriteRef ctx .bit) (inputs : List (CInputRef ctx .bit))
    (separate : ∀ input ∈ inputs, parity.key ∉ input.storageKeys) (store : Store ctx) :
    ((storeStep parity inputs store).read (.storage parity.toCStorageRef)).toBool =
      value inputs store := by
  rw [storeStep, foldStore_read parity inputs separate, clearOp_read,
    Bool.false_xor, value_applyOp parity inputs separate (clearOp parity) rfl store]

/-- The true clear/fold changes no other structural caller input. -/
lemma storeStep_read_other (parity : CWriteRef ctx .bit)
    (inputs : List (CInputRef ctx .bit)) {shape : CShape} (observed : CInputRef ctx shape)
    (separate : parity.key ∉ observed.storageKeys) (store : Store ctx) :
    (storeStep parity inputs store).read observed = store.read observed := by
  rw [storeStep, foldStore_read_other parity inputs observed separate]
  exact Store.read_applyOp_of_not_mem_storageKeys store (clearOp parity) observed separate

end

end QuantumAlg.EncodedBit.WindowLookup.MaskParity
