/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Relabeling.References
import all QuantumAlg.Core.Execution.Context.Relabeling.Unitary
import all QuantumAlg.Core.Execution.Local.Framing

/-!
# Injective placement of actual local circuit instructions

The compiler rebuilds the original allocation-free fragment with the existing
Circuit constructors. Native gates use their rewritten physical addresses,
Z measurements name the corresponding actual systems and finite writable
cells, and stored-value branches retain their structural inputs. No additional
interpreter, state callback, resource witness or runtime operation is supplied.
-/

namespace QuantumAlg.Execution.ContextRelabeling

noncomputable section

/-- Name the mapped actual writable cell at the corresponding system's proved dimension. -/
def measurement (ctx : RuntimeCtx .quantum) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension)) :
    CWriteRef (ctx.relabel keys physical)
      (.finite ((ctx.relabel keys physical).quantumLayout.wire
        (positions ctx keys physical wire)).dimension) :=
  Eq.mp (congrArg
    (fun dimension : ℕ+ => CWriteRef (ctx.relabel keys physical) (.finite dimension))
    (positions_dimension ctx keys physical wire).symm) (writable keys physical output)

/-- Rebuild the original local instructions with their prescribed physical and storage maps. -/
def localCircuit : {model : ExecutionModel} → {pre post : RuntimeCtx model.kind} →
    (code : Circuit model pre post) → (supported : code.IsLocal) →
    (keys : StorageKey ↪ StorageKey) → (physical : Nat ↪ Nat) →
    Circuit model (pre.relabel keys physical) (post.relabel keys physical)
  | _, _, _, .id ctx, _, keys, physical => .id (ctx.relabel keys physical)
  | _, _, _, .classical _, supported, _, _ => False.elim supported
  | _, _, _, .classicalQuery _, supported, _, _ => False.elim supported
  | _, _, _, .unitary (ctx := ctx) program, _, keys, physical =>
      .unitary (unitaryProgram ctx keys physical program)
  | _, _, _, .measureZ (ctx := ctx) wire output, _, keys, physical =>
      .measureZ (positions ctx keys physical wire) (measurement ctx keys physical wire output)
  | _, _, _, .retain _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .prepareZero _ _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, keys, physical =>
      .seq (localCircuit first supported.1 keys physical)
        (localCircuit second supported.2 keys physical)
  | _, _, _, .branch ref body, supported, keys, physical =>
      .branch (input keys physical ref) fun value =>
        localCircuit (body value) (supported value) keys physical
  | _, _, _, .iterate count body, supported, keys, physical =>
      .iterate count (localCircuit body supported keys physical)
  | _, _, _, .workspace _ _ _ _ _, supported, _, _ => False.elim supported

/-- The actual finite paths retain every observed outcome and stored-value branch choice. -/
def localPathEquiv : {model : ExecutionModel} → {pre post : RuntimeCtx model.kind} →
    (code : Circuit model pre post) → (supported : code.IsLocal) →
    (keys : StorageKey ↪ StorageKey) → (physical : Nat ↪ Nat) →
    code.Path ≃ (localCircuit code supported keys physical).Path
  | _, _, _, .id _, _, _, _ => Equiv.refl Unit
  | _, _, _, .classical _, supported, _, _ => False.elim supported
  | _, _, _, .classicalQuery _, supported, _, _ => False.elim supported
  | _, _, _, .unitary _, _, _, _ => Equiv.refl Unit
  | _, _, _, .measureZ (ctx := ctx) wire _, _, keys, physical =>
      finCongr (congrArg PNat.val (positions_dimension ctx keys physical wire).symm)
  | _, _, _, .retain _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .prepareZero _ _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, keys, physical =>
      Equiv.prodCongr (localPathEquiv first supported.1 keys physical)
        (localPathEquiv second supported.2 keys physical)
  | _, _, _, .branch _ body, supported, keys, physical =>
      Equiv.sigmaCongrRight fun value =>
        localPathEquiv (body value) (supported value) keys physical
  | _, _, _, .iterate _ body, supported, keys, physical =>
      Equiv.piCongrRight fun _ => localPathEquiv body supported keys physical
  | _, _, _, .workspace _ _ _ _ _, supported, _, _ => False.elim supported

/-- Rebuilt instructions remain in the same local fragment of the original interpreter. -/
theorem localCircuit_isLocal : {model : ExecutionModel} → {pre post : RuntimeCtx model.kind} →
    (code : Circuit model pre post) → (supported : code.IsLocal) →
    (keys : StorageKey ↪ StorageKey) → (physical : Nat ↪ Nat) →
    (localCircuit code supported keys physical).IsLocal
  | _, _, _, .id _, _, _, _ => trivial
  | _, _, _, .classical _, supported, _, _ => False.elim supported
  | _, _, _, .classicalQuery _, supported, _, _ => False.elim supported
  | _, _, _, .unitary _, _, _, _ => trivial
  | _, _, _, .measureZ _ _, _, _, _ => trivial
  | _, _, _, .retain _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .prepareZero _ _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, keys, physical =>
      ⟨localCircuit_isLocal first supported.1 keys physical,
        localCircuit_isLocal second supported.2 keys physical⟩
  | _, _, _, .branch _ body, supported, keys, physical =>
      fun value => localCircuit_isLocal (body value) (supported value) keys physical
  | _, _, _, .iterate _ body, supported, keys, physical =>
      localCircuit_isLocal body supported keys physical
  | _, _, _, .workspace _ _ _ _ _, supported, _, _ => False.elim supported

end

end QuantumAlg.Execution.ContextRelabeling
