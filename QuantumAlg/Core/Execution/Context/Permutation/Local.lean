/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Permutation.References
import all QuantumAlg.Core.Execution.Context.Permutation.Unitary
import all QuantumAlg.Core.Execution.Local.Framing

/-!
# Actual local instructions in permuted entry coordinates

The compiler recurses on the existing allocation-free local fragment and
emits the same Circuit constructors. Every measurement names the same wire
and the same writable finite cell; every branch reads its original stored
value. Actual preparation remains outside this compiler. The finite path
correspondence retains each observed outcome and selected branch.
-/

namespace QuantumAlg.Execution.ContextPermutation

noncomputable section

/-- Local execution keeps the same complete entries at its output. -/
theorem postPermutation {kind : ProblemKind} {pre post target : RuntimeCtx kind}
    (code : Circuit pre post) (supported : code.IsLocal)
    (same : pre.entries.Perm target.entries) : post.entries.Perm target.entries :=
  code.isLocal_endpoints supported ▸ same

/-- Name the identical writable cell at the corresponding wire's proved dimension. -/
def measurement {source target : RuntimeCtx .quantum}
    (same : source.entries.Perm target.entries) (wire : Fin source.systemCount)
    (output : CWriteRef source (.finite (source.quantumLayout.wire wire).dimension)) :
    CWriteRef target (.finite (target.quantumLayout.wire (positions same wire)).dimension) :=
  Eq.mp (congrArg (fun dimension : ℕ+ => CWriteRef target (.finite dimension))
    (congrArg QuantumWire.dimension (positions_wire same wire)).symm) (writable same output)

/-- Rebuild the original local circuit using the target's identical live cells and wires. -/
def localCircuit : {kind : ProblemKind} → {pre post : RuntimeCtx kind} →
    (code : Circuit pre post) → (supported : code.IsLocal) → (target : RuntimeCtx kind) →
    (same : pre.entries.Perm target.entries) → Circuit target target
  | _, _, _, .id _, _, target, _ => .id target
  | _, _, _, .classical _, supported, _, _ => False.elim supported
  | _, _, _, .declaredCall _, supported, _, _ => False.elim supported
  | _, _, _, .unitary program placed, _, _, same =>
      .unitary (unitaryProgram same program) (unitaryProgram_physical same program placed)
  | _, _, _, .measureZ wire output, _, _, same =>
      .measureZ (positions same wire) (measurement same wire output)
  | _, _, _, .randomBits _ _, supported, _, _ => False.elim supported
  | _, _, _, .retain _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .prepare _ _ _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, target, same =>
      .seq (localCircuit first supported.1 target same)
        (localCircuit second supported.2 target (postPermutation first supported.1 same))
  | _, _, _, .branch ref body, supported, target, same =>
      .branch (input same ref) fun value => localCircuit (body value) (supported value) target same
  | _, _, _, .iterate count body, supported, target, same =>
      .iterate count (localCircuit body supported target same)
  | _, _, _, .workspace _ _ _ _ _, supported, _, _ => False.elim supported

/-- Original and rebuilt execution paths have exactly corresponding finite observations. -/
def localPathEquiv : {kind : ProblemKind} → {pre post : RuntimeCtx kind} →
    (code : Circuit pre post) → (supported : code.IsLocal) → (target : RuntimeCtx kind) →
    (same : pre.entries.Perm target.entries) →
    code.Path ≃ (localCircuit code supported target same).Path
  | _, _, _, .id _, _, _, _ => Equiv.refl Unit
  | _, _, _, .classical _, supported, _, _ => False.elim supported
  | _, _, _, .declaredCall _, supported, _, _ => False.elim supported
  | _, _, _, .unitary _ _, _, _, _ => Equiv.refl Unit
  | _, _, _, .measureZ wire _, _, _, same =>
      finCongr (congrArg (fun dimension : ℕ+ => (dimension : Nat))
        (congrArg QuantumWire.dimension (positions_wire same wire)).symm)
  | _, _, _, .randomBits _ _, supported, _, _ => False.elim supported
  | _, _, _, .retain _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .prepare _ _ _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, target, same =>
      Equiv.prodCongr (localPathEquiv first supported.1 target same)
        (localPathEquiv second supported.2 target (postPermutation first supported.1 same))
  | _, _, _, .branch _ body, supported, target, same =>
      Equiv.sigmaCongrRight fun value =>
        localPathEquiv (body value) (supported value) target same
  | _, _, _, .iterate _ body, supported, target, same =>
      Equiv.piCongrRight fun _ => localPathEquiv body supported target same
  | _, _, _, .workspace _ _ _ _ _, supported, _, _ => False.elim supported

/-- Rebuilt instructions remain in the same local fragment of the original interpreter. -/
theorem localCircuit_isLocal : {kind : ProblemKind} → {pre post : RuntimeCtx kind} →
    (code : Circuit pre post) → (supported : code.IsLocal) → (target : RuntimeCtx kind) →
    (same : pre.entries.Perm target.entries) →
    (localCircuit code supported target same).IsLocal
  | _, _, _, .id _, _, _, _ => trivial
  | _, _, _, .classical _, supported, _, _ => False.elim supported
  | _, _, _, .declaredCall _, supported, _, _ => False.elim supported
  | _, _, _, .unitary _ _, _, _, _ => trivial
  | _, _, _, .measureZ _ _, _, _, _ => trivial
  | _, _, _, .randomBits _ _, supported, _, _ => False.elim supported
  | _, _, _, .retain _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .prepare _ _ _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, target, same =>
      ⟨localCircuit_isLocal first supported.1 target same,
        localCircuit_isLocal second supported.2 target (postPermutation first supported.1 same)⟩
  | _, _, _, .branch _ body, supported, target, same =>
      fun value => localCircuit_isLocal (body value) (supported value) target same
  | _, _, _, .iterate _ body, supported, target, same =>
      localCircuit_isLocal body supported target same
  | _, _, _, .workspace _ _ _ _ _, supported, _, _ => False.elim supported

end

end QuantumAlg.Execution.ContextPermutation
