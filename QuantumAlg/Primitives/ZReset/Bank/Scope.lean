/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# A real scratch scope around reset of the same physical bank

One finite two-valued classical cell is allocated by the existing lexical
workspace constructor, reused by all measurement-and-correction pairs, and
popped when the scope exits. The input and output contexts are identical.
All physical systems and earlier classical results remain live in the complete
Output, including a bank of width zero.

The scratch cell contributes to both live-space peaks while it exists. Its
lexical entry and exit add no native event under the existing interpreter;
the measurement and selected correction events are all charged. The circuit
neither prepares a quantum system nor releases one.
-/

namespace QuantumAlg.ZReset.BankScope

noncomputable section

variable {ctx : RuntimeCtx .quantum}

/-- The single actual scratch cell is fresh from every incoming live key. -/
def workContext (ctx : RuntimeCtx .quantum) : RuntimeCtx .quantum :=
  ctx.addWorkspace ctx.canonicalFreshKey (.finite 2) ctx.canonicalFreshKey_fresh

/-- Writable access to precisely the allocated two-valued lexical head. -/
def scratch (ctx : RuntimeCtx .quantum) : CWriteRef (workContext ctx) (.finite 2) :=
  CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.finite 2) ctx.canonicalFreshKey_fresh

/-- Adding the actual classical scratch preserves every wire's physical dimension. -/
theorem zResetBankScope_work_qubits (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2) :
    ∀ wire : Fin (workContext ctx).systemCount,
      ((workContext ctx).quantumLayout.wire wire).dimension = 2 :=
  qubits

/-- Enter one real scratch scope, reset the existing bank and pop only that classical cell. -/
def code (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.finite 2) ctx.canonicalFreshKey_fresh
    (Bank.code (zResetBankScope_work_qubits qubits) (scratch ctx))

/-- The complete final manifest lists every original bank and classical-result key. -/
def run (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2) : AlgorithmRun ctx ctx .unit where
  code := code qubits
  output := Output.all ctx .unit

/-- The actual classical scratch adds no physical quantum identity. -/
theorem zResetBankScope_work_physicalIdx :
    (workContext ctx).physicalIdx = ctx.physicalIdx := rfl

/-- The actual lexical body retains exactly the incoming number of physical systems. -/
theorem zResetBankScope_work_systemCount :
    (workContext ctx).systemCount = ctx.systemCount := rfl

/-- Every actual scope path has the independent native reset envelope for its physical width. -/
theorem zResetBankScope_resourcePool_le (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2) (path : (code qubits).Path) :
    (code qubits).resourcePool path ≤ Bank.envelope ctx.systemCount :=
  Bank.zResetBank_resourcePool_le (zResetBankScope_work_qubits qubits) (scratch ctx) path

/-- The lexical scope emits exactly its two actual reset events per existing qubit. -/
theorem zResetBankScope_eventTrace_length (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2) (path : (code qubits).Path) :
    ((code qubits).eventTrace path).length = 2 * ctx.systemCount :=
  Bank.zResetBank_eventTrace_length (zResetBankScope_work_qubits qubits) (scratch ctx) path

/-- Unit-duration depth includes every executed measurement and selected correction. -/
theorem zResetBankScope_unitDepth (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2) (path : (code qubits).Path) :
    (code qubits).depth (fun _ => 1) path = 2 * ctx.systemCount :=
  Bank.zResetBank_unitDepth (zResetBankScope_work_qubits qubits) (scratch ctx) path

/-- The resident peak counts the existing bank and exactly the one live scratch cell. -/
theorem zResetBankScope_peakResidentSpace (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2) (path : (code qubits).Path) :
    (code qubits).peakResidentSpace path =
      SpacePool.ofShape (.finite 2) + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey (.finite 2)
    ctx.canonicalFreshKey_fresh
    (Bank.code (zResetBankScope_work_qubits qubits) (scratch ctx)) path).trans
      ((congrArg (SpacePool.max ctx.residentSpace)
        (Bank.zResetBank_peakResidentSpace
          (zResetBankScope_work_qubits qubits) (scratch ctx) path)).trans ?_)
  change SpacePool.max ctx.residentSpace
    (SpacePool.ofShape (.finite 2) + ctx.residentSpace) = _
  apply SpacePool.ext
  intro axis
  exact max_eq_right (Nat.le_add_left _ _)

/-- The same one-bit lexical cell contributes to auxiliary peak without a second bank. -/
theorem zResetBankScope_peakAuxiliarySpace (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2) (path : (code qubits).Path) :
    (code qubits).peakAuxiliarySpace path =
      SpacePool.ofShape (.finite 2) + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey (.finite 2)
    ctx.canonicalFreshKey_fresh
    (Bank.code (zResetBankScope_work_qubits qubits) (scratch ctx)) path).trans
      ((congrArg (SpacePool.max ctx.auxiliarySpace)
        (Bank.zResetBank_peakAuxiliarySpace
          (zResetBankScope_work_qubits qubits) (scratch ctx) path)).trans ?_)
  change SpacePool.max ctx.auxiliarySpace
    (SpacePool.ofShape (.finite 2) + ctx.auxiliarySpace) = _
  apply SpacePool.ext
  intro axis
  exact max_eq_right (Nat.le_add_left _ _)

/-- The unchanged final manifest omits no incoming live key. -/
theorem zResetBankScope_output_listing (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2) :
    (run qubits).output.listing = ctx.keys := rfl

end

end QuantumAlg.ZReset.BankScope
