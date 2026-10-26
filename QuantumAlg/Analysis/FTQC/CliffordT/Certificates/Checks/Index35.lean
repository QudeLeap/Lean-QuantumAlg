/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word35Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word35State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word35Step0 :
    word35Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word35State1 := by decide +kernel

private def word35Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word35State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word35Step1 :
    word35Chunk1.foldl (fun acc a => a.applyPacked acc)
      word35State1 = word35State2 := by decide +kernel

private def word35Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word35State3 : PackedMat2 :=
    ⟨⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word35Step2 :
    word35Chunk2.foldl (fun acc a => a.applyPacked acc)
      word35State2 = word35State3 := by decide +kernel

private def word35Chunk3 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word35State4 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word35Step3 :
    word35Chunk3.foldl (fun acc a => a.applyPacked acc)
      word35State3 = word35State4 := by decide +kernel

private def word35Chunk4 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word35State5 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word35Step4 :
    word35Chunk4.foldl (fun acc a => a.applyPacked acc)
      word35State4 = word35State5 := by decide +kernel

private def word35Chunk5 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word35State6 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 1)⟩⟩⟩
private lemma word35Step5 :
    word35Chunk5.foldl (fun acc a => a.applyPacked acc)
      word35State5 = word35State6 := by decide +kernel

private def word35Chunk6 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word35State7 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 4),
        ((7 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-7 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩⟩⟩
private lemma word35Step6 :
    word35Chunk6.foldl (fun acc a => a.applyPacked acc)
      word35State6 = word35State7 := by decide +kernel

private def word35Chunk7 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word35State8 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 4),
        ((9 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-11 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((-11 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-13 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((-5 : Dyadic) * half ^ 3),
        ((5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word35Step7 :
    word35Chunk7.foldl (fun acc a => a.applyPacked acc)
      word35State7 = word35State8 := by decide +kernel

private def word35Chunk8 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word35State9 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 4),
        ((-11 : Dyadic) * half ^ 6)⟩,
       ⟨((13 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((23 : Dyadic) * half ^ 6)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((-27 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((27 : Dyadic) * half ^ 6)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-23 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 6)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((-11 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word35Step8 :
    word35Chunk8.foldl (fun acc a => a.applyPacked acc)
      word35State8 = word35State9 := by decide +kernel

private def word35Chunk9 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word35State10 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 4),
        ((11 : Dyadic) * half ^ 7)⟩,
       ⟨((-15 : Dyadic) * half ^ 6),
        ((45 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((35 : Dyadic) * half ^ 6),
        ((27 : Dyadic) * half ^ 7)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((-35 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((-35 : Dyadic) * half ^ 7)⟩,
       ⟨((35 : Dyadic) * half ^ 6),
        ((27 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 6),
        ((-45 : Dyadic) * half ^ 7)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((-11 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word35Step9 :
    word35Chunk9.foldl (fun acc a => a.applyPacked acc)
      word35State9 = word35State10 := by decide +kernel

private def word35Chunk10 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word35State11 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-7 : Dyadic) * half ^ 5)⟩,
       ⟨((49 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 7),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 7),
        ((25 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-21 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 7)⟩,
       ⟨((29 : Dyadic) * half ^ 6),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-29 : Dyadic) * half ^ 7),
        ((45 : Dyadic) * half ^ 7)⟩,
       ⟨((-27 : Dyadic) * half ^ 7),
        ((-53 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word35Step10 :
    word35Chunk10.foldl (fun acc a => a.applyPacked acc)
      word35State10 = word35State11 := by decide +kernel

private def word35Chunk11 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word35State12 : PackedMat2 :=
    ⟨⟨⟨((-193 : Dyadic) * half ^ 8),
        ((9 : Dyadic) * half ^ 7)⟩,
       ⟨((75 : Dyadic) * half ^ 8),
        ((27 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((69 : Dyadic) * half ^ 8),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((23 : Dyadic) * half ^ 8),
        ((87 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-95 : Dyadic) * half ^ 8),
        ((23 : Dyadic) * half ^ 8)⟩,
       ⟨((-79 : Dyadic) * half ^ 8),
        ((-23 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 8),
        ((67 : Dyadic) * half ^ 7)⟩,
       ⟨((45 : Dyadic) * half ^ 8),
        ((-59 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word35Step11 :
    word35Chunk11.foldl (fun acc a => a.applyPacked acc)
      word35State11 = word35State12 := by decide +kernel

private def word35Chunk12 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word35State13 : PackedMat2 :=
    ⟨⟨⟨((43 : Dyadic) * half ^ 8),
        ((-133 : Dyadic) * half ^ 8)⟩,
       ⟨((-73 : Dyadic) * half ^ 7),
        ((-15 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 5),
        ((-29 : Dyadic) * half ^ 9)⟩,
       ⟨((-17 : Dyadic) * half ^ 7),
        ((-31 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-17 : Dyadic) * half ^ 7),
        ((-31 : Dyadic) * half ^ 9)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((-29 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((73 : Dyadic) * half ^ 7),
        ((15 : Dyadic) * half ^ 7)⟩,
       ⟨((-43 : Dyadic) * half ^ 8),
        ((133 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word35Step12 :
    word35Chunk12.foldl (fun acc a => a.applyPacked acc)
      word35State12 = word35State13 := by decide +kernel

private def word35Chunk13 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word35State14 : PackedMat2 :=
    ⟨⟨⟨((-15 : Dyadic) * half ^ 8),
        ((425 : Dyadic) * half ^ 10)⟩,
       ⟨((27 : Dyadic) * half ^ 9),
        ((-331 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((127 : Dyadic) * half ^ 8),
        ((141 : Dyadic) * half ^ 10)⟩,
       ⟨((51 : Dyadic) * half ^ 9),
        ((-277 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-51 : Dyadic) * half ^ 9),
        ((277 : Dyadic) * half ^ 10)⟩,
       ⟨((-127 : Dyadic) * half ^ 8),
        ((-141 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((27 : Dyadic) * half ^ 9),
        ((-331 : Dyadic) * half ^ 10)⟩,
       ⟨((-15 : Dyadic) * half ^ 8),
        ((425 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word35Step13 :
    word35Chunk13.foldl (fun acc a => a.applyPacked acc)
      word35State13 = word35State14 := by decide +kernel

private def word35Chunk14 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word35State15 : PackedMat2 :=
    ⟨⟨⟨((61 : Dyadic) * half ^ 8),
        ((447 : Dyadic) * half ^ 10)⟩,
       ⟨((-27 : Dyadic) * half ^ 6),
        ((107 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((165 : Dyadic) * half ^ 10),
        ((149 : Dyadic) * half ^ 10)⟩,
       ⟨((123 : Dyadic) * half ^ 10),
        ((-335 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((165 : Dyadic) * half ^ 10),
        ((149 : Dyadic) * half ^ 10)⟩,
       ⟨((-123 : Dyadic) * half ^ 10),
        ((335 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-61 : Dyadic) * half ^ 8),
        ((-447 : Dyadic) * half ^ 10)⟩,
       ⟨((-27 : Dyadic) * half ^ 6),
        ((107 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word35Step14 :
    word35Chunk14.foldl (fun acc a => a.applyPacked acc)
      word35State14 = word35State15 := by decide +kernel

private def word35Chunk15 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word35State16 : PackedMat2 :=
    ⟨⟨⟨((-81 : Dyadic) * half ^ 9),
        ((1015 : Dyadic) * half ^ 11)⟩,
       ⟨((49 : Dyadic) * half ^ 7),
        ((29 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-967 : Dyadic) * half ^ 11),
        ((-299 : Dyadic) * half ^ 11)⟩,
       ⟨((15 : Dyadic) * half ^ 11),
        ((-383 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((341 : Dyadic) * half ^ 10),
        ((119 : Dyadic) * half ^ 9)⟩,
       ⟨((-21 : Dyadic) * half ^ 9),
        ((491 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((1073 : Dyadic) * half ^ 11),
        ((115 : Dyadic) * half ^ 10)⟩,
       ⟨((957 : Dyadic) * half ^ 11),
        ((-277 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word35Step15 :
    word35Chunk15.foldl (fun acc a => a.applyPacked acc)
      word35State15 = word35State16 := by decide +kernel

private def word35Chunk16 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word35State17 : PackedMat2 :=
    ⟨⟨⟨((1261 : Dyadic) * half ^ 12),
        ((-765 : Dyadic) * half ^ 12)⟩,
       ⟨((-1175 : Dyadic) * half ^ 12),
        ((375 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-1397 : Dyadic) * half ^ 12),
        ((-321 : Dyadic) * half ^ 11)⟩,
       ⟨((-1409 : Dyadic) * half ^ 12),
        ((-1299 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((657 : Dyadic) * half ^ 12),
        ((3 : Dyadic) * half ^ 11)⟩,
       ⟨((1941 : Dyadic) * half ^ 12),
        ((1403 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((2265 : Dyadic) * half ^ 12),
        ((-609 : Dyadic) * half ^ 11)⟩,
       ⟨((735 : Dyadic) * half ^ 12),
        ((43 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word35Step16 :
    word35Chunk16.foldl (fun acc a => a.applyPacked acc)
      word35State16 = word35State17 := by decide +kernel

private def word35Chunk17 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word35State18 : PackedMat2 :=
    ⟨⟨⟨((-2845 : Dyadic) * half ^ 13),
        ((-177 : Dyadic) * half ^ 11)⟩,
       ⟨((1263 : Dyadic) * half ^ 13),
        ((4199 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((2883 : Dyadic) * half ^ 13),
        ((-1241 : Dyadic) * half ^ 12)⟩,
       ⟨((369 : Dyadic) * half ^ 13),
        ((-439 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-2883 : Dyadic) * half ^ 13),
        ((1241 : Dyadic) * half ^ 12)⟩,
       ⟨((369 : Dyadic) * half ^ 13),
        ((-439 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-2845 : Dyadic) * half ^ 13),
        ((-177 : Dyadic) * half ^ 11)⟩,
       ⟨((-1263 : Dyadic) * half ^ 13),
        ((-4199 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word35Step17 :
    word35Chunk17.foldl (fun acc a => a.applyPacked acc)
      word35State17 = word35State18 := by decide +kernel

private def word35Chunk18 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word35State19 : PackedMat2 :=
    ⟨⟨⟨((121 : Dyadic) * half ^ 13),
        ((-4335 : Dyadic) * half ^ 13)⟩,
       ⟨((1899 : Dyadic) * half ^ 12),
        ((-351 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-921 : Dyadic) * half ^ 13),
        ((2531 : Dyadic) * half ^ 14)⟩,
       ⟨((-1451 : Dyadic) * half ^ 13),
        ((-4167 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1451 : Dyadic) * half ^ 13),
        ((4167 : Dyadic) * half ^ 14)⟩,
       ⟨((921 : Dyadic) * half ^ 13),
        ((-2531 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1899 : Dyadic) * half ^ 12),
        ((-351 : Dyadic) * half ^ 13)⟩,
       ⟨((121 : Dyadic) * half ^ 13),
        ((-4335 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word35Step18 :
    word35Chunk18.foldl (fun acc a => a.applyPacked acc)
      word35State18 = word35State19 := by decide +kernel

private def word35Chunk19 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word35State20 : PackedMat2 :=
    ⟨⟨⟨((8929 : Dyadic) * half ^ 14),
        ((-5685 : Dyadic) * half ^ 15)⟩,
       ⟨((-3209 : Dyadic) * half ^ 14),
        ((4049 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((3245 : Dyadic) * half ^ 13),
        ((1711 : Dyadic) * half ^ 14)⟩,
       ⟨((-9859 : Dyadic) * half ^ 14),
        ((-2107 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1909 : Dyadic) * half ^ 13),
        ((-16349 : Dyadic) * half ^ 15)⟩,
       ⟨((-99 : Dyadic) * half ^ 12),
        ((-3369 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-4867 : Dyadic) * half ^ 14),
        ((6069 : Dyadic) * half ^ 14)⟩,
       ⟨((409 : Dyadic) * half ^ 13),
        ((-715 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word35Step19 :
    word35Chunk19.foldl (fun acc a => a.applyPacked acc)
      word35State19 = word35State20 := by decide +kernel

private def word35Chunk20 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word35State21 : PackedMat2 :=
    ⟨⟨⟨((-4483 : Dyadic) * half ^ 14),
        ((10387 : Dyadic) * half ^ 16)⟩,
       ⟨((3119 : Dyadic) * half ^ 15),
        ((-16317 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((11105 : Dyadic) * half ^ 14),
        ((11509 : Dyadic) * half ^ 16)⟩,
       ⟨((5485 : Dyadic) * half ^ 15),
        ((-20345 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((2209 : Dyadic) * half ^ 14),
        ((-27695 : Dyadic) * half ^ 16)⟩,
       ⟨((-15927 : Dyadic) * half ^ 15),
        ((-16725 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-2965 : Dyadic) * half ^ 15),
        ((-5847 : Dyadic) * half ^ 16)⟩,
       ⟨((1669 : Dyadic) * half ^ 12),
        ((-12085 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word35Step20 :
    word35Chunk20.foldl (fun acc a => a.applyPacked acc)
      word35State20 = word35State21 := by decide +kernel

private def word35Chunk21 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word35State22 : PackedMat2 :=
    ⟨⟨⟨((-4963 : Dyadic) * half ^ 14),
        ((-3531 : Dyadic) * half ^ 17)⟩,
       ⟨((-29509 : Dyadic) * half ^ 16),
        ((-44269 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((29409 : Dyadic) * half ^ 16),
        ((-38151 : Dyadic) * half ^ 17)⟩,
       ⟨((-4729 : Dyadic) * half ^ 15),
        ((26903 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-4729 : Dyadic) * half ^ 15),
        ((26903 : Dyadic) * half ^ 17)⟩,
       ⟨((29409 : Dyadic) * half ^ 16),
        ((-38151 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((29509 : Dyadic) * half ^ 16),
        ((44269 : Dyadic) * half ^ 17)⟩,
       ⟨((4963 : Dyadic) * half ^ 14),
        ((3531 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word35Step21 :
    word35Chunk21.foldl (fun acc a => a.applyPacked acc)
      word35State21 = word35State22 := by decide +kernel

private def word35Chunk22 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word35State23 : PackedMat2 :=
    ⟨⟨⟨((-4785 : Dyadic) * half ^ 17),
        ((-17763 : Dyadic) * half ^ 17)⟩,
       ⟨((-99139 : Dyadic) * half ^ 17),
        ((-9653 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((1867 : Dyadic) * half ^ 16),
        ((-22343 : Dyadic) * half ^ 16)⟩,
       ⟨((16313 : Dyadic) * half ^ 16),
        ((-26823 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-1867 : Dyadic) * half ^ 16),
        ((22343 : Dyadic) * half ^ 16)⟩,
       ⟨((16313 : Dyadic) * half ^ 16),
        ((-26823 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-4785 : Dyadic) * half ^ 17),
        ((-17763 : Dyadic) * half ^ 17)⟩,
       ⟨((99139 : Dyadic) * half ^ 17),
        ((9653 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word35Step22 :
    word35Chunk22.foldl (fun acc a => a.applyPacked acc)
      word35State22 = word35State23 := by decide +kernel

private def word35Chunk23 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word35State24 : PackedMat2 :=
    ⟨⟨⟨((67347 : Dyadic) * half ^ 18),
        ((-19909 : Dyadic) * half ^ 17)⟩,
       ⟨((-56717 : Dyadic) * half ^ 18),
        ((-90079 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-117213 : Dyadic) * half ^ 18),
        ((755 : Dyadic) * half ^ 12)⟩,
       ⟨((-149051 : Dyadic) * half ^ 18),
        ((-21713 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((70033 : Dyadic) * half ^ 18),
        ((15919 : Dyadic) * half ^ 18)⟩,
       ⟨((-26607 : Dyadic) * half ^ 18),
        ((33283 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-50261 : Dyadic) * half ^ 18),
        ((-3877 : Dyadic) * half ^ 14)⟩,
       ⟨((-129897 : Dyadic) * half ^ 18),
        ((5315 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word35Step23 :
    word35Chunk23.foldl (fun acc a => a.applyPacked acc)
      word35State23 = word35State24 := by decide +kernel

private def word35Chunk24 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word35State25 : PackedMat2 :=
    ⟨⟨⟨((-11619 : Dyadic) * half ^ 16),
        ((141507 : Dyadic) * half ^ 19)⟩,
       ⟨((-21551 : Dyadic) * half ^ 17),
        ((-229667 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((18497 : Dyadic) * half ^ 15),
        ((-8367 : Dyadic) * half ^ 17)⟩,
       ⟨((-15371 : Dyadic) * half ^ 18),
        ((-53023 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-15371 : Dyadic) * half ^ 18),
        ((-53023 : Dyadic) * half ^ 18)⟩,
       ⟨((18497 : Dyadic) * half ^ 15),
        ((-8367 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((21551 : Dyadic) * half ^ 17),
        ((229667 : Dyadic) * half ^ 19)⟩,
       ⟨((11619 : Dyadic) * half ^ 16),
        ((-141507 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word35Step24 :
    word35Chunk24.foldl (fun acc a => a.applyPacked acc)
      word35State24 = word35State25 := by decide +kernel

private def word35Chunk25 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word35State26 : PackedMat2 :=
    ⟨⟨⟨((49995 : Dyadic) * half ^ 17),
        ((242761 : Dyadic) * half ^ 20)⟩,
       ⟨((-424119 : Dyadic) * half ^ 19),
        ((88771 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-61199 : Dyadic) * half ^ 19),
        ((172331 : Dyadic) * half ^ 20)⟩,
       ⟨((-2273 : Dyadic) * half ^ 18),
        ((77297 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-62407 : Dyadic) * half ^ 18),
        ((65745 : Dyadic) * half ^ 20)⟩,
       ⟨((-47517 : Dyadic) * half ^ 19),
        ((56653 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((82883 : Dyadic) * half ^ 18),
        ((-224139 : Dyadic) * half ^ 20)⟩,
       ⟨((76995 : Dyadic) * half ^ 19),
        ((624099 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word35Step25 :
    word35Chunk25.foldl (fun acc a => a.applyPacked acc)
      word35State25 = word35State26 := by decide +kernel

private def word35Chunk26 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word35State27 : PackedMat2 :=
    ⟨⟨⟨((-102601 : Dyadic) * half ^ 19),
        ((448973 : Dyadic) * half ^ 21)⟩,
       ⟨((-62495 : Dyadic) * half ^ 20),
        ((-101409 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-486329 : Dyadic) * half ^ 20),
        ((583877 : Dyadic) * half ^ 21)⟩,
       ⟨((72767 : Dyadic) * half ^ 17),
        ((635159 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((72767 : Dyadic) * half ^ 17),
        ((635159 : Dyadic) * half ^ 21)⟩,
       ⟨((-486329 : Dyadic) * half ^ 20),
        ((583877 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((62495 : Dyadic) * half ^ 20),
        ((101409 : Dyadic) * half ^ 21)⟩,
       ⟨((102601 : Dyadic) * half ^ 19),
        ((-448973 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word35Step26 :
    word35Chunk26.foldl (fun acc a => a.applyPacked acc)
      word35State26 = word35State27 := by decide +kernel

private def word35Chunk27 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word35State28 : PackedMat2 :=
    ⟨⟨⟨((-49025 : Dyadic) * half ^ 20),
        ((-202401 : Dyadic) * half ^ 21)⟩,
       ⟨((-140485 : Dyadic) * half ^ 20),
        ((21757 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((175523 : Dyadic) * half ^ 21),
        ((-937757 : Dyadic) * half ^ 21)⟩,
       ⟨((424021 : Dyadic) * half ^ 21),
        ((802721 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((33759 : Dyadic) * half ^ 19),
        ((-74943 : Dyadic) * half ^ 19)⟩,
       ⟨((870239 : Dyadic) * half ^ 20),
        ((124249 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((493823 : Dyadic) * half ^ 21),
        ((-94755 : Dyadic) * half ^ 20)⟩,
       ⟨((-898625 : Dyadic) * half ^ 21),
        ((22865 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word35Step27 :
    word35Chunk27.foldl (fun acc a => a.applyPacked acc)
      word35State27 = word35State28 := by decide +kernel

private def word35Chunk28 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word35State29 : PackedMat2 :=
    ⟨⟨⟨((-384569 : Dyadic) * half ^ 22),
        ((-702135 : Dyadic) * half ^ 22)⟩,
       ⟨((2417221 : Dyadic) * half ^ 22),
        ((-481943 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1846199 : Dyadic) * half ^ 22),
        ((-178723 : Dyadic) * half ^ 22)⟩,
       ⟨((-1282159 : Dyadic) * half ^ 22),
        ((-674623 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1846199 : Dyadic) * half ^ 22),
        ((-178723 : Dyadic) * half ^ 22)⟩,
       ⟨((1282159 : Dyadic) * half ^ 22),
        ((674623 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((384569 : Dyadic) * half ^ 22),
        ((702135 : Dyadic) * half ^ 22)⟩,
       ⟨((2417221 : Dyadic) * half ^ 22),
        ((-481943 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word35Step28 :
    word35Chunk28.foldl (fun acc a => a.applyPacked acc)
      word35State28 = word35State29 := by decide +kernel

private def word35Chunk29 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word35State30 : PackedMat2 :=
    ⟨⟨⟨((-904275 : Dyadic) * half ^ 21),
        ((86403 : Dyadic) * half ^ 23)⟩,
       ⟨((-796413 : Dyadic) * half ^ 21),
        ((2627323 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((2341725 : Dyadic) * half ^ 22),
        ((487021 : Dyadic) * half ^ 21)⟩,
       ⟨((81303 : Dyadic) * half ^ 21),
        ((-678771 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-1652813 : Dyadic) * half ^ 22),
        ((-2179119 : Dyadic) * half ^ 23)⟩,
       ⟨((295271 : Dyadic) * half ^ 22),
        ((2504331 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-317615 : Dyadic) * half ^ 20),
        ((-53931 : Dyadic) * half ^ 21)⟩,
       ⟨((-1356863 : Dyadic) * half ^ 22),
        ((106293 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word35Step29 :
    word35Chunk29.foldl (fun acc a => a.applyPacked acc)
      word35State29 = word35State30 := by decide +kernel

private def word35Chunk30 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word35State31 : PackedMat2 :=
    ⟨⟨⟨((2010477 : Dyadic) * half ^ 22),
        ((-4296339 : Dyadic) * half ^ 24)⟩,
       ⟨((656167 : Dyadic) * half ^ 23),
        ((-1741707 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((898507 : Dyadic) * half ^ 21),
        ((5954589 : Dyadic) * half ^ 24)⟩,
       ⟨((-608643 : Dyadic) * half ^ 23),
        ((4900619 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-1356901 : Dyadic) * half ^ 21),
        ((-2985385 : Dyadic) * half ^ 24)⟩,
       ⟨((-526985 : Dyadic) * half ^ 23),
        ((-4202671 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-3019023 : Dyadic) * half ^ 23),
        ((4677121 : Dyadic) * half ^ 24)⟩,
       ⟨((-319329 : Dyadic) * half ^ 21),
        ((3364787 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word35Step30 :
    word35Chunk30.foldl (fun acc a => a.applyPacked acc)
      word35State30 = word35State31 := by decide +kernel

private def word35Chunk31 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word35State32 : PackedMat2 :=
    ⟨⟨⟨((-9548465 : Dyadic) * half ^ 24),
        ((862061 : Dyadic) * half ^ 23)⟩,
       ⟨((-262879 : Dyadic) * half ^ 24),
        ((1755777 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((781277 : Dyadic) * half ^ 23),
        ((-2737219 : Dyadic) * half ^ 23)⟩,
       ⟨((2243527 : Dyadic) * half ^ 22),
        ((2890531 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-2583907 : Dyadic) * half ^ 24),
        ((5268331 : Dyadic) * half ^ 24)⟩,
       ⟨((-8364969 : Dyadic) * half ^ 24),
        ((-3705777 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-1308919 : Dyadic) * half ^ 22),
        ((613209 : Dyadic) * half ^ 21)⟩,
       ⟨((223429 : Dyadic) * half ^ 21),
        ((4642793 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word35Step31 :
    word35Chunk31.foldl (fun acc a => a.applyPacked acc)
      word35State31 = word35State32 := by decide +kernel

private def word35Chunk32 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word35State33 : PackedMat2 :=
    ⟨⟨⟨((12685231 : Dyadic) * half ^ 25),
        ((-635593 : Dyadic) * half ^ 21)⟩,
       ⟨((-962803 : Dyadic) * half ^ 25),
        ((-4013195 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-19660105 : Dyadic) * half ^ 25),
        ((-4839531 : Dyadic) * half ^ 25)⟩,
       ⟨((16892081 : Dyadic) * half ^ 25),
        ((443887 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((6615079 : Dyadic) * half ^ 25),
        ((18276093 : Dyadic) * half ^ 25)⟩,
       ⟨((-3063983 : Dyadic) * half ^ 25),
        ((-346003 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-6156293 : Dyadic) * half ^ 25),
        ((6824017 : Dyadic) * half ^ 25)⟩,
       ⟨((14182683 : Dyadic) * half ^ 25),
        ((-2930607 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word35Step32 :
    word35Chunk32.foldl (fun acc a => a.applyPacked acc)
      word35State32 = word35State33 := by decide +kernel

private def word35Chunk33 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word35State34 : PackedMat2 :=
    ⟨⟨⟨((-6497813 : Dyadic) * half ^ 24),
        ((-1577667 : Dyadic) * half ^ 26)⟩,
       ⟨((965353 : Dyadic) * half ^ 23),
        ((-9748279 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-10207425 : Dyadic) * half ^ 25),
        ((-14129835 : Dyadic) * half ^ 25)⟩,
       ⟨((-7572923 : Dyadic) * half ^ 24),
        ((4478441 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((7572923 : Dyadic) * half ^ 24),
        ((-4478441 : Dyadic) * half ^ 24)⟩,
       ⟨((10207425 : Dyadic) * half ^ 25),
        ((14129835 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((965353 : Dyadic) * half ^ 23),
        ((-9748279 : Dyadic) * half ^ 26)⟩,
       ⟨((-6497813 : Dyadic) * half ^ 24),
        ((-1577667 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word35Step33 :
    word35Chunk33.foldl (fun acc a => a.applyPacked acc)
      word35State33 = word35State34 := by decide +kernel

private def word35Chunk34 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word35State35 : PackedMat2 :=
    ⟨⟨⟨((18392473 : Dyadic) * half ^ 26),
        ((19822179 : Dyadic) * half ^ 27)⟩,
       ⟨((283353 : Dyadic) * half ^ 25),
        ((-5902023 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-3396419 : Dyadic) * half ^ 26),
        ((6150113 : Dyadic) * half ^ 27)⟩,
       ⟨((1925387 : Dyadic) * half ^ 25),
        ((-88383743 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((1925387 : Dyadic) * half ^ 25),
        ((-88383743 : Dyadic) * half ^ 27)⟩,
       ⟨((-3396419 : Dyadic) * half ^ 26),
        ((6150113 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-283353 : Dyadic) * half ^ 25),
        ((5902023 : Dyadic) * half ^ 27)⟩,
       ⟨((-18392473 : Dyadic) * half ^ 26),
        ((-19822179 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word35Step34 :
    word35Chunk34.foldl (fun acc a => a.applyPacked acc)
      word35State34 = word35State35 := by decide +kernel

private def word35Chunk35 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word35State36 : PackedMat2 :=
    ⟨⟨⟨((66522401 : Dyadic) * half ^ 27),
        ((1107493 : Dyadic) * half ^ 23)⟩,
       ⟨((53607265 : Dyadic) * half ^ 27),
        ((5125309 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-5281381 : Dyadic) * half ^ 26),
        ((31882569 : Dyadic) * half ^ 27)⟩,
       ⟨((-21205021 : Dyadic) * half ^ 25),
        ((4101355 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-48287989 : Dyadic) * half ^ 27),
        ((47691423 : Dyadic) * half ^ 27)⟩,
       ⟨((-15477149 : Dyadic) * half ^ 27),
        ((-37128661 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((13985253 : Dyadic) * half ^ 26),
        ((60064833 : Dyadic) * half ^ 27)⟩,
       ⟨((3734635 : Dyadic) * half ^ 26),
        ((201799 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word35Step35 :
    word35Chunk35.foldl (fun acc a => a.applyPacked acc)
      word35State35 = word35State36 := by decide +kernel

private def word35Chunk36 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word35State37 : PackedMat2 :=
    ⟨⟨⟨((-102987573 : Dyadic) * half ^ 28),
        ((72677203 : Dyadic) * half ^ 28)⟩,
       ⟨((76460875 : Dyadic) * half ^ 28),
        ((51604861 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((94977957 : Dyadic) * half ^ 28),
        ((-2326175 : Dyadic) * half ^ 24)⟩,
       ⟨((-44274323 : Dyadic) * half ^ 28),
        ((-70657403 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((94977957 : Dyadic) * half ^ 28),
        ((-2326175 : Dyadic) * half ^ 24)⟩,
       ⟨((44274323 : Dyadic) * half ^ 28),
        ((70657403 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((102987573 : Dyadic) * half ^ 28),
        ((-72677203 : Dyadic) * half ^ 28)⟩,
       ⟨((76460875 : Dyadic) * half ^ 28),
        ((51604861 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word35Step36 :
    word35Chunk36.foldl (fun acc a => a.applyPacked acc)
      word35State36 = word35State37 := by decide +kernel

private def word35Chunk37 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word35State38 : PackedMat2 :=
    ⟨⟨⟨((88384867 : Dyadic) * half ^ 28),
        ((-28943639 : Dyadic) * half ^ 26)⟩,
       ⟨((17498317 : Dyadic) * half ^ 27),
        ((39755969 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((569233 : Dyadic) * half ^ 21),
        ((152372011 : Dyadic) * half ^ 29)⟩,
       ⟨((-9608671 : Dyadic) * half ^ 26),
        ((-171217347 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-9608671 : Dyadic) * half ^ 26),
        ((-171217347 : Dyadic) * half ^ 29)⟩,
       ⟨((569233 : Dyadic) * half ^ 21),
        ((152372011 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-17498317 : Dyadic) * half ^ 27),
        ((-39755969 : Dyadic) * half ^ 28)⟩,
       ⟨((-88384867 : Dyadic) * half ^ 28),
        ((28943639 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word35Step37 :
    word35Chunk37.foldl (fun acc a => a.applyPacked acc)
      word35State37 = word35State38 := by decide +kernel

private def word35Chunk38 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word35State39 : PackedMat2 :=
    ⟨⟨⟨((-208255001 : Dyadic) * half ^ 29),
        ((-270169081 : Dyadic) * half ^ 30)⟩,
       ⟨((-20057081 : Dyadic) * half ^ 29),
        ((512999035 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-154155001 : Dyadic) * half ^ 29),
        ((61711101 : Dyadic) * half ^ 29)⟩,
       ⟨((92818389 : Dyadic) * half ^ 28),
        ((-72584349 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((67147725 : Dyadic) * half ^ 28),
        ((-339791779 : Dyadic) * half ^ 30)⟩,
       ⟨((339789 : Dyadic) * half ^ 24),
        ((-31481777 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((195792029 : Dyadic) * half ^ 28),
        ((5881185 : Dyadic) * half ^ 25)⟩,
       ⟨((121414977 : Dyadic) * half ^ 29),
        ((-114156041 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word35Step38 :
    word35Chunk38.foldl (fun acc a => a.applyPacked acc)
      word35State38 = word35State39 := by decide +kernel

private def word35Chunk39 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word35State40 : PackedMat2 :=
    ⟨⟨⟨((-404267001 : Dyadic) * half ^ 30),
        ((-806086835 : Dyadic) * half ^ 31)⟩,
       ⟨((14888407 : Dyadic) * half ^ 27),
        ((-165114545 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((146040425 : Dyadic) * half ^ 30),
        ((107027777 : Dyadic) * half ^ 31)⟩,
       ⟨((-79845195 : Dyadic) * half ^ 28),
        ((1007694793 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((557361285 : Dyadic) * half ^ 30),
        ((-173340355 : Dyadic) * half ^ 31)⟩,
       ⟨((-112583377 : Dyadic) * half ^ 28),
        ((465421205 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((242800345 : Dyadic) * half ^ 29),
        ((285159745 : Dyadic) * half ^ 31)⟩,
       ⟨((320486145 : Dyadic) * half ^ 30),
        ((523374257 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word35Step39 :
    word35Chunk39.foldl (fun acc a => a.applyPacked acc)
      word35State39 = word35State40 := by decide +kernel

private def word35Chunk40 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word35State41 : PackedMat2 :=
    ⟨⟨⟨((-183916403 : Dyadic) * half ^ 30),
        ((-204189953 : Dyadic) * half ^ 30)⟩,
       ⟨((-509857527 : Dyadic) * half ^ 30),
        ((-51225559 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((912009247 : Dyadic) * half ^ 31),
        ((-215227099 : Dyadic) * half ^ 31)⟩,
       ⟨((1474221363 : Dyadic) * half ^ 31),
        ((-4179763 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-912009247 : Dyadic) * half ^ 31),
        ((215227099 : Dyadic) * half ^ 31)⟩,
       ⟨((1474221363 : Dyadic) * half ^ 31),
        ((-4179763 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-183916403 : Dyadic) * half ^ 30),
        ((-204189953 : Dyadic) * half ^ 30)⟩,
       ⟨((509857527 : Dyadic) * half ^ 30),
        ((51225559 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word35Step40 :
    word35Chunk40.foldl (fun acc a => a.applyPacked acc)
      word35State40 = word35State41 := by decide +kernel

private def word35Chunk41 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word35State42 : PackedMat2 :=
    ⟨⟨⟨((1114964489 : Dyadic) * half ^ 32),
        ((-265917173 : Dyadic) * half ^ 31)⟩,
       ⟨((-1944505287 : Dyadic) * half ^ 32),
        ((-1423915197 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1536842755 : Dyadic) * half ^ 32),
        ((331142229 : Dyadic) * half ^ 30)⟩,
       ⟨((-116065333 : Dyadic) * half ^ 32),
        ((1207768705 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((116800211 : Dyadic) * half ^ 32),
        ((-710388711 : Dyadic) * half ^ 32)⟩,
       ⟨((-2532337621 : Dyadic) * half ^ 32),
        ((206613511 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-892080851 : Dyadic) * half ^ 32),
        ((-191216861 : Dyadic) * half ^ 29)⟩,
       ⟨((-1955749543 : Dyadic) * half ^ 32),
        ((-414770399 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word35Step41 :
    word35Chunk41.foldl (fun acc a => a.applyPacked acc)
      word35State41 = word35State42 := by decide +kernel

private def word35Chunk42 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word35State43 : PackedMat2 :=
    ⟨⟨⟨((23876137 : Dyadic) * half ^ 28),
        ((3249268397 : Dyadic) * half ^ 33)⟩,
       ⟨((199867929 : Dyadic) * half ^ 31),
        ((-3302793677 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((228580251 : Dyadic) * half ^ 29),
        ((-303719143 : Dyadic) * half ^ 31)⟩,
       ⟨((1417222099 : Dyadic) * half ^ 32),
        ((811636991 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((1417222099 : Dyadic) * half ^ 32),
        ((811636991 : Dyadic) * half ^ 32)⟩,
       ⟨((228580251 : Dyadic) * half ^ 29),
        ((-303719143 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-199867929 : Dyadic) * half ^ 31),
        ((3302793677 : Dyadic) * half ^ 33)⟩,
       ⟨((-23876137 : Dyadic) * half ^ 28),
        ((-3249268397 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word35Step42 :
    word35Chunk42.foldl (fun acc a => a.applyPacked acc)
      word35State42 = word35State43 := by decide +kernel

private def word35Chunk43 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word35State44 : PackedMat2 :=
    ⟨⟨⟨((2133377319 : Dyadic) * half ^ 32),
        ((5690104043 : Dyadic) * half ^ 34)⟩,
       ⟨((-1092133477 : Dyadic) * half ^ 33),
        ((2833863541 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-3031834529 : Dyadic) * half ^ 33),
        ((5336803711 : Dyadic) * half ^ 34)⟩,
       ⟨((1534948899 : Dyadic) * half ^ 32),
        ((-1629700771 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-926775735 : Dyadic) * half ^ 32),
        ((-38063269 : Dyadic) * half ^ 34)⟩,
       ⟨((-3483252241 : Dyadic) * half ^ 33),
        ((6101732327 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((266373987 : Dyadic) * half ^ 29),
        ((3174621161 : Dyadic) * half ^ 34)⟩,
       ⟨((1428120251 : Dyadic) * half ^ 33),
        ((5358888115 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word35Step43 :
    word35Chunk43.foldl (fun acc a => a.applyPacked acc)
      word35State43 = word35State44 := by decide +kernel

private def word35Chunk44 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word35State45 : PackedMat2 :=
    ⟨⟨⟨((1285333619 : Dyadic) * half ^ 34),
        ((-2125470795 : Dyadic) * half ^ 33)⟩,
       ⟨((12690769705 : Dyadic) * half ^ 34),
        ((1100290223 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((3855971805 : Dyadic) * half ^ 33),
        ((-514841403 : Dyadic) * half ^ 32)⟩,
       ⟨((-789011845 : Dyadic) * half ^ 32),
        ((2085352105 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((3855971805 : Dyadic) * half ^ 33),
        ((-514841403 : Dyadic) * half ^ 32)⟩,
       ⟨((789011845 : Dyadic) * half ^ 32),
        ((-2085352105 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1285333619 : Dyadic) * half ^ 34),
        ((2125470795 : Dyadic) * half ^ 33)⟩,
       ⟨((12690769705 : Dyadic) * half ^ 34),
        ((1100290223 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word35Step44 :
    word35Chunk44.foldl (fun acc a => a.applyPacked acc)
      word35State44 = word35State45 := by decide +kernel

private def word35Chunk45 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word35State46 : PackedMat2 :=
    ⟨⟨⟨((-28904596495 : Dyadic) * half ^ 35),
        ((1144118785 : Dyadic) * half ^ 35)⟩,
       ⟨((2530447131 : Dyadic) * half ^ 35),
        ((2631295055 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((322649775 : Dyadic) * half ^ 35),
        ((1375649915 : Dyadic) * half ^ 35)⟩,
       ⟨((-808121885 : Dyadic) * half ^ 35),
        ((-3707996719 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-8791643353 : Dyadic) * half ^ 35),
        ((-282692915 : Dyadic) * half ^ 34)⟩,
       ⟨((-6040343523 : Dyadic) * half ^ 35),
        ((-242736055 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-9381061435 : Dyadic) * half ^ 35),
        ((-15717521813 : Dyadic) * half ^ 35)⟩,
       ⟨((-11669299005 : Dyadic) * half ^ 35),
        ((6593537341 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word35Step45 :
    word35Chunk45.foldl (fun acc a => a.applyPacked acc)
      word35State45 = word35State46 := by decide +kernel

private def word35Chunk46 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word35State47 : PackedMat2 :=
    ⟨⟨⟨((-32016283945 : Dyadic) * half ^ 36),
        ((-1606106597 : Dyadic) * half ^ 36)⟩,
       ⟨((17186432573 : Dyadic) * half ^ 36),
        ((-10018303921 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-47974041145 : Dyadic) * half ^ 36),
        ((-7427746317 : Dyadic) * half ^ 36)⟩,
       ⟨((10322772851 : Dyadic) * half ^ 36),
        ((-767753533 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-47974041145 : Dyadic) * half ^ 36),
        ((-7427746317 : Dyadic) * half ^ 36)⟩,
       ⟨((-10322772851 : Dyadic) * half ^ 36),
        ((767753533 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((32016283945 : Dyadic) * half ^ 36),
        ((1606106597 : Dyadic) * half ^ 36)⟩,
       ⟨((17186432573 : Dyadic) * half ^ 36),
        ((-10018303921 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word35Step46 :
    word35Chunk46.foldl (fun acc a => a.applyPacked acc)
      word35State46 = word35State47 := by decide +kernel

private def word35Chunk47 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word35State48 : PackedMat2 :=
    ⟨⟨⟨((-3414435593 : Dyadic) * half ^ 36),
        ((1711489511 : Dyadic) * half ^ 35)⟩,
       ⟨((-8850472697 : Dyadic) * half ^ 34),
        ((22364366487 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-11705244981 : Dyadic) * half ^ 35),
        ((-49246938567 : Dyadic) * half ^ 37)⟩,
       ⟨((-10456899107 : Dyadic) * half ^ 35),
        ((-21706331725 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((13770303421 : Dyadic) * half ^ 36),
        ((624172937 : Dyadic) * half ^ 35)⟩,
       ⟨((-17738317573 : Dyadic) * half ^ 35),
        ((-2770268011 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-18941387465 : Dyadic) * half ^ 36),
        ((31987455195 : Dyadic) * half ^ 37)⟩,
       ⟨((-25787345509 : Dyadic) * half ^ 36),
        ((38816326381 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word35Step47 :
    word35Chunk47.foldl (fun acc a => a.applyPacked acc)
      word35State47 = word35State48 := by decide +kernel

private def word35Chunk48 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word35State49 : PackedMat2 :=
    ⟨⟨⟨((-34842101985 : Dyadic) * half ^ 37),
        ((130357484875 : Dyadic) * half ^ 38)⟩,
       ⟨((-19798713017 : Dyadic) * half ^ 37),
        ((-79679807869 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-5662575027 : Dyadic) * half ^ 37),
        ((-19707675869 : Dyadic) * half ^ 37)⟩,
       ⟨((-15451990463 : Dyadic) * half ^ 35),
        ((-22174964719 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((1233644425 : Dyadic) * half ^ 36),
        ((56145386825 : Dyadic) * half ^ 38)⟩,
       ⟨((10470660147 : Dyadic) * half ^ 35),
        ((67470536879 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-26254661593 : Dyadic) * half ^ 35),
        ((1880423621 : Dyadic) * half ^ 35)⟩,
       ⟨((25338838503 : Dyadic) * half ^ 37),
        ((-27320407501 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word35Step48 :
    word35Chunk48.foldl (fun acc a => a.applyPacked acc)
      word35State48 = word35State49 := by decide +kernel

private def word35Chunk49 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word35State50 : PackedMat2 :=
    ⟨⟨⟨((10132921889 : Dyadic) * half ^ 34),
        ((-9575679149 : Dyadic) * half ^ 39)⟩,
       ⟨((52178090123 : Dyadic) * half ^ 38),
        ((222867014621 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-35080820643 : Dyadic) * half ^ 38),
        ((154954056969 : Dyadic) * half ^ 39)⟩,
       ⟨((9900396185 : Dyadic) * half ^ 36),
        ((-117176774181 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((9900396185 : Dyadic) * half ^ 36),
        ((-117176774181 : Dyadic) * half ^ 39)⟩,
       ⟨((-35080820643 : Dyadic) * half ^ 38),
        ((154954056969 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-52178090123 : Dyadic) * half ^ 38),
        ((-222867014621 : Dyadic) * half ^ 39)⟩,
       ⟨((-10132921889 : Dyadic) * half ^ 34),
        ((9575679149 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word35Step49 :
    word35Chunk49.foldl (fun acc a => a.applyPacked acc)
      word35State49 = word35State50 := by decide +kernel

private def word35Chunk50 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word35State51 : PackedMat2 :=
    ⟨⟨⟨((71673261737 : Dyadic) * half ^ 39),
        ((-191677670281 : Dyadic) * half ^ 39)⟩,
       ⟨((-160507087597 : Dyadic) * half ^ 39),
        ((72580326481 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((214802955923 : Dyadic) * half ^ 39),
        ((177581227035 : Dyadic) * half ^ 39)⟩,
       ⟨((7267563307 : Dyadic) * half ^ 39),
        ((-76194383521 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-329969994077 : Dyadic) * half ^ 39),
        ((-25941924077 : Dyadic) * half ^ 37)⟩,
       ⟨((25192459993 : Dyadic) * half ^ 39),
        ((111035259615 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-336838323243 : Dyadic) * half ^ 39),
        ((116090174667 : Dyadic) * half ^ 39)⟩,
       ⟨((46517017319 : Dyadic) * half ^ 39),
        ((22208456465 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word35Step50 :
    word35Chunk50.foldl (fun acc a => a.applyPacked acc)
      word35State50 = word35State51 := by decide +kernel

private def word35Chunk51 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word35State52 : PackedMat2 :=
    ⟨⟨⟨((-60184233519 : Dyadic) * half ^ 38),
        ((638651559 : Dyadic) * half ^ 36)⟩,
       ⟨((200233143969 : Dyadic) * half ^ 39),
        ((-101837004569 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((67101640611 : Dyadic) * half ^ 38),
        ((-66585416647 : Dyadic) * half ^ 40)⟩,
       ⟨((20131823859 : Dyadic) * half ^ 37),
        ((632682923973 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-20131823859 : Dyadic) * half ^ 37),
        ((-632682923973 : Dyadic) * half ^ 40)⟩,
       ⟨((-67101640611 : Dyadic) * half ^ 38),
        ((66585416647 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((200233143969 : Dyadic) * half ^ 39),
        ((-101837004569 : Dyadic) * half ^ 39)⟩,
       ⟨((-60184233519 : Dyadic) * half ^ 38),
        ((638651559 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word35Step51 :
    word35Chunk51.foldl (fun acc a => a.applyPacked acc)
      word35State51 = word35State52 := by decide +kernel

private def word35Chunk52 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word35State53 : PackedMat2 :=
    ⟨⟨⟨((-255967213553 : Dyadic) * half ^ 40),
        ((-341876603471 : Dyadic) * half ^ 41)⟩,
       ⟨((-33847616397 : Dyadic) * half ^ 39),
        ((240081125227 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-661092539065 : Dyadic) * half ^ 40),
        ((-432556844609 : Dyadic) * half ^ 41)⟩,
       ⟨((221835478245 : Dyadic) * half ^ 39),
        ((-805139374969 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-618848109789 : Dyadic) * half ^ 40),
        ((-217421582575 : Dyadic) * half ^ 41)⟩,
       ⟨((46572816295 : Dyadic) * half ^ 38),
        ((-1104763495555 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((25448869561 : Dyadic) * half ^ 39),
        ((323662446347 : Dyadic) * half ^ 41)⟩,
       ⟨((290978864349 : Dyadic) * half ^ 40),
        ((188271980759 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word35Step52 :
    word35Chunk52.foldl (fun acc a => a.applyPacked acc)
      word35State52 = word35State53 := by decide +kernel

private def word35Chunk53 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word35State54 : PackedMat2 :=
    ⟨⟨⟨((-56114991483 : Dyadic) * half ^ 37),
        ((-1451415135941 : Dyadic) * half ^ 42)⟩,
       ⟨((-277512110771 : Dyadic) * half ^ 41),
        ((-546030486861 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((406459843143 : Dyadic) * half ^ 40),
        ((-1860417609159 : Dyadic) * half ^ 42)⟩,
       ⟨((-68568231323 : Dyadic) * half ^ 41),
        ((-841521755265 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((337742420553 : Dyadic) * half ^ 39),
        ((-744351454963 : Dyadic) * half ^ 42)⟩,
       ⟨((509447926947 : Dyadic) * half ^ 41),
        ((-881487917609 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-998722811401 : Dyadic) * half ^ 41),
        ((-1175351974499 : Dyadic) * half ^ 42)⟩,
       ⟨((-113173081135 : Dyadic) * half ^ 39),
        ((-620327752957 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word35Step53 :
    word35Chunk53.foldl (fun acc a => a.applyPacked acc)
      word35State53 = word35State54 := by decide +kernel

private def word35Chunk54 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word35State55 : PackedMat2 :=
    ⟨⟨⟨((-90260036327 : Dyadic) * half ^ 42),
        ((809383869751 : Dyadic) * half ^ 41)⟩,
       ⟨((-1687618795681 : Dyadic) * half ^ 42),
        ((-730564594711 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-1075819622819 : Dyadic) * half ^ 41),
        ((533003036523 : Dyadic) * half ^ 41)⟩,
       ⟨((-23996206729 : Dyadic) * half ^ 39),
        ((135743043965 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-1075819622819 : Dyadic) * half ^ 41),
        ((533003036523 : Dyadic) * half ^ 41)⟩,
       ⟨((23996206729 : Dyadic) * half ^ 39),
        ((-135743043965 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((90260036327 : Dyadic) * half ^ 42),
        ((-809383869751 : Dyadic) * half ^ 41)⟩,
       ⟨((-1687618795681 : Dyadic) * half ^ 42),
        ((-730564594711 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word35Step54 :
    word35Chunk54.foldl (fun acc a => a.applyPacked acc)
      word35State54 = word35State55 := by decide +kernel

private def word35Chunk55 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word35State56 : PackedMat2 :=
    ⟨⟨⟨((7076793520323 : Dyadic) * half ^ 43),
        ((304863080049 : Dyadic) * half ^ 43)⟩,
       ⟨((-3204488069003 : Dyadic) * half ^ 43),
        ((33445993893 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((2233721763597 : Dyadic) * half ^ 43),
        ((-668614550101 : Dyadic) * half ^ 43)⟩,
       ⟨((-192534362027 : Dyadic) * half ^ 43),
        ((583791402159 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((3003780158737 : Dyadic) * half ^ 43),
        ((-303282015703 : Dyadic) * half ^ 41)⟩,
       ⟨((1666551058535 : Dyadic) * half ^ 43),
        ((1020593700785 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((237971092263 : Dyadic) * half ^ 43),
        ((5140640794663 : Dyadic) * half ^ 43)⟩,
       ⟨((-371755067835 : Dyadic) * half ^ 43),
        ((-484038181415 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word35Step55 :
    word35Chunk55.foldl (fun acc a => a.applyPacked acc)
      word35State55 = word35State56 := by decide +kernel

private def word35Chunk56 : List Letter := [.h, .t, .h]
private def word35State57 : PackedMat2 :=
    ⟨⟨⟨((1569033316865 : Dyadic) * half ^ 41),
        ((3563761261799 : Dyadic) * half ^ 44)⟩,
       ⟨((-486823790303 : Dyadic) * half ^ 43),
        ((688472805595 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((-237777525725 : Dyadic) * half ^ 39),
        ((5380291227325 : Dyadic) * half ^ 44)⟩,
       ⟨((-1051113220165 : Dyadic) * half ^ 43),
        ((1486498571547 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((237777525725 : Dyadic) * half ^ 39),
        ((-5380291227325 : Dyadic) * half ^ 44)⟩,
       ⟨((-1051113220165 : Dyadic) * half ^ 43),
        ((1486498571547 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((1569033316865 : Dyadic) * half ^ 41),
        ((3563761261799 : Dyadic) * half ^ 44)⟩,
       ⟨((486823790303 : Dyadic) * half ^ 43),
        ((-688472805595 : Dyadic) * half ^ 44)⟩⟩⟩
private lemma word35Step56 :
    word35Chunk56.foldl (fun acc a => a.applyPacked acc)
      word35State56 = word35State57 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word35_check : check word35 35 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word35 = word35State57.toMatrix := by
    unfold evalRingPacked
    change ((
      word35Chunk0 ++ word35Chunk1 ++ word35Chunk2 ++ word35Chunk3 ++
      word35Chunk4 ++ word35Chunk5 ++ word35Chunk6 ++ word35Chunk7 ++
      word35Chunk8 ++ word35Chunk9 ++ word35Chunk10 ++ word35Chunk11 ++
      word35Chunk12 ++ word35Chunk13 ++ word35Chunk14 ++ word35Chunk15 ++
      word35Chunk16 ++ word35Chunk17 ++ word35Chunk18 ++ word35Chunk19 ++
      word35Chunk20 ++ word35Chunk21 ++ word35Chunk22 ++ word35Chunk23 ++
      word35Chunk24 ++ word35Chunk25 ++ word35Chunk26 ++ word35Chunk27 ++
      word35Chunk28 ++ word35Chunk29 ++ word35Chunk30 ++ word35Chunk31 ++
      word35Chunk32 ++ word35Chunk33 ++ word35Chunk34 ++ word35Chunk35 ++
      word35Chunk36 ++ word35Chunk37 ++ word35Chunk38 ++ word35Chunk39 ++
      word35Chunk40 ++ word35Chunk41 ++ word35Chunk42 ++ word35Chunk43 ++
      word35Chunk44 ++ word35Chunk45 ++ word35Chunk46 ++ word35Chunk47 ++
      word35Chunk48 ++ word35Chunk49 ++ word35Chunk50 ++ word35Chunk51 ++
      word35Chunk52 ++ word35Chunk53 ++ word35Chunk54 ++ word35Chunk55 ++
      word35Chunk56
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word35Step0, word35Step1, word35Step2, word35Step3, word35Step4,
      word35Step5, word35Step6, word35Step7, word35Step8, word35Step9,
      word35Step10, word35Step11, word35Step12, word35Step13, word35Step14,
      word35Step15, word35Step16, word35Step17, word35Step18, word35Step19,
      word35Step20, word35Step21, word35Step22, word35Step23, word35Step24,
      word35Step25, word35Step26, word35Step27, word35Step28, word35Step29,
      word35Step30, word35Step31, word35Step32, word35Step33, word35Step34,
      word35Step35, word35Step36, word35Step37, word35Step38, word35Step39,
      word35Step40, word35Step41, word35Step42, word35Step43, word35Step44,
      word35Step45, word35Step46, word35Step47, word35Step48, word35Step49,
      word35Step50, word35Step51, word35Step52, word35Step53, word35Step54,
      word35Step55, word35Step56]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
