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
private def word31Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word31State1 : PackedMat2 :=
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
private lemma word31Step0 :
    word31Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word31State1 := by decide +kernel

private def word31Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word31State2 : PackedMat2 :=
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
private lemma word31Step1 :
    word31Chunk1.foldl (fun acc a => a.applyPacked acc)
      word31State1 = word31State2 := by decide +kernel

private def word31Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word31State3 : PackedMat2 :=
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
private lemma word31Step2 :
    word31Chunk2.foldl (fun acc a => a.applyPacked acc)
      word31State2 = word31State3 := by decide +kernel

private def word31Chunk3 : List Letter := [.h, .s, .h, .s, .h, .s, .s, .h]
private def word31State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word31Step3 :
    word31Chunk3.foldl (fun acc a => a.applyPacked acc)
      word31State3 = word31State4 := by decide +kernel

private def word31Chunk4 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word31State5 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩⟩
private lemma word31Step4 :
    word31Chunk4.foldl (fun acc a => a.applyPacked acc)
      word31State4 = word31State5 := by decide +kernel

private def word31Chunk5 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word31State6 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩⟩
private lemma word31Step5 :
    word31Chunk5.foldl (fun acc a => a.applyPacked acc)
      word31State5 = word31State6 := by decide +kernel

private def word31Chunk6 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word31State7 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word31Step6 :
    word31Chunk6.foldl (fun acc a => a.applyPacked acc)
      word31State6 = word31State7 := by decide +kernel

private def word31Chunk7 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word31State8 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((9 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((9 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word31Step7 :
    word31Chunk7.foldl (fun acc a => a.applyPacked acc)
      word31State7 = word31State8 := by decide +kernel

private def word31Chunk8 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word31State9 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((13 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 5),
        ((-7 : Dyadic) * half ^ 4)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((-7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((-21 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-5 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word31Step8 :
    word31Chunk8.foldl (fun acc a => a.applyPacked acc)
      word31State8 = word31State9 := by decide +kernel

private def word31Chunk9 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word31State10 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 6),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 6),
        ((13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 6),
        ((-23 : Dyadic) * half ^ 6)⟩,
       ⟨((-51 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-25 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((21 : Dyadic) * half ^ 6),
        ((27 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((19 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 6)⟩,
       ⟨((7 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word31Step9 :
    word31Chunk9.foldl (fun acc a => a.applyPacked acc)
      word31State9 = word31State10 := by decide +kernel

private def word31Chunk10 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word31State11 : PackedMat2 :=
    ⟨⟨⟨((-39 : Dyadic) * half ^ 6),
        ((-33 : Dyadic) * half ^ 7)⟩,
       ⟨((-11 : Dyadic) * half ^ 5),
        ((13 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((-11 : Dyadic) * half ^ 7)⟩,
       ⟨((-29 : Dyadic) * half ^ 6),
        ((33 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((-11 : Dyadic) * half ^ 7)⟩,
       ⟨((29 : Dyadic) * half ^ 6),
        ((-33 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((39 : Dyadic) * half ^ 6),
        ((33 : Dyadic) * half ^ 7)⟩,
       ⟨((-11 : Dyadic) * half ^ 5),
        ((13 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word31Step10 :
    word31Chunk10.foldl (fun acc a => a.applyPacked acc)
      word31State10 = word31State11 := by decide +kernel

private def word31Chunk11 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word31State12 : PackedMat2 :=
    ⟨⟨⟨((-15 : Dyadic) * half ^ 7),
        ((-31 : Dyadic) * half ^ 8)⟩,
       ⟨((-17 : Dyadic) * half ^ 6),
        ((35 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 6),
        ((163 : Dyadic) * half ^ 8)⟩,
       ⟨((-23 : Dyadic) * half ^ 7),
        ((11 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-87 : Dyadic) * half ^ 7),
        ((17 : Dyadic) * half ^ 8)⟩,
       ⟨((-19 : Dyadic) * half ^ 5),
        ((-29 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 6),
        ((-49 : Dyadic) * half ^ 8)⟩,
       ⟨((-33 : Dyadic) * half ^ 7),
        ((19 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word31Step11 :
    word31Chunk11.foldl (fun acc a => a.applyPacked acc)
      word31State11 = word31State12 := by decide +kernel

private def word31Chunk12 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word31State13 : PackedMat2 :=
    ⟨⟨⟨((9 : Dyadic) * half ^ 8),
        ((49 : Dyadic) * half ^ 8)⟩,
       ⟨((43 : Dyadic) * half ^ 8),
        ((-55 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((201 : Dyadic) * half ^ 8),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-17 : Dyadic) * half ^ 8),
        ((19 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((201 : Dyadic) * half ^ 8),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((17 : Dyadic) * half ^ 8),
        ((-19 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 8),
        ((-49 : Dyadic) * half ^ 8)⟩,
       ⟨((43 : Dyadic) * half ^ 8),
        ((-55 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word31Step12 :
    word31Chunk12.foldl (fun acc a => a.applyPacked acc)
      word31State12 = word31State13 := by decide +kernel

private def word31Chunk13 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word31State14 : PackedMat2 :=
    ⟨⟨⟨((-5 : Dyadic) * half ^ 9),
        ((173 : Dyadic) * half ^ 9)⟩,
       ⟨((-193 : Dyadic) * half ^ 9),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-55 : Dyadic) * half ^ 9),
        ((71 : Dyadic) * half ^ 8)⟩,
       ⟨((347 : Dyadic) * half ^ 9),
        ((25 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-117 : Dyadic) * half ^ 9),
        ((201 : Dyadic) * half ^ 9)⟩,
       ⟨((167 : Dyadic) * half ^ 9),
        ((73 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((173 : Dyadic) * half ^ 9),
        ((47 : Dyadic) * half ^ 8)⟩,
       ⟨((-173 : Dyadic) * half ^ 9),
        ((99 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word31Step13 :
    word31Chunk13.foldl (fun acc a => a.applyPacked acc)
      word31State13 = word31State14 := by decide +kernel

private def word31Chunk14 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word31State15 : PackedMat2 :=
    ⟨⟨⟨((297 : Dyadic) * half ^ 9),
        ((-147 : Dyadic) * half ^ 10)⟩,
       ⟨((171 : Dyadic) * half ^ 9),
        ((5 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-17 : Dyadic) * half ^ 8),
        ((93 : Dyadic) * half ^ 10)⟩,
       ⟨((47 : Dyadic) * half ^ 8),
        ((489 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-47 : Dyadic) * half ^ 8),
        ((-489 : Dyadic) * half ^ 10)⟩,
       ⟨((17 : Dyadic) * half ^ 8),
        ((-93 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((171 : Dyadic) * half ^ 9),
        ((5 : Dyadic) * half ^ 10)⟩,
       ⟨((297 : Dyadic) * half ^ 9),
        ((-147 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word31Step14 :
    word31Chunk14.foldl (fun acc a => a.applyPacked acc)
      word31State14 = word31State15 := by decide +kernel

private def word31Chunk15 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word31State16 : PackedMat2 :=
    ⟨⟨⟨((-129 : Dyadic) * half ^ 8),
        ((461 : Dyadic) * half ^ 11)⟩,
       ⟨((11 : Dyadic) * half ^ 10),
        ((135 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((75 : Dyadic) * half ^ 10),
        ((-683 : Dyadic) * half ^ 11)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((749 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((75 : Dyadic) * half ^ 10),
        ((-683 : Dyadic) * half ^ 11)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-749 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((129 : Dyadic) * half ^ 8),
        ((-461 : Dyadic) * half ^ 11)⟩,
       ⟨((11 : Dyadic) * half ^ 10),
        ((135 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word31Step15 :
    word31Chunk15.foldl (fun acc a => a.applyPacked acc)
      word31State15 = word31State16 := by decide +kernel

private def word31Chunk16 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word31State17 : PackedMat2 :=
    ⟨⟨⟨((-627 : Dyadic) * half ^ 11),
        ((281 : Dyadic) * half ^ 12)⟩,
       ⟨((-291 : Dyadic) * half ^ 10),
        ((-41 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-129 : Dyadic) * half ^ 10),
        ((-1957 : Dyadic) * half ^ 12)⟩,
       ⟨((-211 : Dyadic) * half ^ 11),
        ((1671 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((143 : Dyadic) * half ^ 11),
        ((469 : Dyadic) * half ^ 12)⟩,
       ⟨((907 : Dyadic) * half ^ 10),
        ((47 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 8),
        ((-1209 : Dyadic) * half ^ 12)⟩,
       ⟨((161 : Dyadic) * half ^ 11),
        ((-45 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word31Step16 :
    word31Chunk16.foldl (fun acc a => a.applyPacked acc)
      word31State16 = word31State17 := by decide +kernel

private def word31Chunk17 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word31State18 : PackedMat2 :=
    ⟨⟨⟨((163 : Dyadic) * half ^ 10),
        ((229 : Dyadic) * half ^ 12)⟩,
       ⟨((-463 : Dyadic) * half ^ 11),
        ((-355 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-291 : Dyadic) * half ^ 10),
        ((-1073 : Dyadic) * half ^ 12)⟩,
       ⟨((255 : Dyadic) * half ^ 9),
        ((-665 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-291 : Dyadic) * half ^ 10),
        ((-1073 : Dyadic) * half ^ 12)⟩,
       ⟨((-255 : Dyadic) * half ^ 9),
        ((665 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-163 : Dyadic) * half ^ 10),
        ((-229 : Dyadic) * half ^ 12)⟩,
       ⟨((-463 : Dyadic) * half ^ 11),
        ((-355 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word31Step17 :
    word31Chunk17.foldl (fun acc a => a.applyPacked acc)
      word31State17 = word31State18 := by decide +kernel

private def word31Chunk18 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word31State19 : PackedMat2 :=
    ⟨⟨⟨((759 : Dyadic) * half ^ 13),
        ((907 : Dyadic) * half ^ 13)⟩,
       ⟨((-1653 : Dyadic) * half ^ 13),
        ((1421 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1271 : Dyadic) * half ^ 13),
        ((143 : Dyadic) * half ^ 11)⟩,
       ⟨((-6533 : Dyadic) * half ^ 13),
        ((-725 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1297 : Dyadic) * half ^ 13),
        ((-2631 : Dyadic) * half ^ 13)⟩,
       ⟨((-153 : Dyadic) * half ^ 13),
        ((-1951 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1935 : Dyadic) * half ^ 13),
        ((603 : Dyadic) * half ^ 12)⟩,
       ⟨((-3749 : Dyadic) * half ^ 13),
        ((447 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word31Step18 :
    word31Chunk18.foldl (fun acc a => a.applyPacked acc)
      word31State18 = word31State19 := by decide +kernel

private def word31Chunk19 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word31State20 : PackedMat2 :=
    ⟨⟨⟨((3729 : Dyadic) * half ^ 13),
        ((249 : Dyadic) * half ^ 14)⟩,
       ⟨((597 : Dyadic) * half ^ 13),
        ((6445 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1761 : Dyadic) * half ^ 12),
        ((-3811 : Dyadic) * half ^ 14)⟩,
       ⟨((-669 : Dyadic) * half ^ 11),
        ((-3231 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((669 : Dyadic) * half ^ 11),
        ((3231 : Dyadic) * half ^ 14)⟩,
       ⟨((-1761 : Dyadic) * half ^ 12),
        ((3811 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((597 : Dyadic) * half ^ 13),
        ((6445 : Dyadic) * half ^ 14)⟩,
       ⟨((3729 : Dyadic) * half ^ 13),
        ((249 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word31Step19 :
    word31Chunk19.foldl (fun acc a => a.applyPacked acc)
      word31State19 = word31State20 := by decide +kernel

private def word31Chunk20 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word31State21 : PackedMat2 :=
    ⟨⟨⟨((-319 : Dyadic) * half ^ 13),
        ((7211 : Dyadic) * half ^ 15)⟩,
       ⟨((13695 : Dyadic) * half ^ 14),
        ((597 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((1963 : Dyadic) * half ^ 14),
        ((7143 : Dyadic) * half ^ 15)⟩,
       ⟨((1819 : Dyadic) * half ^ 13),
        ((-4837 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((1153 : Dyadic) * half ^ 14),
        ((5601 : Dyadic) * half ^ 15)⟩,
       ⟨((2995 : Dyadic) * half ^ 13),
        ((-1675 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-61 : Dyadic) * half ^ 8),
        ((-13057 : Dyadic) * half ^ 15)⟩,
       ⟨((-3307 : Dyadic) * half ^ 14),
        ((14333 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word31Step20 :
    word31Chunk20.foldl (fun acc a => a.applyPacked acc)
      word31State20 = word31State21 := by decide +kernel

private def word31Chunk21 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word31State22 : PackedMat2 :=
    ⟨⟨⟨((-8597 : Dyadic) * half ^ 15),
        ((-4135 : Dyadic) * half ^ 14)⟩,
       ⟨((-4439 : Dyadic) * half ^ 15),
        ((4499 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-3515 : Dyadic) * half ^ 15),
        ((-8519 : Dyadic) * half ^ 15)⟩,
       ⟨((-3829 : Dyadic) * half ^ 15),
        ((15957 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((3515 : Dyadic) * half ^ 15),
        ((8519 : Dyadic) * half ^ 15)⟩,
       ⟨((-3829 : Dyadic) * half ^ 15),
        ((15957 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-8597 : Dyadic) * half ^ 15),
        ((-4135 : Dyadic) * half ^ 14)⟩,
       ⟨((4439 : Dyadic) * half ^ 15),
        ((-4499 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word31Step21 :
    word31Chunk21.foldl (fun acc a => a.applyPacked acc)
      word31State21 = word31State22 := by decide +kernel

private def word31Chunk22 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word31State23 : PackedMat2 :=
    ⟨⟨⟨((-717 : Dyadic) * half ^ 16),
        ((357 : Dyadic) * half ^ 12)⟩,
       ⟨((-7259 : Dyadic) * half ^ 16),
        ((-7829 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-25729 : Dyadic) * half ^ 16),
        ((-15551 : Dyadic) * half ^ 16)⟩,
       ⟨((12191 : Dyadic) * half ^ 16),
        ((-18573 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((21595 : Dyadic) * half ^ 16),
        ((-1185 : Dyadic) * half ^ 12)⟩,
       ⟨((52697 : Dyadic) * half ^ 16),
        ((6769 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-13541 : Dyadic) * half ^ 16),
        ((-3271 : Dyadic) * half ^ 16)⟩,
       ⟨((-2117 : Dyadic) * half ^ 16),
        ((-997 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word31Step22 :
    word31Chunk22.foldl (fun acc a => a.applyPacked acc)
      word31State22 = word31State23 := by decide +kernel

private def word31Chunk23 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word31State24 : PackedMat2 :=
    ⟨⟨⟨((-17129 : Dyadic) * half ^ 17),
        ((3775 : Dyadic) * half ^ 17)⟩,
       ⟨((44239 : Dyadic) * half ^ 17),
        ((571 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((42989 : Dyadic) * half ^ 17),
        ((-7227 : Dyadic) * half ^ 14)⟩,
       ⟨((-61105 : Dyadic) * half ^ 17),
        ((-35119 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((22697 : Dyadic) * half ^ 17),
        ((-52047 : Dyadic) * half ^ 17)⟩,
       ⟨((-92935 : Dyadic) * half ^ 17),
        ((-4529 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-5361 : Dyadic) * half ^ 17),
        ((-7671 : Dyadic) * half ^ 15)⟩,
       ⟨((-12911 : Dyadic) * half ^ 17),
        ((-13555 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word31Step23 :
    word31Chunk23.foldl (fun acc a => a.applyPacked acc)
      word31State23 = word31State24 := by decide +kernel

private def word31Chunk24 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word31State25 : PackedMat2 :=
    ⟨⟨⟨((3875 : Dyadic) * half ^ 13),
        ((34397 : Dyadic) * half ^ 18)⟩,
       ⟨((9293 : Dyadic) * half ^ 17),
        ((-15779 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((96537 : Dyadic) * half ^ 17),
        ((-26067 : Dyadic) * half ^ 18)⟩,
       ⟨((-26573 : Dyadic) * half ^ 16),
        ((-9981 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-96537 : Dyadic) * half ^ 17),
        ((26067 : Dyadic) * half ^ 18)⟩,
       ⟨((-26573 : Dyadic) * half ^ 16),
        ((-9981 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((3875 : Dyadic) * half ^ 13),
        ((34397 : Dyadic) * half ^ 18)⟩,
       ⟨((-9293 : Dyadic) * half ^ 17),
        ((15779 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word31Step24 :
    word31Chunk24.foldl (fun acc a => a.applyPacked acc)
      word31State24 = word31State25 := by decide +kernel

private def word31Chunk25 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word31State26 : PackedMat2 :=
    ⟨⟨⟨((-31 : Dyadic) * half ^ 15),
        ((-131869 : Dyadic) * half ^ 19)⟩,
       ⟨((15593 : Dyadic) * half ^ 18),
        ((-183941 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((79547 : Dyadic) * half ^ 18),
        ((193503 : Dyadic) * half ^ 19)⟩,
       ⟨((-5659 : Dyadic) * half ^ 14),
        ((138685 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((83047 : Dyadic) * half ^ 17),
        ((-10997 : Dyadic) * half ^ 19)⟩,
       ⟨((27409 : Dyadic) * half ^ 18),
        ((170091 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((157905 : Dyadic) * half ^ 18),
        ((-15345 : Dyadic) * half ^ 19)⟩,
       ⟨((-6509 : Dyadic) * half ^ 16),
        ((15841 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word31Step25 :
    word31Chunk25.foldl (fun acc a => a.applyPacked acc)
      word31State25 = word31State26 := by decide +kernel

private def word31Chunk26 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word31State27 : PackedMat2 :=
    ⟨⟨⟨((-227009 : Dyadic) * half ^ 19),
        ((-5029 : Dyadic) * half ^ 19)⟩,
       ⟨((-274733 : Dyadic) * half ^ 19),
        ((19001 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((283799 : Dyadic) * half ^ 19),
        ((-27865 : Dyadic) * half ^ 18)⟩,
       ⟨((202639 : Dyadic) * half ^ 19),
        ((49089 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-283799 : Dyadic) * half ^ 19),
        ((27865 : Dyadic) * half ^ 18)⟩,
       ⟨((202639 : Dyadic) * half ^ 19),
        ((49089 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-227009 : Dyadic) * half ^ 19),
        ((-5029 : Dyadic) * half ^ 19)⟩,
       ⟨((274733 : Dyadic) * half ^ 19),
        ((-19001 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word31Step26 :
    word31Chunk26.foldl (fun acc a => a.applyPacked acc)
      word31State26 = word31State27 := by decide +kernel

private def word31Chunk27 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word31State28 : PackedMat2 :=
    ⟨⟨⟨((307123 : Dyadic) * half ^ 20),
        ((-2791 : Dyadic) * half ^ 20)⟩,
       ⟨((-342915 : Dyadic) * half ^ 20),
        ((-119591 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-328071 : Dyadic) * half ^ 20),
        ((109123 : Dyadic) * half ^ 18)⟩,
       ⟨((504185 : Dyadic) * half ^ 20),
        ((123047 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-504185 : Dyadic) * half ^ 20),
        ((-123047 : Dyadic) * half ^ 20)⟩,
       ⟨((328071 : Dyadic) * half ^ 20),
        ((-109123 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-342915 : Dyadic) * half ^ 20),
        ((-119591 : Dyadic) * half ^ 19)⟩,
       ⟨((307123 : Dyadic) * half ^ 20),
        ((-2791 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word31Step27 :
    word31Chunk27.foldl (fun acc a => a.applyPacked acc)
      word31State27 = word31State28 := by decide +kernel

private def word31Chunk28 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word31State29 : PackedMat2 :=
    ⟨⟨⟨((-262535 : Dyadic) * half ^ 21),
        ((-79889 : Dyadic) * half ^ 21)⟩,
       ⟨((-210843 : Dyadic) * half ^ 21),
        ((-233247 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-700133 : Dyadic) * half ^ 21),
        ((-241631 : Dyadic) * half ^ 20)⟩,
       ⟨((902665 : Dyadic) * half ^ 21),
        ((-615993 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-132731 : Dyadic) * half ^ 21),
        ((801399 : Dyadic) * half ^ 21)⟩,
       ⟨((-1099255 : Dyadic) * half ^ 21),
        ((50633 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((853099 : Dyadic) * half ^ 21),
        ((-12923 : Dyadic) * half ^ 20)⟩,
       ⟨((1012877 : Dyadic) * half ^ 21),
        ((236689 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word31Step28 :
    word31Chunk28.foldl (fun acc a => a.applyPacked acc)
      word31State28 = word31State29 := by decide +kernel

private def word31Chunk29 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word31State30 : PackedMat2 :=
    ⟨⟨⟨((-465919 : Dyadic) * half ^ 21),
        ((-184989 : Dyadic) * half ^ 22)⟩,
       ⟨((-113611 : Dyadic) * half ^ 21),
        ((-1088297 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-222197 : Dyadic) * half ^ 18),
        ((259843 : Dyadic) * half ^ 22)⟩,
       ⟨((-235769 : Dyadic) * half ^ 20),
        ((-534545 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((137351 : Dyadic) * half ^ 21),
        ((1124557 : Dyadic) * half ^ 21)⟩,
       ⟨((-198597 : Dyadic) * half ^ 20),
        ((653019 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-636643 : Dyadic) * half ^ 21),
        ((-289765 : Dyadic) * half ^ 21)⟩,
       ⟨((225827 : Dyadic) * half ^ 20),
        ((-88077 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word31Step29 :
    word31Chunk29.foldl (fun acc a => a.applyPacked acc)
      word31State29 = word31State30 := by decide +kernel

private def word31Chunk30 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word31State31 : PackedMat2 :=
    ⟨⟨⟨((351095 : Dyadic) * half ^ 19),
        ((661135 : Dyadic) * half ^ 23)⟩,
       ⟨((-1460489 : Dyadic) * half ^ 22),
        ((-210767 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((2180389 : Dyadic) * half ^ 22),
        ((-1216325 : Dyadic) * half ^ 23)⟩,
       ⟨((-664889 : Dyadic) * half ^ 21),
        ((-366429 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((2180389 : Dyadic) * half ^ 22),
        ((-1216325 : Dyadic) * half ^ 23)⟩,
       ⟨((664889 : Dyadic) * half ^ 21),
        ((366429 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-351095 : Dyadic) * half ^ 19),
        ((-661135 : Dyadic) * half ^ 23)⟩,
       ⟨((-1460489 : Dyadic) * half ^ 22),
        ((-210767 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word31Step30 :
    word31Chunk30.foldl (fun acc a => a.applyPacked acc)
      word31State30 = word31State31 := by decide +kernel

private def word31Chunk31 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word31State32 : PackedMat2 :=
    ⟨⟨⟨((-334317 : Dyadic) * half ^ 21),
        ((916131 : Dyadic) * half ^ 21)⟩,
       ⟨((2642905 : Dyadic) * half ^ 22),
        ((684781 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-855755 : Dyadic) * half ^ 22),
        ((102959 : Dyadic) * half ^ 21)⟩,
       ⟨((1471987 : Dyadic) * half ^ 22),
        ((674493 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((855755 : Dyadic) * half ^ 22),
        ((-102959 : Dyadic) * half ^ 21)⟩,
       ⟨((1471987 : Dyadic) * half ^ 22),
        ((674493 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-334317 : Dyadic) * half ^ 21),
        ((916131 : Dyadic) * half ^ 21)⟩,
       ⟨((-2642905 : Dyadic) * half ^ 22),
        ((-684781 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word31Step31 :
    word31Chunk31.foldl (fun acc a => a.applyPacked acc)
      word31State31 = word31State32 := by decide +kernel

private def word31Chunk32 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word31State33 : PackedMat2 :=
    ⟨⟨⟨((3129567 : Dyadic) * half ^ 24),
        ((-1405817 : Dyadic) * half ^ 24)⟩,
       ⟨((-230363 : Dyadic) * half ^ 24),
        ((51739 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-6469607 : Dyadic) * half ^ 24),
        ((-2180137 : Dyadic) * half ^ 23)⟩,
       ⟨((-3342267 : Dyadic) * half ^ 24),
        ((6667349 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-11027623 : Dyadic) * half ^ 24),
        ((-781835 : Dyadic) * half ^ 23)⟩,
       ⟨((-2307075 : Dyadic) * half ^ 24),
        ((4905937 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((8028409 : Dyadic) * half ^ 24),
        ((-1679965 : Dyadic) * half ^ 24)⟩,
       ⟨((5216775 : Dyadic) * half ^ 24),
        ((724801 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word31Step32 :
    word31Chunk32.foldl (fun acc a => a.applyPacked acc)
      word31State32 = word31State33 := by decide +kernel

private def word31Chunk33 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word31State34 : PackedMat2 :=
    ⟨⟨⟨((-5488809 : Dyadic) * half ^ 23),
        ((-79695 : Dyadic) * half ^ 19)⟩,
       ⟨((3134815 : Dyadic) * half ^ 24),
        ((-836435 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((1703165 : Dyadic) * half ^ 23),
        ((-2775355 : Dyadic) * half ^ 24)⟩,
       ⟨((2198255 : Dyadic) * half ^ 24),
        ((-7241979 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((2198255 : Dyadic) * half ^ 24),
        ((-7241979 : Dyadic) * half ^ 24)⟩,
       ⟨((1703165 : Dyadic) * half ^ 23),
        ((-2775355 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-3134815 : Dyadic) * half ^ 24),
        ((836435 : Dyadic) * half ^ 24)⟩,
       ⟨((5488809 : Dyadic) * half ^ 23),
        ((79695 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word31Step33 :
    word31Chunk33.foldl (fun acc a => a.applyPacked acc)
      word31State33 = word31State34 := by decide +kernel

private def word31Chunk34 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word31State35 : PackedMat2 :=
    ⟨⟨⟨((-979939 : Dyadic) * half ^ 25),
        ((42007 : Dyadic) * half ^ 20)⟩,
       ⟨((-847359 : Dyadic) * half ^ 25),
        ((-3934667 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-940629 : Dyadic) * half ^ 25),
        ((-12049289 : Dyadic) * half ^ 25)⟩,
       ⟨((1816259 : Dyadic) * half ^ 25),
        ((-12857723 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-404217 : Dyadic) * half ^ 24),
        ((344611 : Dyadic) * half ^ 23)⟩,
       ⟨((-6226753 : Dyadic) * half ^ 23),
        ((437815 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((4270723 : Dyadic) * half ^ 23),
        ((-33145 : Dyadic) * half ^ 24)⟩,
       ⟨((3598611 : Dyadic) * half ^ 23),
        ((913649 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word31Step34 :
    word31Chunk34.foldl (fun acc a => a.applyPacked acc)
      word31State34 = word31State35 := by decide +kernel

private def word31Chunk35 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word31State36 : PackedMat2 :=
    ⟨⟨⟨((1396901 : Dyadic) * half ^ 26),
        ((23670985 : Dyadic) * half ^ 26)⟩,
       ⟨((-11087629 : Dyadic) * half ^ 26),
        ((-24300391 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((25363669 : Dyadic) * half ^ 26),
        ((-2415843 : Dyadic) * half ^ 23)⟩,
       ⟨((-11205729 : Dyadic) * half ^ 26),
        ((-1046883 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((25363669 : Dyadic) * half ^ 26),
        ((-2415843 : Dyadic) * half ^ 23)⟩,
       ⟨((11205729 : Dyadic) * half ^ 26),
        ((1046883 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-1396901 : Dyadic) * half ^ 26),
        ((-23670985 : Dyadic) * half ^ 26)⟩,
       ⟨((-11087629 : Dyadic) * half ^ 26),
        ((-24300391 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word31Step35 :
    word31Chunk35.foldl (fun acc a => a.applyPacked acc)
      word31State35 = word31State36 := by decide +kernel

private def word31Chunk36 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word31State37 : PackedMat2 :=
    ⟨⟨⟨((83025773 : Dyadic) * half ^ 27),
        ((-12455073 : Dyadic) * half ^ 27)⟩,
       ⟨((23060853 : Dyadic) * half ^ 27),
        ((14969035 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-18131457 : Dyadic) * half ^ 27),
        ((15345293 : Dyadic) * half ^ 26)⟩,
       ⟨((-10595103 : Dyadic) * half ^ 27),
        ((-19798037 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-50488623 : Dyadic) * half ^ 27),
        ((3768177 : Dyadic) * half ^ 27)⟩,
       ⟨((10892549 : Dyadic) * half ^ 27),
        ((-897705 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-72331213 : Dyadic) * half ^ 27),
        ((7495615 : Dyadic) * half ^ 25)⟩,
       ⟨((-47421067 : Dyadic) * half ^ 27),
        ((-53043313 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word31Step36 :
    word31Chunk36.foldl (fun acc a => a.applyPacked acc)
      word31State36 = word31State37 := by decide +kernel

private def word31Chunk37 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word31State38 : PackedMat2 :=
    ⟨⟨⟨((-14919771 : Dyadic) * half ^ 27),
        ((-7540953 : Dyadic) * half ^ 28)⟩,
       ⟨((96091475 : Dyadic) * half ^ 27),
        ((-9192257 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((2421907 : Dyadic) * half ^ 22),
        ((-10788493 : Dyadic) * half ^ 28)⟩,
       ⟨((-2524637 : Dyadic) * half ^ 23),
        ((-39780657 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((2524637 : Dyadic) * half ^ 23),
        ((39780657 : Dyadic) * half ^ 28)⟩,
       ⟨((-2421907 : Dyadic) * half ^ 22),
        ((10788493 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((96091475 : Dyadic) * half ^ 27),
        ((-9192257 : Dyadic) * half ^ 28)⟩,
       ⟨((-14919771 : Dyadic) * half ^ 27),
        ((-7540953 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word31Step37 :
    word31Chunk37.foldl (fun acc a => a.applyPacked acc)
      word31State37 = word31State38 := by decide +kernel

private def word31Chunk38 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word31State39 : PackedMat2 :=
    ⟨⟨⟨((-9987965 : Dyadic) * half ^ 26),
        ((-54497379 : Dyadic) * half ^ 29)⟩,
       ⟨((-196878875 : Dyadic) * half ^ 28),
        ((93611501 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((73480725 : Dyadic) * half ^ 28),
        ((159272109 : Dyadic) * half ^ 29)⟩,
       ⟨((38845435 : Dyadic) * half ^ 27),
        ((58558043 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((27228769 : Dyadic) * half ^ 26),
        ((151171595 : Dyadic) * half ^ 29)⟩,
       ⟨((50357033 : Dyadic) * half ^ 28),
        ((-4210145 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-19557061 : Dyadic) * half ^ 28),
        ((236830735 : Dyadic) * half ^ 29)⟩,
       ⟨((9256805 : Dyadic) * half ^ 25),
        ((-156927015 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word31Step38 :
    word31Chunk38.foldl (fun acc a => a.applyPacked acc)
      word31State38 = word31State39 := by decide +kernel

private def word31Chunk39 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word31State40 : PackedMat2 :=
    ⟨⟨⟨((8446125 : Dyadic) * half ^ 26),
        ((-268055605 : Dyadic) * half ^ 29)⟩,
       ⟨((-13320833 : Dyadic) * half ^ 25),
        ((-28400687 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((15532749 : Dyadic) * half ^ 26),
        ((7527463 : Dyadic) * half ^ 29)⟩,
       ⟨((13380061 : Dyadic) * half ^ 28),
        ((23685457 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-15532749 : Dyadic) * half ^ 26),
        ((-7527463 : Dyadic) * half ^ 29)⟩,
       ⟨((13380061 : Dyadic) * half ^ 28),
        ((23685457 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((8446125 : Dyadic) * half ^ 26),
        ((-268055605 : Dyadic) * half ^ 29)⟩,
       ⟨((13320833 : Dyadic) * half ^ 25),
        ((28400687 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word31Step39 :
    word31Chunk39.foldl (fun acc a => a.applyPacked acc)
      word31State39 = word31State40 := by decide +kernel

private def word31Chunk40 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word31State41 : PackedMat2 :=
    ⟨⟨⟨((-519989001 : Dyadic) * half ^ 30),
        ((48859317 : Dyadic) * half ^ 30)⟩,
       ⟨((135922445 : Dyadic) * half ^ 30),
        ((-132484967 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-336562175 : Dyadic) * half ^ 30),
        ((-34500957 : Dyadic) * half ^ 28)⟩,
       ⟨((291975073 : Dyadic) * half ^ 30),
        ((174638749 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-291975073 : Dyadic) * half ^ 30),
        ((-174638749 : Dyadic) * half ^ 30)⟩,
       ⟨((336562175 : Dyadic) * half ^ 30),
        ((34500957 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((135922445 : Dyadic) * half ^ 30),
        ((-132484967 : Dyadic) * half ^ 28)⟩,
       ⟨((-519989001 : Dyadic) * half ^ 30),
        ((48859317 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word31Step40 :
    word31Chunk40.foldl (fun acc a => a.applyPacked acc)
      word31State40 = word31State41 := by decide +kernel

private def word31Chunk41 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word31State42 : PackedMat2 :=
    ⟨⟨⟨((-433715133 : Dyadic) * half ^ 31),
        ((83699139 : Dyadic) * half ^ 31)⟩,
       ⟨((132378359 : Dyadic) * half ^ 31),
        ((-255035223 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-1066362143 : Dyadic) * half ^ 31),
        ((-105214607 : Dyadic) * half ^ 29)⟩,
       ⟨((-726217897 : Dyadic) * half ^ 31),
        ((382035937 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((802894365 : Dyadic) * half ^ 31),
        ((170072123 : Dyadic) * half ^ 31)⟩,
       ⟨((-38822491 : Dyadic) * half ^ 31),
        ((-224072505 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((1103840031 : Dyadic) * half ^ 31),
        ((-141523373 : Dyadic) * half ^ 30)⟩,
       ⟨((936441753 : Dyadic) * half ^ 31),
        ((150668387 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word31Step41 :
    word31Chunk41.foldl (fun acc a => a.applyPacked acc)
      word31State41 = word31State42 := by decide +kernel

private def word31Chunk42 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word31State43 : PackedMat2 :=
    ⟨⟨⟨((550691031 : Dyadic) * half ^ 31),
        ((1007284187 : Dyadic) * half ^ 32)⟩,
       ⟨((-1600107407 : Dyadic) * half ^ 31),
        ((598113435 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-137303523 : Dyadic) * half ^ 30),
        ((-1364698941 : Dyadic) * half ^ 32)⟩,
       ⟨((-108667157 : Dyadic) * half ^ 30),
        ((-126935433 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((108667157 : Dyadic) * half ^ 30),
        ((126935433 : Dyadic) * half ^ 32)⟩,
       ⟨((137303523 : Dyadic) * half ^ 30),
        ((1364698941 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1600107407 : Dyadic) * half ^ 31),
        ((598113435 : Dyadic) * half ^ 32)⟩,
       ⟨((550691031 : Dyadic) * half ^ 31),
        ((1007284187 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word31Step42 :
    word31Chunk42.foldl (fun acc a => a.applyPacked acc)
      word31State42 = word31State43 := by decide +kernel

private def word31Chunk43 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word31State44 : PackedMat2 :=
    ⟨⟨⟨((735668033 : Dyadic) * half ^ 31),
        ((672336249 : Dyadic) * half ^ 33)⟩,
       ⟨((3228104295 : Dyadic) * half ^ 32),
        ((724453317 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-1727047801 : Dyadic) * half ^ 32),
        ((2032475077 : Dyadic) * half ^ 33)⟩,
       ⟨((-31549861 : Dyadic) * half ^ 29),
        ((-722420681 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((327513599 : Dyadic) * half ^ 31),
        ((-1979446689 : Dyadic) * half ^ 33)⟩,
       ⟨((1377447879 : Dyadic) * half ^ 32),
        ((-1474648913 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-698394783 : Dyadic) * half ^ 32),
        ((-4699440361 : Dyadic) * half ^ 33)⟩,
       ⟨((13029267 : Dyadic) * half ^ 31),
        ((1756768229 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word31Step43 :
    word31Chunk43.foldl (fun acc a => a.applyPacked acc)
      word31State43 = word31State44 := by decide +kernel

private def word31Chunk44 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word31State45 : PackedMat2 :=
    ⟨⟨⟨((-1404083467 : Dyadic) * half ^ 32),
        ((747899067 : Dyadic) * half ^ 33)⟩,
       ⟨((234370791 : Dyadic) * half ^ 32),
        ((2290254979 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-471615165 : Dyadic) * half ^ 32),
        ((-1728064119 : Dyadic) * half ^ 33)⟩,
       ⟨((-980201137 : Dyadic) * half ^ 31),
        ((213835263 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((471615165 : Dyadic) * half ^ 32),
        ((1728064119 : Dyadic) * half ^ 33)⟩,
       ⟨((-980201137 : Dyadic) * half ^ 31),
        ((213835263 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1404083467 : Dyadic) * half ^ 32),
        ((747899067 : Dyadic) * half ^ 33)⟩,
       ⟨((-234370791 : Dyadic) * half ^ 32),
        ((-2290254979 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word31Step44 :
    word31Chunk44.foldl (fun acc a => a.applyPacked acc)
      word31State44 = word31State45 := by decide +kernel

private def word31Chunk45 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word31State46 : PackedMat2 :=
    ⟨⟨⟨((-549955209 : Dyadic) * half ^ 34),
        ((-1309699791 : Dyadic) * half ^ 32)⟩,
       ⟨((-1869304039 : Dyadic) * half ^ 34),
        ((-4574653041 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-99866701 : Dyadic) * half ^ 34),
        ((3537079769 : Dyadic) * half ^ 34)⟩,
       ⟨((1208439043 : Dyadic) * half ^ 34),
        ((-4584131021 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((12705341811 : Dyadic) * half ^ 34),
        ((-81769109 : Dyadic) * half ^ 31)⟩,
       ⟨((5631182273 : Dyadic) * half ^ 34),
        ((-554286171 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((664146123 : Dyadic) * half ^ 34),
        ((-659674415 : Dyadic) * half ^ 34)⟩,
       ⟨((-9813452205 : Dyadic) * half ^ 34),
        ((-151203703 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word31Step45 :
    word31Chunk45.foldl (fun acc a => a.applyPacked acc)
      word31State45 = word31State46 := by decide +kernel

private def word31Chunk46 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word31State47 : PackedMat2 :=
    ⟨⟨⟨((-2454183333 : Dyadic) * half ^ 33),
        ((6596479937 : Dyadic) * half ^ 34)⟩,
       ⟨((-4799697295 : Dyadic) * half ^ 34),
        ((-2661295743 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((499552057 : Dyadic) * half ^ 32),
        ((1123435575 : Dyadic) * half ^ 33)⟩,
       ⟨((-9493172997 : Dyadic) * half ^ 34),
        ((-15415011 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-9493172997 : Dyadic) * half ^ 34),
        ((-15415011 : Dyadic) * half ^ 30)⟩,
       ⟨((499552057 : Dyadic) * half ^ 32),
        ((1123435575 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((4799697295 : Dyadic) * half ^ 34),
        ((2661295743 : Dyadic) * half ^ 33)⟩,
       ⟨((2454183333 : Dyadic) * half ^ 33),
        ((-6596479937 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word31Step46 :
    word31Chunk46.foldl (fun acc a => a.applyPacked acc)
      word31State46 = word31State47 := by decide +kernel

private def word31Chunk47 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word31State48 : PackedMat2 :=
    ⟨⟨⟨((20486168495 : Dyadic) * half ^ 35),
        ((12319830865 : Dyadic) * half ^ 36)⟩,
       ⟨((-4388445153 : Dyadic) * half ^ 33),
        ((11088530053 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((1033921937 : Dyadic) * half ^ 34),
        ((4598366179 : Dyadic) * half ^ 36)⟩,
       ⟨((2778816327 : Dyadic) * half ^ 35),
        ((-24200667655 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-1033921937 : Dyadic) * half ^ 34),
        ((-4598366179 : Dyadic) * half ^ 36)⟩,
       ⟨((2778816327 : Dyadic) * half ^ 35),
        ((-24200667655 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((20486168495 : Dyadic) * half ^ 35),
        ((12319830865 : Dyadic) * half ^ 36)⟩,
       ⟨((4388445153 : Dyadic) * half ^ 33),
        ((-11088530053 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word31Step47 :
    word31Chunk47.foldl (fun acc a => a.applyPacked acc)
      word31State47 = word31State48 := by decide +kernel

private def word31Chunk48 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word31State49 : PackedMat2 :=
    ⟨⟨⟨((-8358127197 : Dyadic) * half ^ 35),
        ((7671280321 : Dyadic) * half ^ 36)⟩,
       ⟨((9985744707 : Dyadic) * half ^ 34),
        ((281573403 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((5084253561 : Dyadic) * half ^ 35),
        ((28465639065 : Dyadic) * half ^ 36)⟩,
       ⟨((-11108151825 : Dyadic) * half ^ 35),
        ((3839163269 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((5084253561 : Dyadic) * half ^ 35),
        ((28465639065 : Dyadic) * half ^ 36)⟩,
       ⟨((11108151825 : Dyadic) * half ^ 35),
        ((-3839163269 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((8358127197 : Dyadic) * half ^ 35),
        ((-7671280321 : Dyadic) * half ^ 36)⟩,
       ⟨((9985744707 : Dyadic) * half ^ 34),
        ((281573403 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word31Step48 :
    word31Chunk48.foldl (fun acc a => a.applyPacked acc)
      word31State48 = word31State49 := by decide +kernel

private def word31Chunk49 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word31State50 : PackedMat2 :=
    ⟨⟨⟨((-66699082103 : Dyadic) * half ^ 37),
        ((15068060583 : Dyadic) * half ^ 36)⟩,
       ⟨((30229125683 : Dyadic) * half ^ 37),
        ((68971710445 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((36264124085 : Dyadic) * half ^ 37),
        ((2579913277 : Dyadic) * half ^ 37)⟩,
       ⟨((-8440528123 : Dyadic) * half ^ 37),
        ((9979303217 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-8440528123 : Dyadic) * half ^ 37),
        ((9979303217 : Dyadic) * half ^ 36)⟩,
       ⟨((36264124085 : Dyadic) * half ^ 37),
        ((2579913277 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-30229125683 : Dyadic) * half ^ 37),
        ((-68971710445 : Dyadic) * half ^ 37)⟩,
       ⟨((66699082103 : Dyadic) * half ^ 37),
        ((-15068060583 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word31Step49 :
    word31Chunk49.foldl (fun acc a => a.applyPacked acc)
      word31State49 = word31State50 := by decide +kernel

private def word31Chunk50 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word31State51 : PackedMat2 :=
    ⟨⟨⟨((9620911193 : Dyadic) * half ^ 36),
        ((-77814699491 : Dyadic) * half ^ 37)⟩,
       ⟨((17490107351 : Dyadic) * half ^ 37),
        ((14446333393 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((5478685045 : Dyadic) * half ^ 35),
        ((1332456689 : Dyadic) * half ^ 32)⟩,
       ⟨((4741127425 : Dyadic) * half ^ 37),
        ((1517219145 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-6847045901 : Dyadic) * half ^ 34),
        ((-26655867605 : Dyadic) * half ^ 38)⟩,
       ⟨((-3812607611 : Dyadic) * half ^ 34),
        ((-17173612755 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-48922032705 : Dyadic) * half ^ 37),
        ((36731929737 : Dyadic) * half ^ 38)⟩,
       ⟨((-106707366277 : Dyadic) * half ^ 37),
        ((1751715035 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word31Step50 :
    word31Chunk50.foldl (fun acc a => a.applyPacked acc)
      word31State50 = word31State51 := by decide +kernel

private def word31Chunk51 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word31State52 : PackedMat2 :=
    ⟨⟨⟨((-118343139125 : Dyadic) * half ^ 38),
        ((7354178805 : Dyadic) * half ^ 39)⟩,
       ⟨((53764008423 : Dyadic) * half ^ 37),
        ((-103475571525 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((1011391667 : Dyadic) * half ^ 31),
        ((-17177955697 : Dyadic) * half ^ 39)⟩,
       ⟨((152897612777 : Dyadic) * half ^ 38),
        ((93007767911 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((1011391667 : Dyadic) * half ^ 31),
        ((-17177955697 : Dyadic) * half ^ 39)⟩,
       ⟨((-152897612777 : Dyadic) * half ^ 38),
        ((-93007767911 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((118343139125 : Dyadic) * half ^ 38),
        ((-7354178805 : Dyadic) * half ^ 39)⟩,
       ⟨((53764008423 : Dyadic) * half ^ 37),
        ((-103475571525 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word31Step51 :
    word31Chunk51.foldl (fun acc a => a.applyPacked acc)
      word31State51 = word31State52 := by decide +kernel

private def word31Chunk52 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word31State53 : PackedMat2 :=
    ⟨⟨⟨((63936413181 : Dyadic) * half ^ 39),
        ((201132304519 : Dyadic) * half ^ 40)⟩,
       ⟨((-15770243931 : Dyadic) * half ^ 36),
        ((-388010012575 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((15749573379 : Dyadic) * half ^ 35),
        ((-41239320431 : Dyadic) * half ^ 40)⟩,
       ⟨((-109429460215 : Dyadic) * half ^ 39),
        ((469889471637 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-214325075603 : Dyadic) * half ^ 39),
        ((-142563713849 : Dyadic) * half ^ 40)⟩,
       ⟨((127782198017 : Dyadic) * half ^ 38),
        ((-361422634279 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-23359713507 : Dyadic) * half ^ 37),
        ((-62225538267 : Dyadic) * half ^ 40)⟩,
       ⟨((294571158547 : Dyadic) * half ^ 39),
        ((190098364629 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word31Step52 :
    word31Chunk52.foldl (fun acc a => a.applyPacked acc)
      word31State52 = word31State53 := by decide +kernel

private def word31Chunk53 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word31State54 : PackedMat2 :=
    ⟨⟨⟨((218361858091 : Dyadic) * half ^ 39),
        ((11498341825 : Dyadic) * half ^ 39)⟩,
       ⟨((-288033386729 : Dyadic) * half ^ 39),
        ((-4976138973 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-3623238229 : Dyadic) * half ^ 36),
        ((-88478284021 : Dyadic) * half ^ 39)⟩,
       ⟨((392909529441 : Dyadic) * half ^ 39),
        ((-29482968171 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-3623238229 : Dyadic) * half ^ 36),
        ((-88478284021 : Dyadic) * half ^ 39)⟩,
       ⟨((-392909529441 : Dyadic) * half ^ 39),
        ((29482968171 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-218361858091 : Dyadic) * half ^ 39),
        ((-11498341825 : Dyadic) * half ^ 39)⟩,
       ⟨((-288033386729 : Dyadic) * half ^ 39),
        ((-4976138973 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word31Step53 :
    word31Chunk53.foldl (fun acc a => a.applyPacked acc)
      word31State53 = word31State54 := by decide +kernel

private def word31Chunk54 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word31State55 : PackedMat2 :=
    ⟨⟨⟨((415620604545 : Dyadic) * half ^ 41),
        ((201405869691 : Dyadic) * half ^ 39)⟩,
       ⟨((279297838365 : Dyadic) * half ^ 41),
        ((-974965525081 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-1157752739643 : Dyadic) * half ^ 41),
        ((41182685145 : Dyadic) * half ^ 41)⟩,
       ⟨((-144910570629 : Dyadic) * half ^ 41),
        ((25616811505 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((61284560875 : Dyadic) * half ^ 41),
        ((506421084507 : Dyadic) * half ^ 41)⟩,
       ⟨((143649931165 : Dyadic) * half ^ 41),
        ((-20354114223 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((1780589003845 : Dyadic) * half ^ 41),
        ((34080691545 : Dyadic) * half ^ 40)⟩,
       ⟨((169342046317 : Dyadic) * half ^ 41),
        ((-347459221455 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word31Step54 :
    word31Chunk54.foldl (fun acc a => a.applyPacked acc)
      word31State54 = word31State55 := by decide +kernel

private def word31Chunk55 : List Letter := [.t, .h, .s, .t, .h, .t, .h]
private def word31State56 : PackedMat2 :=
    ⟨⟨⟨((1244850929403 : Dyadic) * half ^ 41),
        ((1349403444481 : Dyadic) * half ^ 42)⟩,
       ⟨((-839610508123 : Dyadic) * half ^ 41),
        ((1187388563149 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((80362068183 : Dyadic) * half ^ 39),
        ((-454596506899 : Dyadic) * half ^ 42)⟩,
       ⟨((-77007255373 : Dyadic) * half ^ 38),
        ((871237639597 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-80362068183 : Dyadic) * half ^ 39),
        ((454596506899 : Dyadic) * half ^ 42)⟩,
       ⟨((-77007255373 : Dyadic) * half ^ 38),
        ((871237639597 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1244850929403 : Dyadic) * half ^ 41),
        ((1349403444481 : Dyadic) * half ^ 42)⟩,
       ⟨((839610508123 : Dyadic) * half ^ 41),
        ((-1187388563149 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word31Step55 :
    word31Chunk55.foldl (fun acc a => a.applyPacked acc)
      word31State55 = word31State56 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word31_check : check word31 31 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word31 = word31State56.toMatrix := by
    unfold evalRingPacked
    change ((
      word31Chunk0 ++ word31Chunk1 ++ word31Chunk2 ++ word31Chunk3 ++
      word31Chunk4 ++ word31Chunk5 ++ word31Chunk6 ++ word31Chunk7 ++
      word31Chunk8 ++ word31Chunk9 ++ word31Chunk10 ++ word31Chunk11 ++
      word31Chunk12 ++ word31Chunk13 ++ word31Chunk14 ++ word31Chunk15 ++
      word31Chunk16 ++ word31Chunk17 ++ word31Chunk18 ++ word31Chunk19 ++
      word31Chunk20 ++ word31Chunk21 ++ word31Chunk22 ++ word31Chunk23 ++
      word31Chunk24 ++ word31Chunk25 ++ word31Chunk26 ++ word31Chunk27 ++
      word31Chunk28 ++ word31Chunk29 ++ word31Chunk30 ++ word31Chunk31 ++
      word31Chunk32 ++ word31Chunk33 ++ word31Chunk34 ++ word31Chunk35 ++
      word31Chunk36 ++ word31Chunk37 ++ word31Chunk38 ++ word31Chunk39 ++
      word31Chunk40 ++ word31Chunk41 ++ word31Chunk42 ++ word31Chunk43 ++
      word31Chunk44 ++ word31Chunk45 ++ word31Chunk46 ++ word31Chunk47 ++
      word31Chunk48 ++ word31Chunk49 ++ word31Chunk50 ++ word31Chunk51 ++
      word31Chunk52 ++ word31Chunk53 ++ word31Chunk54 ++ word31Chunk55
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word31Step0, word31Step1, word31Step2, word31Step3, word31Step4,
      word31Step5, word31Step6, word31Step7, word31Step8, word31Step9,
      word31Step10, word31Step11, word31Step12, word31Step13, word31Step14,
      word31Step15, word31Step16, word31Step17, word31Step18, word31Step19,
      word31Step20, word31Step21, word31Step22, word31Step23, word31Step24,
      word31Step25, word31Step26, word31Step27, word31Step28, word31Step29,
      word31Step30, word31Step31, word31Step32, word31Step33, word31Step34,
      word31Step35, word31Step36, word31Step37, word31Step38, word31Step39,
      word31Step40, word31Step41, word31Step42, word31Step43, word31Step44,
      word31Step45, word31Step46, word31Step47, word31Step48, word31Step49,
      word31Step50, word31Step51, word31Step52, word31Step53, word31Step54,
      word31Step55]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
