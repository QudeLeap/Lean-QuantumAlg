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
private def word11Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word11State1 : PackedMat2 :=
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
private lemma word11Step0 :
    word11Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word11State1 := by decide +kernel

private def word11Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word11State2 : PackedMat2 :=
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
private lemma word11Step1 :
    word11Chunk1.foldl (fun acc a => a.applyPacked acc)
      word11State1 = word11State2 := by decide +kernel

private def word11Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word11State3 : PackedMat2 :=
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
private lemma word11Step2 :
    word11Chunk2.foldl (fun acc a => a.applyPacked acc)
      word11State2 = word11State3 := by decide +kernel

private def word11Chunk3 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word11State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word11Step3 :
    word11Chunk3.foldl (fun acc a => a.applyPacked acc)
      word11State3 = word11State4 := by decide +kernel

private def word11Chunk4 : List Letter := [.h, .s, .h, .s, .h, .s, .s, .h]
private def word11State5 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(-1 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(-1 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word11Step4 :
    word11Chunk4.foldl (fun acc a => a.applyPacked acc)
      word11State4 = word11State5 := by decide +kernel

private def word11Chunk5 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word11State6 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩⟩
private lemma word11Step5 :
    word11Chunk5.foldl (fun acc a => a.applyPacked acc)
      word11State5 = word11State6 := by decide +kernel

private def word11Chunk6 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word11State7 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word11Step6 :
    word11Chunk6.foldl (fun acc a => a.applyPacked acc)
      word11State6 = word11State7 := by decide +kernel

private def word11Chunk7 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word11State8 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word11Step7 :
    word11Chunk7.foldl (fun acc a => a.applyPacked acc)
      word11State7 = word11State8 := by decide +kernel

private def word11Chunk8 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word11State9 : PackedMat2 :=
    ⟨⟨⟨((13 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((-11 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((9 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((-17 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word11Step8 :
    word11Chunk8.foldl (fun acc a => a.applyPacked acc)
      word11State8 = word11State9 := by decide +kernel

private def word11Chunk9 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word11State10 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 3),
        ((9 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((21 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((15 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word11Step9 :
    word11Chunk9.foldl (fun acc a => a.applyPacked acc)
      word11State9 = word11State10 := by decide +kernel

private def word11Chunk10 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word11State11 : PackedMat2 :=
    ⟨⟨⟨((21 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-5 : Dyadic) * half ^ 6),
        ((31 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((33 : Dyadic) * half ^ 6),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((7 : Dyadic) * half ^ 6),
        ((-13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((33 : Dyadic) * half ^ 6),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 6),
        ((13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-21 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-5 : Dyadic) * half ^ 6),
        ((31 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word11Step10 :
    word11Chunk10.foldl (fun acc a => a.applyPacked acc)
      word11State10 = word11State11 := by decide +kernel

private def word11Chunk11 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word11State12 : PackedMat2 :=
    ⟨⟨⟨((17 : Dyadic) * half ^ 7),
        ((7 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 7),
        ((69 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-27 : Dyadic) * half ^ 7),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((-17 : Dyadic) * half ^ 7),
        ((43 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-31 : Dyadic) * half ^ 7),
        ((11 : Dyadic) * half ^ 6)⟩,
       ⟨((55 : Dyadic) * half ^ 7),
        ((5 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((97 : Dyadic) * half ^ 7),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-41 : Dyadic) * half ^ 7),
        ((9 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word11Step11 :
    word11Chunk11.foldl (fun acc a => a.applyPacked acc)
      word11State11 = word11State12 := by decide +kernel

private def word11Chunk12 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word11State13 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 8)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((15 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 7),
        ((-139 : Dyadic) * half ^ 8)⟩,
       ⟨((21 : Dyadic) * half ^ 7),
        ((-57 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 7),
        ((-139 : Dyadic) * half ^ 8)⟩,
       ⟨((-21 : Dyadic) * half ^ 7),
        ((57 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 5),
        ((9 : Dyadic) * half ^ 8)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((15 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word11Step12 :
    word11Chunk12.foldl (fun acc a => a.applyPacked acc)
      word11State12 = word11State13 := by decide +kernel

private def word11Chunk13 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word11State14 : PackedMat2 :=
    ⟨⟨⟨((25 : Dyadic) * half ^ 8),
        ((7 : Dyadic) * half ^ 9)⟩,
       ⟨((19 : Dyadic) * half ^ 6),
        ((143 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-157 : Dyadic) * half ^ 8),
        ((135 : Dyadic) * half ^ 9)⟩,
       ⟨((-9 : Dyadic) * half ^ 5),
        ((-141 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-69 : Dyadic) * half ^ 7),
        ((85 : Dyadic) * half ^ 9)⟩,
       ⟨((-3 : Dyadic) * half ^ 8),
        ((-229 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-17 : Dyadic) * half ^ 6),
        ((-51 : Dyadic) * half ^ 9)⟩,
       ⟨((-75 : Dyadic) * half ^ 8),
        ((-101 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word11Step13 :
    word11Chunk13.foldl (fun acc a => a.applyPacked acc)
      word11State13 = word11State14 := by decide +kernel

private def word11Chunk14 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word11State15 : PackedMat2 :=
    ⟨⟨⟨((-113 : Dyadic) * half ^ 8),
        ((21 : Dyadic) * half ^ 9)⟩,
       ⟨((15 : Dyadic) * half ^ 5),
        ((75 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((91 : Dyadic) * half ^ 8),
        ((-45 : Dyadic) * half ^ 8)⟩,
       ⟨((-111 : Dyadic) * half ^ 8),
        ((67 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((23 : Dyadic) * half ^ 9),
        ((5 : Dyadic) * half ^ 7)⟩,
       ⟨((157 : Dyadic) * half ^ 9),
        ((-101 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((171 : Dyadic) * half ^ 9),
        ((7 : Dyadic) * half ^ 9)⟩,
       ⟨((-129 : Dyadic) * half ^ 9),
        ((-233 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word11Step14 :
    word11Chunk14.foldl (fun acc a => a.applyPacked acc)
      word11State14 = word11State15 := by decide +kernel

private def word11Chunk15 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word11State16 : PackedMat2 :=
    ⟨⟨⟨((-81 : Dyadic) * half ^ 9),
        ((-347 : Dyadic) * half ^ 10)⟩,
       ⟨((145 : Dyadic) * half ^ 9),
        ((-37 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-27 : Dyadic) * half ^ 7),
        ((137 : Dyadic) * half ^ 9)⟩,
       ⟨((-349 : Dyadic) * half ^ 9),
        ((-35 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((239 : Dyadic) * half ^ 10),
        ((-457 : Dyadic) * half ^ 10)⟩,
       ⟨((309 : Dyadic) * half ^ 10),
        ((241 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((421 : Dyadic) * half ^ 10),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((273 : Dyadic) * half ^ 10),
        ((113 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word11Step15 :
    word11Chunk15.foldl (fun acc a => a.applyPacked acc)
      word11State15 = word11State16 := by decide +kernel

private def word11Chunk16 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word11State17 : PackedMat2 :=
    ⟨⟨⟨((-617 : Dyadic) * half ^ 11),
        ((469 : Dyadic) * half ^ 11)⟩,
       ⟨((-175 : Dyadic) * half ^ 11),
        ((-87 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((1385 : Dyadic) * half ^ 11),
        ((349 : Dyadic) * half ^ 11)⟩,
       ⟨((1011 : Dyadic) * half ^ 11),
        ((-111 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-127 : Dyadic) * half ^ 11),
        ((-599 : Dyadic) * half ^ 10)⟩,
       ⟨((-571 : Dyadic) * half ^ 11),
        ((-187 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((295 : Dyadic) * half ^ 11),
        ((-99 : Dyadic) * half ^ 9)⟩,
       ⟨((643 : Dyadic) * half ^ 11),
        ((-221 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word11Step16 :
    word11Chunk16.foldl (fun acc a => a.applyPacked acc)
      word11State16 = word11State17 := by decide +kernel

private def word11Chunk17 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word11State18 : PackedMat2 :=
    ⟨⟨⟨((53 : Dyadic) * half ^ 9),
        ((217 : Dyadic) * half ^ 11)⟩,
       ⟨((-781 : Dyadic) * half ^ 11),
        ((-341 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-71 : Dyadic) * half ^ 11),
        ((995 : Dyadic) * half ^ 11)⟩,
       ⟨((265 : Dyadic) * half ^ 9),
        ((-57 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((1223 : Dyadic) * half ^ 11),
        ((-1131 : Dyadic) * half ^ 12)⟩,
       ⟨((-767 : Dyadic) * half ^ 11),
        ((-989 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-279 : Dyadic) * half ^ 10),
        ((-993 : Dyadic) * half ^ 12)⟩,
       ⟨((-31 : Dyadic) * half ^ 9),
        ((-569 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word11Step17 :
    word11Chunk17.foldl (fun acc a => a.applyPacked acc)
      word11State17 = word11State18 := by decide +kernel

private def word11Chunk18 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word11State19 : PackedMat2 :=
    ⟨⟨⟨((277 : Dyadic) * half ^ 12),
        ((1813 : Dyadic) * half ^ 13)⟩,
       ⟨((-1893 : Dyadic) * half ^ 12),
        ((-1611 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((277 : Dyadic) * half ^ 10),
        ((-2763 : Dyadic) * half ^ 13)⟩,
       ⟨((565 : Dyadic) * half ^ 10),
        ((-217 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-277 : Dyadic) * half ^ 10),
        ((2763 : Dyadic) * half ^ 13)⟩,
       ⟨((565 : Dyadic) * half ^ 10),
        ((-217 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((277 : Dyadic) * half ^ 12),
        ((1813 : Dyadic) * half ^ 13)⟩,
       ⟨((1893 : Dyadic) * half ^ 12),
        ((1611 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word11Step18 :
    word11Chunk18.foldl (fun acc a => a.applyPacked acc)
      word11State18 = word11State19 := by decide +kernel

private def word11Chunk19 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word11State20 : PackedMat2 :=
    ⟨⟨⟨((555 : Dyadic) * half ^ 11),
        ((4731 : Dyadic) * half ^ 14)⟩,
       ⟨((4531 : Dyadic) * half ^ 13),
        ((1591 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1091 : Dyadic) * half ^ 11),
        ((3641 : Dyadic) * half ^ 14)⟩,
       ⟨((-749 : Dyadic) * half ^ 13),
        ((2433 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((151 : Dyadic) * half ^ 11),
        ((-3615 : Dyadic) * half ^ 14)⟩,
       ⟨((-3037 : Dyadic) * half ^ 13),
        ((5113 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-785 : Dyadic) * half ^ 12),
        ((2311 : Dyadic) * half ^ 14)⟩,
       ⟨((3161 : Dyadic) * half ^ 13),
        ((6751 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word11Step19 :
    word11Chunk19.foldl (fun acc a => a.applyPacked acc)
      word11State19 = word11State20 := by decide +kernel

private def word11Chunk20 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word11State21 : PackedMat2 :=
    ⟨⟨⟨((1141 : Dyadic) * half ^ 12),
        ((-99 : Dyadic) * half ^ 12)⟩,
       ⟨((1531 : Dyadic) * half ^ 13),
        ((8113 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((3305 : Dyadic) * half ^ 13),
        ((-3215 : Dyadic) * half ^ 14)⟩,
       ⟨((-3231 : Dyadic) * half ^ 13),
        ((69 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-3231 : Dyadic) * half ^ 13),
        ((69 : Dyadic) * half ^ 12)⟩,
       ⟨((3305 : Dyadic) * half ^ 13),
        ((-3215 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1531 : Dyadic) * half ^ 13),
        ((-8113 : Dyadic) * half ^ 14)⟩,
       ⟨((-1141 : Dyadic) * half ^ 12),
        ((99 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word11Step20 :
    word11Chunk20.foldl (fun acc a => a.applyPacked acc)
      word11State20 = word11State21 := by decide +kernel

private def word11Chunk21 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word11State22 : PackedMat2 :=
    ⟨⟨⟨((2609 : Dyadic) * half ^ 15),
        ((-1481 : Dyadic) * half ^ 15)⟩,
       ⟨((9673 : Dyadic) * half ^ 15),
        ((3621 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((14697 : Dyadic) * half ^ 15),
        ((-3813 : Dyadic) * half ^ 15)⟩,
       ⟨((577 : Dyadic) * half ^ 15),
        ((-4397 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-14697 : Dyadic) * half ^ 15),
        ((3813 : Dyadic) * half ^ 15)⟩,
       ⟨((577 : Dyadic) * half ^ 15),
        ((-4397 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((2609 : Dyadic) * half ^ 15),
        ((-1481 : Dyadic) * half ^ 15)⟩,
       ⟨((-9673 : Dyadic) * half ^ 15),
        ((-3621 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word11Step21 :
    word11Chunk21.foldl (fun acc a => a.applyPacked acc)
      word11State21 = word11State22 := by decide +kernel

private def word11Chunk22 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word11State23 : PackedMat2 :=
    ⟨⟨⟨((-5847 : Dyadic) * half ^ 16),
        ((12269 : Dyadic) * half ^ 16)⟩,
       ⟨((-619 : Dyadic) * half ^ 16),
        ((-13079 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((41217 : Dyadic) * half ^ 16),
        ((-4753 : Dyadic) * half ^ 16)⟩,
       ⟨((-25559 : Dyadic) * half ^ 16),
        ((-4919 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-14591 : Dyadic) * half ^ 16),
        ((7829 : Dyadic) * half ^ 16)⟩,
       ⟨((5085 : Dyadic) * half ^ 16),
        ((8347 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((13889 : Dyadic) * half ^ 16),
        ((3233 : Dyadic) * half ^ 16)⟩,
       ⟨((-38427 : Dyadic) * half ^ 16),
        ((1307 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word11Step22 :
    word11Chunk22.foldl (fun acc a => a.applyPacked acc)
      word11State22 = word11State23 := by decide +kernel

private def word11Chunk23 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word11State24 : PackedMat2 :=
    ⟨⟨⟨((33187 : Dyadic) * half ^ 16),
        ((7779 : Dyadic) * half ^ 16)⟩,
       ⟨((-8151 : Dyadic) * half ^ 15),
        ((1343 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((5475 : Dyadic) * half ^ 15),
        ((19393 : Dyadic) * half ^ 16)⟩,
       ⟨((10461 : Dyadic) * half ^ 16),
        ((-28235 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-5475 : Dyadic) * half ^ 15),
        ((-19393 : Dyadic) * half ^ 16)⟩,
       ⟨((10461 : Dyadic) * half ^ 16),
        ((-28235 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((33187 : Dyadic) * half ^ 16),
        ((7779 : Dyadic) * half ^ 16)⟩,
       ⟨((8151 : Dyadic) * half ^ 15),
        ((-1343 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word11Step23 :
    word11Chunk23.foldl (fun acc a => a.applyPacked acc)
      word11State23 = word11State24 := by decide +kernel

private def word11Chunk24 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word11State25 : PackedMat2 :=
    ⟨⟨⟨((57551 : Dyadic) * half ^ 17),
        ((67425 : Dyadic) * half ^ 18)⟩,
       ⟨((2225 : Dyadic) * half ^ 15),
        ((-51229 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-24655 : Dyadic) * half ^ 17),
        ((138155 : Dyadic) * half ^ 18)⟩,
       ⟨((3485 : Dyadic) * half ^ 16),
        ((-2615 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-3485 : Dyadic) * half ^ 16),
        ((2615 : Dyadic) * half ^ 18)⟩,
       ⟨((24655 : Dyadic) * half ^ 17),
        ((-138155 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((2225 : Dyadic) * half ^ 15),
        ((-51229 : Dyadic) * half ^ 18)⟩,
       ⟨((57551 : Dyadic) * half ^ 17),
        ((67425 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word11Step24 :
    word11Chunk24.foldl (fun acc a => a.applyPacked acc)
      word11State24 = word11State25 := by decide +kernel

private def word11Chunk25 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word11State26 : PackedMat2 :=
    ⟨⟨⟨((-37447 : Dyadic) * half ^ 17),
        ((12535 : Dyadic) * half ^ 17)⟩,
       ⟨((-3409 : Dyadic) * half ^ 16),
        ((108365 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((12021 : Dyadic) * half ^ 15),
        ((-50357 : Dyadic) * half ^ 18)⟩,
       ⟨((5967 : Dyadic) * half ^ 14),
        ((21467 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((35511 : Dyadic) * half ^ 18),
        ((23955 : Dyadic) * half ^ 16)⟩,
       ⟨((-136225 : Dyadic) * half ^ 18),
        ((87 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-133435 : Dyadic) * half ^ 18),
        ((44265 : Dyadic) * half ^ 18)⟩,
       ⟨((83295 : Dyadic) * half ^ 18),
        ((30629 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word11Step25 :
    word11Chunk25.foldl (fun acc a => a.applyPacked acc)
      word11State25 = word11State26 := by decide +kernel

private def word11Chunk26 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word11State27 : PackedMat2 :=
    ⟨⟨⟨((-31599 : Dyadic) * half ^ 19),
        ((71301 : Dyadic) * half ^ 17)⟩,
       ⟨((-35063 : Dyadic) * half ^ 19),
        ((17597 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-262477 : Dyadic) * half ^ 19),
        ((-20545 : Dyadic) * half ^ 19)⟩,
       ⟨((51785 : Dyadic) * half ^ 19),
        ((117555 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-51785 : Dyadic) * half ^ 19),
        ((-117555 : Dyadic) * half ^ 19)⟩,
       ⟨((262477 : Dyadic) * half ^ 19),
        ((20545 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-35063 : Dyadic) * half ^ 19),
        ((17597 : Dyadic) * half ^ 17)⟩,
       ⟨((-31599 : Dyadic) * half ^ 19),
        ((71301 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word11Step26 :
    word11Chunk26.foldl (fun acc a => a.applyPacked acc)
      word11State26 = word11State27 := by decide +kernel

private def word11Chunk27 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word11State28 : PackedMat2 :=
    ⟨⟨⟨((467371 : Dyadic) * half ^ 20),
        ((-129559 : Dyadic) * half ^ 19)⟩,
       ⟨((12167 : Dyadic) * half ^ 20),
        ((355487 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-307691 : Dyadic) * half ^ 20),
        ((-95441 : Dyadic) * half ^ 18)⟩,
       ⟨((328225 : Dyadic) * half ^ 20),
        ((-2091 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-383855 : Dyadic) * half ^ 20),
        ((10267 : Dyadic) * half ^ 20)⟩,
       ⟨((-379673 : Dyadic) * half ^ 20),
        ((-158979 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-96369 : Dyadic) * half ^ 20),
        ((-239769 : Dyadic) * half ^ 20)⟩,
       ⟨((614605 : Dyadic) * half ^ 20),
        ((-113801 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word11Step27 :
    word11Chunk27.foldl (fun acc a => a.applyPacked acc)
      word11State27 = word11State28 := by decide +kernel

private def word11Chunk28 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word11State29 : PackedMat2 :=
    ⟨⟨⟨((-738999 : Dyadic) * half ^ 20),
        ((35375 : Dyadic) * half ^ 19)⟩,
       ⟨((42975 : Dyadic) * half ^ 19),
        ((-346397 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-7759 : Dyadic) * half ^ 15),
        ((-10867 : Dyadic) * half ^ 17)⟩,
       ⟨((-202583 : Dyadic) * half ^ 20),
        ((-37313 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((7759 : Dyadic) * half ^ 15),
        ((10867 : Dyadic) * half ^ 17)⟩,
       ⟨((-202583 : Dyadic) * half ^ 20),
        ((-37313 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-738999 : Dyadic) * half ^ 20),
        ((35375 : Dyadic) * half ^ 19)⟩,
       ⟨((-42975 : Dyadic) * half ^ 19),
        ((346397 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word11Step28 :
    word11Chunk28.foldl (fun acc a => a.applyPacked acc)
      word11State28 = word11State29 := by decide +kernel

private def word11Chunk29 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word11State30 : PackedMat2 :=
    ⟨⟨⟨((220495 : Dyadic) * half ^ 20),
        ((-334333 : Dyadic) * half ^ 22)⟩,
       ⟨((-1643361 : Dyadic) * half ^ 21),
        ((359105 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-30867 : Dyadic) * half ^ 18),
        ((-552617 : Dyadic) * half ^ 22)⟩,
       ⟨((-428149 : Dyadic) * half ^ 21),
        ((-1403987 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((425685 : Dyadic) * half ^ 21),
        ((181213 : Dyadic) * half ^ 22)⟩,
       ⟨((489151 : Dyadic) * half ^ 20),
        ((675085 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((346719 : Dyadic) * half ^ 21),
        ((-2084351 : Dyadic) * half ^ 22)⟩,
       ⟨((6193 : Dyadic) * half ^ 20),
        ((-1202371 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word11Step29 :
    word11Chunk29.foldl (fun acc a => a.applyPacked acc)
      word11State29 = word11State30 := by decide +kernel

private def word11Chunk30 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word11State31 : PackedMat2 :=
    ⟨⟨⟨((265523 : Dyadic) * half ^ 20),
        ((-14871 : Dyadic) * half ^ 22)⟩,
       ⟨((307061 : Dyadic) * half ^ 20),
        ((-554267 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-282729 : Dyadic) * half ^ 21),
        ((38889 : Dyadic) * half ^ 18)⟩,
       ⟨((-823571 : Dyadic) * half ^ 20),
        ((-524905 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-823571 : Dyadic) * half ^ 20),
        ((-524905 : Dyadic) * half ^ 22)⟩,
       ⟨((-282729 : Dyadic) * half ^ 21),
        ((38889 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-307061 : Dyadic) * half ^ 20),
        ((554267 : Dyadic) * half ^ 21)⟩,
       ⟨((-265523 : Dyadic) * half ^ 20),
        ((14871 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word11Step30 :
    word11Chunk30.foldl (fun acc a => a.applyPacked acc)
      word11State30 = word11State31 := by decide +kernel

private def word11Chunk31 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word11State32 : PackedMat2 :=
    ⟨⟨⟨((-4490957 : Dyadic) * half ^ 23),
        ((16107 : Dyadic) * half ^ 18)⟩,
       ⟨((-1855015 : Dyadic) * half ^ 23),
        ((2861055 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((3778627 : Dyadic) * half ^ 23),
        ((593907 : Dyadic) * half ^ 21)⟩,
       ⟨((1764053 : Dyadic) * half ^ 23),
        ((-767871 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1607757 : Dyadic) * half ^ 23),
        ((-692835 : Dyadic) * half ^ 21)⟩,
       ⟨((-3143499 : Dyadic) * half ^ 23),
        ((-1007287 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((3376479 : Dyadic) * half ^ 23),
        ((-1586493 : Dyadic) * half ^ 22)⟩,
       ⟨((-2345631 : Dyadic) * half ^ 23),
        ((-1317971 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word11Step31 :
    word11Chunk31.foldl (fun acc a => a.applyPacked acc)
      word11State31 = word11State32 := by decide +kernel

private def word11Chunk32 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word11State33 : PackedMat2 :=
    ⟨⟨⟨((560905 : Dyadic) * half ^ 23),
        ((-6584141 : Dyadic) * half ^ 24)⟩,
       ⟨((-1273737 : Dyadic) * half ^ 23),
        ((-3715219 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((283047 : Dyadic) * half ^ 22),
        ((7407553 : Dyadic) * half ^ 24)⟩,
       ⟨((-281009 : Dyadic) * half ^ 21),
        ((4655105 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((43007 : Dyadic) * half ^ 18),
        ((845065 : Dyadic) * half ^ 23)⟩,
       ⟨((-6031329 : Dyadic) * half ^ 23),
        ((278971 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1434461 : Dyadic) * half ^ 23),
        ((-917321 : Dyadic) * half ^ 23)⟩,
       ⟨((-321855 : Dyadic) * half ^ 19),
        ((-5569 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word11Step32 :
    word11Chunk32.foldl (fun acc a => a.applyPacked acc)
      word11State32 = word11State33 := by decide +kernel

private def word11Chunk33 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word11State34 : PackedMat2 :=
    ⟨⟨⟨((402407 : Dyadic) * half ^ 24),
        ((7478897 : Dyadic) * half ^ 25)⟩,
       ⟨((-970283 : Dyadic) * half ^ 22),
        ((-10989307 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((660429 : Dyadic) * half ^ 24),
        ((-14087747 : Dyadic) * half ^ 25)⟩,
       ⟨((2070591 : Dyadic) * half ^ 22),
        ((-4389635 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((2070591 : Dyadic) * half ^ 22),
        ((-4389635 : Dyadic) * half ^ 25)⟩,
       ⟨((660429 : Dyadic) * half ^ 24),
        ((-14087747 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((970283 : Dyadic) * half ^ 22),
        ((10989307 : Dyadic) * half ^ 25)⟩,
       ⟨((-402407 : Dyadic) * half ^ 24),
        ((-7478897 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word11Step33 :
    word11Chunk33.foldl (fun acc a => a.applyPacked acc)
      word11State33 = word11State34 := by decide +kernel

private def word11Chunk34 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word11State35 : PackedMat2 :=
    ⟨⟨⟨((4888525 : Dyadic) * half ^ 23),
        ((10695011 : Dyadic) * half ^ 26)⟩,
       ⟨((-7886831 : Dyadic) * half ^ 25),
        ((-8908797 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((2261545 : Dyadic) * half ^ 24),
        ((-25061555 : Dyadic) * half ^ 26)⟩,
       ⟨((9062771 : Dyadic) * half ^ 25),
        ((-18320867 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-421293 : Dyadic) * half ^ 22),
        ((-4539681 : Dyadic) * half ^ 26)⟩,
       ⟨((21691211 : Dyadic) * half ^ 25),
        ((-13585861 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-612619 : Dyadic) * half ^ 21),
        ((-27440931 : Dyadic) * half ^ 26)⟩,
       ⟨((893107 : Dyadic) * half ^ 25),
        ((11667269 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word11Step34 :
    word11Chunk34.foldl (fun acc a => a.applyPacked acc)
      word11State34 = word11State35 := by decide +kernel

private def word11Chunk35 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word11State36 : PackedMat2 :=
    ⟨⟨⟨((6032553 : Dyadic) * half ^ 26),
        ((-11147 : Dyadic) * half ^ 18)⟩,
       ⟨((3067819 : Dyadic) * half ^ 26),
        ((-5534551 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((33208025 : Dyadic) * half ^ 26),
        ((-646967 : Dyadic) * half ^ 21)⟩,
       ⟨((-23663577 : Dyadic) * half ^ 26),
        ((-30498245 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((33208025 : Dyadic) * half ^ 26),
        ((-646967 : Dyadic) * half ^ 21)⟩,
       ⟨((23663577 : Dyadic) * half ^ 26),
        ((30498245 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-6032553 : Dyadic) * half ^ 26),
        ((11147 : Dyadic) * half ^ 18)⟩,
       ⟨((3067819 : Dyadic) * half ^ 26),
        ((-5534551 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word11Step35 :
    word11Chunk35.foldl (fun acc a => a.applyPacked acc)
      word11State35 = word11State36 := by decide +kernel

private def word11Chunk36 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word11State37 : PackedMat2 :=
    ⟨⟨⟨((421981 : Dyadic) * half ^ 24),
        ((38306351 : Dyadic) * half ^ 27)⟩,
       ⟨((11444435 : Dyadic) * half ^ 25),
        ((2458881 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-1215033 : Dyadic) * half ^ 26),
        ((78154623 : Dyadic) * half ^ 27)⟩,
       ⟨((-1358885 : Dyadic) * half ^ 26),
        ((19117711 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((1215033 : Dyadic) * half ^ 26),
        ((-78154623 : Dyadic) * half ^ 27)⟩,
       ⟨((-1358885 : Dyadic) * half ^ 26),
        ((19117711 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((421981 : Dyadic) * half ^ 24),
        ((38306351 : Dyadic) * half ^ 27)⟩,
       ⟨((-11444435 : Dyadic) * half ^ 25),
        ((-2458881 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word11Step36 :
    word11Chunk36.foldl (fun acc a => a.applyPacked acc)
      word11State36 = word11State37 := by decide +kernel

private def word11Chunk37 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word11State38 : PackedMat2 :=
    ⟨⟨⟨((540555 : Dyadic) * half ^ 27),
        ((41306553 : Dyadic) * half ^ 28)⟩,
       ⟨((1967023 : Dyadic) * half ^ 25),
        ((-16188445 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((71668889 : Dyadic) * half ^ 27),
        ((58921875 : Dyadic) * half ^ 28)⟩,
       ⟨((-15202225 : Dyadic) * half ^ 26),
        ((135434833 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((15202225 : Dyadic) * half ^ 26),
        ((-135434833 : Dyadic) * half ^ 28)⟩,
       ⟨((-71668889 : Dyadic) * half ^ 27),
        ((-58921875 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((1967023 : Dyadic) * half ^ 25),
        ((-16188445 : Dyadic) * half ^ 28)⟩,
       ⟨((540555 : Dyadic) * half ^ 27),
        ((41306553 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word11Step37 :
    word11Chunk37.foldl (fun acc a => a.applyPacked acc)
      word11State37 = word11State38 := by decide +kernel

private def word11Chunk38 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word11State39 : PackedMat2 :=
    ⟨⟨⟨((13799727 : Dyadic) * half ^ 28),
        ((36676495 : Dyadic) * half ^ 29)⟩,
       ⟨((-43014197 : Dyadic) * half ^ 27),
        ((65572093 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((38539189 : Dyadic) * half ^ 28),
        ((63088345 : Dyadic) * half ^ 29)⟩,
       ⟨((1982679 : Dyadic) * half ^ 26),
        ((340897667 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((138904661 : Dyadic) * half ^ 28),
        ((-30608473 : Dyadic) * half ^ 29)⟩,
       ⟨((100996503 : Dyadic) * half ^ 27),
        ((46469905 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-14447799 : Dyadic) * half ^ 28),
        ((99828121 : Dyadic) * half ^ 29)⟩,
       ⟨((-25562147 : Dyadic) * half ^ 27),
        ((72228667 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word11Step38 :
    word11Chunk38.foldl (fun acc a => a.applyPacked acc)
      word11State38 = word11State39 := by decide +kernel

private def word11Chunk39 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word11State40 : PackedMat2 :=
    ⟨⟨⟨((114774173 : Dyadic) * half ^ 29),
        ((-189435153 : Dyadic) * half ^ 29)⟩,
       ⟨((40832631 : Dyadic) * half ^ 29),
        ((-99234319 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-30870765 : Dyadic) * half ^ 29),
        ((-49561799 : Dyadic) * half ^ 28)⟩,
       ⟨((393236583 : Dyadic) * half ^ 29),
        ((3613321 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-393236583 : Dyadic) * half ^ 29),
        ((-3613321 : Dyadic) * half ^ 25)⟩,
       ⟨((30870765 : Dyadic) * half ^ 29),
        ((49561799 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((40832631 : Dyadic) * half ^ 29),
        ((-99234319 : Dyadic) * half ^ 29)⟩,
       ⟨((114774173 : Dyadic) * half ^ 29),
        ((-189435153 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word11Step39 :
    word11Chunk39.foldl (fun acc a => a.applyPacked acc)
      word11State39 = word11State40 := by decide +kernel

private def word11Chunk40 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word11State41 : PackedMat2 :=
    ⟨⟨⟨((-639044221 : Dyadic) * half ^ 30),
        ((267827107 : Dyadic) * half ^ 30)⟩,
       ⟨((-183857165 : Dyadic) * half ^ 30),
        ((43363083 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-478469921 : Dyadic) * half ^ 30),
        ((-269977531 : Dyadic) * half ^ 30)⟩,
       ⟨((-350643637 : Dyadic) * half ^ 30),
        ((-82594489 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-435166509 : Dyadic) * half ^ 30),
        ((-414556779 : Dyadic) * half ^ 30)⟩,
       ⟨((-104788553 : Dyadic) * half ^ 30),
        ((-31956571 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-354553273 : Dyadic) * half ^ 30),
        ((411450693 : Dyadic) * half ^ 30)⟩,
       ⟨((-181100941 : Dyadic) * half ^ 30),
        ((28449191 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word11Step40 :
    word11Chunk40.foldl (fun acc a => a.applyPacked acc)
      word11State40 = word11State41 := by decide +kernel

private def word11Chunk41 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word11State42 : PackedMat2 :=
    ⟨⟨⟨((2077385 : Dyadic) * half ^ 30),
        ((-83218305 : Dyadic) * half ^ 30)⟩,
       ⟨((-359792209 : Dyadic) * half ^ 29),
        ((83795011 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-95472963 : Dyadic) * half ^ 29),
        ((-186734715 : Dyadic) * half ^ 29)⟩,
       ⟨((-539439139 : Dyadic) * half ^ 30),
        ((20098663 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((393568093 : Dyadic) * half ^ 30),
        ((-348493213 : Dyadic) * half ^ 31)⟩,
       ⟨((-353370767 : Dyadic) * half ^ 30),
        ((-730385065 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-41753329 : Dyadic) * half ^ 28),
        ((721661803 : Dyadic) * half ^ 31)⟩,
       ⟨((-288353 : Dyadic) * half ^ 29),
        ((717507033 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word11Step41 :
    word11Chunk41.foldl (fun acc a => a.applyPacked acc)
      word11State41 = word11State42 := by decide +kernel

private def word11Chunk42 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word11State43 : PackedMat2 :=
    ⟨⟨⟨((-763709787 : Dyadic) * half ^ 31),
        ((1295951881 : Dyadic) * half ^ 32)⟩,
       ⟨((-1182134463 : Dyadic) * half ^ 31),
        ((-1092733025 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-250911699 : Dyadic) * half ^ 30),
        ((1087132687 : Dyadic) * half ^ 32)⟩,
       ⟨((-229557491 : Dyadic) * half ^ 30),
        ((-530416989 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-250911699 : Dyadic) * half ^ 30),
        ((1087132687 : Dyadic) * half ^ 32)⟩,
       ⟨((229557491 : Dyadic) * half ^ 30),
        ((530416989 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((763709787 : Dyadic) * half ^ 31),
        ((-1295951881 : Dyadic) * half ^ 32)⟩,
       ⟨((-1182134463 : Dyadic) * half ^ 31),
        ((-1092733025 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word11Step42 :
    word11Chunk42.foldl (fun acc a => a.applyPacked acc)
      word11State42 = word11State43 := by decide +kernel

private def word11Chunk43 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word11State44 : PackedMat2 :=
    ⟨⟨⟨((2756444193 : Dyadic) * half ^ 32),
        ((-1395624929 : Dyadic) * half ^ 33)⟩,
       ⟨((-523833987 : Dyadic) * half ^ 31),
        ((-1111025461 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1444638241 : Dyadic) * half ^ 32),
        ((1472614443 : Dyadic) * half ^ 33)⟩,
       ⟨((-278322855 : Dyadic) * half ^ 29),
        ((-249521953 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-278322855 : Dyadic) * half ^ 29),
        ((-249521953 : Dyadic) * half ^ 33)⟩,
       ⟨((1444638241 : Dyadic) * half ^ 32),
        ((1472614443 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((523833987 : Dyadic) * half ^ 31),
        ((1111025461 : Dyadic) * half ^ 33)⟩,
       ⟨((-2756444193 : Dyadic) * half ^ 32),
        ((1395624929 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word11Step43 :
    word11Chunk43.foldl (fun acc a => a.applyPacked acc)
      word11State43 = word11State44 := by decide +kernel

private def word11Chunk44 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word11State45 : PackedMat2 :=
    ⟨⟨⟨((1878625885 : Dyadic) * half ^ 33),
        ((859179475 : Dyadic) * half ^ 31)⟩,
       ⟨((200780491 : Dyadic) * half ^ 33),
        ((-620446915 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((2651529309 : Dyadic) * half ^ 33),
        ((1013886487 : Dyadic) * half ^ 33)⟩,
       ⟨((3951560481 : Dyadic) * half ^ 33),
        ((-2188088083 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((293550399 : Dyadic) * half ^ 31),
        ((-3301544895 : Dyadic) * half ^ 33)⟩,
       ⟨((-1600987285 : Dyadic) * half ^ 32),
        ((325007793 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((14920785 : Dyadic) * half ^ 27),
        ((259925797 : Dyadic) * half ^ 31)⟩,
       ⟨((739813195 : Dyadic) * half ^ 30),
        ((838922697 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word11Step44 :
    word11Chunk44.foldl (fun acc a => a.applyPacked acc)
      word11State44 = word11State45 := by decide +kernel

private def word11Chunk45 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word11State46 : PackedMat2 :=
    ⟨⟨⟨((1187569875 : Dyadic) * half ^ 34),
        ((-564947015 : Dyadic) * half ^ 33)⟩,
       ⟨((6584336115 : Dyadic) * half ^ 34),
        ((4770120665 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1522489335 : Dyadic) * half ^ 34),
        ((1980451955 : Dyadic) * half ^ 33)⟩,
       ⟨((-2675013259 : Dyadic) * half ^ 34),
        ((8985307125 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((12946211035 : Dyadic) * half ^ 34),
        ((-2098751297 : Dyadic) * half ^ 34)⟩,
       ⟨((-5024403215 : Dyadic) * half ^ 34),
        ((288130981 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-3640226635 : Dyadic) * half ^ 34),
        ((-3885952995 : Dyadic) * half ^ 34)⟩,
       ⟨((5900014695 : Dyadic) * half ^ 34),
        ((168648945 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word11Step45 :
    word11Chunk45.foldl (fun acc a => a.applyPacked acc)
      word11State45 = word11State46 := by decide +kernel

private def word11Chunk46 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word11State47 : PackedMat2 :=
    ⟨⟨⟨((-362854825 : Dyadic) * half ^ 34),
        ((-2109340263 : Dyadic) * half ^ 33)⟩,
       ⟨((-1695235705 : Dyadic) * half ^ 33),
        ((-718899869 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-558390907 : Dyadic) * half ^ 32),
        ((-4063975517 : Dyadic) * half ^ 33)⟩,
       ⟨((9999374827 : Dyadic) * half ^ 34),
        ((-69137053 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((558390907 : Dyadic) * half ^ 32),
        ((4063975517 : Dyadic) * half ^ 33)⟩,
       ⟨((9999374827 : Dyadic) * half ^ 34),
        ((-69137053 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-362854825 : Dyadic) * half ^ 34),
        ((-2109340263 : Dyadic) * half ^ 33)⟩,
       ⟨((1695235705 : Dyadic) * half ^ 33),
        ((718899869 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word11Step46 :
    word11Chunk46.foldl (fun acc a => a.applyPacked acc)
      word11State46 = word11State47 := by decide +kernel

private def word11Chunk47 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word11State48 : PackedMat2 :=
    ⟨⟨⟨((-11340214595 : Dyadic) * half ^ 35),
        ((-1561525235 : Dyadic) * half ^ 33)⟩,
       ⟨((5683648291 : Dyadic) * half ^ 35),
        ((2519976929 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((8216082349 : Dyadic) * half ^ 35),
        ((-14243564795 : Dyadic) * half ^ 35)⟩,
       ⟨((-1216625731 : Dyadic) * half ^ 35),
        ((-14424198567 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((14333881681 : Dyadic) * half ^ 34),
        ((-3499728309 : Dyadic) * half ^ 35)⟩,
       ⟨((-45158443 : Dyadic) * half ^ 33),
        ((-589544255 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-603073541 : Dyadic) * half ^ 34),
        ((-176767697 : Dyadic) * half ^ 31)⟩,
       ⟨((-5643027399 : Dyadic) * half ^ 34),
        ((-8511931443 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word11Step47 :
    word11Chunk47.foldl (fun acc a => a.applyPacked acc)
      word11State47 = word11State48 := by decide +kernel

private def word11Chunk48 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word11State49 : PackedMat2 :=
    ⟨⟨⟨((-46843613533 : Dyadic) * half ^ 36),
        ((-805027509 : Dyadic) * half ^ 32)⟩,
       ⟨((-1079673107 : Dyadic) * half ^ 36),
        ((4153901391 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-26064356777 : Dyadic) * half ^ 36),
        ((6367141017 : Dyadic) * half ^ 34)⟩,
       ⟨((-9346259987 : Dyadic) * half ^ 36),
        ((-6948259083 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-26064356777 : Dyadic) * half ^ 36),
        ((6367141017 : Dyadic) * half ^ 34)⟩,
       ⟨((9346259987 : Dyadic) * half ^ 36),
        ((6948259083 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((46843613533 : Dyadic) * half ^ 36),
        ((805027509 : Dyadic) * half ^ 32)⟩,
       ⟨((-1079673107 : Dyadic) * half ^ 36),
        ((4153901391 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word11Step48 :
    word11Chunk48.foldl (fun acc a => a.applyPacked acc)
      word11State48 = word11State49 := by decide +kernel

private def word11Chunk49 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word11State50 : PackedMat2 :=
    ⟨⟨⟨((-78833468953 : Dyadic) * half ^ 37),
        ((1639509609 : Dyadic) * half ^ 33)⟩,
       ⟨((36457305729 : Dyadic) * half ^ 37),
        ((-4780143729 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((55894306163 : Dyadic) * half ^ 37),
        ((1982301785 : Dyadic) * half ^ 33)⟩,
       ⟨((68510349713 : Dyadic) * half ^ 37),
        ((6852288961 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-38569117521 : Dyadic) * half ^ 37),
        ((-31101163969 : Dyadic) * half ^ 36)⟩,
       ⟨((-24864539599 : Dyadic) * half ^ 37),
        ((6308021775 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((21452010015 : Dyadic) * half ^ 37),
        ((-5297020403 : Dyadic) * half ^ 35)⟩,
       ⟨((31012297473 : Dyadic) * half ^ 37),
        ((-57645387341 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word11Step49 :
    word11Chunk49.foldl (fun acc a => a.applyPacked acc)
      word11State49 = word11State50 := by decide +kernel

private def word11Chunk50 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word11State51 : PackedMat2 :=
    ⟨⟨⟨((35950653961 : Dyadic) * half ^ 37),
        ((-5292062083 : Dyadic) * half ^ 35)⟩,
       ⟨((-39226026531 : Dyadic) * half ^ 36),
        ((3489823157 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((9219597045 : Dyadic) * half ^ 35),
        ((11404931729 : Dyadic) * half ^ 37)⟩,
       ⟨((53028094907 : Dyadic) * half ^ 37),
        ((5965439659 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((9219597045 : Dyadic) * half ^ 35),
        ((11404931729 : Dyadic) * half ^ 37)⟩,
       ⟨((-53028094907 : Dyadic) * half ^ 37),
        ((-5965439659 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-35950653961 : Dyadic) * half ^ 37),
        ((5292062083 : Dyadic) * half ^ 35)⟩,
       ⟨((-39226026531 : Dyadic) * half ^ 36),
        ((3489823157 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word11Step50 :
    word11Chunk50.foldl (fun acc a => a.applyPacked acc)
      word11State50 = word11State51 := by decide +kernel

private def word11Chunk51 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word11State52 : PackedMat2 :=
    ⟨⟨⟨((-203029145 : Dyadic) * half ^ 38),
        ((-85569317 : Dyadic) * half ^ 39)⟩,
       ⟨((2041210967 : Dyadic) * half ^ 34),
        ((-289147085875 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((18868602139 : Dyadic) * half ^ 38),
        ((-136092965207 : Dyadic) * half ^ 39)⟩,
       ⟨((4346117489 : Dyadic) * half ^ 33),
        ((86364654171 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((111228809689 : Dyadic) * half ^ 38),
        ((120207157509 : Dyadic) * half ^ 39)⟩,
       ⟨((-12432077759 : Dyadic) * half ^ 37),
        ((157944361787 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((144530758279 : Dyadic) * half ^ 38),
        ((-32862404617 : Dyadic) * half ^ 39)⟩,
       ⟨((36154081899 : Dyadic) * half ^ 36),
        ((-32456346327 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word11Step51 :
    word11Chunk51.foldl (fun acc a => a.applyPacked acc)
      word11State51 = word11State52 := by decide +kernel

private def word11Chunk52 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word11State53 : PackedMat2 :=
    ⟨⟨⟨((30201694321 : Dyadic) * half ^ 39),
        ((-138425465801 : Dyadic) * half ^ 39)⟩,
       ⟨((269550341301 : Dyadic) * half ^ 39),
        ((-2053417743 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-68224194467 : Dyadic) * half ^ 39),
        ((-275364033271 : Dyadic) * half ^ 39)⟩,
       ⟨((172174679093 : Dyadic) * half ^ 39),
        ((-8348809659 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((68224194467 : Dyadic) * half ^ 39),
        ((275364033271 : Dyadic) * half ^ 39)⟩,
       ⟨((172174679093 : Dyadic) * half ^ 39),
        ((-8348809659 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((30201694321 : Dyadic) * half ^ 39),
        ((-138425465801 : Dyadic) * half ^ 39)⟩,
       ⟨((-269550341301 : Dyadic) * half ^ 39),
        ((2053417743 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word11Step52 :
    word11Chunk52.foldl (fun acc a => a.applyPacked acc)
      word11State52 = word11State53 := by decide +kernel

private def word11Chunk53 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word11State54 : PackedMat2 :=
    ⟨⟨⟨((-40838505725 : Dyadic) * half ^ 38),
        ((171805262979 : Dyadic) * half ^ 40)⟩,
       ⟨((-22480877143 : Dyadic) * half ^ 35),
        ((96280478211 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-225745030587 : Dyadic) * half ^ 39),
        ((68885511637 : Dyadic) * half ^ 40)⟩,
       ⟨((-188938997889 : Dyadic) * half ^ 39),
        ((-339869570133 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-225745030587 : Dyadic) * half ^ 39),
        ((68885511637 : Dyadic) * half ^ 40)⟩,
       ⟨((188938997889 : Dyadic) * half ^ 39),
        ((339869570133 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((40838505725 : Dyadic) * half ^ 38),
        ((-171805262979 : Dyadic) * half ^ 40)⟩,
       ⟨((-22480877143 : Dyadic) * half ^ 35),
        ((96280478211 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word11Step53 :
    word11Chunk53.foldl (fun acc a => a.applyPacked acc)
      word11State53 = word11State54 := by decide +kernel

private def word11Chunk54 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word11State55 : PackedMat2 :=
    ⟨⟨⟨((666991326515 : Dyadic) * half ^ 40),
        ((155049527365 : Dyadic) * half ^ 41)⟩,
       ⟨((-47443518531 : Dyadic) * half ^ 38),
        ((-510776772899 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((391867380121 : Dyadic) * half ^ 40),
        ((-552991536779 : Dyadic) * half ^ 41)⟩,
       ⟨((-32990763021 : Dyadic) * half ^ 36),
        ((-30975461303 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-32990763021 : Dyadic) * half ^ 36),
        ((-30975461303 : Dyadic) * half ^ 41)⟩,
       ⟨((391867380121 : Dyadic) * half ^ 40),
        ((-552991536779 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((47443518531 : Dyadic) * half ^ 38),
        ((510776772899 : Dyadic) * half ^ 41)⟩,
       ⟨((-666991326515 : Dyadic) * half ^ 40),
        ((-155049527365 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word11Step54 :
    word11Chunk54.foldl (fun acc a => a.applyPacked acc)
      word11State54 = word11State55 := by decide +kernel

private def word11Chunk55 : List Letter := [.h, .t, .h, .s, .t, .h, .s]
private def word11State56 : PackedMat2 :=
    ⟨⟨⟨((872675809825 : Dyadic) * half ^ 41),
        ((29308357613 : Dyadic) * half ^ 36)⟩,
       ⟨((-235652826505 : Dyadic) * half ^ 41),
        ((41061614487 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-214913402567 : Dyadic) * half ^ 41),
        ((151966724323 : Dyadic) * half ^ 41)⟩,
       ⟨((1027883245333 : Dyadic) * half ^ 41),
        ((-726823213043 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((214913402567 : Dyadic) * half ^ 41),
        ((-151966724323 : Dyadic) * half ^ 41)⟩,
       ⟨((1027883245333 : Dyadic) * half ^ 41),
        ((-726823213043 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((872675809825 : Dyadic) * half ^ 41),
        ((29308357613 : Dyadic) * half ^ 36)⟩,
       ⟨((235652826505 : Dyadic) * half ^ 41),
        ((-41061614487 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word11Step55 :
    word11Chunk55.foldl (fun acc a => a.applyPacked acc)
      word11State55 = word11State56 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word11_check : check word11 11 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word11 = word11State56.toMatrix := by
    unfold evalRingPacked
    change ((
      word11Chunk0 ++ word11Chunk1 ++ word11Chunk2 ++ word11Chunk3 ++
      word11Chunk4 ++ word11Chunk5 ++ word11Chunk6 ++ word11Chunk7 ++
      word11Chunk8 ++ word11Chunk9 ++ word11Chunk10 ++ word11Chunk11 ++
      word11Chunk12 ++ word11Chunk13 ++ word11Chunk14 ++ word11Chunk15 ++
      word11Chunk16 ++ word11Chunk17 ++ word11Chunk18 ++ word11Chunk19 ++
      word11Chunk20 ++ word11Chunk21 ++ word11Chunk22 ++ word11Chunk23 ++
      word11Chunk24 ++ word11Chunk25 ++ word11Chunk26 ++ word11Chunk27 ++
      word11Chunk28 ++ word11Chunk29 ++ word11Chunk30 ++ word11Chunk31 ++
      word11Chunk32 ++ word11Chunk33 ++ word11Chunk34 ++ word11Chunk35 ++
      word11Chunk36 ++ word11Chunk37 ++ word11Chunk38 ++ word11Chunk39 ++
      word11Chunk40 ++ word11Chunk41 ++ word11Chunk42 ++ word11Chunk43 ++
      word11Chunk44 ++ word11Chunk45 ++ word11Chunk46 ++ word11Chunk47 ++
      word11Chunk48 ++ word11Chunk49 ++ word11Chunk50 ++ word11Chunk51 ++
      word11Chunk52 ++ word11Chunk53 ++ word11Chunk54 ++ word11Chunk55
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word11Step0, word11Step1, word11Step2, word11Step3, word11Step4,
      word11Step5, word11Step6, word11Step7, word11Step8, word11Step9,
      word11Step10, word11Step11, word11Step12, word11Step13, word11Step14,
      word11Step15, word11Step16, word11Step17, word11Step18, word11Step19,
      word11Step20, word11Step21, word11Step22, word11Step23, word11Step24,
      word11Step25, word11Step26, word11Step27, word11Step28, word11Step29,
      word11Step30, word11Step31, word11Step32, word11Step33, word11Step34,
      word11Step35, word11Step36, word11Step37, word11Step38, word11Step39,
      word11Step40, word11Step41, word11Step42, word11Step43, word11Step44,
      word11Step45, word11Step46, word11Step47, word11Step48, word11Step49,
      word11Step50, word11Step51, word11Step52, word11Step53, word11Step54,
      word11Step55]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
