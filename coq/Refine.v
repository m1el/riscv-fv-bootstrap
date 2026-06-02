(** * General refinement (T1) in Coq -- mirror of lean/Hex0/Refine.lean.

    Proof-grade theorem: for ALL inputs, the real `core` computes `coreSpec`.
    No vm_compute on the general statement -- it is genuine induction.

    STATUS: the full step ENGINE is ported and proved (kernel-checked):
    `fetch_code` + all 12 `step_*` lemmas + the state-projection lemmas, mirroring
    `lean/Hex0/Refine.lean`. `decode (wordAt off)` reduces under `vm_compute` at
    concrete offsets, so the step lemmas apply exactly as in Lean. Remaining
    frontier (`Admitted`, the large tail): the arithmetic toolkit, `runUntil`
    composition, `core_eof`, `LoopInv`, the per-token dispatch, induction, and the
    `observe↔coreSpec` conversion. Methodology + port map: PROOF.md §5,§8. *)

From Coq Require Import ZArith List Lia Bool.
From Hex0Coq Require Import Spec Rv64i Image Harness.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Per-step reduction primitive (PROVED).
    `core`'s first instruction `li t0,0` = `addi x5,x0,0`, bytes 93 02 00 00,
    word 0x293 = 659. One [step] computes its effect; data stays symbolic. *)
Theorem step_li_t0 : forall s,
  s.(mem) s.(pc) = 147 ->
  s.(mem) (s.(pc) + 1) = 2 ->
  s.(mem) (s.(pc) + 2) = 0 ->
  s.(mem) (s.(pc) + 3) = 0 ->
  s.(pc) = 2147483784 ->
  (step s).(pc) = 2147483788 /\ rget (step s) 5 = 0.
Proof.
  intros s h0 h1 h2 h3 hpc.
  unfold step, fetch32.
  rewrite h0, h1, h2, h3.
  (* fetched word is now the closed value 659; decode + effect compute *)
  change (147 + 2 * 256 + 0 * 65536 + 0 * 16777216) with 659.
  rewrite hpc. cbn. split; reflexivity.
Qed.

(** ** Engine: fetch at a code offset + per-instruction step lemmas.
    Mirror of `Refine.lean`'s `fetch_code` + `step_*`. Words are [Z]; the
    decode of a closed word reduces under [cbn]/[vm_compute] at call sites. *)

Definition nthb (i : Z) : Z := nth (Z.to_nat i) coreBytes 0.

Definition wordAt (off : Z) : Z :=
  nthb off + nthb (off + 1) * 256 + nthb (off + 2) * 65536 + nthb (off + 3) * 16777216.

Definition CodeLoaded (s : State) : Prop :=
  forall i, 0 <= i < Z.of_nat (length coreBytes) -> s.(mem) (coreAddr + i) = nthb i.

(* state projections *)
Lemma setPc_pc s p : (setPc s p).(pc) = p. Proof. reflexivity. Qed.
Lemma setPc_mem s p : (setPc s p).(mem) = s.(mem). Proof. reflexivity. Qed.
Lemma setPc_rget s p i : rget (setPc s p) i = rget s i. Proof. reflexivity. Qed.
Lemma rset_pc s rd v : (rset s rd v).(pc) = s.(pc).
Proof. unfold rset; destruct (rd =? 0); reflexivity. Qed.
Lemma rset_mem s rd v : (rset s rd v).(mem) = s.(mem).
Proof. unfold rset; destruct (rd =? 0); reflexivity. Qed.
Lemma rget_zero s : rget s 0 = 0. Proof. reflexivity. Qed.

Lemma rset_rget s rd v i : rd <> 0 -> i <> 0 ->
  rget (rset s rd v) i = if i =? rd then v else rget s i.
Proof.
  intros hrd hi. unfold rget, rset.
  destruct (rd =? 0) eqn:Erd; [apply Z.eqb_eq in Erd; lia|].
  destruct (i =? 0) eqn:Ei; [apply Z.eqb_eq in Ei; lia|].
  reflexivity.
Qed.

Lemma fetch_code : forall s off,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> fetch32 s = wordAt off.
Proof.
  intros s off hc ho1 ho2 hpc.
  unfold fetch32, wordAt. rewrite hpc.
  replace (coreAddr + off + 1) with (coreAddr + (off + 1)) by lia.
  replace (coreAddr + off + 2) with (coreAddr + (off + 2)) by lia.
  replace (coreAddr + off + 3) with (coreAddr + (off + 3)) by lia.
  rewrite (hc off ltac:(lia)), (hc (off+1) ltac:(lia)),
          (hc (off+2) ltac:(lia)), (hc (off+3) ltac:(lia)).
  reflexivity.
Qed.

Lemma step_addi : forall s off rd rs1 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Iaddi rd rs1 imm ->
  step s = setPc (rset s rd (wadd (rget s rs1) imm)) (wadd s.(pc) 4).
Proof.
  intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity.
Qed.

Lemma step_bgeu : forall s off rs1 rs2 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ibgeu rs1 rs2 imm ->
  step s = setPc s (if ultb (rget s rs1) (rget s rs2) then wadd s.(pc) 4 else wadd s.(pc) imm).
Proof.
  intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity.
Qed.

Lemma step_add : forall s off rd rs1 rs2,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Iadd rd rs1 rs2 ->
  step s = setPc (rset s rd (wadd (rget s rs1) (rget s rs2))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 rs2 hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_or : forall s off rd rs1 rs2,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ior rd rs1 rs2 ->
  step s = setPc (rset s rd (wor (rget s rs1) (rget s rs2))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 rs2 hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_slli : forall s off rd rs1 sh,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Islli rd rs1 sh ->
  step s = setPc (rset s rd (wshl (rget s rs1) sh)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 sh hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_lbu : forall s off rd rs1 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ilbu rd rs1 imm ->
  step s = setPc (rset s rd ((s.(mem) (wadd (rget s rs1) imm)) mod 256)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_sb : forall s off rs1 rs2 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Isb rs1 rs2 imm ->
  step s = setPc (storeByte s (wadd (rget s rs1) imm) (rget s rs2)) (wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_beq : forall s off rs1 rs2 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ibeq rs1 rs2 imm ->
  step s = setPc s (if (rget s rs1) =? (rget s rs2) then wadd s.(pc) imm else wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_blt : forall s off rs1 rs2 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Iblt rs1 rs2 imm ->
  step s = setPc s (if sltb (rget s rs1) (rget s rs2) then wadd s.(pc) imm else wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_bge : forall s off rs1 rs2 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ibge rs1 rs2 imm ->
  step s = setPc s (if sltb (rget s rs1) (rget s rs2) then wadd s.(pc) 4 else wadd s.(pc) imm).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_jal : forall s off rd imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ijal rd imm ->
  step s = setPc (rset s rd (wadd s.(pc) 4)) (wadd s.(pc) imm).
Proof. intros s off rd imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_jalr : forall s off rd rs1 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ijalr rd rs1 imm ->
  step s = setPc (rset s rd (wadd s.(pc) 4))
                 (wadd (rget s rs1) imm - (wadd (rget s rs1) imm) mod 2).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

(** ** Well-formedness: input region fits before the output region, etc. *)
Record WellFormed (inp : list Z) (cap : Z) : Prop := {
  in_fits  : inputAddr + Z.of_nat (length inp) <= outAddr;
  out_fits : outAddr + cap < 2 ^ 64;
  bytes_ok : forall b, In b inp -> 0 <= b < 256
}.

(** ** The general refinement theorem (FRONTIER).
    Proof outline (mirrors the Lean file): establish the main-loop invariant from
    the initial state, prove one iteration preserves it or halts correctly (case
    analysis on the next char's class), induct on the remaining input length. *)
Theorem core_refines : forall (inp : list Z) (cap : Z),
  WellFormed inp cap ->
  runOn inp cap = specOn (zin inp) (Z.to_nat cap).
Proof.
Admitted.
