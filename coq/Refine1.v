(** * General refinement for hex1 in Coq -- mirror of lean/Hex1/Refine.lean.

    Target (the Coq port of the campaign theorem, cf. Refine.v for hex0):

      core1_refines : forall inp cap, WellFormed1 inp cap ->
        runOn1-style observation of the real core1 bytes = coreSpec1 inp cap

    proved by genuine induction (no vm_compute on the general statement),
    over the THREE loops of core1 (init / pass 1 / pass 2) and the label
    table region.

    STATUS: IN PROGRESS -- engine layer (chunk 1).
    - fetch at a code offset (Image1) + the 16 per-instruction step lemmas
      (hex0's 12 + SUB SRLI LD SD);
    - storeWord/loadWord state projections, per-byte reads, the frame
      lemma, and the 8-digit reassembly [loadWord_storeWord];
    - the wsub/wshr arithmetic bridges.
    The generic toolkit (state projections, wrap_small/wadd_id/toS_small/
    sltb_small, runUntil composition incl. runUntil_stab) is REUSED from
    the hex0 port (Hex0Coq.Refine) -- those lemmas are Image-independent. *)

From Coq Require Import ZArith List Lia Bool.
From Equations Require Import Equations.
From Hex0Coq Require Import Spec1 Rv64i Harness1 Refine.
From Hex0Coq Require Image1.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Engine: fetch at a code offset + per-instruction step lemmas
    (Image1 versions; mirror of lean/Hex1/RefineBase.lean). *)

Definition nthb1 (i : Z) : Z := nth (Z.to_nat i) Image1.coreBytes 0.

Definition wordAt1 (off : Z) : Z :=
  nthb1 off + nthb1 (off + 1) * 256 + nthb1 (off + 2) * 65536 + nthb1 (off + 3) * 16777216.

Definition CodeLoaded1 (s : State) : Prop :=
  forall i, 0 <= i < Z.of_nat (length Image1.coreBytes) ->
    s.(mem) (Image1.coreAddr + i) = nthb1 i.

Lemma coreBytes1_len : Z.of_nat (length Image1.coreBytes) = 724.
Proof. reflexivity. Qed.
Lemma coreAddr1_pos k : 0 <= k -> Image1.coreAddr + k <> 0.
Proof. unfold Image1.coreAddr; lia. Qed.
Lemma CodeLoaded1_eqmem s t : t.(mem) = s.(mem) -> CodeLoaded1 s -> CodeLoaded1 t.
Proof. intros He H i Hi. rewrite He. exact (H i Hi). Qed.

Lemma fetch_code1 : forall s off,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> fetch32 s = wordAt1 off.
Proof.
  intros s off hc ho1 ho2 hpc.
  unfold fetch32, wordAt1. rewrite hpc.
  replace (Image1.coreAddr + off + 1) with (Image1.coreAddr + (off + 1)) by lia.
  replace (Image1.coreAddr + off + 2) with (Image1.coreAddr + (off + 2)) by lia.
  replace (Image1.coreAddr + off + 3) with (Image1.coreAddr + (off + 3)) by lia.
  rewrite (hc off ltac:(lia)), (hc (off+1) ltac:(lia)),
          (hc (off+2) ltac:(lia)), (hc (off+3) ltac:(lia)).
  reflexivity.
Qed.

(* the 16 per-instruction step lemmas, all the same one-line proof *)
Lemma step1_addi : forall s off rd rs1 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Iaddi rd rs1 imm ->
  step s = setPc (rset s rd (wadd (rget s rs1) imm)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_add : forall s off rd rs1 rs2,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Iadd rd rs1 rs2 ->
  step s = setPc (rset s rd (wadd (rget s rs1) (rget s rs2))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 rs2 hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_sub : forall s off rd rs1 rs2,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Isub rd rs1 rs2 ->
  step s = setPc (rset s rd (wsub (rget s rs1) (rget s rs2))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 rs2 hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_or : forall s off rd rs1 rs2,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ior rd rs1 rs2 ->
  step s = setPc (rset s rd (wor (rget s rs1) (rget s rs2))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 rs2 hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_slli : forall s off rd rs1 sh,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Islli rd rs1 sh ->
  step s = setPc (rset s rd (wshl (rget s rs1) sh)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 sh hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_srli : forall s off rd rs1 sh,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Isrli rd rs1 sh ->
  step s = setPc (rset s rd (wshr (rget s rs1) sh)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 sh hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_lbu : forall s off rd rs1 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ilbu rd rs1 imm ->
  step s = setPc (rset s rd ((s.(mem) (wadd (rget s rs1) imm)) mod 256)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_ld : forall s off rd rs1 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ild rd rs1 imm ->
  step s = setPc (rset s rd (loadWord s (wadd (rget s rs1) imm))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_sb : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Isb rs1 rs2 imm ->
  step s = setPc (storeByte s (wadd (rget s rs1) imm) (rget s rs2)) (wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_sd : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Isd rs1 rs2 imm ->
  step s = setPc (storeWord s (wadd (rget s rs1) imm) (rget s rs2)) (wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_beq : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ibeq rs1 rs2 imm ->
  step s = setPc s (if (rget s rs1) =? (rget s rs2) then wadd s.(pc) imm else wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_blt : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Iblt rs1 rs2 imm ->
  step s = setPc s (if sltb (rget s rs1) (rget s rs2) then wadd s.(pc) imm else wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_bge : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ibge rs1 rs2 imm ->
  step s = setPc s (if sltb (rget s rs1) (rget s rs2) then wadd s.(pc) 4 else wadd s.(pc) imm).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_bgeu : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ibgeu rs1 rs2 imm ->
  step s = setPc s (if ultb (rget s rs1) (rget s rs2) then wadd s.(pc) 4 else wadd s.(pc) imm).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_jal : forall s off rd imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ijal rd imm ->
  step s = setPc (rset s rd (wadd s.(pc) 4)) (wadd s.(pc) imm).
Proof. intros s off rd imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_jalr : forall s off rd rs1 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ijalr rd rs1 imm ->
  step s = setPc (rset s rd (wadd s.(pc) 4))
                 (wadd (rget s rs1) imm - (wadd (rget s rs1) imm) mod 2).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

(** ** storeWord / loadWord state lemmas (mirror of RefineBase.lean's
    storeWord_pc/rget/frame/get0..7 + assemble_bytes; addresses are [Z],
    so distinctness is just [lia]). *)

Lemma storeWord_pc s a v : (storeWord s a v).(pc) = s.(pc).
Proof. reflexivity. Qed.
Lemma storeWord_reg s a v : (storeWord s a v).(reg) = s.(reg).
Proof. reflexivity. Qed.
Lemma storeWord_rget s a v i : rget (storeWord s a v) i = rget s i.
Proof. reflexivity. Qed.

(* the full byte map of an 8-byte store (outermost test = last store, a+7) *)
Lemma storeWord_mem_at : forall s a v x,
  (storeWord s a v).(mem) x =
  (if x =? a + 7 then (v / 2 ^ 56) mod 256
   else if x =? a + 6 then (v / 2 ^ 48) mod 256
   else if x =? a + 5 then (v / 2 ^ 40) mod 256
   else if x =? a + 4 then (v / 2 ^ 32) mod 256
   else if x =? a + 3 then (v / 2 ^ 24) mod 256
   else if x =? a + 2 then (v / 2 ^ 16) mod 256
   else if x =? a + 1 then (v / 2 ^ 8) mod 256
   else if x =? a then v mod 256
   else s.(mem) x).
Proof. reflexivity. Qed.

(* reading outside the 8 stored bytes is unchanged *)
Lemma storeWord_frame : forall s a v x,
  (forall k, 0 <= k < 8 -> x <> a + k) ->
  (storeWord s a v).(mem) x = s.(mem) x.
Proof.
  intros s a v x h. rewrite storeWord_mem_at.
  pose proof (h 0 ltac:(lia)). pose proof (h 1 ltac:(lia)).
  pose proof (h 2 ltac:(lia)). pose proof (h 3 ltac:(lia)).
  pose proof (h 4 ltac:(lia)). pose proof (h 5 ltac:(lia)).
  pose proof (h 6 ltac:(lia)). pose proof (h 7 ltac:(lia)).
  repeat (rewrite (proj2 (Z.eqb_neq _ _)) by lia). reflexivity.
Qed.

(* per-byte reads of the stored word: byte k of [storeWord s a v] at a+k *)
Lemma storeWord_get : forall s a v k, 0 <= k < 8 ->
  (storeWord s a v).(mem) (a + k) = (v / 2 ^ (8 * k)) mod 256.
Proof.
  intros s a v k hk.
  assert (hk8 : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  destruct hk8 as [->| [->| [->| [->| [->| [->| [->| ->]]]]]]];
    [ replace (a + 0) with a by lia | | | | | | | ];
    rewrite storeWord_mem_at;
    repeat (rewrite (proj2 (Z.eqb_neq _ _)) by lia);
    rewrite Z.eqb_refl;
    try reflexivity.
  (* k = 0: 8*0 = 0; v / 2^0 = v *)
  now rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
Qed.

(* the base-256 digit reassembly: loadWord after storeWord at the same
   address returns the stored (in-range) value (Lean's assemble_bytes). *)
Lemma digits8 : forall v, 0 <= v < 2 ^ 64 ->
  v mod 256
  + (v / 2 ^ 8) mod 256 * 2 ^ 8
  + (v / 2 ^ 16) mod 256 * 2 ^ 16
  + (v / 2 ^ 24) mod 256 * 2 ^ 24
  + (v / 2 ^ 32) mod 256 * 2 ^ 32
  + (v / 2 ^ 40) mod 256 * 2 ^ 40
  + (v / 2 ^ 48) mod 256 * 2 ^ 48
  + (v / 2 ^ 56) mod 256 * 2 ^ 56 = v.
Proof.
  intros v hv.
  replace (v / 2 ^ 16) with (v / 2 ^ 8 / 2 ^ 8) by (rewrite Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 24) with (v / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 32) with (v / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 40) with (v / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 48) with (v / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 56) with (v / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)
    by (rewrite !Z.div_div by lia; reflexivity).
  set (x1 := v / 2 ^ 8). set (x2 := x1 / 2 ^ 8). set (x3 := x2 / 2 ^ 8).
  set (x4 := x3 / 2 ^ 8). set (x5 := x4 / 2 ^ 8). set (x6 := x5 / 2 ^ 8).
  set (x7 := x6 / 2 ^ 8).
  pose proof (Z.div_mod v (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x1 (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x2 (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x3 (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x4 (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x5 (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x6 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound v (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x1 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x2 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x3 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x4 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x5 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x6 (2 ^ 8) ltac:(lia)).
  assert (hx7 : x7 = v / 2 ^ 56).
  { unfold x7, x6, x5, x4, x3, x2, x1. rewrite !Z.div_div by lia. reflexivity. }
  assert (hx7b : 0 <= x7 < 2 ^ 8).
  { rewrite hx7. split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia. }
  assert (hx7m : x7 mod 256 = x7) by (apply Z.mod_small; lia).
  rewrite hx7m.
  change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536.
  change (2 ^ 24) with 16777216. change (2 ^ 32) with 4294967296.
  change (2 ^ 40) with 1099511627776. change (2 ^ 48) with 281474976710656.
  change (2 ^ 56) with 72057594037927936.
  lia.
Qed.

Lemma loadWord_storeWord : forall s a v, 0 <= v < 2 ^ 64 ->
  loadWord (storeWord s a v) a = v.
Proof.
  intros s a v hv. unfold loadWord.
  pose proof (storeWord_get s a v 0 ltac:(lia)) as G0.
  replace (a + 0) with a in G0 by lia.
  pose proof (storeWord_get s a v 1 ltac:(lia)) as G1.
  pose proof (storeWord_get s a v 2 ltac:(lia)) as G2.
  pose proof (storeWord_get s a v 3 ltac:(lia)) as G3.
  pose proof (storeWord_get s a v 4 ltac:(lia)) as G4.
  pose proof (storeWord_get s a v 5 ltac:(lia)) as G5.
  pose proof (storeWord_get s a v 6 ltac:(lia)) as G6.
  pose proof (storeWord_get s a v 7 ltac:(lia)) as G7.
  rewrite G0, G1, G2, G3, G4, G5, G6, G7.
  change (8 * 0) with 0. change (8 * 1) with 8. change (8 * 2) with 16.
  change (8 * 3) with 24. change (8 * 4) with 32. change (8 * 5) with 40.
  change (8 * 6) with 48. change (8 * 7) with 56.
  rewrite Z.pow_0_r, Z.div_1_r.
  apply digits8. exact hv.
Qed.

(** ** Arithmetic bridges for the new instructions. *)

(* sub with no underflow: the Z value *)
Lemma wsub_id a b : 0 <= a - b < 2 ^ 64 -> wsub a b = a - b.
Proof. unfold wsub. apply wrap_small. Qed.

(* logical shift right = division by 2^n *)
Lemma wshr_div a n : 0 <= n -> wshr a n = a / 2 ^ n.
Proof. intros hn. unfold wshr. apply Z.shiftr_div_pow2. exact hn. Qed.
