(** * General refinement (T1) in Coq -- mirror of lean/Hex0/Refine.lean.

    Proof-grade theorem: for ALL inputs, the real `core` computes `coreSpec`.
    No vm_compute on the general statement -- it is genuine induction.

    STATUS: `core_refines` is PROVED modulo the single per-token dispatch lemma
    `loop_iteration` (the only `Admitted`).  Everything that assembles it is
    kernel-checked, mirroring `lean/Hex0/Refine.lean` §5:
      - `fetch_code` + all 12 `step_*` lemmas + state/storeByte projections
        (`decode (wordAt off)` reduces under `vm_compute` at concrete offsets, so
        the step lemmas apply exactly as in Lean);
      - arithmetic toolkit: `wrap_small`, `wadd_id`, `toS_small`, `sltb_small`;
      - `runUntil` composition: `runUntil_halt`, `runUntil_one`, `runUntil_S`,
        `runUntil_add`, `runUntil_stab` (large-fuel halt absorption);
      - spec-side token decomposition: `decodeS_spacing`/`byte`/`comment`;
      - `core_eof` -- the EOF base case (4-step run to a correct halt);
      - `LoopInv` (the 18-field invariant) + `eof_result`;
      - `loop_correct` -- the induction (fuel bound `50*|rest| + 4`);
      - `init_loopinv` -- the prologue (2-step run to the loop head);
      - `core_refines` -- prologue + induction + `runOn<->coreSpec` conversion.
    Remaining frontier (`Admitted`, line ~425): `loop_iteration` -- the per-token
    dispatch (spacing/byte/comment + the four halting error classes), the large
    mechanical tail (~2500 Lean lines).  `Print Assumptions core_refines` =>
    `loop_iteration` + `functional_extensionality_dep` (a standard, consistent
    axiom, used for `mem : Z -> Z` state equality -- cf. Lean's propext/choice).
    Two Coq-specific notes vs Lean (see PROOF.md §8): (1) `runOn` uses a *fixed*
    fuel (100000), so the assembly bounds the step count (Lean used ∃fuel) and
    absorbs the slack via `runUntil_stab` -- note `lia` cannot reason about the
    nat literal `100000` (it is `Nat.of_num_uint`), so the bound `F <= 100000`
    is proved through `Z` (`Nat2Z.inj_le` + `vm_compute (Z.of_nat 100000)`);
    (2) the model's bytes are `Z` but the spec is on `nat`, so `LoopInv`/dispatch
    carry `Z.of_nat`/`Z.to_nat` (`zin`) conversions. *)

From Coq Require Import ZArith List Lia Bool.
From Equations Require Import Equations.
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

(* storeByte touches only memory *)
Lemma storeByte_pc s a b : (storeByte s a b).(pc) = s.(pc). Proof. reflexivity. Qed.
Lemma storeByte_reg s a b : (storeByte s a b).(reg) = s.(reg). Proof. reflexivity. Qed.
Lemma storeByte_rget s a b i : rget (storeByte s a b) i = rget s i. Proof. reflexivity. Qed.
Lemma storeByte_mem s a b : (storeByte s a b).(mem) = (fun x => if x =? a then b mod 256 else s.(mem) x).
Proof. reflexivity. Qed.

(** ** Arithmetic toolkit (mirror of ult_ofNat/slt_ofNat/ofNat_ne/setWidth8). *)

Lemma wrap_small z : 0 <= z < 2 ^ 64 -> wrap z = z.
Proof. unfold wrap, w64. apply Z.mod_small. Qed.

(* address arithmetic with no 64-bit wraparound *)
Lemma wadd_id a b : 0 <= a + b < 2 ^ 64 -> wadd a b = a + b.
Proof. unfold wadd. apply wrap_small. Qed.

Lemma toS_small x : 0 <= x < 2 ^ 63 -> toS x = x.
Proof. unfold toS. intros h. destruct (x >=? 2 ^ 63) eqn:E; [lia | reflexivity]. Qed.

(* signed compare = unsigned compare on small (< 2^63) values *)
Lemma sltb_small a b : 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> sltb a b = (a <? b).
Proof. intros ha hb. unfold sltb. rewrite (toS_small a ha), (toS_small b hb). reflexivity. Qed.

(** ** runUntil (= Lean runFuel) composition. *)

Lemma runUntil_halt n s : s.(pc) = 0 -> runUntil 0 n s = s.
Proof. intros h. destruct n; [reflexivity|]. simpl. rewrite h, Z.eqb_refl. reflexivity. Qed.

Lemma runUntil_one s : s.(pc) <> 0 -> runUntil 0 1 s = step s.
Proof.
  intros h. simpl. destruct (s.(pc) =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity].
Qed.

Lemma runUntil_S n s : s.(pc) <> 0 -> runUntil 0 (S n) s = runUntil 0 n (step s).
Proof.
  intros h. simpl. destruct (s.(pc) =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity].
Qed.

Lemma runUntil_add a b s : runUntil 0 (a + b) s = runUntil 0 b (runUntil 0 a s).
Proof.
  revert b s. induction a as [|k ih]; intros b s; simpl; [reflexivity|].
  destruct (s.(pc) =? 0) eqn:E.
  - apply Z.eqb_eq in E. now rewrite (runUntil_halt b s E).
  - apply ih.
Qed.

(* Once the machine has halted by fuel [f], any larger fuel [g] gives the same
   state.  Used to absorb the fixed 100000-fuel run in [runOn] into the
   step-count bound the loop actually needs (avoids nat-subtraction lia, which
   chokes on the [Nat.of_num_uint 100000] literal). *)
Lemma runUntil_stab f s : (runUntil 0 f s).(pc) = 0 ->
  forall g, (f <= g)%nat -> runUntil 0 g s = runUntil 0 f s.
Proof.
  intros Hhalt g Hle. induction Hle as [|g Hle IH].
  - reflexivity.
  - rewrite <- Nat.add_1_r, (runUntil_add g 1 s), IH.
    exact (runUntil_halt 1 (runUntil 0 f s) Hhalt).
Qed.

(** ** Spec-side token decomposition (mirror of decodeS_spacing/byte/comment). *)

Lemma decodeS_spacing c rest : isComment c = false -> isSpace c = true ->
  decodeS High (c :: rest) = decodeS High rest.
Proof. intros hc hs. simp decodeS. rewrite hc, hs. reflexivity. Qed.

Lemma decodeS_byte chi clo rest hi lo :
  isComment chi = false -> isSpace chi = false -> nibble chi = Some hi ->
  isLowStop clo = false -> nibble clo = Some lo ->
  decodeS High (chi :: clo :: rest) =
    ((hi * 16 + lo)%nat :: fst (decodeS High rest), snd (decodeS High rest)).
Proof.
  intros hc hs hh hlc hl. simp decodeS. rewrite hc, hs, hh. simp decodeS. rewrite hlc, hl.
  destruct (decodeS High rest) as [out st]. reflexivity.
Qed.

Lemma decodeS_comment c rest : isComment c = true ->
  decodeS High (c :: rest) = decodeS High (skipComment rest).
Proof. intros hc. simp decodeS. rewrite hc. reflexivity. Qed.

(** ** EOF base case (mirror of core_eof). *)

Lemma coreBytes_len : Z.of_nat (length coreBytes) = 324. Proof. reflexivity. Qed.
Lemma coreAddr_pos k : 0 <= k -> coreAddr + k <> 0. Proof. unfold coreAddr; lia. Qed.
Lemma CodeLoaded_eqmem s t : t.(mem) = s.(mem) -> CodeLoaded s -> CodeLoaded t.
Proof. intros hm hcs i Hi. rewrite hm. apply hcs; exact Hi. Qed.

Lemma core_eof : forall s L E,
  CodeLoaded s -> s.(pc) = coreAddr + 8 ->
  rget s 5 = L -> rget s 11 = L -> rget s 6 = E -> rget s 1 = 0 -> 0 <= E < 2 ^ 64 ->
  (runUntil 0 4 s).(pc) = 0 /\ rget (runUntil 0 4 s) 10 = 0 /\
  rget (runUntil 0 4 s) 11 = E /\ (runUntil 0 4 s).(mem) = s.(mem).
Proof.
  intros s L E hc hpc h5 h11 h6 h1 hE.
  (* step 1: bgeu t0,a1 taken (t0 = a1) -> .Lok (264) *)
  assert (hs1 : step s = setPc s (coreAddr + 264)).
  { rewrite (step_bgeu s 8 5 11 256 hc ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc
              ltac:(vm_compute; reflexivity)).
    rewrite h5, h11. unfold ultb. rewrite Z.ltb_irrefl. cbn match.
    rewrite hpc, (wadd_id (coreAddr+8) 256 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s1 := setPc s (coreAddr + 264)) in *.
  assert (hpc1 : s1.(pc) = coreAddr + 264) by (unfold s1; apply setPc_pc).
  assert (hc1 : CodeLoaded s1) by (apply (CodeLoaded_eqmem s); [reflexivity| exact hc]).
  (* step 2: li a0,0 -> 268 *)
  assert (hs2 : step s1 = setPc (rset s1 10 0) (coreAddr + 268)).
  { rewrite (step_addi s1 264 10 0 0 hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1
              ltac:(vm_compute; reflexivity)).
    rewrite rget_zero, (wadd_id 0 0 ltac:(lia)), hpc1,
            (wadd_id (coreAddr+264) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s2 := setPc (rset s1 10 0) (coreAddr + 268)) in *.
  assert (hpc2 : s2.(pc) = coreAddr + 268) by (unfold s2; apply setPc_pc).
  assert (hc2 : CodeLoaded s2) by
    (apply (CodeLoaded_eqmem s); [unfold s2, s1; rewrite setPc_mem, rset_mem, setPc_mem; reflexivity| exact hc]).
  assert (h6_2 : rget s2 6 = E).
  { unfold s2. rewrite setPc_rget, (rset_rget s1 10 0 6 ltac:(lia) ltac:(lia)).
    unfold s1. rewrite setPc_rget. exact h6. }
  (* step 3: mv a1,t1 -> 272 *)
  assert (hs3 : step s2 = setPc (rset s2 11 E) (coreAddr + 272)).
  { rewrite (step_addi s2 268 11 6 0 hc2 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc2
              ltac:(vm_compute; reflexivity)).
    rewrite h6_2, (wadd_id E 0 ltac:(lia)), Z.add_0_r, hpc2,
            (wadd_id (coreAddr+268) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s3 := setPc (rset s2 11 E) (coreAddr + 272)) in *.
  assert (hpc3 : s3.(pc) = coreAddr + 272) by (unfold s3; apply setPc_pc).
  assert (hc3 : CodeLoaded s3) by
    (apply (CodeLoaded_eqmem s); [unfold s3,s2,s1; rewrite !setPc_mem, !rset_mem; reflexivity| exact hc]).
  assert (h1_3 : rget s3 1 = 0).
  { unfold s3. rewrite setPc_rget, (rset_rget s2 11 E 1 ltac:(lia) ltac:(lia)).
    unfold s2. rewrite setPc_rget, (rset_rget s1 10 0 1 ltac:(lia) ltac:(lia)).
    unfold s1. rewrite setPc_rget. exact h1. }
  (* step 4: ret -> pc = 0 *)
  assert (hs4 : step s3 = setPc s3 0).
  { rewrite (step_jalr s3 272 0 1 0 hc3 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc3
              ltac:(vm_compute; reflexivity)).
    assert (Hr : rset s3 0 (wadd s3.(pc) 4) = s3) by (unfold rset; reflexivity).
    rewrite Hr, h1_3, (wadd_id 0 0 ltac:(lia)). reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; apply coreAddr_pos; lia).
  assert (hp3 : s3.(pc) <> 0) by (rewrite hpc3; apply coreAddr_pos; lia).
  assert (hrun : runUntil 0 4 s = setPc s3 0).
  { rewrite (runUntil_S 3 s hp0), hs1, (runUntil_S 2 s1 hp1), hs2,
            (runUntil_S 1 s2 hp2), hs3, (runUntil_S 0 s3 hp3), hs4. reflexivity. }
  rewrite hrun. refine (conj _ (conj _ (conj _ _))).
  - rewrite setPc_pc. reflexivity.
  - rewrite setPc_rget. unfold s3. rewrite setPc_rget, (rset_rget s2 11 E 10 ltac:(lia) ltac:(lia)).
    unfold s2. rewrite setPc_rget, (rset_rget s1 10 0 10 ltac:(lia) ltac:(lia)). reflexivity.
  - rewrite setPc_rget. unfold s3. rewrite setPc_rget, (rset_rget s2 11 E 11 ltac:(lia) ltac:(lia)).
    reflexivity.
  - rewrite setPc_mem. unfold s3, s2, s1. rewrite !setPc_mem, !rset_mem. reflexivity.
Qed.

(** ** Helpers for the EOF base case. *)

Lemma decodeS_nil : decodeS High [] = ([], Ok). Proof. now simp decodeS. Qed.

Lemma readMem_eq : forall l m base,
  (forall j, (j < length l)%nat -> m (base + Z.of_nat j) = Z.of_nat (nth j l 0%nat)) ->
  readMem m base (length l) = l.
Proof.
  induction l as [|a l' IH]; intros m base H; simpl; [reflexivity|].
  f_equal.
  - specialize (H 0%nat ltac:(simpl; lia)).
    replace (base + Z.of_nat 0) with base in H by lia. simpl in H. rewrite H. apply Nat2Z.id.
  - apply IH. intros j Hj. specialize (H (S j) ltac:(simpl; lia)). simpl in H.
    rewrite <- H. f_equal. lia.
Qed.

(** ** Loop invariant + the induction backbone (mirror of LoopInv/loop_correct).

    Per the fuel-bound approach: each iteration runs <= 50 instructions per input
    char consumed, so the whole loop halts within [50 * |rest| + 4] steps -- a
    closed (non-existential) bound, so it composes with the fixed-fuel `runOn`. *)

Record LoopInv (inp : list Z) (cap : Z) (s : State) (rest : list Z) (emitted : list nat) : Prop := {
  li_at_loop : s.(pc) = coreAddr + 8;
  li_code    : CodeLoaded s;
  li_a0      : rget s 10 = inputAddr;
  li_a1      : rget s 11 = Z.of_nat (length inp);
  li_a2      : rget s 12 = outAddr;
  li_a3      : rget s 13 = cap;
  li_ra      : rget s 1 = 0;
  li_in_mem  : forall j, 0 <= j < Z.of_nat (length inp) ->
                 s.(mem) (inputAddr + j) = nth (Z.to_nat j) inp 0;
  li_in_lt   : inputAddr + Z.of_nat (length inp) < 2 ^ 64;
  li_bytes   : forall b, In b inp -> 0 <= b < 256;
  li_in_fits : inputAddr + Z.of_nat (length inp) <= outAddr;
  li_out_lt  : outAddr + cap < 2 ^ 64;
  li_idx     : rget s 5 = Z.of_nat (length inp) - Z.of_nat (length rest);
  li_suffix  : skipn (length inp - length rest) inp = rest;
  li_outidx  : rget s 6 = Z.of_nat (length emitted);
  li_emit_le : (length emitted <= Z.to_nat cap)%nat;
  li_out_mem : forall j, (j < length emitted)%nat ->
                 s.(mem) (outAddr + Z.of_nat j) = Z.of_nat (nth j emitted 0%nat);
  li_spec    : decodeS High (zin inp) =
                 (emitted ++ fst (decodeS High (zin rest)), snd (decodeS High (zin rest)))
}.

(* The halted observation matches coreSpec. *)
Definition Result (f : State) (inp : list Z) (cap : Z) : Prop :=
  let '(st, bs, ln) := coreSpec (zin inp) (Z.to_nat cap) in
  f.(pc) = 0 /\ rget f 10 = Z.of_nat st /\ rget f 11 = Z.of_nat ln /\
  readMem f.(mem) outAddr ln = bs.

Lemma Result_pc f inp cap : Result f inp cap -> f.(pc) = 0.
Proof. unfold Result. destruct (coreSpec (zin inp) (Z.to_nat cap)) as [[st bs] ln]. tauto. Qed.

(* Base case: input exhausted -> halts Ok with output preserved. (Uses core_eof;
   the readMem/coreSpec packaging is the remaining detail -- Admitted for now.) *)
Theorem eof_result : forall inp cap emitted s,
  LoopInv inp cap s [] emitted -> Result (runUntil 0 4 s) inp cap.
Proof.
  intros inp cap emitted s HI.
  destruct HI as [Hpc Hcode Ha0 Ha1 Ha2 Ha3 Hra Hinmem Hinlt Hbytes Hinfits Houtlt
                  Hidx Hsuf Houtidx Hemitle Houtmem Hspec].
  assert (h5 : rget s 5 = Z.of_nat (length inp)) by (rewrite Hidx; simpl length; lia).
  assert (hE : 0 <= Z.of_nat (length emitted) < 2 ^ 64) by (unfold outAddr in Houtlt; lia).
  destruct (core_eof s (Z.of_nat (length inp)) (Z.of_nat (length emitted))
              Hcode Hpc h5 Ha1 Houtidx Hra hE) as [Hp [H10 [H11 Hmem]]].
  (* coreSpec computes to (0, emitted, length emitted) *)
  assert (Hdec : Spec.decode (zin inp) = (emitted, Ok)).
  { unfold Spec.decode. rewrite Hspec. change (zin []) with (@nil nat).
    rewrite decodeS_nil. simpl. rewrite app_nil_r. reflexivity. }
  assert (Hcs : coreSpec (zin inp) (Z.to_nat cap) = (0%nat, emitted, length emitted)).
  { unfold coreSpec. rewrite Hdec.
    destruct (Z.to_nat cap <? length emitted)%nat eqn:Ecap.
    - apply Nat.ltb_lt in Ecap. lia.
    - reflexivity. }
  unfold Result. rewrite Hcs. repeat split.
  - exact Hp.
  - rewrite H10. reflexivity.
  - rewrite H11. reflexivity.
  - rewrite Hmem. apply readMem_eq. intros j Hj. exact (Houtmem j Hj).
Qed.

(* One iteration: consume >= 1 char in <= 50 steps/char, preserving LoopInv, or
   halt correctly. The per-token dispatch (FRONTIER) -- Admitted for now. *)
Theorem loop_iteration : forall inp cap rest emitted s,
  rest <> [] -> LoopInv inp cap s rest emitted ->
  exists k,
    (exists rest' emitted', (length rest' < length rest)%nat /\
        (k <= 50 * (length rest - length rest'))%nat /\
        LoopInv inp cap (runUntil 0 k s) rest' emitted')
    \/ ((k <= 50 * length rest)%nat /\ Result (runUntil 0 k s) inp cap).
Admitted.

(* The induction (PROVED): from any LoopInv state the machine halts correctly
   within [50 * |rest| + 4] steps. The fuel-bound (point 1) made fully explicit. *)
Theorem loop_correct : forall inp cap n rest emitted s,
  (length rest <= n)%nat -> LoopInv inp cap s rest emitted ->
  Result (runUntil 0 (50 * length rest + 4) s) inp cap.
Proof.
  intros inp cap n. induction n as [|n IH]; intros rest emitted s hn hinv.
  - assert (rest = []) by (destruct rest; [reflexivity| simpl in hn; lia]).
    subst rest. exact (eof_result inp cap emitted s hinv).
  - destruct rest as [|c rest''] eqn:Er.
    + exact (eof_result inp cap emitted s hinv).
    + destruct (loop_iteration inp cap (c :: rest'') emitted s ltac:(discriminate) hinv)
        as [k [ [rest' [emitted' [Hlt [Hkb Hinv']]]] | [Hkb Hres] ]].
      * (* continue: k <= 50*(|rest|-|rest'|) chars consumed *)
        set (A := (50 * length (c :: rest'') + 4)%nat).
        assert (HkA : (k <= A)%nat) by (unfold A; lia).
        replace A with (k + (A - k))%nat by lia. rewrite runUntil_add.
        assert (HBle : (50 * length rest' + 4 <= A - k)%nat) by (unfold A; simpl length in *; lia).
        replace (A - k)%nat with ((50 * length rest' + 4) + ((A - k) - (50 * length rest' + 4)))%nat by lia.
        rewrite runUntil_add.
        assert (HIH : Result (runUntil 0 (50 * length rest' + 4) (runUntil 0 k s)) inp cap)
          by (apply (IH rest' emitted'); [simpl length in *; lia | exact Hinv']).
        rewrite (runUntil_halt _ _ (Result_pc _ _ _ HIH)). exact HIH.
      * (* halt *)
        set (A := (50 * length (c :: rest'') + 4)%nat).
        assert (HkA : (k <= A)%nat) by (unfold A; lia).
        replace A with (k + (A - k))%nat by lia. rewrite runUntil_add.
        rewrite (runUntil_halt _ _ (Result_pc _ _ _ Hres)). exact Hres.
Qed.

(** ** Well-formedness: input region fits before the output region, etc. *)
Record WellFormed (inp : list Z) (cap : Z) : Prop := {
  in_fits  : inputAddr + Z.of_nat (length inp) <= outAddr;
  out_fits : outAddr + cap < 2 ^ 64;
  bytes_ok : forall b, In b inp -> 0 <= b < 256
}.

(** ** Prologue: from the initial state, `li t0,0; li t1,0` reach the loop head
    establishing the initial invariant (full input remaining, nothing emitted). *)
Theorem init_loopinv : forall inp cap, WellFormed inp cap ->
  LoopInv inp cap (runUntil 0 2 (mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr))) inp [].
Proof.
  intros inp cap HW. destruct HW as [Hfits Hfit2 Hbytes].
  set (init := mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr)).
  assert (Hmem0 : init.(mem) = memWith inp inputAddr) by reflexivity.
  assert (Hpc0 : init.(pc) = coreAddr) by reflexivity.
  assert (Hcode0 : CodeLoaded init).
  { intros i Hi. rewrite coreBytes_len in Hi. rewrite Hmem0. unfold memWith.
    replace ((coreAddr <=? coreAddr + i) && (coreAddr + i <? coreAddr + Z.of_nat (length coreBytes)))
      with true
      by (symmetry; apply andb_true_iff; split;
          [apply Z.leb_le; lia | apply Z.ltb_lt; rewrite coreBytes_len; lia]).
    cbv iota. replace (coreAddr + i - coreAddr) with i by lia. unfold nthb. reflexivity. }
  assert (hs1 : step init = setPc (rset init 5 0) (coreAddr + 4)).
  { rewrite (step_addi init 0 5 0 0 Hcode0 ltac:(lia) ltac:(rewrite coreBytes_len; lia) Hpc0
              ltac:(vm_compute; reflexivity)).
    rewrite rget_zero, (wadd_id 0 0 ltac:(lia)), Hpc0,
            (wadd_id coreAddr 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s1 := setPc (rset init 5 0) (coreAddr + 4)) in *.
  assert (hpc1 : s1.(pc) = coreAddr + 4) by reflexivity.
  assert (hc1 : CodeLoaded s1) by (apply (CodeLoaded_eqmem init); [reflexivity| exact Hcode0]).
  assert (hs2 : step s1 = setPc (rset s1 6 0) (coreAddr + 8)).
  { rewrite (step_addi s1 4 6 0 0 hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1
              ltac:(vm_compute; reflexivity)).
    rewrite rget_zero, (wadd_id 0 0 ltac:(lia)), hpc1,
            (wadd_id (coreAddr+4) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s2 := setPc (rset s1 6 0) (coreAddr + 8)) in *.
  assert (hp0 : init.(pc) <> 0) by (rewrite Hpc0; unfold coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  assert (hrun : runUntil 0 2 init = s2)
    by (rewrite (runUntil_S 1 init hp0), hs1, (runUntil_S 0 s1 hp1), hs2; reflexivity).
  rewrite hrun.
  assert (Hmem2 : s2.(mem) = memWith inp inputAddr)
    by (unfold s2, s1; rewrite !setPc_mem, !rset_mem; exact Hmem0).
  assert (R10 : rget s2 10 = inputAddr) by (unfold s2, s1, init; reflexivity).
  assert (R11 : rget s2 11 = Z.of_nat (length inp)) by (unfold s2, s1, init; reflexivity).
  assert (R12 : rget s2 12 = outAddr) by (unfold s2, s1, init; reflexivity).
  assert (R13 : rget s2 13 = cap) by (unfold s2, s1, init; reflexivity).
  assert (R1 : rget s2 1 = 0) by (unfold s2, s1, init; reflexivity).
  assert (R5 : rget s2 5 = 0) by (unfold s2, s1, init; reflexivity).
  assert (R6 : rget s2 6 = 0) by (unfold s2, s1, init; reflexivity).
  refine {| li_at_loop := _; li_code := _; li_a0 := R10; li_a1 := R11; li_a2 := R12;
            li_a3 := R13; li_ra := R1; li_in_mem := _; li_in_lt := _; li_bytes := Hbytes;
            li_in_fits := Hfits; li_out_lt := Hfit2; li_idx := _; li_suffix := _;
            li_outidx := _; li_emit_le := _; li_out_mem := _; li_spec := _ |}.
  - reflexivity.
  - apply (CodeLoaded_eqmem init); [exact Hmem2| exact Hcode0].
  - intros j Hj. rewrite Hmem2. unfold memWith.
    replace ((coreAddr <=? inputAddr + j) && (inputAddr + j <? coreAddr + Z.of_nat (length coreBytes)))
      with false
      by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge;
          rewrite coreBytes_len; unfold coreAddr, inputAddr; lia).
    cbv iota.
    replace ((inputAddr <=? inputAddr + j) && (inputAddr + j <? inputAddr + Z.of_nat (length inp)))
      with true
      by (symmetry; apply andb_true_iff; split;
          [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
    cbv iota. replace (inputAddr + j - inputAddr) with j by lia. reflexivity.
  - unfold inputAddr, outAddr in *; lia.
  - rewrite R5; lia.
  - rewrite Nat.sub_diag; reflexivity.
  - rewrite R6; reflexivity.
  - simpl; lia.
  - intros j Hj; simpl in Hj; lia.
  - rewrite app_nil_l; apply surjective_pairing.
Qed.

(** ** The general refinement theorem: PROVED modulo the per-token dispatch
    (`loop_iteration`). Mirrors the Lean assembly; the fixed 100000 fuel suffices
    because the loop halts within [2 + 50*|inp| + 4] steps and |inp| <= 484. *)
Theorem core_refines : forall (inp : list Z) (cap : Z),
  WellFormed inp cap ->
  runOn inp cap = specOn (zin inp) (Z.to_nat cap).
Proof.
  intros inp cap HW.
  assert (Hlen : (length inp <= 484)%nat)
    by (destruct HW as [Hfits _ _]; unfold inputAddr, outAddr in Hfits; lia).
  pose proof (init_loopinv inp cap HW) as HLI.
  set (init := mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr)) in *.
  pose proof (loop_correct inp cap (length inp) inp [] (runUntil 0 2 init) (le_n _) HLI) as HR.
  rewrite <- (runUntil_add 2 (50 * length inp + 4) init) in HR.
  (* The loop halts by fuel [2 + (50*|inp| + 4)] <= 100000 (since |inp| <= 484),
     so the fixed 100000-fuel run in [runOn] coincides with it. *)
  assert (HF : (2 + (50 * length inp + 4) <= 100000)%nat).
  { apply Nat2Z.inj_le.
    replace (Z.of_nat 100000) with 100000%Z by (vm_compute; reflexivity).
    lia. }
  assert (Hhalt : runUntil 0 100000 init
                  = runUntil 0 (2 + (50 * length inp + 4)) init)
    by (apply (runUntil_stab _ _ (Result_pc _ _ _ HR)); exact HF).
  unfold runOn. fold init. rewrite Hhalt.
  unfold specOn, Result in *.
  destruct (coreSpec (zin inp) (Z.to_nat cap)) as [[st bs] ln].
  destruct HR as [Hp [H10 [H11 Hmemr]]].
  rewrite H10, H11, Nat2Z.id, Hmemr. reflexivity.
Qed.
