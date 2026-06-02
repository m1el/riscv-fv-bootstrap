(** * RvCrossStep.v -- foundations for the execute/step cross-check (task #7, T2).

    Forward-simulation of our [Rv64i.step] against riscv-coq's [Run.run1 RV64I]
    over the Minimal [OState] machine (coq-riscv.0.0.5). This file establishes the
    two foundational, instruction-independent pieces of that simulation, both
    [Admitted]-free:

    - the WORD/Z ARITHMETIC BRIDGE: every riscv-coq [word 64] operation that
      [ExecuteI] uses (add / or / unsigned-< / signed-<) computes our corresponding
      [Z]-mod-2^64 operation (wadd / wor / ultb / sltb) under [word.unsigned];
    - the FETCH BRIDGE [fetch_combine]: one [run1] instruction fetch
      (combine of the 4 little-endian bytes that [load_bytes 4] reads) equals the
      32-bit word our [fetch32] reads, given the riscv memory map agrees with our
      byte memory on the 4 fetch addresses.

    Also recorded: the state-bridge relation [Rrel] / well-formedness [WFrel]
    (CROSSCHECK.md §3) that [step_agrees] will use. Remaining for T2: the [run1]
    monad reduction + the 12 per-instruction [exec_*] lemmas + [step_agrees] +
    the transport corollary [core_refines_riscv]. *)

From Coq Require Import ZArith List Lia Bool. Import ListNotations.
Require Import Hex0Coq.Rv64i Hex0Coq.RvCross.
Require Import riscv.Spec.Decode riscv.Spec.Machine riscv.Spec.Execute.
Require Import riscv.Utility.Utility riscv.Platform.Memory.
Require Import riscv.Platform.RiscvMachine riscv.Platform.Minimal riscv.Platform.Run.
Require Import riscv.Utility.Monads. Import OStateOperations.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Word.LittleEndian coqutil.Word.LittleEndianList.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Byte.
Require Import coqutil.Z.BitOps coqutil.Z.prove_Zeq_bitwise.
Require Import bedrock2.ZnWords.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Byte / bit helpers for the fetch combine.                           *)
(* ------------------------------------------------------------------ *)

Lemma byte_uoz : forall z, 0 <= z < 256 -> byte.unsigned (byte.of_Z z) = z.
Proof. intros. rewrite byte.unsigned_of_Z. unfold byte.wrap. apply Z.mod_small. lia. Qed.

Lemma testbit_hi : forall a i, 0 <= a < 256 -> 8 <= i -> Z.testbit a i = false.
Proof. intros a i Ha Hi. apply (testbit_above (n:=a) (p:=8)); [ change (2^8) with 256; lia | lia | lia ]. Qed.

(** A low byte and a high-shifted value share no bits. *)
Lemma land_lo_hi : forall a b, 0 <= a < 256 -> 0 <= b -> Z.land a (b * 256) = 0.
Proof.
  intros a b Ha Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  replace (b * 256) with (Z.shiftl b 8) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; ring).
  destruct (i <? 8) eqn:E.
  - apply Z.ltb_lt in E. rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
  - apply Z.ltb_ge in E. rewrite testbit_hi by lia. reflexivity.
Qed.

(* ================================================================== *)
(* The word/Z arithmetic bridge.                                       *)
(* ================================================================== *)

Section WordBridge.
  Context {word: word.word 64} {word_ok: word.ok word}.

  (** coqutil's modular [word.wrap] at width 64 is our [Rv64i.wrap]. *)
  Lemma wrap64 : forall z, word.wrap z = Rv64i.wrap z.
  Proof. intros. unfold word.wrap, Rv64i.wrap, Rv64i.w64. reflexivity. Qed.

  (** [ExecuteI]'s [x + y] (= word.add) computes our [wadd]. *)
  Lemma br_add : forall a b : word,
    word.unsigned (word.add a b) = Rv64i.wadd (word.unsigned a) (word.unsigned b).
  Proof. intros. rewrite word.unsigned_add. apply wrap64. Qed.

  (** [or x y] (= word.or) computes our [wor]. *)
  Lemma br_or : forall a b : word,
    word.unsigned (word.or a b) = Rv64i.wor (word.unsigned a) (word.unsigned b).
  Proof.
    intros. rewrite word.unsigned_or, wrap64. unfold Rv64i.wor, Rv64i.wrap, Rv64i.w64.
    pose proof (word.unsigned_range a). pose proof (word.unsigned_range b).
    apply Z.mod_small. apply lor_lt; lia.
  Qed.

  (** [ltu x y] (= word.ltu) is our unsigned compare [ultb]. *)
  Lemma br_ltu : forall a b : word,
    word.ltu a b = Rv64i.ultb (word.unsigned a) (word.unsigned b).
  Proof. intros. rewrite word.unsigned_ltu. reflexivity. Qed.

  (** our signed reading [toS] is riscv-coq's [word.signed]. *)
  Lemma toS_signed : forall a : word, Rv64i.toS (word.unsigned a) = word.signed a.
  Proof.
    intros. rewrite word.signed_eq_swrap_unsigned. unfold word.swrap, Rv64i.toS, Rv64i.w64.
    pose proof (word.unsigned_range a).
    destruct (word.unsigned a >=? 2 ^ 63) eqn:E.
    - apply Z.geb_le in E.
      replace (word.unsigned a + 2 ^ (64 - 1)) with ((word.unsigned a - 2^63) + 1 * 2 ^ 64) by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
    - rewrite Z.geb_leb in E. apply Z.leb_gt in E.
      replace (64 - 1) with 63 by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  (** the signed branch test [x < y] (= word.lts) is our [sltb]. *)
  Lemma br_lts : forall a b : word,
    word.lts a b = Rv64i.sltb (word.unsigned a) (word.unsigned b).
  Proof. intros. rewrite word.signed_lts. unfold Rv64i.sltb. rewrite !toS_signed. reflexivity. Qed.

  (** a register written by an arithmetic instruction: storing [word.add] of two
      [of_Z]'d operands is storing the [of_Z] of our [wadd] result -- the shape
      [RegAgree] of the post-state needs. *)
  Lemma wadd_of_Z : forall a b,
    word.of_Z (word:=word) (Rv64i.wadd a b) = word.add (word.of_Z a) (word.of_Z b).
  Proof.
    intros. apply word.unsigned_inj. rewrite br_add, !word.unsigned_of_Z.
    unfold Rv64i.wadd, Rv64i.wrap, Rv64i.w64, word.wrap.
    rewrite <- Z.add_mod by (apply Z.pow_nonzero; lia).
    rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
  Qed.
End WordBridge.

(* ================================================================== *)
(* The fetch bridge: one run1 fetch = our fetch32.                     *)
(* ================================================================== *)

Section Fetch.
  Context {word: word.word 64} {word_ok: word.ok word}.
  Context {Mem: map.map word Init.Byte.byte} {Mem_ok: map.ok Mem}.

  (** If the riscv memory map holds our bytes [f 0..3] at [pc..pc+3] (no address
      wraparound), then [load_bytes 4] succeeds and [combine] of those bytes is the
      little-endian 32-bit word our [fetch32] reads. *)
  Lemma fetch_combine : forall (rm:Mem) (pc:word) (f: Z -> Z),
    word.unsigned pc + 4 <= 2 ^ 64 ->
    (forall i, 0 <= i < 4 -> map.get rm (word.add pc (word.of_Z i)) = Some (byte.of_Z (f i))) ->
    (forall i, 0 <= i < 4 -> 0 <= f i < 256) ->
    exists bs, Memory.load_bytes 4 rm pc = Some bs /\
      LittleEndian.combine 4 bs = f 0 + f 1 * 256 + f 2 * 65536 + f 3 * 16777216.
  Proof.
    intros rm pc f Hnw Hget Hrange.
    pose proof (Hget 0 ltac:(lia)) as G0. pose proof (Hget 1 ltac:(lia)) as G1.
    pose proof (Hget 2 ltac:(lia)) as G2. pose proof (Hget 3 ltac:(lia)) as G3.
    pose proof (Hrange 0 ltac:(lia)). pose proof (Hrange 1 ltac:(lia)).
    pose proof (Hrange 2 ltac:(lia)). pose proof (Hrange 3 ltac:(lia)).
    unfold Memory.load_bytes, Memory.footprint. cbn [HList.tuple.unfoldn].
    replace (word.add pc (word.of_Z 0)) with pc in G0 by ZnWords.
    replace (word.add (word.add pc (word.of_Z 1)) (word.of_Z 1)) with (word.add pc (word.of_Z 2)) in * by ZnWords.
    replace (word.add (word.add pc (word.of_Z 2)) (word.of_Z 1)) with (word.add pc (word.of_Z 3)) in * by ZnWords.
    unfold map.getmany_of_tuple. cbn [HList.tuple.map HList.tuple.option_all].
    rewrite G0, G1, G2, G3.
    eexists. split; [reflexivity|].
    rewrite combine_eq. cbn [HList.tuple.to_list]. cbv [LittleEndianList.le_combine].
    rewrite !byte_uoz by assumption.
    change (Z.shiftl 0 8) with 0. rewrite Z.lor_0_r.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
    rewrite (or_to_plus (f 2)) by (apply land_lo_hi; lia).
    rewrite (or_to_plus (f 1)) by (apply land_lo_hi; lia).
    rewrite (or_to_plus (f 0)) by (apply land_lo_hi; lia).
    ring.
  Qed.
End Fetch.

(* ================================================================== *)
(* run1 reduction toolkit: how one Minimal OState cycle reduces.        *)
(* These are instruction-independent and reusable across all exec_*.    *)
(* ================================================================== *)

Section Run1.
  Context {BW: Bitwidth 64}.
  Context {word: word.word 64} {word_ok: word.ok word}.
  Context {Mem: map.map word Init.Byte.byte} {Mem_ok: map.ok Mem}.
  Context {Registers: map.map Z word} {Reg_ok: map.ok Registers}.

  (** A successful, executable fetch reduces [run1] to: run [execute] of the
      decoded instruction on the (fetch leaves state unchanged) machine, then
      [endCycleNormal]. *)
  Lemma run1_fetch : forall (m:RiscvMachine) bs,
    isXAddr4B m.(getPc) m.(getXAddrs) = true ->
    Memory.load_bytes 4 m.(getMem) m.(getPc) = Some bs ->
    Run.run1 RV64I m =
      (let (o, m3) := Execute.execute (decode RV64I (LittleEndian.combine 4 bs)) m in
       match o with Some _ => endCycleNormal m3 | None => (None, m3) end).
  Proof.
    intros m bs Hx Hl.
    unfold Run.run1, Machine.getPC, Machine.loadWord, IsRiscvMachine, loadN, fail_if_None.
    cbv [Bind Return OState_Monad get put]. cbn [fst snd]. rewrite Hl, Hx. reflexivity.
  Qed.

  (** Reading register [r] (1..31) returns its mapped value, state unchanged. *)
  Lemma getReg_red : forall (m:RiscvMachine) r v, 1 <= r < 32 ->
    map.get m.(getRegs) r = Some v ->
    Machine.getRegister r m = (Some v, m).
  Proof.
    intros m r v Hr Hg.
    unfold Machine.getRegister, IsRiscvMachine.
    destruct (Z.eq_dec r Register0) as [E|_].
    - exfalso; cbn in E; lia.
    - replace ((0 <? r) && (r <? 32)) with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
      cbv [Bind Return OState_Monad get]. cbn [fst snd]. rewrite Hg. reflexivity.
  Qed.

  (** Writing register [rd] (1..31) puts into the register map, nothing else. *)
  Lemma setReg_red : forall (m:RiscvMachine) rd v, 1 <= rd < 32 ->
    Machine.setRegister rd v m = (Some tt, withRegs (map.put m.(getRegs) rd v) m).
  Proof.
    intros m rd v Hr.
    unfold Machine.setRegister, IsRiscvMachine.
    destruct (Z.eq_dec rd Register0) as [E|_].
    - exfalso; cbn in E; lia.
    - replace ((0 <? rd) && (rd <? 32)) with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
      unfold update. cbv [Bind Return OState_Monad get put]. cbn [fst snd]. reflexivity.
  Qed.

  (** [endCycleNormal]: pc := nextPc, nextPc := nextPc + 4. *)
  Lemma endcycle_red : forall (m:RiscvMachine),
    endCycleNormal m = (Some tt, withPc m.(getNextPc) (withNextPc (word.add m.(getNextPc) (word.of_Z 4)) m)).
  Proof.
    intros m. unfold endCycleNormal, IsRiscvMachine, update.
    cbv [Bind Return OState_Monad get put]. cbn [fst snd]. reflexivity.
  Qed.
End Run1.

(* ================================================================== *)
(* The state-bridge relation (CROSSCHECK.md §3), for [step_agrees].    *)
(* The simulation theorem itself is future work (see file header).     *)
(* ================================================================== *)

Section Bridge.
  Context {BW: Bitwidth 64}.
  Context {word: word.word 64} {word_ok: word.ok word}.
  Context {Mem: map.map word Init.Byte.byte} {Mem_ok: map.ok Mem}.
  Context {Registers: map.map Z word} {Reg_ok: map.ok Registers}.

  Notation RMach := (@RiscvMachine.RiscvMachine 64 word Registers Mem).

  (** registers x1..x31 agree (x0 reads 0 on both sides). *)
  Definition RegAgree (s:Rv64i.State) (m:RMach) : Prop :=
    forall r, 1 <= r < 32 ->
      map.get m.(getRegs) r = Some (word.of_Z (Rv64i.rget s r)) /\ 0 <= Rv64i.rget s r < 2 ^ 64.

  (** the riscv memory map agrees with our byte memory on a domain [D] of words. *)
  Definition MemAgree (s:Rv64i.State) (m:RMach) (D: word -> Prop) : Prop :=
    forall a, D a -> map.get m.(getMem) a = Some (byte.of_Z (s.(mem) (word.unsigned a)))
                     /\ 0 <= s.(mem) (word.unsigned a) < 256.

  (** PC agrees and the sequential-next-PC invariant [nextPc = pc + 4] holds
      (run1 maintains this; endCycleNormal relies on it). *)
  Definition PcAgree (s:Rv64i.State) (m:RMach) : Prop :=
    word.unsigned m.(getPc) = s.(pc) /\ m.(getNextPc) = word.add m.(getPc) (word.of_Z 4).

  (** the full bridge over a memory domain [D]. *)
  Definition Rrel (s:Rv64i.State) (m:RMach) (D: word -> Prop) : Prop :=
    RegAgree s m /\ MemAgree s m D /\ PcAgree s m.

  (** well-formedness preconditions for one step: the 4 fetch bytes are mapped
      and executable, and pc does not wrap. (Per-instruction data accesses add
      their own [D]-membership; see CROSSCHECK.md §3/§5.) *)
  Definition WFfetch (s:Rv64i.State) (m:RMach) (D: word -> Prop) : Prop :=
    word.unsigned m.(getPc) + 4 <= 2 ^ 64 /\
    (forall i, 0 <= i < 4 -> D (word.add m.(getPc) (word.of_Z i))) /\
    isXAddr4 m.(getPc) m.(getXAddrs).

  (** register read under [RegAgree], handling x0 (both sides read 0). The
      bridge corollary the per-instruction [exec_*] lemmas use to resolve
      [getRegister rs1] / [getRegister rs2]. *)
  Lemma getReg_R : forall s (m:RMach) r, RegAgree s m -> 0 <= r < 32 ->
    Machine.getRegister r m = (Some (word.of_Z (Rv64i.rget s r)), m).
  Proof.
    intros s m r Hra Hr.
    destruct (Z.eq_dec r 0) as [E|NE].
    - subst r. unfold Machine.getRegister, IsRiscvMachine.
      destruct (Z.eq_dec 0 Register0) as [_|C]; [|exfalso; cbn in C; lia].
      unfold Rv64i.rget. cbn. reflexivity.
    - destruct (Hra r ltac:(lia)) as [Hg _]. apply getReg_red; [lia | exact Hg].
  Qed.
End Bridge.
