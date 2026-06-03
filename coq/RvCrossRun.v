(** * RvCrossRun.v -- the transport corollary [core_refines_riscv] (task #7, T2).

    [step_agrees] (RvCrossExec.v) shows ONE [Rv64i.step] = ONE riscv-coq
    [Run.run1 RV64I] cycle, under the state bridge [Rrel] and the per-step side
    conditions [WFstep].  This file lifts that single-step simulation over a WHOLE
    run by induction (the analogue of [loop_correct]) and composes it with the
    finished [core_refines]:

      - [rrun]          -- iterate [run1] in lockstep with our [runUntil], stopping
                           when the model halts ([pc = 0]).
      - [transport_run] -- forward simulation: given [Rrel] at the start and the
                           per-step side conditions along the run ([RunWF]), [rrun]
                           succeeds and lands [Rrel]-related to [runUntil].
      - [core_refines_riscv] -- instantiate at [mkInit]; compose with the model
                           result ([init_loopinv] + [loop_correct], i.e. exactly the
                           first half of [core_refines]) so the RISC-V REFERENCE
                           MODEL running the real [core] bytes computes [coreSpec]
                           (halts with the spec status in a0, length in a1, and a
                           state [Rrel]-related to the spec output in memory).

    What remains as explicit hypotheses (the honest residual, factored cleanly):
      1. [Rrel (mkInit ...) m D] -- a riscv-coq init machine matching our init.
      2. [RunWF ...] -- the §5 side conditions (fetch executable + mapped, branch/
         jump targets 4-aligned, load/store targets in [D], decode <> Iunknown) hold
         at every non-halted state along the run.  These are the per-cycle
         obligations that [step_agrees] consumes; discharging them unconditionally
         from the [CodeLoaded]/[LoopInv] geometry (xaddr preservation, store
         disjointness) is a separate, larger effort -- see CROSSCHECK.md §3/§5. *)

From Coq Require Import ZArith List Lia Bool. Import ListNotations.
Require Import Hex0Coq.Rv64i Hex0Coq.RvCross Hex0Coq.RvCrossStep Hex0Coq.RvCrossExec.
Require Import Hex0Coq.Spec Hex0Coq.Image Hex0Coq.Harness Hex0Coq.Refine.
Require Import riscv.Spec.Decode riscv.Spec.Machine riscv.Platform.Run.
Require Import riscv.Platform.RiscvMachine riscv.Platform.Minimal.
Require Import riscv.Utility.Monads. Import OStateOperations.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Byte.
Local Open Scope Z_scope.

(* iterate [Rv64i.step] [k] times, with NO halt check -- so the index shift
   [nstep (S k) s = nstep k (step s)] holds DEFINITIONALLY (the lemma below relies
   on it).  This is the trace of model states a run visits before it halts. *)
Fixpoint nstep (k : nat) (s : Rv64i.State) : Rv64i.State :=
  match k with
  | O => s
  | S j => nstep j (Rv64i.step s)
  end.

Section Run.
  Context {BW: Bitwidth 64}.
  Context {word: word.word 64} {word_ok: word.ok word}.
  Context {Mem: map.map word Init.Byte.byte} {Mem_ok: map.ok Mem}.
  Context {Registers: map.map Z word} {Reg_ok: map.ok Registers}.

  Notation RMach := (@RiscvMachine.RiscvMachine 64 word Registers Mem).

  (* run [run1] in lockstep with [runUntil 0 _ s]: at each cycle, if the model has
     halted ([pc = 0]) stop and return the current machine; otherwise take one
     [run1] cycle (which must succeed) and recurse on [step s]. *)
  Fixpoint rrun (fuel : nat) (s : Rv64i.State) (m : RMach) : option RMach :=
    match fuel with
    | O => Some m
    | S k => if s.(Rv64i.pc) =? 0 then Some m
             else match Run.run1 RV64I m with
                  | (Some tt, m') => rrun k (Rv64i.step s) m'
                  | _ => None
                  end
    end.

  (* the per-step side conditions hold at every non-halted state of the run: at
     state [nstep k s] (for [k < fuel], not yet halted), for WHATEVER riscv machine
     [mk] is [Rrel]-related there, [WFstep] holds and the instruction is modelled.
     This is exactly the bundle [step_agrees] consumes, quantified over the run. *)
  Definition RunWF (s : Rv64i.State) (D : word -> Prop) (fuel : nat) : Prop :=
    forall k mk, (k < fuel)%nat -> (nstep k s).(Rv64i.pc) <> 0 ->
      Rrel (nstep k s) mk D ->
      WFstep (nstep k s) mk D /\
      Rv64i.decode (Rv64i.fetch32 (nstep k s)) <> Iunknown.

  (* THE forward simulation: lift [step_agrees] over a whole run by induction. *)
  Lemma transport_run : forall fuel s (m : RMach) D,
    Rrel s m D -> RunWF s D fuel ->
    exists m', rrun fuel s m = Some m' /\ Rrel (Rv64i.runUntil 0 fuel s) m' D.
  Proof.
    induction fuel as [|fuel IH]; intros s m D HR HWF.
    - (* fuel = 0: nothing to run; [runUntil 0 0 s = s]. *)
      exists m. split; [reflexivity| exact HR].
    - cbn [rrun]. destruct (s.(Rv64i.pc) =? 0) eqn:Ep.
      + (* halted: [runUntil] returns [s], [rrun] returns [m]. *)
        apply Z.eqb_eq in Ep.
        exists m. split; [reflexivity|].
        rewrite (runUntil_halt (S fuel) s Ep). exact HR.
      + (* not halted: take one [run1] cycle via [step_agrees], then recurse. *)
        apply Z.eqb_neq in Ep.
        destruct (HWF 0%nat m (Nat.lt_0_succ fuel) Ep HR) as [HWs Hni].
        destruct (step_agrees s m D HR HWs Hni) as [m1 [Hrun1 HR1]].
        assert (HWF' : RunWF (Rv64i.step s) D fuel).
        { intros k mk Hk Hpc Hrel. refine (HWF (S k) mk _ Hpc Hrel). lia. }
        destruct (IH (Rv64i.step s) m1 D HR1 HWF') as [m' [Hrm' HRR']].
        exists m'. split.
        * rewrite Hrun1. exact Hrm'.
        * rewrite (runUntil_S fuel s Ep). exact HRR'.
  Qed.

  (* the model-side result, lifted from [init_loopinv] + [loop_correct]: running
     the model from [mkInit] for [2 + (50*|inp| + 4)] steps halts in a [coreSpec]-
     correct state.  This is the first half of [core_refines] (before the fixed-
     100000-fuel restab); we reuse it as the composition target. *)
  Lemma model_result : forall inp cap, WellFormed inp cap ->
    Result (Rv64i.runUntil 0 (2 + (50 * length inp + 4))
              (mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr))) inp cap.
  Proof.
    intros inp cap HW.
    pose proof (init_loopinv inp cap HW) as HLI.
    set (init := mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr)) in *.
    pose proof (loop_correct inp cap (length inp) inp [] (Rv64i.runUntil 0 2 init)
                  (le_n _) HLI) as HR.
    rewrite <- (runUntil_add 2 (50 * length inp + 4) init) in HR.
    exact HR.
  Qed.

  (** ** The transport corollary.  The riscv-coq reference model, started in a
      machine [m] matching our [mkInit] and run with [rrun] for the model's halting
      fuel, succeeds and lands in a machine [mfin] that (a) is [Rrel]-related to the
      model's halted state, which (b) provably computes [coreSpec] -- so [mfin]'s
      PC is 0, a0 holds the spec status, a1 the spec output length, and the bridge
      [Rrel] carries the spec output bytes in [mfin]'s memory on [D]. *)
  Theorem core_refines_riscv : forall inp cap (m : RMach) D,
    WellFormed inp cap ->
    Rrel (mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr)) m D ->
    RunWF (mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr)) D
          (2 + (50 * length inp + 4)) ->
    exists mfin,
      rrun (2 + (50 * length inp + 4))
           (mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr)) m = Some mfin
      /\ Rrel (Rv64i.runUntil 0 (2 + (50 * length inp + 4))
                 (mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr))) mfin D
      /\ Result (Rv64i.runUntil 0 (2 + (50 * length inp + 4))
                  (mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr))) inp cap
      /\ word.unsigned mfin.(getPc) = 0
      /\ (forall st bs ln, coreSpec (zin inp) (Z.to_nat cap) = (st, bs, ln) ->
            map.get mfin.(getRegs) 10 = Some (word.of_Z (Z.of_nat st)) /\
            map.get mfin.(getRegs) 11 = Some (word.of_Z (Z.of_nat ln))).
  Proof.
    intros inp cap m D HW HRrel HWF.
    set (F := (2 + (50 * length inp + 4))%nat).
    set (init := mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr)) in *.
    destruct (transport_run F init m D HRrel HWF) as [mfin [Hrr HRf]].
    pose proof (model_result inp cap HW) as HRes. fold init F in HRes.
    set (f := Rv64i.runUntil 0 F init) in *.
    pose proof HRf as HRfc. destruct HRfc as (HRA & _ & HPC). destruct HPC as [Hpc _].
    exists mfin.
    split; [exact Hrr|].
    split; [exact HRf|].
    split; [exact HRes|].
    split.
    - (* PC = 0 *)
      rewrite Hpc. exact (Result_pc f inp cap HRes).
    - (* a0 = status, a1 = length *)
      intros st bs ln Hcs.
      unfold Result in HRes. rewrite Hcs in HRes. cbn beta iota in HRes.
      destruct HRes as (_ & H10 & H11 & _).
      split.
      + destruct (HRA 10 ltac:(lia)) as [Hg _]. rewrite Hg, H10. reflexivity.
      + destruct (HRA 11 ltac:(lia)) as [Hg _]. rewrite Hg, H11. reflexivity.
  Qed.

End Run.
