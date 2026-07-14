(** * Generic-SC: the lambda-Rust-Generic machine over an event semantics

    This file implements the "lambda-Rust-Generic" (Generic-SC) rules from
    the paper, lifting a sequential event semantics ([EvSem], from
    VST.sepcomp.event_semantics) to a sequentially consistent concurrent
    machine with a lambda-Rust-style reader/writer race detector and SC
    atomic operations.

    A machine configuration is <<(tp, m, mu)>> where [tp] is a thread pool,
    [m] a CompCert memory, and [mu] a reader/writer state map.  A thread
    performs a sequential step in two phases: [Core_Try] runs the underlying
    [ev_step], _claims_ the footprint of the step's event trace in [mu], and
    installs the trace in the thread pool; [Core_Commit] releases the claim.
    A claim that overlaps with another thread's outstanding claim is
    unsatisfiable, so a racing thread is stuck between another thread's Try
    and Commit -- exactly the lambda-Rust view of non-atomic accesses as
    spanning two steps.  Atomic operations ([SC_Read], [SC_Write], the CAS
    rules) execute in a single machine step and merely check [mu].

    ** Deviations from the rules as written in the paper

    1. Memory is updated at [Core_Try], not at [Core_Commit]; there is no
       [interp]/replay.  The paper notes that for race-free programs the
       choice is immaterial and picks Commit only to align with lambda-Rust.
       Over CompCert memories the Commit choice is in fact not well-defined:
       [Mem.alloc] deterministically returns the current [nextblock], so if
       two threads Try (each recording an [Alloc] of the same fresh block)
       before either Commits, the second Commit cannot replay its trace --
       its recorded block is already taken.  Deferred replay would thus make
       perfectly race-free allocations stuck.  Race detection is unaffected
       by the change, since it lives entirely in [mu], whose claims still
       span the Try-Commit window.

    2. [claim]/[commit] act on the _footprint set_ of the whole trace rather
       than folding [incrRW]/[decrRW] over events one at a time.  A single
       sequential step emits a whole list of events and may touch the same
       byte more than once: e.g. Clight's [x = x + 1] is one corestep that
       both reads and writes [x].  Folding per event would make a thread's
       own [Write] block its own [Read] (Wst is not re-enterable), sticking
       race-free programs.  Instead the trace is treated as one combined
       access: bytes written (or allocated/freed) require [Rst 0] and become
       [Wst]; bytes only read require no writer and gain one reader.
       [commit] is the pointwise inverse (see [commit_undoes_claim]).

    3. Locations are bytes: [mu : block -> Z -> RWState], total, with
       untouched (in particular unallocated) bytes sitting at [Rst 0] --
       the counterpart of absence from the paper's partial map.  Events and
       atomic operations cover byte ranges, and atomics check every byte of
       their chunk's footprint.

    4. The paper lists [AllocEv]/[FreeEv] but only sketches [incrRW] for
       reads.  Here both count as writes: a [Free] racing with a read is a
       race, so the freed range is claimed; an [Alloc] claims its entire
       block (following [cur_perm] in event_semantics.v, which also ignores
       the [lo]/[hi] bounds), which is vacuous for other threads -- the
       block is fresh -- but keeps dead bytes uniformly at [Rst 0].

    5. There are no explicit continuations: the paper's
       [at_external(op, vs, K)] becomes [at_external] returning an external
       function plus arguments, decoded by the [decode_atomic] parameter,
       and [K[[v]]] becomes [after_external].  N.B. the paper's remark that
       "RetKind = Unit for atomic read, and RetKind = Val for atomic write"
       has the two swapped; here a read returns [Some v], a write returns
       [None] (unit), and CAS returns [Some Vtrue]/[Some Vfalse].

    6. The paper's SC-Cas-Suc does not update the memory, so a successful
       CAS would never store [v_new]; here it does ([Mem.store]).

    7. The paper's SC-Cas-Fail requires [n > 0], under which a failing CAS
       with no concurrent readers would be stuck; here it only requires
       that no non-atomic write be in progress (any [Rst n]).  The [n > 0]
       looks like a copy-paste from SC-Cas-Stuck.

    8. The core-state type [C] has no distinguished stuck state, so thread
       pool entries are [Running c T] or [StuckState], and SC_Cas_Stuck
       moves the thread to [StuckState].  Its side condition is generalized
       from "[Rst n], [n > 0]" to "some byte of the footprint is not
       [Rst 0]": a would-succeed CAS during a non-atomic _write_ is equally
       a race, and this way it is reported by the same rule rather than by
       implicit stuckness.  (The rule must exist at all because [ValEq] and
       [ValNEq] may overlap -- lambda-Rust's [lit_eq] is nondeterministic --
       and safety must not be able to escape through SC_Cas-Fail when the
       racy success branch is also enabled.)

    9. [ValEq]/[ValNEq] and [decode_atomic] are parameters of the machine,
       instantiated per language; sample C instantiations are given at the
       end of the file.  Atomic operations carry a [memory_chunk], since a
       CompCert memory access needs one (the paper's abstract locations
       hold whole values).

    10. As in the paper's Generic-SC figure (and unlike APM), there is no
        scheduler: the stepping thread is chosen nondeterministically.  The
        figure has no spawn/halt rules, so none are given here either. *)

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import List.
Import ListNotations.

Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.event_semantics.
Require Import stdpp.gmap.
Import Address Values.

(** ** Reader/writer states

    The state of one memory byte, as in lambda-Rust: [Rst n] means [n]
    threads are between Try and Commit of a step that reads the byte;
    [Wst] means some thread is mid-step on a write to it. *)

Inductive rw_state : Type :=
| Rst (n : nat)
| Wst.

Definition rw_map := gmap address rw_state.

Definition initial_rw : rw_map := ∅.

(** ** Footprints of event traces *)

(** Bytes written by an event; allocation and freeing count as writes
    (deviations 2 and 4 above). *)
Definition ev_writes (e : mem_event) (b : block) (ofs : Z) : bool :=
  match e with
  | event_semantics.Write b' ofs' bytes =>
      eq_block b' b && zle ofs' ofs && zlt ofs (ofs' + Zlength bytes)
  | event_semantics.Read _ _ _ _ => false
  | event_semantics.Alloc b' lo hi => eq_block b' b
  | event_semantics.Free l =>
      existsb (fun x => let '(b', lo, hi) := x in
                        eq_block b' b && zle lo ofs && zlt ofs hi) l
  end.

Definition ev_reads (e : mem_event) (b : block) (ofs : Z) : bool :=
  match e with
  | event_semantics.Read b' ofs' n _ =>
      eq_block b' b && zle ofs' ofs && zlt ofs (ofs' + n)
  | _ => false
  end.

Definition trace_writes (T : list mem_event) (b : block) (ofs : Z) : bool :=
  existsb (fun e => ev_writes e b ofs) T.

Definition trace_reads (T : list mem_event) (b : block) (ofs : Z) : bool :=
  existsb (fun e => ev_reads e b ofs) T.

(** ** Claiming and committing a trace

    [claim T mu mu'] is the paper's [incrRW], on the footprint of the whole
    trace: it is satisfiable only if no byte written by [T] has an
    outstanding reader or writer and no byte read by [T] has an outstanding
    writer.  [commit T mu mu'] ([decrRW]) releases the claim; its [Wst]
    requirement on written bytes is an assertion of the machine invariant,
    so a violation shows up as stuckness rather than being papered over. *)

Fixpoint change_rw_state (f : option rw_state -> option (option rw_state)) mu (b : block) (ofs : Z) n : option rw_map :=
  match n with
  | O => Some mu
  | S n' => match f (mu !! (b, ofs)) with
            | Some (Some s) => change_rw_state f (<[(b, ofs) := s]> mu) b (ofs + 1) n'
            | Some None => change_rw_state f (delete (b, ofs) mu) b (ofs + 1) n'
            | None => None
            end
  end.

Definition claim_read := change_rw_state
  (λ s, match s with Some (Rst n) => Some (Some (Rst (S n))) | _ => None end).

Definition claim_write := change_rw_state
  (λ s, match s with Some (Rst O) => Some (Some Wst) | _ => None end).

Definition claim_alloc := change_rw_state
  (λ s, match s with None => Some (Some (Rst O)) | _ => None end).

Fixpoint claim (T : list mem_event) (mu : rw_map) : option rw_map :=
  match T with
  | [] => Some mu
  | e :: es =>
      match e with
      | Read b ofs n bytes => option_bind _ _ (claim es) (claim_read mu b ofs (length bytes))
      | Write b ofs bytes => option_bind _ _ (claim es) (claim_write mu b ofs (length bytes))
      | Alloc b lo hi => option_bind _ _ (claim es) (claim_alloc mu b lo (Z.to_nat (hi - lo)))
      | Free lb => Some mu (* free happens in commit *)
      end
  end.

(*Definition claim (T : list mem_event) (mu mu' : rw_map) : Prop :=
  forall b ofs,
    if trace_writes T b ofs then mu b ofs = Rst 0 /\ mu' b ofs = Wst
    else if trace_reads T b ofs then
      exists n, mu b ofs = Rst n /\ mu' b ofs = Rst (S n)
    else mu' b ofs = mu b ofs.*)

Definition commit_read := change_rw_state
  (λ s, match s with Some (Rst (S n)) => Some (Some (Rst n)) | _ => None end).

Definition commit_write := change_rw_state
  (λ s, match s with Some Wst => Some (Some (Rst O)) | _ => None end).

Definition commit_free := change_rw_state
  (λ s, match s with Some _ => Some None | _ => None end).

Fixpoint commit (T : list mem_event) (mu : rw_map) : option rw_map :=
  match T with
  | [] => Some mu
  | e :: es =>
      match e with
      | Read b ofs n bytes => option_bind _ _ (commit es) (commit_read mu b ofs (length bytes))
      | Write b ofs bytes => option_bind _ _ (commit es) (commit_write mu b ofs (length bytes))
      | Alloc b lo hi => Some mu (* alloc happens in claim *)
      | Free lb => option_bind _ _ (commit es)
          (foldr (λ '(b, lo, hi) o, match o with
             | Some mu => commit_free mu b lo (Z.to_nat (hi - lo))
             | None => None end) (Some mu) lb)
      end
  end.

(*Definition commit (T : list mem_event) (mu mu' : rw_map) : Prop :=
  forall b ofs,
    if trace_writes T b ofs then mu b ofs = Wst /\ mu' b ofs = Rst 0
    else if trace_reads T b ofs then
      exists n, mu b ofs = Rst (S n) /\ mu' b ofs = Rst n
    else mu' b ofs = mu b ofs.*)

(** Sanity check: with no interference in between, Commit restores the
    reader/writer map that Try started from. *)
Definition is_read_or_write e :=
  match e with Read _ _ _ _ | Write _ _ _ => true | _ => false end.

Lemma commit_undoes_claim : forall T mu mu' mu'',
  Forall is_read_or_write T ->
  claim T mu = Some mu' -> commit T mu' = Some mu'' ->
  forall l, mu'' !! l = mu !! l.
Proof.
  intros T mu mu' mu'' Hrw Hclaim Hcommit l.
  induction Hrw in mu', mu'', Hclaim, Hcommit |- *; simpl in *.
  - inv Hclaim. done.
  - destruct x eqn: Hx; try done.
    + destruct claim_write eqn: Hclaimx; inv Hclaim.
      admit. (* prove something about claim_write and commit_write *)
    + admit.
Admitted.

(** ** Atomic operations

    How the underlying language phrases atomic operations as external
    calls is a parameter of the machine ([decode_atomic] below); this is
    their common shape.  Each operation carries the [memory_chunk] it
    accesses. *)

Inductive atomic_op : Type :=
| ALoad (chunk : memory_chunk) (b : block) (ofs : Z)
| AStore (chunk : memory_chunk) (b : block) (ofs : Z) (v : val)
| ACAS (chunk : memory_chunk) (b : block) (ofs : Z) (v_exp v_new : val).

Section GenericSC.

Context {C : Type}.

(** The single-threaded input semantics. *)
Variable sem : @EvSem C.

(** Recognizes the external calls that are this machine's atomic
    operations; all other external calls are outside the machine's scope
    (no rule applies). *)
Variable decode_atomic : external_function -> list val -> option atomic_op.

(** Value (in)equality for CAS, relative to a memory.  In C both are
    deterministic and mutually exclusive (see [c_ValEq]/[c_ValNEq] below);
    in lambda-Rust comparisons involving dangling pointers make them
    overlap, which is what forces the explicit SC_Cas_Stuck rule. *)
Variable ValEq ValNEq : mem -> val -> val -> Prop.

(** ** Thread pools *)

Inductive tstate : Type :=
| Running (c : C) (T : list mem_event)
| StuckState.

Definition tpool := nat -> option tstate.

Definition upd_tp (tp : tpool) (i : nat) (st : tstate) : tpool :=
  fun j => if Nat.eq_dec j i then Some st else tp j.

Definition initial_tp (c : C) : tpool :=
  fun i => if Nat.eq_dec i O then Some (Running c []) else None.

(** [mu] conditions on the byte range of an atomic access *)

(** No non-atomic write in progress anywhere in the range (paper: mu(l) = Rst n). *)
Definition no_writer (mu : rw_map) (b : block) (ofs len : Z) : Prop :=
  forall o, ofs <= o < ofs + len -> mu b o <> Wst.

(** No non-atomic access at all in progress in the range (paper: mu(l) = Rst 0). *)
Definition unclaimed (mu : rw_map) (b : block) (ofs len : Z) : Prop :=
  forall o, ofs <= o < ofs + len -> mu b o = Rst 0.

(** ** The machine *)

Inductive step : tpool -> mem -> rw_map -> tpool -> mem -> rw_map -> Prop :=

| Core_Try : forall tp m mu i c T c' m' mu'
    (Hget : tp i = Some (Running c []))
    (Hstep : ev_step sem c m T c' m')
    (Hclaim : claim T mu mu'),
    step tp m mu (upd_tp tp i (Running c' T)) m' mu'

| Core_Commit : forall tp m mu i c T mu'
    (Hget : tp i = Some (Running c T))
    (Hne : T <> [])
    (Hcommit : commit T mu mu'),
    step tp m mu (upd_tp tp i (Running c [])) m mu'

| SC_Read : forall tp m mu i c ef args chunk b ofs v c'
    (Hget : tp i = Some (Running c []))
    (Hext : at_external sem c m = Some (ef, args))
    (Hdec : decode_atomic ef args = Some (ALoad chunk b ofs))
    (Hmu : no_writer mu b ofs (size_chunk chunk))
    (Hload : Mem.load chunk m b ofs = Some v)
    (Hret : after_external sem (Some v) c m = Some c'),
    step tp m mu (upd_tp tp i (Running c' [])) m mu

| SC_Write : forall tp m mu i c ef args chunk b ofs v m' c'
    (Hget : tp i = Some (Running c []))
    (Hext : at_external sem c m = Some (ef, args))
    (Hdec : decode_atomic ef args = Some (AStore chunk b ofs v))
    (Hmu : unclaimed mu b ofs (size_chunk chunk))
    (Hstore : Mem.store chunk m b ofs v = Some m')
    (Hret : after_external sem None c m' = Some c'),
    step tp m mu (upd_tp tp i (Running c' [])) m' mu

| SC_Cas_Suc : forall tp m mu i c ef args chunk b ofs v_exp v_new v_cur m' c'
    (Hget : tp i = Some (Running c []))
    (Hext : at_external sem c m = Some (ef, args))
    (Hdec : decode_atomic ef args = Some (ACAS chunk b ofs v_exp v_new))
    (Hmu : unclaimed mu b ofs (size_chunk chunk))
    (Hload : Mem.load chunk m b ofs = Some v_cur)
    (Heq : ValEq m v_cur v_exp)
    (Hstore : Mem.store chunk m b ofs v_new = Some m')
    (Hret : after_external sem (Some Vtrue) c m' = Some c'),
    step tp m mu (upd_tp tp i (Running c' [])) m' mu

| SC_Cas_Fail : forall tp m mu i c ef args chunk b ofs v_exp v_new v_cur c'
    (Hget : tp i = Some (Running c []))
    (Hext : at_external sem c m = Some (ef, args))
    (Hdec : decode_atomic ef args = Some (ACAS chunk b ofs v_exp v_new))
    (Hmu : no_writer mu b ofs (size_chunk chunk))
    (Hload : Mem.load chunk m b ofs = Some v_cur)
    (Hneq : ValNEq m v_cur v_exp)
    (Hret : after_external sem (Some Vfalse) c m = Some c'),
    step tp m mu (upd_tp tp i (Running c' [])) m mu

| SC_Cas_Stuck : forall tp m mu i c ef args chunk b ofs v_exp v_new v_cur o
    (Hget : tp i = Some (Running c []))
    (Hext : at_external sem c m = Some (ef, args))
    (Hdec : decode_atomic ef args = Some (ACAS chunk b ofs v_exp v_new))
    (Hload : Mem.load chunk m b ofs = Some v_cur)
    (Heq : ValEq m v_cur v_exp)
    (Ho : ofs <= o < ofs + size_chunk chunk)
    (Hmu : mu b o <> Rst 0),
    step tp m mu (upd_tp tp i StuckState) m mu.

End GenericSC.

(** ** Sample C instantiation of the parameters

    Atomics are word-sized here for concreteness; a real Clight
    instantiation would read the chunk off the external function's
    signature. *)

Local Open Scope string_scope.

Definition c_decode_atomic (ef : external_function) (args : list val)
  : option atomic_op :=
  match ef, args with
  | EF_external "atomic_load" _, [Vptr b ofs] =>
      Some (ALoad Mint32 b (Ptrofs.unsigned ofs))
  | EF_external "atomic_store" _, [Vptr b ofs; v] =>
      Some (AStore Mint32 b (Ptrofs.unsigned ofs) v)
  | EF_external "atomic_CAS" _, [Vptr b ofs; v_exp; v_new] =>
      Some (ACAS Mint32 b (Ptrofs.unsigned ofs) v_exp v_new)
  | _, _ => None
  end.

(** In C, value comparison is deterministic ([c_ValEq] and [c_ValNEq] are
    mutually exclusive), so SC_Cas_Fail and SC_Cas_Stuck never overlap; a
    comparison that CompCert leaves undefined (e.g. on [Vundef]) satisfies
    neither, and the CAS is stuck with no rule applying. *)

Definition c_ValEq (m : mem) (v1 v2 : val) : Prop :=
  Val.cmpu_bool (Mem.valid_pointer m) Ceq v1 v2 = Some true.

Definition c_ValNEq (m : mem) (v1 v2 : val) : Prop :=
  Val.cmpu_bool (Mem.valid_pointer m) Ceq v1 v2 = Some false.
