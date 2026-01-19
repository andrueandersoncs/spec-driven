------------------------------- MODULE TwoPhase -----------------------------
(***************************************************************************)
(* Two-Phase Commit Protocol                                               *)
(*                                                                         *)
(* This specification describes how a Transaction Manager (TM) coordinates *)
(* Resource Managers (RMs) to achieve atomic commit. This is the standard  *)
(* protocol used in distributed databases and microservices.               *)
(*                                                                         *)
(* Phase 1 (Prepare): TM asks all RMs if they can commit                   *)
(* Phase 2 (Commit/Abort): TM tells all RMs the final decision             *)
(*                                                                         *)
(* Key insight: This spec shows that 2PC IMPLEMENTS TCommit - it achieves  *)
(* the safety property that all RMs agree on the outcome.                  *)
(***************************************************************************)
CONSTANT RM \* The set of resource managers

VARIABLES
  rmState,       \* rmState[rm] is the state of resource manager rm.
  tmState,       \* The state of the transaction manager.
  tmPrepared,    \* The set of RMs from which the TM has received "Prepared"
  msgs           \* The set of all messages that have been sent.

Message ==
  (*************************************************************************)
  (* The set of all possible messages.                                     *)
  (* - "Prepared" messages: RM -> TM (I'm ready to commit)                 *)
  (* - "Commit"/"Abort" messages: TM -> all RMs (final decision)           *)
  (*************************************************************************)
  [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]

TPTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Message

TPInit ==
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ msgs = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* Transaction Manager Actions                                             *)
(***************************************************************************)
TMRcvPrepared(rm) ==
  (*************************************************************************)
  (* The TM receives a "Prepared" message from resource manager rm.        *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit ==
  (*************************************************************************)
  (* The TM commits the transaction; enabled iff the TM is in its initial  *)
  (* state and every RM has sent a "Prepared" message.                     *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort ==
  (*************************************************************************)
  (* The TM spontaneously aborts the transaction.                          *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Resource Manager Actions                                                *)
(***************************************************************************)
RMPrepare(rm) ==
  (*************************************************************************)
  (* Resource manager rm prepares (votes YES).                             *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared>>

RMChooseToAbort(rm) ==
  (*************************************************************************)
  (* Resource manager rm spontaneously decides to abort (votes NO).        *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvCommitMsg(rm) ==
  (*************************************************************************)
  (* Resource manager rm is told by the TM to commit.                      *)
  (*************************************************************************)
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvAbortMsg(rm) ==
  (*************************************************************************)
  (* Resource manager rm is told by the TM to abort.                       *)
  (*************************************************************************)
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

-----------------------------------------------------------------------------
TPNext ==
  \/ TMCommit \/ TMAbort
  \/ \E rm \in RM :
       TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
         \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)

TPSpec == TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, msgs>>
  (*************************************************************************)
  (* The complete spec of the Two-Phase Commit protocol.                   *)
  (*************************************************************************)

THEOREM TPSpec => []TPTypeOK
  (*************************************************************************)
  (* This theorem asserts that the type-correctness predicate TPTypeOK is  *)
  (* an invariant of the specification.                                    *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now assert that Two-Phase Commit implements Transaction Commit.      *)
(* This is a REFINEMENT: 2PC is a correct implementation of TCommit.       *)
(***************************************************************************)
TC == INSTANCE TCommit

THEOREM TPSpec => TC!TCSpec
  (*************************************************************************)
  (* This theorem asserts that the specification TPSpec of the Two-Phase   *)
  (* Commit protocol implements the specification TCSpec of the            *)
  (* Transaction Commit protocol.                                          *)
  (*************************************************************************)
=============================================================================
