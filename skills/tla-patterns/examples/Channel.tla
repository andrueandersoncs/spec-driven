---------------------------- MODULE Channel -------------------------------
(***************************************************************************)
(* Asynchronous Communication Channel                                      *)
(*                                                                         *)
(* This spec models a single-slot channel between a Sender and Receiver    *)
(* using a handshake protocol. This is the foundation of message passing   *)
(* in distributed systems.                                                 *)
(*                                                                         *)
(* The channel has three fields:                                           *)
(*   - val: the data being transmitted                                     *)
(*   - rdy: sender's flag (toggled when sending)                           *)
(*   - ack: receiver's flag (toggled when receiving)                       *)
(*                                                                         *)
(* Protocol:                                                               *)
(*   - Sender waits until rdy = ack, then sends by toggling rdy            *)
(*   - Receiver waits until rdy ≠ ack, then receives by toggling ack       *)
(*                                                                         *)
(* This is useful for modeling: message queues, API calls, event buses     *)
(***************************************************************************)
EXTENDS Naturals
CONSTANT Data
VARIABLE chan

TypeInvariant == chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]
-----------------------------------------------------------------------
Init == /\ TypeInvariant
        /\ chan.ack = chan.rdy

Send(d) ==
  (*************************************************************************)
  (* Sender action: enabled when rdy = ack (channel is "empty")            *)
  (* Sends data d by setting val and toggling the rdy bit                  *)
  (*************************************************************************)
  /\ chan.rdy = chan.ack
  /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Rcv ==
  (*************************************************************************)
  (* Receiver action: enabled when rdy ≠ ack (channel has data)            *)
  (* Receives by toggling the ack bit to match rdy                         *)
  (*************************************************************************)
  /\ chan.rdy # chan.ack
  /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next == (\E d \in Data : Send(d)) \/ Rcv

Spec == Init /\ [][Next]_chan
-----------------------------------------------------------------------
(***************************************************************************)
(* Safety Properties                                                       *)
(***************************************************************************)

\* The type invariant is always maintained
THEOREM Spec => []TypeInvariant

\* Additional property: rdy and ack only differ by at most 1 (mod 2)
\* This ensures proper alternation between sender and receiver
Alternation == (chan.rdy = chan.ack) \/ (chan.rdy = 1 - chan.ack)

=======================================================================
