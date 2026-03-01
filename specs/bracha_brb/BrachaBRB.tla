---- MODULE BrachaBRB ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS
  Proc,        \* set of processes
  Values,      \* broadcast values
  Byzantine,   \* subset of Proc
  Initiator,   \* designated broadcaster
  ByzBudget    \* how many messages can the Byzantine nodes send

n == Cardinality(Proc)
t == Cardinality(Byzantine)

ASSUME
  /\ Byzantine \subseteq Proc
  /\ Initiator \in Proc
  /\ n > 3 * t

\* Symmetry set for TLC performance
Symmetry == Permutations(Proc)

(* =====Type definitions===== *)

MsgTypes == {"INIT","ECHO","READY"}
\* message payload at the protocol layer, this can be forged
Msg == [type: MsgTypes, orig: Proc, val: Values]
\* network packet, we assume the sender/receiver information cannot be forged
Packet == [from: Proc, to: Proc, payload: Msg]

(* =====Helper operators===== *)

\* Helper to treat sequence elements as a set
Range(s) == { s[i] : i \in 1..Len(s) }

\* Helper for non-faulty processes
CorrectProc == Proc \ Byzantine
Correct(p) == p \notin Byzantine

\* Helpers for checking message types given network packet
IsINIT(packet) == packet.payload.type = "INIT"
IsECHO(packet) == packet.payload.type = "ECHO"
IsREADY(packet) == packet.payload.type = "READY"

(*================PlusCal definition of Bracha's BRB algorithm================*)
(*--algorithm BrachaBRB

variables
  \* all packets/messages ever sent in the network
  messages  = {},
  \* messages processed by each process
  processed = [p \in Proc |-> {}],
  \* delivered messages, initialized as a sequence due to integrity
  delivered = [p \in Proc |-> << >>],    

define
  (*====Utility functions====*)
  INIT(orig, val)  == [ type |-> "INIT",  orig |-> orig, val |-> val ]
  ECHO(orig, val)  == [ type |-> "ECHO",  orig |-> orig, val |-> val ]
  READY(orig, val) == [ type |-> "READY", orig |-> orig, val |-> val ]

  (* operators for fetching different messages from each node's message history *)
  RecvINIT(proc) == { pkt \in processed[proc] : IsINIT(pkt) }
  RecvECHO(proc) == { pkt \in processed[proc] : IsECHO(pkt) }
  RecvREADY(proc) == { pkt \in processed[proc] : IsREADY(pkt) }
  SentREADY(proc) == { pkt \in RecvREADY(proc) : pkt.from = proc } 
  SentValue == { pkt.payload.val : pkt \in {pkt \in RecvINIT(Initiator) : pkt.from = Initiator} }
  
  (* find how many messages has a node sent *)
  SentMsgs(proc) == { pkt \in messages : pkt.from = proc }

  (* helper to check if we have received enough message from a given set *)
  RecvEnough(packets, msg, count) ==
    LET senders == { pkt.from : pkt \in { pkt \in packets : pkt.payload = msg } }
    IN 
      Cardinality(senders) > count

  (* helper to check if a pair exists in a sequence *)
  IsDelivered(orig, val, proc) ==
    \E i \in 1..Len(delivered[proc]) : 
        delivered[proc][i].orig = orig /\ delivered[proc][i].val = val

  (*====Properties====*)
  (* type invariant *)
  TypeOK ==
    /\ messages \subseteq Packet  
    /\ \A proc \in Proc :
        /\ processed[proc] \subseteq Packet
        /\ delivered[proc] \in Seq([orig: Proc, val: Values])

  (* The following properties follow the definitions in the book:
     "Fault-Tolerant Message-Passing Distributed Systems" by M. Raynal *)
  (*----------------------------------------------------------------------*)
  (* BRB-validity: If a non-faulty process delivers from a correct Initiator, 
     it must match what the Initiator actually sent. *)
  BRB_Validity == 
    \A proc \in CorrectProc :
      \A i \in 1..Len(delivered[proc]) :
        (delivered[proc][i].orig = Initiator /\ Correct(Initiator)) => 
          (delivered[proc][i].val \in SentValue)

  (* BRB-integrity: No correct process delivers a message more than once. *)
  BRB_Integrity ==
    \A proc \in CorrectProc :
      \A i, j \in 1..Len(delivered[proc]) :
        (i /= j) => (delivered[proc][i] /= delivered[proc][j])
  
  (* BRB-no-duplicity: No two non-faulty processes deliver distinct messages 
     from the same sender (even if that sender is Byzantine). *)
  BRB_NoDuplicity ==
    \A p1, p2 \in CorrectProc :
      \A m1 \in Range(delivered[p1]),  m2 \in Range(delivered[p2]) :
        (m1.orig = m2.orig) => (m1.val = m2.val)

  (* BRB-termination-1: If the sender is non-faulty, all non-faulty processes
     eventually deliver its message. *)
  BRB_Termination1 ==
    Correct(Initiator) => 
      \A proc \in CorrectProc :
        <>(\E msg \in Range(delivered[proc]) : msg.orig = Initiator /\ msg.val \in SentValue)
  
  (* BRB-termination-2: If a non-faulty process delivers a message from
     any p_i (possibly faulty), then all non-faulty processes eventually deliver from p_i. *)
  BRB_Termination2 ==
    \A p1, p2 \in CorrectProc :
      \A proc \in Proc, v \in Values :
        ([orig |-> proc, val |-> v] \in Range(delivered[p1]))
        ~> ([orig |-> proc, val |-> v] \in Range(delivered[p2])) 
end define;

(* simple broadcast macro *)
macro SendAll(proc, msg) begin
  messages := messages \union 
    { [ from |-> proc, to |-> q, payload |-> msg ] : q \in Proc };
end macro;

(* macros for the algorithm *)
macro HandleINIT(proc, pkt) begin
  with msg = pkt.payload do
    (* check that it's the FIRST time we received INIT(orig, -) *)
    if \neg (\E prev \in RecvINIT(proc) : prev.payload.orig = msg.orig) then
      SendAll(proc, ECHO(msg.orig, msg.val));
    end if;
  end with;
end macro;

macro HandleECHO(proc, pkt) begin
  with msg = pkt.payload, readyMsg = READY(msg.orig, msg.val) do
    \* we use (n+t+1)/2 because we want to round up the quorum threshold
    if RecvEnough(RecvECHO(proc), msg, (n + t + 1) \div 2) 
       /\ readyMsg \notin SentREADY(proc) then
      SendAll(proc, readyMsg);
    end if;
  end with;
end macro;

macro HandleREADY(proc, pkt) begin
  with msg = pkt.payload do
    \* condition for amplification (t + 1)
    if RecvEnough(RecvREADY(proc), msg, t) /\ msg \notin SentREADY(proc) then
      SendAll(proc, msg);
    end if;

    \* condition for delivery (2t + 1)
    if RecvEnough(RecvREADY(proc), msg, 2 * t) 
       /\ ~IsDelivered(msg.orig, msg.val, proc) then
      delivered[proc] := Append(delivered[proc], [orig |-> msg.orig, val |-> msg.val]);
    end if;
  end with;
end macro;

(* process of the correct nodes, assumes weak fairness, otherwise *)
(* it's possible for some process to never progress *) 
fair process p \in CorrectProc 
begin
  P_Init:
    \* initial step for the designated Initiator, only correct node follows it
    if self = Initiator then
      with v \in Values do
        \* choose a random value v and broadcast it
        SendAll(self, INIT(self, v));
      end with;
    end if;

  P_Loop:
    \* in single-shot BRB, nodes stop after their first "deliver"
    while Len(delivered[self]) = 0 do
      \* process any message to p that hasn't been processed yet
      with pkt \in {pkt \in messages : pkt.to = self /\ pkt \notin processed[self]} do
        processed[self] := processed[self] \union {pkt};
        \* process each message depending on its type
        if IsINIT(pkt) then
          HandleINIT(self, pkt);
        elsif IsECHO(pkt) then
          HandleECHO(self, pkt);
        elsif IsREADY(pkt) then
          HandleREADY(self, pkt);
        else
          skip; \* discard the message since it's not a valid one
        end if;
      end with;
    end while;
end process;

(* Byzantine processes *)
process b \in Byzantine
begin
  B_Loop:
    \* stop the Byzantine processes once all corrected processors have delivered
    \* or if it has sent `ByzBudget` number of messages
    while /\ \E proc \in CorrectProc : Len(delivered[proc]) = 0 
          /\ Cardinality(SentMsgs(self)) < ByzBudget do
      \* pick a random message to add to the network
      with pkt \in [ from : {self},
                     to : CorrectProc,
                     payload : Msg ] do
        messages := messages \union {pkt};
      end with;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "6949cfea" /\ chksum(tla) = "a79ea51d")
VARIABLES pc, messages, processed, delivered

(* define statement *)
INIT(orig, val)  == [ type |-> "INIT",  orig |-> orig, val |-> val ]
ECHO(orig, val)  == [ type |-> "ECHO",  orig |-> orig, val |-> val ]
READY(orig, val) == [ type |-> "READY", orig |-> orig, val |-> val ]


RecvINIT(proc) == { pkt \in processed[proc] : IsINIT(pkt) }
RecvECHO(proc) == { pkt \in processed[proc] : IsECHO(pkt) }
RecvREADY(proc) == { pkt \in processed[proc] : IsREADY(pkt) }
SentREADY(proc) == { pkt \in RecvREADY(proc) : pkt.from = proc }
SentValue == { pkt.payload.val : pkt \in {pkt \in RecvINIT(Initiator) : pkt.from = Initiator} }


SentMsgs(proc) == { pkt \in messages : pkt.from = proc }


RecvEnough(packets, msg, count) ==
  LET senders == { pkt.from : pkt \in { pkt \in packets : pkt.payload = msg } }
  IN
    Cardinality(senders) > count


IsDelivered(orig, val, proc) ==
  \E i \in 1..Len(delivered[proc]) :
      delivered[proc][i].orig = orig /\ delivered[proc][i].val = val



TypeOK ==
  /\ messages \subseteq Packet
  /\ \A proc \in Proc :
      /\ processed[proc] \subseteq Packet
      /\ delivered[proc] \in Seq([orig: Proc, val: Values])






BRB_Validity ==
  \A proc \in CorrectProc :
    \A i \in 1..Len(delivered[proc]) :
      (delivered[proc][i].orig = Initiator /\ Correct(Initiator)) =>
        (delivered[proc][i].val \in SentValue)


BRB_Integrity ==
  \A proc \in CorrectProc :
    \A i, j \in 1..Len(delivered[proc]) :
      (i /= j) => (delivered[proc][i] /= delivered[proc][j])



BRB_NoDuplicity ==
  \A p1, p2 \in CorrectProc :
    \A m1 \in Range(delivered[p1]),  m2 \in Range(delivered[p2]) :
      (m1.orig = m2.orig) => (m1.val = m2.val)



BRB_Termination1 ==
  Correct(Initiator) =>
    \A proc \in CorrectProc :
      <>(\E msg \in Range(delivered[proc]) : msg.orig = Initiator /\ msg.val \in SentValue)



BRB_Termination2 ==
  \A p1, p2 \in CorrectProc :
    \A proc \in Proc, v \in Values :
      ([orig |-> proc, val |-> v] \in Range(delivered[p1]))
      ~> ([orig |-> proc, val |-> v] \in Range(delivered[p2]))


vars == << pc, messages, processed, delivered >>

ProcSet == (CorrectProc) \cup (Byzantine)

Init == (* Global variables *)
        /\ messages = {}
        /\ processed = [p \in Proc |-> {}]
        /\ delivered = [p \in Proc |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in CorrectProc -> "P_Init"
                                        [] self \in Byzantine -> "B_Loop"]

P_Init(self) == /\ pc[self] = "P_Init"
                /\ IF self = Initiator
                      THEN /\ \E v \in Values:
                                messages' = (          messages \union
                                             { [ from |-> self, to |-> q, payload |-> (INIT(self, v)) ] : q \in Proc })
                      ELSE /\ TRUE
                           /\ UNCHANGED messages
                /\ pc' = [pc EXCEPT ![self] = "P_Loop"]
                /\ UNCHANGED << processed, delivered >>

P_Loop(self) == /\ pc[self] = "P_Loop"
                /\ IF Len(delivered[self]) = 0
                      THEN /\ \E pkt \in {pkt \in messages : pkt.to = self /\ pkt \notin processed[self]}:
                                /\ processed' = [processed EXCEPT ![self] = processed[self] \union {pkt}]
                                /\ IF IsINIT(pkt)
                                      THEN /\ LET msg == pkt.payload IN
                                                IF \neg (\E prev \in RecvINIT(self) : prev.payload.orig = msg.orig)
                                                   THEN /\ messages' = (          messages \union
                                                                        { [ from |-> self, to |-> q, payload |-> (ECHO(msg.orig, msg.val)) ] : q \in Proc })
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED messages
                                           /\ UNCHANGED delivered
                                      ELSE /\ IF IsECHO(pkt)
                                                 THEN /\ LET msg == pkt.payload IN
                                                           LET readyMsg == READY(msg.orig, msg.val) IN
                                                             IF RecvEnough(RecvECHO(self), msg, (n + t + 1) \div 2)
                                                                /\ readyMsg \notin SentREADY(self)
                                                                THEN /\ messages' = (          messages \union
                                                                                     { [ from |-> self, to |-> q, payload |-> readyMsg ] : q \in Proc })
                                                                ELSE /\ TRUE
                                                                     /\ UNCHANGED messages
                                                      /\ UNCHANGED delivered
                                                 ELSE /\ IF IsREADY(pkt)
                                                            THEN /\ LET msg == pkt.payload IN
                                                                      /\ IF RecvEnough(RecvREADY(self), msg, t) /\ msg \notin SentREADY(self)
                                                                            THEN /\ messages' = (          messages \union
                                                                                                 { [ from |-> self, to |-> q, payload |-> msg ] : q \in Proc })
                                                                            ELSE /\ TRUE
                                                                                 /\ UNCHANGED messages
                                                                      /\ IF RecvEnough(RecvREADY(self), msg, 2 * t)
                                                                            /\ ~IsDelivered(msg.orig, msg.val, self)
                                                                            THEN /\ delivered' = [delivered EXCEPT ![self] = Append(delivered[self], [orig |-> msg.orig, val |-> msg.val])]
                                                                            ELSE /\ TRUE
                                                                                 /\ UNCHANGED delivered
                                                            ELSE /\ TRUE
                                                                 /\ UNCHANGED << messages, 
                                                                                 delivered >>
                           /\ pc' = [pc EXCEPT ![self] = "P_Loop"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                           /\ UNCHANGED << messages, processed, delivered >>

p(self) == P_Init(self) \/ P_Loop(self)

B_Loop(self) == /\ pc[self] = "B_Loop"
                /\ IF /\ \E proc \in CorrectProc : Len(delivered[proc]) = 0
                      /\ Cardinality(SentMsgs(self)) < ByzBudget
                      THEN /\ \E pkt \in [ from : {self},
                                           to : CorrectProc,
                                           payload : Msg ]:
                                messages' = (messages \union {pkt})
                           /\ pc' = [pc EXCEPT ![self] = "B_Loop"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                           /\ UNCHANGED messages
                /\ UNCHANGED << processed, delivered >>

b(self) == B_Loop(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in CorrectProc: p(self))
           \/ (\E self \in Byzantine: b(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in CorrectProc : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
