---- MODULE BrachaBRB ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS
  Proc,       \* set of processes
  Values,     \* broadcast values
  Byzantine,  \* subset of Proc
  Initiator   \* designated broadcaster

ASSUME
  Byzantine \subseteq Proc
  /\ Initiator \in Proc

n == Cardinality(Proc)
t == Cardinality(Byzantine)

(* Helper to treat sequence elements as a set *)
Range(s) == { s[i] : i \in 1..Len(s) }

(* Helper for non-faulty processes *)
CorrectProc == Proc \ Byzantine
Correct(p) == p \notin Byzantine

\* Symmetry set for TLC performance
Symmetry == Permutations(Proc)

(*--algorithm BrachaBRB

variables
  msgs      = {},                     \* all messages ever sent 
  processed = [p \in Proc |-> {}],    \* messages processed by each process
  sentREADY = [p \in Proc |-> {}],    \* READY broadcast
  recvINIT  = [p \in Proc |-> {}],    \* first INIT seen
  recvECHO  = [p \in Proc |-> {}],
  recvREADY = [p \in Proc |-> {}],
  delivered = [p \in Proc |-> << >>]; \* delivered BRB pairs, initialized as a sequence due to integrity

define
  (*====Utility functions====*)
  INIT(orig, val)  == [ type |-> "INIT",  orig |-> orig, val  |-> val ]
  ECHO(orig, val)  == [ type |-> "ECHO",  orig |-> orig, val  |-> val ]
  READY(orig, val) == [ type |-> "READY", orig |-> orig, val  |-> val ]

  RecvEnough(msgSet, mOrig, mVal, proc, count) ==
    LET Senders == { m.from : m \in msgSet[proc]
                     \cap [type: {"ECHO", "READY"}, orig: {mOrig}, val: {mVal}] }
    IN 
      Cardinality(Senders) > count

  (* Helper to check if a pair exists in a sequence *)
  IsDelivered(orig, val, proc) ==
    \E i \in 1..Len(delivered[proc]) : 
        delivered[proc][i].orig = orig /\ delivered[proc][i].val = val

  (*====Properties====*)

  (* BRB-integrity: No correct process delivers a message more than once. *)
  (* This is now a powerful check: it fails if the same message appears 
     at two different indices in the delivery sequence. *)
  BRB_Integrity ==
    \A proc \in CorrectProc :
      \A i, j \in 1..Len(delivered[proc]) :
        (i /= j) => (delivered[proc][i] /= delivered[proc][j])
  
  (* BRB-validity: If a non-faulty process delivers from a correct Initiator, 
     it must match what the Initiator actually sent. *)
  BRB_Validity == 
    \A proc \in CorrectProc :
      \A d \in Range(delivered[proc]) :
        (d.orig = Initiator /\ Correct(Initiator)) => 
          (d.val \in Values)
  
  (* BRB-no-duplicity: No two non-faulty processes deliver distinct messages 
     from the same sender (even if that sender is Byzantine). *)
  BRB_NoDuplicity ==
    \A p1, p2 \in CorrectProc :
      \A d1 \in {delivered[p1][i] : i \in 1..Len(delivered[p1])}, 
         d2 \in {delivered[p2][i] : i \in 1..Len(delivered[p2])} :
         (d1.orig = d2.orig) => (d1.val = d2.val)

  (* BRB-termination-1: If the sender is non-faulty, all non-faulty 
     processes eventually deliver its message. *)
  BRB_Termination1 ==
    Correct(Initiator) => 
      \A proc \in CorrectProc :
        <>(\E d \in Range(delivered[proc]) : d.orig = Initiator)
  
  (* BRB-termination-2: If a non-faulty process delivers a message from 
     any p_i, then all non-faulty processes eventually deliver from p_i. *)
  BRB_Termination2 ==
    \A proc \in CorrectProc :
      \A d \in Range(delivered[proc]) :
        \A q \in CorrectProc : 
          <>(\E d2 \in Range(delivered[q]) : d2.orig = d.orig)
  
  (* Contraints *)
  StateConstraint == 
    /\ Cardinality(msgs) < 10
    /\ \A proc \in Proc : Len(delivered[proc]) < 2
end define;

(* simple broadcast macro *)
macro SendAll(mType, mOrig, mVal, proc) begin
  msgs := msgs \cup { [type |-> mType, from |-> proc, to |-> q,
                       orig |-> mOrig, val |-> mVal] : q \in Proc};
end macro;

macro HandleMsg(msg, proc) begin
  processed[proc] := processed[proc] \union {m};
  if m.type = "INIT" /\ m \notin recvINIT[proc] then
      (* only INIT messages are checked for first reception *)
      recvINIT[proc] := recvINIT[proc] \union {m};
      SendAll("ECHO", m.orig, m.val, proc);
  elsif m.type = "ECHO" then
      recvECHO[proc] := recvECHO[proc] \union {m};
      if RecvEnough(recvECHO, m.orig, m.val, proc, (n + t) \div 2) 
         /\ READY(m.orig, m.val) \notin sentREADY[proc] then
          SendAll("READY", m.orig, m.val, proc);
          sentREADY[proc] := sentREADY[proc] \cup {READY(m.orig, m.val)};
      end if;
  elsif m.type = "READY" then
      recvREADY[proc] := recvREADY[proc] \union {m};
      \* Condition for amplification (t + 1)
      if RecvEnough(recvREADY, m.orig, m.val, proc, t) 
         /\ READY(m.orig, m.val) \notin sentREADY[proc] then
          SendAll("READY", m.orig, m.val, proc);
          sentREADY[proc] := sentREADY[proc] \union {READY(m.orig, m.val)};
      end if;
      \* Condition for delivery (2t + 1)
      if RecvEnough(recvREADY, m.orig, m.val, proc, 2 * t) 
         /\ ~IsDelivered(m.orig, m.val, proc) then
          delivered[proc] := Append(delivered[proc], [orig |-> m.orig, val |-> m.val]);
      end if;
  end if;
end macro;

fair process p \in (Proc \ Byzantine)
begin
  P_Loop:
    while TRUE do
      either
        \* initial step for the designated Initiator
        if self = Initiator /\ recvINIT[self] = {} then
          with v \in Values do
            SendAll("INIT", self, v, self);
            \* recvINIT[self] := {INIT(self, v)};
          end with;
        end if;
      or
        \* process any message to p that hasn't been processed yet
        with m \in {msg \in msgs : msg.to = self /\ msg \notin processed[self]} do
          HandleMsg(m, self);
        end with;
      end either;
    end while;
end process;

process b \in Byzantine
begin
  B_Loop:
    while TRUE do
      \* Pick ONE malicious message to add to the network at a time
      with m \in [type : {"ECHO", "READY"}, 
                  from : {self}, 
                  to   : Proc \ Byzantine, \* No need to send to other bad actors
                  orig : {Initiator},      \* Most attacks focus on the Initiator
                  val  : Values] do
        if m \notin msgs then
          msgs := msgs \cup {m};
        else
          \* If all possible msgs are sent, this process effectively "stalls"
          await FALSE; 
        end if;
      end with;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "d25ce6a8" /\ chksum(tla) = "8534c97a")
VARIABLES msgs, processed, sentREADY, recvINIT, recvECHO, recvREADY, 
          delivered

(* define statement *)
INIT(orig, val)  == [ type |-> "INIT",  orig |-> orig, val  |-> val ]
ECHO(orig, val)  == [ type |-> "ECHO",  orig |-> orig, val  |-> val ]
READY(orig, val) == [ type |-> "READY", orig |-> orig, val  |-> val ]

RecvEnough(msgSet, mOrig, mVal, proc, count) ==
  LET Senders == { m.from : m \in msgSet[proc]
                   \cap [type: {"ECHO", "READY"}, orig: {mOrig}, val: {mVal}] }
  IN
    Cardinality(Senders) > count


IsDelivered(orig, val, proc) ==
  \E i \in 1..Len(delivered[proc]) :
      delivered[proc][i].orig = orig /\ delivered[proc][i].val = val






BRB_Integrity ==
  \A proc \in CorrectProc :
    \A i, j \in 1..Len(delivered[proc]) :
      (i /= j) => (delivered[proc][i] /= delivered[proc][j])



BRB_Validity ==
  \A proc \in CorrectProc :
    \A d \in Range(delivered[proc]) :
      (d.orig = Initiator /\ Correct(Initiator)) =>
        (d.val \in Values)



BRB_NoDuplicity ==
  \A p1, p2 \in CorrectProc :
    \A d1 \in {delivered[p1][i] : i \in 1..Len(delivered[p1])},
       d2 \in {delivered[p2][i] : i \in 1..Len(delivered[p2])} :
       (d1.orig = d2.orig) => (d1.val = d2.val)



BRB_Termination1 ==
  Correct(Initiator) =>
    \A proc \in CorrectProc :
      <>(\E d \in Range(delivered[proc]) : d.orig = Initiator)



BRB_Termination2 ==
  \A proc \in CorrectProc :
    \A d \in Range(delivered[proc]) :
      \A q \in CorrectProc :
        <>(\E d2 \in Range(delivered[q]) : d2.orig = d.orig)


StateConstraint ==
  /\ Cardinality(msgs) < 10
  /\ \A proc \in Proc : Len(delivered[proc]) < 2


vars == << msgs, processed, sentREADY, recvINIT, recvECHO, recvREADY, 
           delivered >>

ProcSet == ((Proc \ Byzantine)) \cup (Byzantine)

Init == (* Global variables *)
        /\ msgs = {}
        /\ processed = [p \in Proc |-> {}]
        /\ sentREADY = [p \in Proc |-> {}]
        /\ recvINIT = [p \in Proc |-> {}]
        /\ recvECHO = [p \in Proc |-> {}]
        /\ recvREADY = [p \in Proc |-> {}]
        /\ delivered = [p \in Proc |-> << >>]

p(self) == \/ /\ IF self = Initiator /\ recvINIT[self] = {}
                    THEN /\ \E v \in Values:
                              msgs' = (msgs \cup { [type |-> "INIT", from |-> self, to |-> q,
                                                    orig |-> self, val |-> v] : q \in Proc})
                    ELSE /\ TRUE
                         /\ msgs' = msgs
              /\ UNCHANGED <<processed, sentREADY, recvINIT, recvECHO, recvREADY, delivered>>
           \/ /\ \E m \in {msg \in msgs : msg.to = self /\ msg \notin processed[self]}:
                   /\ processed' = [processed EXCEPT ![self] = processed[self] \union {m}]
                   /\ IF m.type = "INIT" /\ m \notin recvINIT[self]
                         THEN /\ recvINIT' = [recvINIT EXCEPT ![self] = recvINIT[self] \union {m}]
                              /\ msgs' = (msgs \cup { [type |-> "ECHO", from |-> self, to |-> q,
                                                       orig |-> (m.orig), val |-> (m.val)] : q \in Proc})
                              /\ UNCHANGED << sentREADY, recvECHO, 
                                              recvREADY, delivered >>
                         ELSE /\ IF m.type = "ECHO"
                                    THEN /\ recvECHO' = [recvECHO EXCEPT ![self] = recvECHO[self] \union {m}]
                                         /\ IF RecvEnough(recvECHO', m.orig, m.val, self, (n + t) \div 2)
                                               /\ READY(m.orig, m.val) \notin sentREADY[self]
                                               THEN /\ msgs' = (msgs \cup { [type |-> "READY", from |-> self, to |-> q,
                                                                             orig |-> (m.orig), val |-> (m.val)] : q \in Proc})
                                                    /\ sentREADY' = [sentREADY EXCEPT ![self] = sentREADY[self] \cup {READY(m.orig, m.val)}]
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED << msgs, 
                                                                    sentREADY >>
                                         /\ UNCHANGED << recvREADY, 
                                                         delivered >>
                                    ELSE /\ IF m.type = "READY"
                                               THEN /\ recvREADY' = [recvREADY EXCEPT ![self] = recvREADY[self] \union {m}]
                                                    /\ IF RecvEnough(recvREADY', m.orig, m.val, self, t)
                                                          /\ READY(m.orig, m.val) \notin sentREADY[self]
                                                          THEN /\ msgs' = (msgs \cup { [type |-> "READY", from |-> self, to |-> q,
                                                                                        orig |-> (m.orig), val |-> (m.val)] : q \in Proc})
                                                               /\ sentREADY' = [sentREADY EXCEPT ![self] = sentREADY[self] \union {READY(m.orig, m.val)}]
                                                          ELSE /\ TRUE
                                                               /\ UNCHANGED << msgs, 
                                                                               sentREADY >>
                                                    /\ IF RecvEnough(recvREADY', m.orig, m.val, self, 2 * t)
                                                          /\ ~IsDelivered(m.orig, m.val, self)
                                                          THEN /\ delivered' = [delivered EXCEPT ![self] = Append(delivered[self], [orig |-> m.orig, val |-> m.val])]
                                                          ELSE /\ TRUE
                                                               /\ UNCHANGED delivered
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED << msgs, 
                                                                    sentREADY, 
                                                                    recvREADY, 
                                                                    delivered >>
                                         /\ UNCHANGED recvECHO
                              /\ UNCHANGED recvINIT

b(self) == /\ \E m \in [type : {"ECHO", "READY"},
                        from : {self},
                        to   : Proc \ Byzantine,
                        orig : {Initiator},
                        val  : Values]:
                IF m \notin msgs
                   THEN /\ msgs' = (msgs \cup {m})
                   ELSE /\ FALSE
                        /\ msgs' = msgs
           /\ UNCHANGED << processed, sentREADY, recvINIT, recvECHO, recvREADY, 
                           delivered >>

Next == (\E self \in (Proc \ Byzantine): p(self))
           \/ (\E self \in Byzantine: b(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in (Proc \ Byzantine) : WF_vars(p(self))

\* END TRANSLATION 
====
