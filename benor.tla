     ------------- MODULE benor --------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT N, F, MAXROUND, INPUT
ASSUME /\ F < N
Procs == 1..N
 
(*
        --fair algorithm benor
{ 
    \* P1Msg to store all the report messages from phase 1
    \* P2Msg to store all the proposal messages from phase 2
    variable p1Msg={}, p2Msg={}, input = INPUT;
    
    fair process (p \in Procs) \* For all the processes p
    variable decided = -1, r = 1, p1v = input[self], p2v = -1;
    {
        S: while(r <= MAXROUND /\ decided = -1)
        {
            
            \* Label PH1a - Sends report messages to all the nodes
            PH1a: {
                    p1Msg := p1Msg \union {[nodeid |-> self, round |-> r, value |-> p1v]};
                  };
            
            
            \* Label PH1b - Waits for Report messages and based on that sends propose messages
            PH1b: {
            
                    \* Wait for atleast N-F report messages
                    await Cardinality({msg \in p1Msg: msg.round=r}) >= N-F;
                    
                    \* If there are atleast N/2 report messages with value = 0, then send propose messeges with value 0
                    if(Cardinality({msg \in p1Msg: (msg.value=0) /\ (msg.round=r)}) > N \div 2)
                    {
                        p2Msg := p2Msg \union {[nodeid |-> self, round |-> r, value |-> 0]};
                    }
                    else
                        \* If there are atleast N/2 report messages with value = 1, then send propose messeges with value 1
                        if(Cardinality({msg \in p1Msg: (msg.value=1) /\ (msg.round=r)}) > N \div 2)
                        {
                            p2Msg := p2Msg \union {[nodeid |-> self, round |-> r, value |-> 1]};
                        }
                        else
                            \* Else send propose messeges with value -1
                            {
                                p2Msg := p2Msg \union {[nodeid |-> self, round |-> r, value |-> -1]};
                            }
                 };
            
            
            \* Label PH2 - Waits for Proposal messages and based on that either decides a value or moves to next iteration
            PH2: {
            
                    \* Wait for atleast N-F proposal messages
                    await Cardinality({msg \in p2Msg: msg.round=r}) >= N-F;
            
            
                    \* If there are atleast F+1 proposal messages with value = 0, then decide value 0 
                    if(Cardinality({msg \in p2Msg: (msg.value=0) /\ (msg.round=r)}) >= F+1)
                    {
                        decided := 0;
                    }
                    else
                        \* If there are atleast F+1 proposal messages with value = 1, then decide value 1
                        if(Cardinality({msg \in p2Msg: (msg.value=1) /\ (msg.round=r)}) >= F+1)
                        {
                            decided := 1;
                        }
                        else
                            \* If there is atleast 1 proposal messages with value = 0, 
                            \* then set 0 as the initial value for the next iteration
                            if(Cardinality({msg \in p2Msg: (msg.value=0) /\ (msg.round=r)}) >= 1)
                            {
                                p2v := 0;
                                p1v := p2v;
                            }
                            else
                                \* If there is atleast 1 proposal messages with value = 1, 
                                \* then set 1 as the initial value for the next iteration   
                                if(Cardinality({msg \in p2Msg: (msg.value=1) /\ (msg.round=r)}) >= 1)
                                {
                                    p2v := 1;
                                    p1v := p2v;
                                }
                                else
                                 \* Else randomly select between 0 or 1 and set the selected value
                                 \*  as the initial value for the next iteration
                                {
                                    with(i \in{0,1})
                                    {
                                        p2v := i;
                                        p1v := p2v;
                                    }
                                }
                };
                
                r := r+1; \* Increment round number
        };
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES p1Msg, p2Msg, input, pc, decided, r, p1v, p2v

vars == << p1Msg, p2Msg, input, pc, decided, r, p1v, p2v >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ p1Msg = {}
        /\ p2Msg = {}
        /\ input = INPUT
        (* Process p *)
        /\ decided = [self \in Procs |-> -1]
        /\ r = [self \in Procs |-> 1]
        /\ p1v = [self \in Procs |-> input[self]]
        /\ p2v = [self \in Procs |-> -1]
        /\ pc = [self \in ProcSet |-> "S"]

S(self) == /\ pc[self] = "S"
           /\ IF r[self] <= MAXROUND /\ decided[self] = -1
                 THEN /\ pc' = [pc EXCEPT ![self] = "PH1a"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << p1Msg, p2Msg, input, decided, r, p1v, p2v >>

PH1a(self) == /\ pc[self] = "PH1a"
              /\ p1Msg' = (p1Msg \union {[nodeid |-> self, round |-> r[self], value |-> p1v[self]]})
              /\ pc' = [pc EXCEPT ![self] = "PH1b"]
              /\ UNCHANGED << p2Msg, input, decided, r, p1v, p2v >>

PH1b(self) == /\ pc[self] = "PH1b"
              /\ Cardinality({msg \in p1Msg: msg.round=r[self]}) >= N-F
              /\ IF Cardinality({msg \in p1Msg: (msg.value=0) /\ (msg.round=r[self])}) > N \div 2
                    THEN /\ p2Msg' = (p2Msg \union {[nodeid |-> self, round |-> r[self], value |-> 0]})
                    ELSE /\ IF Cardinality({msg \in p1Msg: (msg.value=1) /\ (msg.round=r[self])}) > N \div 2
                               THEN /\ p2Msg' = (p2Msg \union {[nodeid |-> self, round |-> r[self], value |-> 1]})
                               ELSE /\ p2Msg' = (p2Msg \union {[nodeid |-> self, round |-> r[self], value |-> -1]})
              /\ pc' = [pc EXCEPT ![self] = "PH2"]
              /\ UNCHANGED << p1Msg, input, decided, r, p1v, p2v >>

PH2(self) == /\ pc[self] = "PH2"
             /\ Cardinality({msg \in p2Msg: msg.round=r[self]}) >= N-F
             /\ IF Cardinality({msg \in p2Msg: (msg.value=0) /\ (msg.round=r[self])}) >= F+1
                   THEN /\ decided' = [decided EXCEPT ![self] = 0]
                        /\ UNCHANGED << p1v, p2v >>
                   ELSE /\ IF Cardinality({msg \in p2Msg: (msg.value=1) /\ (msg.round=r[self])}) >= F+1
                              THEN /\ decided' = [decided EXCEPT ![self] = 1]
                                   /\ UNCHANGED << p1v, p2v >>
                              ELSE /\ IF Cardinality({msg \in p2Msg: (msg.value=0) /\ (msg.round=r[self])}) >= 1
                                         THEN /\ p2v' = [p2v EXCEPT ![self] = 0]
                                              /\ p1v' = [p1v EXCEPT ![self] = p2v'[self]]
                                         ELSE /\ IF Cardinality({msg \in p2Msg: (msg.value=1) /\ (msg.round=r[self])}) >= 1
                                                    THEN /\ p2v' = [p2v EXCEPT ![self] = 1]
                                                         /\ p1v' = [p1v EXCEPT ![self] = p2v'[self]]
                                                    ELSE /\ \E i \in {0,1}:
                                                              /\ p2v' = [p2v EXCEPT ![self] = i]
                                                              /\ p1v' = [p1v EXCEPT ![self] = p2v'[self]]
                                   /\ UNCHANGED decided
             /\ r' = [r EXCEPT ![self] = r[self]+1]
             /\ pc' = [pc EXCEPT ![self] = "S"]
             /\ UNCHANGED << p1Msg, p2Msg, input >>

p(self) == S(self) \/ PH1a(self) \/ PH1b(self) \/ PH2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Agreement == (\A j,k \in Procs: decided[j] # -1 /\ decided[k] # -1 => decided[j]=decided[k])

Progress  == <> (\A j \in Procs: decided[j] # -1 => decided[j] \in {0,1})

BaitProgress == (\E j \in Procs: decided[j] = -1)

MinorityReport == (\A j \in Procs: decided[j] # 0)

====