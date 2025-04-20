---- MODULE wirelockordered ----
EXTENDS TLC, Integers, Sequences
CONSTANT NULL

People == {1, 2}
Money == 1..10
NumTransfers == 2

(* --algorithm wire
variables
  acct \in [People -> Money];
  lock \in [People ->{NULL}];

define
  NoOverdrafts ==
    \A p \in People:
      acct[p] >= 0
end define;

process wire \in 1..NumTransfers
variable
  amnt \in 1..5;
  from \in People;
  to \in People;
  first \in People;
  second \in People;

begin
  CheckSelf:
  if from /= to then
      
    SetLockOrder:
        if from < to then
            first := from;
            second := to;
        else
            first := to;
            second := from;
        end if;
        
    GetLockTo:
        await lock[first] = NULL;
        lock[first] := self;
    GetLockFrom:
        await lock[second] = NULL;
        lock[second] := self;

    Check:
        if acct[from] >= amnt then
        Withdraw:
            acct[from] := acct[from] - amnt;
        Deposit:
            acct[to] := acct[to] + amnt;
        end if;

    ReleaseLockTo:
        assert lock[first] = self;
        lock[first] := NULL; 
    ReleaseLockFrom:
        assert lock[second] = self;
        lock[second] := NULL; 
    end if;
      
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "3805bdd6" /\ chksum(tla) = "28239359")
VARIABLES pc, acct, lock

(* define statement *)
NoOverdrafts ==
  \A p \in People:
    acct[p] >= 0

VARIABLES amnt, from, to, first, second

vars == << pc, acct, lock, amnt, from, to, first, second >>

ProcSet == (1..NumTransfers)

Init == (* Global variables *)
        /\ acct \in [People -> Money]
        /\ lock \in [People ->{NULL}]
        (* Process wire *)
        /\ amnt \in [1..NumTransfers -> 1..5]
        /\ from \in [1..NumTransfers -> People]
        /\ to \in [1..NumTransfers -> People]
        /\ first \in [1..NumTransfers -> People]
        /\ second \in [1..NumTransfers -> People]
        /\ pc = [self \in ProcSet |-> "CheckSelf"]

CheckSelf(self) == /\ pc[self] = "CheckSelf"
                   /\ IF from[self] /= to[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "SetLockOrder"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << acct, lock, amnt, from, to, first, second >>

SetLockOrder(self) == /\ pc[self] = "SetLockOrder"
                      /\ IF from[self] < to[self]
                            THEN /\ first' = [first EXCEPT ![self] = from[self]]
                                 /\ second' = [second EXCEPT ![self] = to[self]]
                            ELSE /\ first' = [first EXCEPT ![self] = to[self]]
                                 /\ second' = [second EXCEPT ![self] = from[self]]
                      /\ pc' = [pc EXCEPT ![self] = "GetLockTo"]
                      /\ UNCHANGED << acct, lock, amnt, from, to >>

GetLockTo(self) == /\ pc[self] = "GetLockTo"
                   /\ lock[first[self]] = NULL
                   /\ lock' = [lock EXCEPT ![first[self]] = self]
                   /\ pc' = [pc EXCEPT ![self] = "GetLockFrom"]
                   /\ UNCHANGED << acct, amnt, from, to, first, second >>

GetLockFrom(self) == /\ pc[self] = "GetLockFrom"
                     /\ lock[second[self]] = NULL
                     /\ lock' = [lock EXCEPT ![second[self]] = self]
                     /\ pc' = [pc EXCEPT ![self] = "Check"]
                     /\ UNCHANGED << acct, amnt, from, to, first, second >>

Check(self) == /\ pc[self] = "Check"
               /\ IF acct[from[self]] >= amnt[self]
                     THEN /\ pc' = [pc EXCEPT ![self] = "Withdraw"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "ReleaseLockTo"]
               /\ UNCHANGED << acct, lock, amnt, from, to, first, second >>

Withdraw(self) == /\ pc[self] = "Withdraw"
                  /\ acct' = [acct EXCEPT ![from[self]] = acct[from[self]] - amnt[self]]
                  /\ pc' = [pc EXCEPT ![self] = "Deposit"]
                  /\ UNCHANGED << lock, amnt, from, to, first, second >>

Deposit(self) == /\ pc[self] = "Deposit"
                 /\ acct' = [acct EXCEPT ![to[self]] = acct[to[self]] + amnt[self]]
                 /\ pc' = [pc EXCEPT ![self] = "ReleaseLockTo"]
                 /\ UNCHANGED << lock, amnt, from, to, first, second >>

ReleaseLockTo(self) == /\ pc[self] = "ReleaseLockTo"
                       /\ Assert(lock[first[self]] = self, 
                                 "Failure of assertion at line 57, column 9.")
                       /\ lock' = [lock EXCEPT ![first[self]] = NULL]
                       /\ pc' = [pc EXCEPT ![self] = "ReleaseLockFrom"]
                       /\ UNCHANGED << acct, amnt, from, to, first, second >>

ReleaseLockFrom(self) == /\ pc[self] = "ReleaseLockFrom"
                         /\ Assert(lock[second[self]] = self, 
                                   "Failure of assertion at line 60, column 9.")
                         /\ lock' = [lock EXCEPT ![second[self]] = NULL]
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << acct, amnt, from, to, first, second >>

wire(self) == CheckSelf(self) \/ SetLockOrder(self) \/ GetLockTo(self)
                 \/ GetLockFrom(self) \/ Check(self) \/ Withdraw(self)
                 \/ Deposit(self) \/ ReleaseLockTo(self)
                 \/ ReleaseLockFrom(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..NumTransfers: wire(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
