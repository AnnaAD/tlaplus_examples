---- MODULE wiregloballock ----
EXTENDS TLC, Integers
CONSTANT NULL

People == {"alice", "bob"}
Money == 1..10
NumTransfers == 2

(* --algorithm wire
variables
  acct \in [People -> Money];
  lock = NULL;

define
  NoOverdrafts ==
    \A p \in People:
      acct[p] >= 0
end define;

process wire \in 1..NumTransfers
variable
  amnt \in 1..5;
  from \in People;
  to \in People
begin
  GetLock:
    await lock = NULL;
    lock := self;


  Check:
    if acct[from] >= amnt then
      Withdraw:
        acct[from] := acct[from] - amnt;
      Deposit:
        acct[to] := acct[to] + amnt;
    end if;

  ReleaseLock:
    assert lock = self;
    lock := NULL; 

      
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "aadc7f92" /\ chksum(tla) = "120e785f")
VARIABLES pc, acct, lock

(* define statement *)
NoOverdrafts ==
  \A p \in People:
    acct[p] >= 0

VARIABLES amnt, from, to

vars == << pc, acct, lock, amnt, from, to >>

ProcSet == (1..NumTransfers)

Init == (* Global variables *)
        /\ acct \in [People -> Money]
        /\ lock = NULL
        (* Process wire *)
        /\ amnt \in [1..NumTransfers -> 1..5]
        /\ from \in [1..NumTransfers -> People]
        /\ to \in [1..NumTransfers -> People]
        /\ pc = [self \in ProcSet |-> "GetLock"]

GetLock(self) == /\ pc[self] = "GetLock"
                 /\ lock = NULL
                 /\ lock' = self
                 /\ pc' = [pc EXCEPT ![self] = "Check"]
                 /\ UNCHANGED << acct, amnt, from, to >>

Check(self) == /\ pc[self] = "Check"
               /\ IF acct[from[self]] >= amnt[self]
                     THEN /\ pc' = [pc EXCEPT ![self] = "Withdraw"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "ReleaseLock"]
               /\ UNCHANGED << acct, lock, amnt, from, to >>

Withdraw(self) == /\ pc[self] = "Withdraw"
                  /\ acct' = [acct EXCEPT ![from[self]] = acct[from[self]] - amnt[self]]
                  /\ pc' = [pc EXCEPT ![self] = "Deposit"]
                  /\ UNCHANGED << lock, amnt, from, to >>

Deposit(self) == /\ pc[self] = "Deposit"
                 /\ acct' = [acct EXCEPT ![to[self]] = acct[to[self]] + amnt[self]]
                 /\ pc' = [pc EXCEPT ![self] = "ReleaseLock"]
                 /\ UNCHANGED << lock, amnt, from, to >>

ReleaseLock(self) == /\ pc[self] = "ReleaseLock"
                     /\ Assert(lock = self, 
                               "Failure of assertion at line 40, column 5.")
                     /\ lock' = NULL
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << acct, amnt, from, to >>

wire(self) == GetLock(self) \/ Check(self) \/ Withdraw(self)
                 \/ Deposit(self) \/ ReleaseLock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..NumTransfers: wire(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
