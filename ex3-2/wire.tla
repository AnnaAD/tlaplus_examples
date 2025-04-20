---- MODULE wire ----
EXTENDS TLC, Integers

RECURSIVE Sum(_,_)
Sum(f,S) == IF S = {} THEN 0
                      ELSE LET x == CHOOSE x \in S : TRUE
                           IN  f[x] + Sum(f,S \ {x})
                           
People == {"alice", "bob"}
Money == 1..10
NumTransfers == 2

(* --algorithm wire
variables
  acct \in [People -> Money];
  totalMoney =  Sum(acct, People)


define
NoOverdrafts == \A p \in People:acct[p] >= 0 
MoneyInvariant ==  Sum(acct, People) = totalMoney
end define;

process wire \in 1..NumTransfers
variable
  amnt \in 1..5;
  from \in People;
  to \in People
begin
  Check:
    if from /= to /\ acct[from] >= amnt then
      Withdraw:
        acct[from] := acct[from] - amnt;
      Deposit:
        acct[to] := acct[to] + amnt;
    end if;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "6028b865" /\ chksum(tla) = "aecb3644")
VARIABLES pc, acct, totalMoney

(* define statement *)
NoOverdrafts == \A p \in People:acct[p] >= 0
MoneyInvariant ==  Sum(acct, People) = totalMoney

VARIABLES amnt, from, to

vars == << pc, acct, totalMoney, amnt, from, to >>

ProcSet == (1..NumTransfers)

Init == (* Global variables *)
        /\ acct \in [People -> Money]
        /\ totalMoney = Sum(acct, People)
        (* Process wire *)
        /\ amnt \in [1..NumTransfers -> 1..5]
        /\ from \in [1..NumTransfers -> People]
        /\ to \in [1..NumTransfers -> People]
        /\ pc = [self \in ProcSet |-> "Check"]

Check(self) == /\ pc[self] = "Check"
               /\ IF from[self] /= to[self] /\ acct[from[self]] >= amnt[self]
                     THEN /\ pc' = [pc EXCEPT ![self] = "Withdraw"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << acct, totalMoney, amnt, from, to >>

Withdraw(self) == /\ pc[self] = "Withdraw"
                  /\ acct' = [acct EXCEPT ![from[self]] = acct[from[self]] - amnt[self]]
                  /\ pc' = [pc EXCEPT ![self] = "Deposit"]
                  /\ UNCHANGED << totalMoney, amnt, from, to >>

Deposit(self) == /\ pc[self] = "Deposit"
                 /\ acct' = [acct EXCEPT ![to[self]] = acct[to[self]] + amnt[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << totalMoney, amnt, from, to >>

wire(self) == Check(self) \/ Withdraw(self) \/ Deposit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..NumTransfers: wire(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
