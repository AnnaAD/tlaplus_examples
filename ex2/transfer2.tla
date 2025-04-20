---- MODULE transfer2 ----
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10, money \in 1..20;

begin
CHECK: if alice_account >= money then
      A: alice_account := alice_account - money;
      B: bob_account := bob_account + money;
    end if;
C: assert alice_account >= 0;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "14fe9a1b" /\ chksum(tla) = "baec4395")
VARIABLES pc, alice_account, bob_account, money

vars == << pc, alice_account, bob_account, money >>

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 10
        /\ money \in 1..20
        /\ pc = "CHECK"

CHECK == /\ pc = "CHECK"
         /\ IF alice_account >= money
               THEN /\ pc' = "A"
               ELSE /\ pc' = "C"
         /\ UNCHANGED << alice_account, bob_account, money >>

A == /\ pc = "A"
     /\ alice_account' = alice_account - money
     /\ pc' = "B"
     /\ UNCHANGED << bob_account, money >>

B == /\ pc = "B"
     /\ bob_account' = bob_account + money
     /\ pc' = "C"
     /\ UNCHANGED << alice_account, money >>

C == /\ pc = "C"
     /\ Assert(alice_account >= 0, 
               "Failure of assertion at line 12, column 4.")
     /\ pc' = "Done"
     /\ UNCHANGED << alice_account, bob_account, money >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == CHECK \/ A \/ B \/ C
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=====
