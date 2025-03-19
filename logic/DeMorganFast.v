Require Import Logic.

Theorem DeMorgan1: 
forall (p q: Prop), ~p /\ ~q <-> ~(p \/ q).
Proof.
    firstorder.
Qed.

Axiom LEM: forall (p: Prop), p \/ ~p.

Theorem DeMorgan2:
forall (p q : Prop), ~p \/ ~q <-> ~(p /\ q).
Proof.
  split.
  - firstorder.
  - destruct (LEM p); auto.
Qed.