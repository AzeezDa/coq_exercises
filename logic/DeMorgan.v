Require Import Logic.

Theorem DeMorgan1 (p q: Prop):
    ~p /\ ~q <-> ~(p \/ q).
Proof.
    split.
    - intros [not_p not_q] [p_holds | q_holds]; contradiction.
    - intros not_p_or_q.
        unfold not in not_p_or_q.
        split; unfold not; intros; apply not_p_or_q.
        + left. 
            assumption.
        + right. 
            assumption.
Qed.

Axiom LEM: forall (p: Prop), p \/ ~p.

Theorem DeMorgan2:
forall (p q : Prop), ~p \/ ~q <-> ~(p /\ q).
Proof.
    split.
    - intros [not_p | not_q]; unfold not; intros [p_holds q_holds];
        contradiction.
    - intros.
        destruct (LEM p) as [p_holds | not_p].
        destruct (LEM q) as [q_holds | not_q].
        + exfalso. apply H, (conj p_holds q_holds).
        + right. assumption.
        + left. assumption.
Qed.