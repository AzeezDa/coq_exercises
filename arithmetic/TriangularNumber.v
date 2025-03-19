Require Import Lia.

Fixpoint Sum (n: nat) : nat :=
match n with
    0 => 0 | 
    S p => n + Sum p
end.
    

Theorem TriangularNumber: forall (n: nat),
    2*Sum n = n * (n+1).
Proof.
    induction n.
    - reflexivity.
    - simpl. lia.
Qed.