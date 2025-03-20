Require Import String.
Require Import ZArith.
Open Scope string_scope.

Definition Num : Type := nat.
Definition Var : Type := string.

Inductive Aexp : Type :=
    An (n : Num) |
    Ax (x : Var) |
    Aplus (a1 a2 : Aexp) |
    Amult (a1 a2 : Aexp) |
    Asub (a1 a2 : Aexp)
.

Inductive Bexp : Type :=
    Btrue |
    Bfalse |
    Bequals (a1 a2 : Aexp) |
    Bleq (a1 a2 : Aexp) | 
    Bneg (b : Bexp) |
    Bconj (b1 b2 : Bexp)
.

Inductive Stm : Type :=
    Sass (x : Var) (a : Aexp) |
    Sskip |
    Scomp (s1 s2: Stm) |
    Sif (b : Bexp) (s1 s2: Stm) |
    Swhile (b : Bexp) (s: Stm)
.

Definition State : Type := Var -> Z.
Definition ZeroState : State := fun _ => 0%Z.

Fixpoint AEvaluate (a : Aexp) (s: State) : Z :=
match a with
    An n => Z.of_nat n |
    Ax x => s x |
    Aplus a1 a2 => (AEvaluate a1 s) + (AEvaluate a2 s) |
    Amult a1 a2 => (AEvaluate a1 s) * (AEvaluate a2 s) |
    Asub a1 a2 => (AEvaluate a1 s) - (AEvaluate a2 s)
end.

Notation "a1 + a2" := (Aplus a1 a2).
Notation "a1 * a2" := (Amult a1 a2).
Notation "a1 - a2" := (Asub a1 a2).
Notation "a1 = a2" := (Bequals a1 a2).
Notation "a1 <= a2" := (Bleq a1 a2).
Notation "~ b" := (Bneg b).
Notation "b1 /\ b2" := (Bneg b1 b2).
Notation "x := a" := (Sass x a) (at level 200).
Notation "S1 ; S2" := (Scomp S1 S2) (at level 200).
Notation "'if' b 'then' S1 'else' S2" := (Sif b S1 S2) (at level 200).
Notation "'while' b 'do' S" := (Swhile b S) (at level 200).

Lemma example_1_6:
    let s : State := fun (x : Var) => match x with
        "x" => 3%Z |
        _ => 0%Z
        end
    in
    AEvaluate (Ax "x" + An 1) s = 4%Z.
Proof.
    unfold AEvaluate.
    ring.
Qed.