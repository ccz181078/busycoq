Require Import ZifyNat Lia Arith.
Require Import PeanoNat.

Inductive DivMod2{n:nat}:Set :=
| mod2eq0 a {H:n=a*2}: @DivMod2 n
| mod2eq1 a {H:n=1+a*2}: @DivMod2 n
.

Definition mod2 n: @DivMod2 n.
destruct (n mod 2) eqn:E.
- eapply (mod2eq0 (n/2)).
- eapply (mod2eq1 (n/2)).
Unshelve.
all: lia.
Defined.

Inductive DivMod3{n:nat}:Set :=
| mod3eq0 a {H:n=a*3}: @DivMod3 n
| mod3eq1 a {H:n=1+a*3}: @DivMod3 n
| mod3eq2 a {H:n=2+a*3}: @DivMod3 n
.

Definition mod3 n: @DivMod3 n.
destruct (n mod 3) as [|[|]] eqn:E.
- eapply (mod3eq0 (n/3)).
- eapply (mod3eq1 (n/3)).
- eapply (mod3eq2 (n/3)).
Unshelve.
all: lia.
Defined.

Inductive DivMod4{n:nat}:Set :=
| mod4eq0 a {H:n=a*4}: @DivMod4 n
| mod4eq1 a {H:n=1+a*4}: @DivMod4 n
| mod4eq2 a {H:n=2+a*4}: @DivMod4 n
| mod4eq3 a {H:n=3+a*4}: @DivMod4 n
.

Definition mod4 n: @DivMod4 n.
destruct (n mod 4) as [|[|[|]]] eqn:E.
- eapply (mod4eq0 (n/4)).
- eapply (mod4eq1 (n/4)).
- eapply (mod4eq2 (n/4)).
- eapply (mod4eq3 (n/4)).
Unshelve.
all: lia.
Defined.

Inductive DivMod5{n:nat}:Set :=
| mod5eq0 a {H:n=a*5}: @DivMod5 n
| mod5eq1 a {H:n=1+a*5}: @DivMod5 n
| mod5eq2 a {H:n=2+a*5}: @DivMod5 n
| mod5eq3 a {H:n=3+a*5}: @DivMod5 n
| mod5eq4 a {H:n=4+a*5}: @DivMod5 n
.

Definition mod5 n: @DivMod5 n.
destruct (n mod 5) as [|[|[|[|]]]] eqn:E.
- eapply (mod5eq0 (n/5)).
- eapply (mod5eq1 (n/5)).
- eapply (mod5eq2 (n/5)).
- eapply (mod5eq3 (n/5)).
- eapply (mod5eq4 (n/5)).
Unshelve.
all: lia.
Defined.

Inductive DivMod6{n:nat}:Set :=
| mod6eq0 a {H:n=a*6}: @DivMod6 n
| mod6eq1 a {H:n=1+a*6}: @DivMod6 n
| mod6eq2 a {H:n=2+a*6}: @DivMod6 n
| mod6eq3 a {H:n=3+a*6}: @DivMod6 n
| mod6eq4 a {H:n=4+a*6}: @DivMod6 n
| mod6eq5 a {H:n=5+a*6}: @DivMod6 n
.

Definition mod6 n: @DivMod6 n.
destruct (n mod 6) as [|[|[|[|[|]]]]] eqn:E.
- eapply (mod6eq0 (n/6)).
- eapply (mod6eq1 (n/6)).
- eapply (mod6eq2 (n/6)).
- eapply (mod6eq3 (n/6)).
- eapply (mod6eq4 (n/6)).
- eapply (mod6eq5 (n/6)).
Unshelve.
all: lia.
Defined.


Inductive Sub(a b:nat):Set :=
| subge c: a=b+c -> Sub a b
| sublt: a<b -> Sub a b.

Lemma sub a b: Sub a b.
Proof.
  destruct (lt_dec a b) as [E|E].
  - apply sublt,E.
  - eapply subge with (c:=a-b).
    lia.
Qed.

