From BusyCoq Require Import Individual62 ES_v3.
Require Import String List Bool Arith Lia ZifyNat.
Import ListNotations.
Set Default Goal Selector "!".

(* 1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD does not halt from the blank tape.
   At left records in state D the tape is one of three forms:
     fA a c   = 100 (101)^a 110 (011)^c
     fB j b c = 10010111 (010)^j (110)^b 1110 (011)^c
     fC j x c = 10010111 (010)^j 0 (011)^x 10 (011)^c
   Every record step is linear in the counts:
     A: a >= 6: (a-5, c+8); a = 1..5: one exit each.
     B: b >= 27: (j+3, b-27, c+27); b = 0..26: C (j+b-24) (c+2b-25) (53-2b).
     C: j >= 24: (j-24, x-27, c+54); j = 0..23: one exit each.
   No rule halts. The invariant P below keeps the counts above the sizes the rules need. *)

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD").
Open Scope sym.
Notation W101 := [1;0;1].
Notation W011 := [0;1;1].
Notation W010 := [0;1;0].
Notation W110 := [1;1;0].
Definition fA a c r : side := [1;0;0] *> W101^^a *> [1;1;0] *> W011^^c *> r.
Definition fB j b c r : side := [1;0;0;1;0;1;1;1] *> W010^^j *> W110^^b *> [1;1;1;0] *> W011^^c *> r.
Definition fC j x c r : side := [1;0;0;1;0;1;1;1] *> W010^^j *> [0] *> W011^^x *> [1;0] *> W011^^c *> r.
Notation Z9 := [0;0;0;0;0;0;0;0;0].
Notation Z10 := [0;0;0;0;0;0;0;0;0;0].
Notation Z13 := [0;0;0;0;0;0;0;0;0;0;0;0;0].
Notation Z16 := [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0].
Notation Z3 := [0;0;0].

Lemma a_loop a c l r : (l <* Z9) <{{D}} fA (6+a) (2+c) r -[tm]->+ l <{{D}} fA (1+a) (10+c) r.
Proof. unfold fA, fB, fC. es' a c & l r. Qed.
Lemma a_e1 c l r : (l <* Z13) <{{D}} fA 1 (40+c) (Z3 *> r) -[tm]->+ l <{{D}} fB 3 (19+c) 22 ([0] *> r).
Proof. unfold fA, fB, fC. es' c & l r. Qed.
Lemma a_e2 c l r : (l <* Z10) <{{D}} fA 2 (40+c) (Z3 *> r) -[tm]->+ l <{{D}} fA (38+c) 8 ([0] *> r).
Proof. unfold fA, fB, fC. es' c & l r. Qed.
Lemma a_e3 c l r : (l <* Z13) <{{D}} fA 3 (40+c) (Z3 *> r) -[tm]->+ l <{{D}} fA (36+c) 12 ([0] *> r).
Proof. unfold fA, fB, fC. es' c & l r. Qed.
Lemma a_e4 c l r : (l <* Z13) <{{D}} fA 4 (40+c) (Z3 *> r) -[tm]->+ l <{{D}} fB 4 (11+c) 32 ([0] *> r).
Proof. unfold fA, fB, fC. es' c & l r. Qed.
Lemma a_e5 c l r : (l <* Z16) <{{D}} fA 5 (40+c) (Z3 *> r) -[tm]->+ l <{{D}} fB 4 (26+c) 19 ([0] *> r).
Proof. unfold fA, fB, fC. es' c & l r. Qed.
Lemma b_loop j b c l r : (l <* Z9) <{{D}} fB (3+j) (27+b) (2+c) r -[tm]->+ l <{{D}} fB (6+j) b (29+c) r.
Proof. unfold fA, fB, fC. es' j b c & l r. Qed.
Lemma b_e0 j c l r : (l <* Z9) <{{D}} fB (24+j) 0 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (0+j) (5+c) 53 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e1 j c l r : (l <* Z9) <{{D}} fB (24+j) 1 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (1+j) (7+c) 51 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e2 j c l r : (l <* Z9) <{{D}} fB (24+j) 2 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (2+j) (9+c) 49 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e3 j c l r : (l <* Z9) <{{D}} fB (24+j) 3 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (3+j) (11+c) 47 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e4 j c l r : (l <* Z9) <{{D}} fB (24+j) 4 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (4+j) (13+c) 45 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e5 j c l r : (l <* Z9) <{{D}} fB (24+j) 5 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (5+j) (15+c) 43 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e6 j c l r : (l <* Z9) <{{D}} fB (24+j) 6 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (6+j) (17+c) 41 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e7 j c l r : (l <* Z9) <{{D}} fB (24+j) 7 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (7+j) (19+c) 39 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e8 j c l r : (l <* Z9) <{{D}} fB (24+j) 8 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (8+j) (21+c) 37 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e9 j c l r : (l <* Z9) <{{D}} fB (23+j) 9 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (8+j) (23+c) 35 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e10 j c l r : (l <* Z9) <{{D}} fB (23+j) 10 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (9+j) (25+c) 33 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e11 j c l r : (l <* Z9) <{{D}} fB (23+j) 11 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (10+j) (27+c) 31 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e12 j c l r : (l <* Z9) <{{D}} fB (23+j) 12 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (11+j) (29+c) 29 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e13 j c l r : (l <* Z9) <{{D}} fB (23+j) 13 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (12+j) (31+c) 27 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e14 j c l r : (l <* Z9) <{{D}} fB (23+j) 14 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (13+j) (33+c) 25 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e15 j c l r : (l <* Z9) <{{D}} fB (23+j) 15 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (14+j) (35+c) 23 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e16 j c l r : (l <* Z9) <{{D}} fB (23+j) 16 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (15+j) (37+c) 21 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e17 j c l r : (l <* Z9) <{{D}} fB (23+j) 17 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (16+j) (39+c) 19 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e18 j c l r : (l <* Z9) <{{D}} fB (22+j) 18 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (16+j) (41+c) 17 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e19 j c l r : (l <* Z9) <{{D}} fB (22+j) 19 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (17+j) (43+c) 15 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e20 j c l r : (l <* Z9) <{{D}} fB (22+j) 20 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (18+j) (45+c) 13 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e21 j c l r : (l <* Z9) <{{D}} fB (22+j) 21 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (19+j) (47+c) 11 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e22 j c l r : (l <* Z9) <{{D}} fB (22+j) 22 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (20+j) (49+c) 9 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e23 j c l r : (l <* Z9) <{{D}} fB (22+j) 23 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (21+j) (51+c) 7 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e24 j c l r : (l <* Z9) <{{D}} fB (22+j) 24 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (22+j) (53+c) 5 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e25 j c l r : (l <* Z9) <{{D}} fB (22+j) 25 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (23+j) (55+c) 3 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma b_e26 j c l r : (l <* Z9) <{{D}} fB (22+j) 26 (30+c) (Z3 *> r) -[tm]->+ l <{{D}} fC (24+j) (57+c) 1 ([0] *> r).
Proof. unfold fA, fB, fC. es' j c & l r. Qed.
Lemma c_loop j x c l r : (l <* Z9) <{{D}} fC (24+j) (30+x) (1+c) r -[tm]->+ l <{{D}} fC j (3+x) (55+c) r.
Proof. unfold fA, fB, fC. es' j x c & l r. Qed.
Lemma c_e0 x c l r : (l <* Z13) <{{D}} fC 0 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 3 (38+x) (24+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e1 x c l r : (l <* Z10) <{{D}} fC 1 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 3 (35+x) (27+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e2 x c l r : (l <* Z10) <{{D}} fC 2 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 4 (31+x) (31+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e3 x c l r : (l <* Z10) <{{D}} fC 3 (60+x) (1+c) r -[tm]->+ l <{{D}} fA (53+x) (16+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e4 x c l r : (l <* Z13) <{{D}} fC 4 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 4 (33+x) (32+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e5 x c l r : (l <* Z13) <{{D}} fC 5 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 5 (29+x) (36+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e6 x c l r : (l <* Z13) <{{D}} fC 6 (60+x) (1+c) r -[tm]->+ l <{{D}} fA (47+x) (26+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e7 x c l r : (l <* Z10) <{{D}} fC 7 (60+x) (1+c) r -[tm]->+ l <{{D}} fA (48+x) (25+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e8 x c l r : (l <* Z10) <{{D}} fC 8 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 4 (27+x) (41+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e9 x c l r : (l <* Z13) <{{D}} fC 9 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 4 (18+x) (52+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e10 x c l r : (l <* Z13) <{{D}} fC 10 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 4 (19+x) (52+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e11 x c l r : (l <* Z13) <{{D}} fC 11 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 5 (15+x) (56+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e12 x c l r : (l <* Z16) <{{D}} fC 12 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 4 (29+x) (45+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e13 x c l r : (l <* Z13) <{{D}} fC 13 (60+x) (1+c) r -[tm]->+ l <{{D}} fA (38+x) (42+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e14 x c l r : (l <* Z13) <{{D}} fC 14 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 4 (11+x) (64+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e15 x c l r : (l <* Z16) <{{D}} fC 15 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 4 (24+x) (53+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e16 x c l r : (l <* Z16) <{{D}} fC 16 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 4 (25+x) (53+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e17 x c l r : (l <* Z16) <{{D}} fC 17 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 5 (21+x) (57+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e18 x c l r : (l <* Z9) <{{D}} fC 18 (60+x) (1+c) r -[tm]->+ l <{{D}} fC 0 (43+x) (39+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e19 x c l r : (l <* Z16) <{{D}} fC 19 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 3 (21+x) (61+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e20 x c l r : (l <* Z16) <{{D}} fC 20 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 4 (17+x) (65+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e21 x c l r : (l <* Z9) <{{D}} fC 21 (60+x) (1+c) r -[tm]->+ l <{{D}} fC 0 (38+x) (47+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e22 x c l r : (l <* Z16) <{{D}} fC 22 (60+x) (1+c) r -[tm]->+ l <{{D}} fA (28+x) (62+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.
Lemma c_e23 x c l r : (l <* Z16) <{{D}} fC 23 (60+x) (1+c) r -[tm]->+ l <{{D}} fB 3 (13+x) (73+c) r.
Proof. unfold fA, fB, fC. es' x c & l r. Qed.

(* The invariant and the zero lemmas. *)
Lemma Z1 : [0] *> 0inf = 0inf. Proof. solve_const0_eq. Qed.
Lemma ZZ3 : Z3 *> 0inf = 0inf. Proof. solve_const0_eq. Qed.
Lemma ZZ9 : Z9 *> 0inf = 0inf. Proof. solve_const0_eq. Qed.
Lemma ZZ10 : Z10 *> 0inf = 0inf. Proof. solve_const0_eq. Qed.
Lemma ZZ13 : Z13 *> 0inf = 0inf. Proof. solve_const0_eq. Qed.
Lemma ZZ16 : Z16 *> 0inf = 0inf. Proof. solve_const0_eq. Qed.
Ltac zz H := repeat (rewrite ZZ16 in H || rewrite ZZ13 in H || rewrite ZZ10 in H || rewrite ZZ9 in H || rewrite ZZ3 in H || rewrite Z1 in H).

Notation cA a c := (0inf <{{D}} fA a c 0inf).
Notation cB j b c := (0inf <{{D}} fB j b c 0inf).
Notation cC j x c := (0inf <{{D}} fC j x c 0inf).

Inductive P : Q * tape -> Prop :=
| PA a c : 1<=a -> 8<=c -> 1239 <= 8*a+5*c -> P (cA a c)
| PB j b c : 3<=j -> 2<=c -> 216 <= 9*j+b -> 9*j+1696 <= 8*c+7*b -> P (cB j b c)
| PC j x c : 1<=c -> 9*j+1712 <= 8*x -> 212 <= 4*c+9*j -> P (cC j x c)
| PC0 x c : 1<=c -> 1712 <= 8*x -> 202 <= 4*c -> P (cC 0 x c).

(* One record step from each form. *)
Lemma step_A a c : 1<=a -> 8<=c -> 1239 <= 8*a+5*c -> exists c', P c' /\ cA a c -[tm]->+ c'.
Proof.
  intros Ha Hc Hi.
  destruct a as [|[|[|[|[|[|a]]]]]].
  - lia.
  - assert (E: c = 40+(c-40)) by lia. rewrite E.
    pose proof (a_e1 (c-40) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E: c = 40+(c-40)) by lia. rewrite E.
    pose proof (a_e2 (c-40) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PA; lia.
  - assert (E: c = 40+(c-40)) by lia. rewrite E.
    pose proof (a_e3 (c-40) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PA; lia.
  - assert (E: c = 40+(c-40)) by lia. rewrite E.
    pose proof (a_e4 (c-40) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E: c = 40+(c-40)) by lia. rewrite E.
    pose proof (a_e5 (c-40) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E: c = 2+(c-2)) by lia. rewrite E.
    pose proof (a_loop a (c-2) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PA; lia.
Qed.

Lemma step_B j b c : 3<=j -> 2<=c -> 216 <= 9*j+b -> 9*j+1696 <= 8*c+7*b -> exists c', P c' /\ cB j b c -[tm]->+ c'.
Proof.
  intros Hj Hc H1 H2.
  destruct b as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|b]]]]]]]]]]]]]]]]]]]]]]]]]]].
  - assert (E1: j = 24+(j-24)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e0 (j-24) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 24+(j-24)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e1 (j-24) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 24+(j-24)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e2 (j-24) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 24+(j-24)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e3 (j-24) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 24+(j-24)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e4 (j-24) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 24+(j-24)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e5 (j-24) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 24+(j-24)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e6 (j-24) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 24+(j-24)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e7 (j-24) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 24+(j-24)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e8 (j-24) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 23+(j-23)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e9 (j-23) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 23+(j-23)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e10 (j-23) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 23+(j-23)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e11 (j-23) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 23+(j-23)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e12 (j-23) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 23+(j-23)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e13 (j-23) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 23+(j-23)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e14 (j-23) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 23+(j-23)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e15 (j-23) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 23+(j-23)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e16 (j-23) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 23+(j-23)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e17 (j-23) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 22+(j-22)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e18 (j-22) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 22+(j-22)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e19 (j-22) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 22+(j-22)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e20 (j-22) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 22+(j-22)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e21 (j-22) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 22+(j-22)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e22 (j-22) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 22+(j-22)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e23 (j-22) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 22+(j-22)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e24 (j-22) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 22+(j-22)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e25 (j-22) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 22+(j-22)) by lia. assert (E2: c = 30+(c-30)) by lia. rewrite E1, E2.
    pose proof (b_e26 (j-22) (c-30) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
  - assert (E1: j = 3+(j-3)) by lia. assert (E2: c = 2+(c-2)) by lia. rewrite E1, E2.
    pose proof (b_loop (j-3) b (c-2) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
Qed.

Lemma step_C j x c : 1<=c -> 9*j+1712 <= 8*x -> 212 <= 4*c+9*j -> exists c', P c' /\ cC j x c -[tm]->+ c'.
Proof.
  intros Hc H1 H2.
  destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]]]]]]]]]]]]].
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e0 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e1 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e2 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e3 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PA; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e4 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e5 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e6 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PA; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e7 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PA; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e8 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e9 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e10 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e11 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e12 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e13 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PA; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e14 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e15 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e16 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e17 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e18 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC0; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e19 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e20 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e21 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC0; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e22 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PA; lia.
  - assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_e23 (x-60) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PB; lia.
  - assert (E1: x = 30+(x-30)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
    pose proof (c_loop j (x-30) (c-1) 0inf 0inf) as H. zz H.
    refine (ex_intro _ _ (conj _ H)). apply PC; lia.
Qed.

Lemma step_C0 x c : 1<=c -> 1712 <= 8*x -> 202 <= 4*c -> exists c', P c' /\ cC 0 x c -[tm]->+ c'.
Proof.
  intros Hc H1 H2.
  assert (E1: x = 60+(x-60)) by lia. assert (E2: c = 1+(c-1)) by lia. rewrite E1, E2.
  pose proof (c_e0 (x-60) (c-1) 0inf 0inf) as H. zz H.
  refine (ex_intro _ _ (conj _ H)). apply PB; lia.
Qed.

(* The opening: 672,894 steps. *)
Lemma zeros n : [0]^^n *> 0inf = 0inf.
Proof. induction n as [|n IH]; [reflexivity|]. simpl. rewrite IH. rewrite <- const_unfold. reflexivity. Qed.
Lemma init_l l r : (l <* [0]^^565) {{A}}> ([0]^^60 *> r) -[tm]->+ l <{{D}} fA 160 46 ([0]^^1 *> r).
Proof. unfold fA. es' & l r. Qed.
Lemma init : c0 -[tm]->* (0inf <{{D}} fA 160 46 0inf).
Proof.
  pose proof (init_l 0inf 0inf) as H. rewrite !zeros in H.
  apply progress_evstep. exact H.
Qed.

Lemma step_P : forall c, P c -> exists c', P c' /\ c -[tm]->+ c'.
Proof.
  intros c Hc. destruct Hc.
  - apply step_A; assumption.
  - apply step_B; assumption.
  - apply step_C; assumption.
  - apply step_C0; assumption.
Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [ apply init | ].
  apply progress_nonhalt with (P:=P); [ exact step_P | ].
  apply PA; lia.
Qed.

Close Scope sym.
End TM1.
Print Assumptions TM1.nonhalt.
