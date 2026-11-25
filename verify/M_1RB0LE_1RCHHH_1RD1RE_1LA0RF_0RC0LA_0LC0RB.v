From BusyCoq Require Import Individual62 ES_v3.
Require Import String List Bool Arith Lia ZifyNat.
Import ListNotations.
Set Default Goal Selector "!".

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB").
Open Scope string.
Tactic Notation "esr" constr(a) constr(b) constr(c) constr(d) "&" constr(e) constr(f) :=
  (es_v3_pre;
  es_v3_nmp_smp (fun s =>
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  if s=?"d" then d else
  O)
  (fun s =>
  if s=?"e" then e else
  if s=?"f" then f else
  0inf)).
Tactic Notation "esr" constr(a) constr(b) constr(c) constr(d) constr(e) "&" constr(f) constr(g) :=
  (es_v3_pre;
  es_v3_nmp_smp (fun s =>
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  if s=?"d" then d else
  if s=?"e" then e else
  O)
  (fun s =>
  if s=?"f" then f else
  if s=?"g" then g else
  0inf)).
Tactic Notation "esr" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) "&" constr(g) constr(h) :=
  (es_v3_pre;
  es_v3_nmp_smp (fun s =>
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  if s=?"d" then d else
  if s=?"e" then e else
  if s=?"f" then f else
  O)
  (fun s =>
  if s=?"g" then g else
  if s=?"h" then h else
  0inf)).
Close Scope string.
Open Scope sym.
Notation W1000 := [1;0;0;0].
Notation W10 := [1;0].
Notation W01 := [0;1].
Notation W0010 := [0;0;1;0].
Notation M3 := [0;0;0;0;1;0;0;0;0;0;1;0;0;0].
Notation S1w := [0;0;1;0;0;0;0;0;1;0;0;0;0;0].
Notation T1w := [0;0;1;0;0;0;0;0;1;0;0;0;1;0;1].
Notation S2w := [0;0;0;0;0;0;0;1;0;0;0;0;0;1].
Notation T2w := [0;0;0;1;0;1].
Notation S3w := [0;0;0;0;1;0;0;0;0;0;1;0;0;0].
Notation S4w := [0;0;1;0;0;0;0;0;0;0;1;0;0;0].
Notation M5 := [0;0;0;0;0;1;0;0;0;0;0;1;0;0;0].
Notation W7 := [0;1;1;1;1;1;1].
Notation W1110 := [0;1;1;1].
Notation Zr2 := [0;0].
Notation Zr4 := [0;0;0;0].
Notation Zr5 := [0;0;0;0;0].
Notation Zr6 := [0;0;0;0;0;0].
Notation Zr7 := [0;0;0;0;0;0;0].
Notation Zr8 := [0;0;0;0;0;0;0;0].
Notation Zr9 := [0;0;0;0;0;0;0;0;0].
Notation Zr12 := [0;0;0;0;0;0;0;0;0;0;0;0].
Notation Zr13 := [0;0;0;0;0;0;0;0;0;0;0;0;0].
Notation Zs18 := [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0].
Notation B4 := [0;1;1;1;1;0;1].
Notation Y2 := [0;1;0;1;0;1;0;1;0;1;0;1;1;0].
Notation R6 := [1;0;0;1;1;1].
Definition N1 a b d r : side := [0;0;0;0;0;0] *> W1000^^a *> M3 *> W10^^b *> S1w^^d *> T1w *> r.
Definition N2 a b c d r : side := [0;0;0;0;0;0] *> W1000^^a *> M3 *> W10^^b *> [0] *> W01^^c *> S2w^^d *> T2w *> r.
Definition N3 a b z c d r : side := [0;0;0;0;0;0] *> W1000^^a *> M3 *> W10^^b *> [0] *> W01^^z *> M5 *> W10^^c *> S1w^^d *> T1w *> r.
Definition LC x y z Z c d r : side := [0;0;0;0;0;0] *> W1000^^x *> W10^^y *> W0010^^z *> W10^^Z *> M3 *> W10^^c *> S1w^^d *> T1w *> r.
Definition P1 a s r : side := [0;0;0;0;0;0] *> W1000^^a *> S3w^^s *> [1;0;1] *> r.
Definition P2 a b s r : side := [0;0;0;0;0;0] *> W1000^^a *> W10^^b *> S3w^^s *> [1;0;1] *> r.
Definition T0f a s r : side := [0;0;0;0] *> W1000^^a *> S4w^^s *> [0;0;1;0;0;0;1;0;1] *> r.
Definition T1f a b c d r : side := [0;0;0;0] *> W1000^^a *> [0;0;1;0;0;0] *> W10^^b *> [0] *> W01^^c *> S2w^^d *> T2w *> r.
Definition LCm x y n Z c d r : side := [0;0;0;0;0;0] *> W1000^^x *> W10^^y *> W10^^n *> W10^^Z *> M3 *> W10^^c *> S1w^^d *> T1w *> r.
Definition LCc x y z Z c1 n c2 d r : side := [0;0;0;0;0;0] *> W1000^^x *> W10^^y *> W0010^^z *> W10^^Z *> M3 *> W10^^c1 *> W10^^n *> W10^^c2 *> S1w^^d *> T1w *> r.
Lemma n1_cyc a b d l r: (l <* Zr8) <{{A}} N1 a (2+b) (4+d) r -[tm]->+ l <{{A}} N1 (3+a) (14+b) (2+d) r.
Proof. unfold N1. es' a b d & l r. Qed.
Lemma n1_d2 a b l r: (l <* Zr8) <{{A}} N1 a (2+b) 2 r -[tm]->+ l <{{A}} N1 (3+a) (14+b) 0 r.
Proof. unfold N1. es' a b & l r. Qed.
Lemma n1_d3 a b l r: (l <* Zr8) <{{A}} N1 a (2+b) 3 r -[tm]->+ l <{{A}} N1 (3+a) (14+b) 1 r.
Proof. unfold N1. es' a b & l r. Qed.
Lemma p1_r a s l r: (l <* Zr6) <{{A}} P1 a (6+s) r -[tm]->+ l <{{A}} N1 (2+a) 7 (3+s) r.
Proof. unfold P1, N1. es' a s & l r. Qed.
Lemma p2_r a b s l r: (l <* Zr2) <{{A}} P2 a (6+b) (6+s) r -[tm]->+ l <{{A}} N1 (1+a) (6+b) (4+s) r.
Proof. unfold P2, N1. es' a b s & l r. Qed.
Lemma t0_r z d l r: (l <* Zr12) <{{A}} T0f (14+z) (8+d) r -[tm]->+ l <{{A}} LC 5 14 (6+z) 8 7 (4+d) r.
Proof. unfold T0f, LC. es' z d & l r. Qed.
Lemma t1_r z b c d l r: (l <* Zr4) <{{A}} T1f (9+z) (7+b) (6+c) (6+d) r -[tm]->+ l <{{A}} LC 1 6 (6+z) (11+b) (7+c) (4+d) r.
Proof. unfold T1f, LC. esr z b c d & l r. Qed.
Lemma lc_cyc x y z Z c d l r: (l <* Zr8) <{{A}} LC x (6+y) (6+z) (8+Z) (7+c) (4+d) r -[tm]->+ l <{{A}} LC (4+x) (14+y) (1+z) (15+Z) (12+c) (2+d) r.
Proof. unfold LC. esr x y z Z c d & l r. Qed.
Lemma lc_z5 x y Z c d l r: (l <* Zr8) <{{A}} LC x (6+y) 5 (8+Z) (7+c) (4+d) r -[tm]->+ l <{{A}} LCm (4+x) y 29 Z (12+c) (2+d) r.
Proof. unfold LC, LCm. esr x y Z c d & l r. Qed.
Lemma lc_z4 x y Z c d l r: (l <* Zr8) <{{A}} LC x (6+y) 4 (8+Z) (7+c) (4+d) r -[tm]->+ l <{{A}} LCm (4+x) y 27 Z (12+c) (2+d) r.
Proof. unfold LC, LCm. esr x y Z c d & l r. Qed.
Lemma lc_z3 x y Z c d l r: (l <* Zr8) <{{A}} LC x (6+y) 3 (8+Z) (7+c) (4+d) r -[tm]->+ l <{{A}} LCm (4+x) y 25 Z (12+c) (2+d) r.
Proof. unfold LC, LCm. esr x y Z c d & l r. Qed.
Lemma lc_z2 x y Z c d l r: (l <* Zr4) <{{A}} LC x (6+y) 2 (8+Z) (7+c) (4+d) r -[tm]->+ l <{{A}} N3 (2+x) (8+y) (9+Z) (12+c) (2+d) r.
Proof. unfold LC, N3. esr x y Z c d & l r. Qed.
Lemma lc_z1 x y Z c d l r: (l <* Zr4) <{{A}} LC x (6+y) 1 (8+Z) (7+c) (4+d) r -[tm]->+ l <{{A}} N3 (2+x) (6+y) (9+Z) (12+c) (2+d) r.
Proof. unfold LC, N3. esr x y Z c d & l r. Qed.
Lemma lh_r x y c d l r: (l <* Zr2) <{{A}} LC x (6+y) 0 0 (7+c) d r -[tm]->+ l <{{A}} N2 (1+x) (5+y) (11+c) d r.
Proof. unfold LC, N2. esr x y c d & l r. Qed.
Lemma n2_cyc a b c d l r: (l <* Zr6) <{{A}} N2 a (6+b) (7+c) (4+d) r -[tm]->+ l <{{A}} LC (2+a) (14+b) 0 0 (8+c) (2+d) r.
Proof. unfold LC, N2. esr a b c d & l r. Qed.
Lemma n2_d2 a b c l r: (l <* Zr6) <{{A}} N2 a (6+b) (7+c) 2 r -[tm]->+ l <{{A}} LC (2+a) (14+b) 0 0 (8+c) 0 r.
Proof. unfold LC, N2. es' a b c & l r. Qed.
Lemma n2_d3 a b c l r: (l <* Zr6) <{{A}} N2 a (6+b) (7+c) 3 r -[tm]->+ l <{{A}} LC (2+a) (14+b) 0 0 (8+c) 1 r.
Proof. unfold LC, N2. es' a b c & l r. Qed.
Lemma n3_cyc a b z c d l r: (l <* Zr8) <{{A}} N3 a (6+b) (6+z) (7+c) (4+d) r -[tm]->+ l <{{A}} N3 (3+a) (13+b) (6+z) (12+c) (2+d) r.
Proof. unfold N3. esr a b z c d & l r. Qed.
Lemma n3_d2 a b z c l r: (l <* Zr8) <{{A}} N3 a (6+b) (6+z) (7+c) 2 r -[tm]->+ l <{{A}} N3 (3+a) (13+b) (6+z) (12+c) 0 r.
Proof. unfold N3. esr a b z c & l r. Qed.
Lemma n3_d3 a b z c l r: (l <* Zr8) <{{A}} N3 a (6+b) (6+z) (7+c) 3 r -[tm]->+ l <{{A}} N3 (3+a) (13+b) (6+z) (12+c) 1 r.
Proof. unfold N3. esr a b z c & l r. Qed.
Lemma n1s0 a b l r: (l <* Zr8) <{{A}} N1 a (2+b) 0 (Zs18 *> r) -[tm]->+ (l <* W1110^^(3+a) <* W7^^4 <* R6 <* W01^^(9+b) <* [1]) {{E}}> r.
Proof. unfold N1. es' a b & l r. Qed.
Lemma n1s1 a b l r: (l <* Zr8) <{{A}} N1 a (2+b) 1 (Zr9 *> r) -[tm]->+ (l <* W1110^^(3+a) <* W7^^5 <* R6 <* W01^^(8+b) <* [1]) {{E}}> r.
Proof. unfold N1. es' a b & l r. Qed.
Lemma n2s0 a b c l r: (l <* Zr6) <{{A}} N2 a (8+b) (4+c) 0 (Zs18 *> r) -[tm]->+ (l <* W1110^^(3+a) <* Y2 <* Y2 <* W01^^b <* B4 <* W7^^3 <* R6 <* W01^^c <* [1]) {{E}}> r.
Proof. unfold N2. es' a b c & l r. Qed.
Lemma n2s1 a b c l r: (l <* Zr6) <{{A}} N2 a (8+b) (5+c) 1 (Zr9 *> r) -[tm]->+ (l <* W1110^^(3+a) <* Y2 <* Y2 <* W01^^b <* B4 <* W7^^4 <* R6 <* W01^^c <* [1]) {{E}}> r.
Proof. unfold N2. es' a b c & l r. Qed.
Lemma n3s0 a b z c l r: (l <* Zr8) <{{A}} N3 a (6+b) (9+z) (7+c) 0 (Zs18 *> r) -[tm]->+ (l <* W1110^^(3+a) <* W7 <* W7 <* R6 <* W01^^(11+b) <* R6 <* W01^^(6+z) <* B4 <* W7^^3 <* R6 <* W01^^(7+c) <* [1]) {{E}}> r.
Proof. unfold N3. esr a b z c & l r. Qed.
Lemma n3s1 a b z c l r: (l <* Zr8) <{{A}} N3 a (6+b) (9+z) (7+c) 1 (Zr9 *> r) -[tm]->+ (l <* W1110^^(3+a) <* W7 <* W7 <* R6 <* W01^^(11+b) <* R6 <* W01^^(6+z) <* B4 <* W7^^4 <* R6 <* W01^^(6+c) <* [1]) {{E}}> r.
Proof. unfold N3. esr a b z c & l r. Qed.
Lemma qa k q m l r: (l <* W1110^^(1+k) <* W7^^q <* R6 <* W01^^(1+m) <* [1]) {{E}}> Zr5 *> r -[tm]->+ (l <* W1110^^(1+k) <* W7^^(1+q) <* R6 <* W01^^m <* [1]) {{E}}> r.
Proof. es' k q m & l r. Qed.
Lemma qb q m l r: (l <* B4 <* W7^^q <* R6 <* W01^^(1+m) <* [1]) {{E}}> Zr5 *> r -[tm]->+ (l <* B4 <* W7^^(1+q) <* R6 <* W01^^m <* [1]) {{E}}> r.
Proof. es' q m & l r. Qed.
Lemma q1odd k s l r: (l <* W1110^^(4+k) <* W7^^(9+(s*2)) <* R6 <* [1]) {{E}}> Zr9 *> r -[tm]->+ l <{{A}} P1 (4+k) (5+s) r.
Proof. unfold P1. es' k s & l r. Qed.
Lemma q1even k s l r: (l <* [0] <* W1110^^(4+k) <* W7^^(10+(s*2)) <* R6 <* [1]) {{E}}> Zr9 *> r -[tm]->+ l <{{A}} T0f (5+k) (5+s) r.
Proof. unfold T0f. es' k s & l r. Qed.
Lemma q2even a b s l r: (l <* W1110^^(4+a) <* Y2 <* Y2 <* W01^^b <* B4 <* W7^^(10+(s*2)) <* R6 <* [1]) {{E}}> Zr9 *> r -[tm]->+ l <{{A}} P2 (3+a) (16+b) (6+s) r.
Proof. unfold P2. es' a b s & l r. Qed.
Lemma q2odd a b s l r: (l <* [0] <* W1110^^(4+a) <* Y2 <* Y2 <* W01^^b <* B4 <* W7^^(9+(s*2)) <* R6 <* [1]) {{E}}> Zr9 *> r -[tm]->+ l <{{A}} T1f (4+a) 7 (14+b) (4+s) r.
Proof. unfold T1f. es' a b s & l r. Qed.
Lemma q3even k b z s l r: (l <* Zr6 <* W1110^^(4+k) <* W7 <* W7 <* R6 <* W01^^(6+b) <* R6 <* W01^^(6+z) <* B4 <* W7^^(10+(s*2)) <* R6 <* [1]) {{E}}> Zr9 *> r -[tm]->+ l <{{A}} LC (6+k) (16+b) 0 0 (9+z) (4+s) r.
Proof. unfold LC. esr k b z s & l r. Qed.
Lemma q3odd k b z s l r: (l <* Zr13 <* W1110^^(13+k) <* W7 <* W7 <* R6 <* W01^^(6+b) <* R6 <* W01^^(6+z) <* B4 <* W7^^(9+(s*2)) <* R6 <* [1]) {{E}}> Zr9 *> r -[tm]->+ l <{{A}} LCc 5 14 (6+k) 15 (6+b) 6 (6+z) (2+s) r.
Proof. unfold LCc. esr k b z s & l r. Qed.
Ltac flia := repeat (lia || f_equal).

Lemma Z1 : [0] *> 0inf = 0inf. Proof. solve_const0_eq. Qed.
Lemma Z2 : Zr2 *> 0inf = 0inf. Proof. solve_const0_eq. Qed.
Lemma Z4 : Zr4 *> 0inf = 0inf. Proof. solve_const0_eq. Qed.
Lemma Z5 : Zr5 *> 0inf = 0inf. Proof. solve_const0_eq. Qed.
Lemma Z6 : Zr6 *> 0inf = 0inf. Proof. solve_const0_eq. Qed.
Lemma Z8 : Zr8 *> 0inf = 0inf. Proof. solve_const0_eq. Qed.
Lemma Z9 : Zr9 *> 0inf = 0inf. Proof. solve_const0_eq. Qed.
Lemma Z12 : Zr12 *> 0inf = 0inf. Proof. solve_const0_eq. Qed.
Lemma Z13 : Zr13 *> 0inf = 0inf. Proof. solve_const0_eq. Qed.
Lemma Z18 : Zs18 *> 0inf = 0inf. Proof. solve_const0_eq. Qed.

(* Q rounds iterated *)
Lemma qa_loop k m : forall q l,
  (l <* W1110^^(1+k) <* W7^^q <* R6 <* W01^^m <* [1]) {{E}}> 0inf -[tm]->*
  (l <* W1110^^(1+k) <* W7^^(q+m) <* R6 <* [1]) {{E}}> 0inf.
Proof.
  induction m; intros q l.
  - rewrite Nat.add_0_r. apply evstep_refl.
  - eapply evstep_trans.
    + apply progress_evstep. pose proof (qa k q m l 0inf) as H. rewrite Z5 in H. exact H.
    + replace (q + S m) with ((1+q)+m) by lia. exact (IHm (1+q) l).
Qed.

Lemma qb_loop m : forall q l,
  (l <* B4 <* W7^^q <* R6 <* W01^^m <* [1]) {{E}}> 0inf -[tm]->*
  (l <* B4 <* W7^^(q+m) <* R6 <* [1]) {{E}}> 0inf.
Proof.
  induction m; intros q l.
  - rewrite Nat.add_0_r. apply evstep_refl.
  - eapply evstep_trans.
    + apply progress_evstep. pose proof (qb q m l 0inf) as H. rewrite Z5 in H. exact H.
    + replace (q + S m) with ((1+q)+m) by lia. exact (IHm (1+q) l).
Qed.

(* the configurations *)
Notation cN1 a b d := (0inf <{{A}} N1 a b d 0inf).
Notation cN2 a b c d := (0inf <{{A}} N2 a b c d 0inf).
Notation cN3 a b z c d := (0inf <{{A}} N3 a b z c d 0inf).
Notation cLC x y z Z c d := (0inf <{{A}} LC x y z Z c d 0inf).
Notation cP1 a s := (0inf <{{A}} P1 a s 0inf).
Notation cP2 a b s := (0inf <{{A}} P2 a b s 0inf).
Notation cT0 a s := (0inf <{{A}} T0f a s 0inf).
Notation cT1 a b c d := (0inf <{{A}} T1f a b c d 0inf).

(* ends of the one-block phase *)
Lemma n1e0_even k t : cN1 (1+k) (2+t*2) 0 -[tm]->+ cP1 (4+k) (7+t).
Proof.
  pose proof (n1s0 (1+k) (t*2) 0inf 0inf) as H1. rewrite Z8, Z18 in H1.
  pose proof (qa_loop (2+(1+k)) (9+t*2) 4 0inf) as H2.
  pose proof (q1odd k (2+t) 0inf 0inf) as H3. rewrite Z9 in H3.
  eapply progress_trans; [ eapply progress_evstep_trans; [ exact H1 | exact H2 ] | exact H3 ].
Qed.
Lemma n1e1_even k t : cN1 (1+k) (2+t*2) 1 -[tm]->+ cP1 (4+k) (7+t).
Proof.
  pose proof (n1s1 (1+k) (t*2) 0inf 0inf) as H1. rewrite Z8, Z9 in H1.
  pose proof (qa_loop (2+(1+k)) (8+t*2) 5 0inf) as H2.
  pose proof (q1odd k (2+t) 0inf 0inf) as H3. rewrite Z9 in H3.
  eapply progress_trans; [ eapply progress_evstep_trans; [ exact H1 | exact H2 ] | exact H3 ].
Qed.
Lemma n1e0_odd k t : cN1 (1+k) (3+t*2) 0 -[tm]->+ cT0 (5+k) (7+t).
Proof.
  pose proof (n1s0 (1+k) (1+t*2) 0inf 0inf) as H1. rewrite Z8, Z18 in H1.
  pose proof (qa_loop (2+(1+k)) (9+(1+t*2)) 4 0inf) as H2.
  pose proof (q1even k (2+t) 0inf 0inf) as H3. rewrite Z1, Z9 in H3.
  eapply progress_trans; [ eapply progress_evstep_trans; [ exact H1 | exact H2 ] | exact H3 ].
Qed.
Lemma n1e1_odd k t : cN1 (1+k) (3+t*2) 1 -[tm]->+ cT0 (5+k) (7+t).
Proof.
  pose proof (n1s1 (1+k) (1+t*2) 0inf 0inf) as H1. rewrite Z8, Z9 in H1.
  pose proof (qa_loop (2+(1+k)) (8+(1+t*2)) 5 0inf) as H2.
  pose proof (q1even k (2+t) 0inf 0inf) as H3. rewrite Z1, Z9 in H3.
  eapply progress_trans; [ eapply progress_evstep_trans; [ exact H1 | exact H2 ] | exact H3 ].
Qed.

(* ends of the two-block phase *)
Lemma n2e0_odd k b s : cN2 (1+k) (8+b) (4+(7+s*2)) 0 -[tm]->+ cP2 (3+k) (16+b) (6+s).
Proof.
  pose proof (n2s0 (1+k) b (7+s*2) 0inf 0inf) as H1. rewrite Z6, Z18 in H1.
  pose proof (qb_loop (7+s*2) 3 (0inf <* W1110^^(3+(1+k)) <* Y2 <* Y2 <* W01^^b)) as H2.
  pose proof (q2even k b s 0inf 0inf) as H3. rewrite Z9 in H3.
  eapply progress_trans; [ eapply progress_evstep_trans; [ exact H1 | exact H2 ] | exact H3 ].
Qed.
Lemma n2e1_odd k b s : cN2 (1+k) (8+b) (5+(6+s*2)) 1 -[tm]->+ cP2 (3+k) (16+b) (6+s).
Proof.
  pose proof (n2s1 (1+k) b (6+s*2) 0inf 0inf) as H1. rewrite Z6, Z9 in H1.
  pose proof (qb_loop (6+s*2) 4 (0inf <* W1110^^(3+(1+k)) <* Y2 <* Y2 <* W01^^b)) as H2.
  pose proof (q2even k b s 0inf 0inf) as H3. rewrite Z9 in H3.
  eapply progress_trans; [ eapply progress_evstep_trans; [ exact H1 | exact H2 ] | exact H3 ].
Qed.
Lemma n2e0_even k b s : cN2 (1+k) (8+b) (4+(6+s*2)) 0 -[tm]->+ cT1 (4+k) 7 (14+b) (4+s).
Proof.
  pose proof (n2s0 (1+k) b (6+s*2) 0inf 0inf) as H1. rewrite Z6, Z18 in H1.
  pose proof (qb_loop (6+s*2) 3 (0inf <* W1110^^(3+(1+k)) <* Y2 <* Y2 <* W01^^b)) as H2.
  pose proof (q2odd k b s 0inf 0inf) as H3. rewrite Z1, Z9 in H3.
  eapply progress_trans; [ eapply progress_evstep_trans; [ exact H1 | exact H2 ] | exact H3 ].
Qed.
Lemma n2e1_even k b s : cN2 (1+k) (8+b) (5+(5+s*2)) 1 -[tm]->+ cT1 (4+k) 7 (14+b) (4+s).
Proof.
  pose proof (n2s1 (1+k) b (5+s*2) 0inf 0inf) as H1. rewrite Z6, Z9 in H1.
  pose proof (qb_loop (5+s*2) 4 (0inf <* W1110^^(3+(1+k)) <* Y2 <* Y2 <* W01^^b)) as H2.
  pose proof (q2odd k b s 0inf 0inf) as H3. rewrite Z1, Z9 in H3.
  eapply progress_trans; [ eapply progress_evstep_trans; [ exact H1 | exact H2 ] | exact H3 ].
Qed.

(* ends of the three-block phase *)
Lemma n3e0_odd k b z s : cN3 (1+k) (6+b) (9+z) (7+s*2) 0 -[tm]->+ cLC (6+k) (21+b) 0 0 (9+z) (4+s).
Proof.
  pose proof (n3s0 (1+k) b z (s*2) 0inf 0inf) as H1. rewrite Z8, Z18 in H1.
  pose proof (qb_loop (7+s*2) 3 (0inf <* W1110^^(3+(1+k)) <* W7 <* W7 <* R6 <* W01^^(11+b) <* R6 <* W01^^(6+z))) as H2.
  pose proof (q3even k (5+b) z s 0inf 0inf) as H3. rewrite Z6, Z9 in H3.
  eapply progress_trans; [ eapply progress_evstep_trans; [ exact H1 | exact H2 ] | exact H3 ].
Qed.
Lemma n3e1_odd k b z s : cN3 (1+k) (6+b) (9+z) (7+s*2) 1 -[tm]->+ cLC (6+k) (21+b) 0 0 (9+z) (4+s).
Proof.
  pose proof (n3s1 (1+k) b z (s*2) 0inf 0inf) as H1. rewrite Z8, Z9 in H1.
  pose proof (qb_loop (6+s*2) 4 (0inf <* W1110^^(3+(1+k)) <* W7 <* W7 <* R6 <* W01^^(11+b) <* R6 <* W01^^(6+z))) as H2.
  pose proof (q3even k (5+b) z s 0inf 0inf) as H3. rewrite Z6, Z9 in H3.
  eapply progress_trans; [ eapply progress_evstep_trans; [ exact H1 | exact H2 ] | exact H3 ].
Qed.
Lemma n3e0_even k b z s : cN3 (10+k) (6+b) (9+z) (7+(1+s*2)) 0 -[tm]->+ 0inf <{{A}} LCc 5 14 (6+k) 15 (6+(5+b)) 6 (6+z) (2+(1+s)) 0inf.
Proof.
  pose proof (n3s0 (10+k) b z (1+s*2) 0inf 0inf) as H1. rewrite Z8, Z18 in H1.
  pose proof (qb_loop (7+(1+s*2)) 3 (0inf <* W1110^^(3+(10+k)) <* W7 <* W7 <* R6 <* W01^^(11+b) <* R6 <* W01^^(6+z))) as H2.
  pose proof (q3odd k (5+b) z (1+s) 0inf 0inf) as H3. rewrite Z13, Z9 in H3.
  eapply progress_trans; [ eapply progress_evstep_trans; [ exact H1 | exact H2 ] | exact H3 ].
Qed.
Lemma n3e1_even k b z s : cN3 (10+k) (6+b) (9+z) (7+(1+s*2)) 1 -[tm]->+ 0inf <{{A}} LCc 5 14 (6+k) 15 (6+(5+b)) 6 (6+z) (2+(1+s)) 0inf.
Proof.
  pose proof (n3s1 (10+k) b z (1+s*2) 0inf 0inf) as H1. rewrite Z8, Z9 in H1.
  pose proof (qb_loop (6+(1+s*2)) 4 (0inf <* W1110^^(3+(10+k)) <* W7 <* W7 <* R6 <* W01^^(11+b) <* R6 <* W01^^(6+z))) as H2.
  pose proof (q3odd k (5+b) z (1+s) 0inf 0inf) as H3. rewrite Z13, Z9 in H3.
  eapply progress_trans; [ eapply progress_evstep_trans; [ exact H1 | exact H2 ] | exact H3 ].
Qed.

(* merging equal blocks *)
Lemma LCm_eq x y n Z c d r : LCm x y n Z c d r = LC x (y+n+Z) 0 0 c d r.
Proof.
  unfold LCm, LC. rewrite !lpow_add'. replace (y+(n+Z)) with (y+n+Z) by lia. reflexivity.
Qed.
Lemma LCc_eq x y z Z c1 n c2 d r : LCc x y z Z c1 n c2 d r = LC x y z Z (c1+n+c2) d r.
Proof.
  unfold LCc, LC. rewrite !lpow_add'. replace (c1+(n+c2)) with (c1+n+c2) by lia. reflexivity.
Qed.

(* the invariant *)
Inductive P : Q * tape -> Prop :=
| PN1 a b d : 24<=a -> 7<=b -> 4*a+29 <= 5*b+24*d -> P (cN1 a b d)
| PP1 a s : 22<=a -> 6<=s -> 4*a+74 <= 24*s -> P (cP1 a s)
| PP2 a b s : 23<=a -> 7<=b -> 6<=s -> 4*a+81 <= 5*b+24*s -> P (cP2 a b s)
| PT0 a s : 28<=a -> 16<=s -> 2*a+22 <= 5*s -> P (cT0 a s)
| PT1 a b c d : 24<=a -> 7<=b -> 6<=c -> 6<=d -> 2*a+22 <= 5*d -> 8*a+702 <= 50*c+65*d ->
    676 <= 40*b+26*c+17*d+49*a -> 261 <= 15*d+2*a -> 4*a+29 <= 5*b+12*c+24*d -> P (cT1 a b c d)
| PLC x y z Z c d : 1<=z -> 6<=y -> 8<=Z -> 7<=c -> 2*z+18 <= 5*d -> 40*x+8*z+606 <= 50*c+65*d ->
    32*x+649 <= 40*Z+26*c+17*d+49*z -> 4*x <= 5*y+12*Z+37 -> 235 <= 10*x+15*d+2*z ->
    4*x <= 5*y+5*Z+12*c+9 -> P (cLC x y z Z c d)
| PLH x y c d : 9<=y -> 7<=c -> 43 <= 2*x+3*d -> 8*x+118 <= 10*c+13*d -> 4*x <= 5*y+12*c+2 -> P (cLC x y 0 0 c d)
| PN2 a b c d : 8<=b -> 11<=c -> 45 <= 2*a+3*d -> 8*a+150 <= 10*c+13*d -> 4*a+37 <= 5*b+12*c -> P (cN2 a b c d)
| PN3 a b z c d : 6<=b -> 9<=z -> 7<=c -> 45 <= 2*a+3*d -> 8*a+73 <= 10*c+13*d ->
    32*a+623 <= 40*z+26*c+17*d -> 4*a <= 5*b+12*z+37 -> P (cN3 a b z c d).

Ltac fin_ := repeat constructor; lia.

Lemma step_N1 a b d : 24<=a -> 7<=b -> 4*a+29 <= 5*b+24*d -> exists c', P c' /\ cN1 a b d -[tm]->+ c'.
Proof.
  intros Ha Hb Hi.
  destruct d as [|[|[|[|d]]]].
  - (* d=0 *)
    destruct a as [|k]; [lia|].
    destruct (Nat.Even_or_Odd b) as [[t Ht]|[t Ht]].
    + assert (E: b = 2+(t-1)*2) by lia. rewrite E.
      refine (ex_intro _ _ (conj _ (n1e0_even k (t-1)))). apply PP1; lia.
    + assert (E: b = 3+(t-1)*2) by lia. rewrite E.
      refine (ex_intro _ _ (conj _ (n1e0_odd k (t-1)))). apply PT0; lia.
  - destruct a as [|k]; [lia|].
    destruct (Nat.Even_or_Odd b) as [[t Ht]|[t Ht]].
    + assert (E: b = 2+(t-1)*2) by lia. rewrite E.
      refine (ex_intro _ _ (conj _ (n1e1_even k (t-1)))). apply PP1; lia.
    + assert (E: b = 3+(t-1)*2) by lia. rewrite E.
      refine (ex_intro _ _ (conj _ (n1e1_odd k (t-1)))). apply PT0; lia.
  - assert (E: b = 2+(b-2)) by lia. rewrite E.
    pose proof (n1_d2 a (b-2) 0inf 0inf) as H. rewrite Z8 in H.
    refine (ex_intro _ _ (conj _ H)). apply PN1; lia.
  - assert (E: b = 2+(b-2)) by lia. rewrite E.
    pose proof (n1_d3 a (b-2) 0inf 0inf) as H. rewrite Z8 in H.
    refine (ex_intro _ _ (conj _ H)). apply PN1; lia.
  - assert (E: b = 2+(b-2)) by lia. rewrite E.
    pose proof (n1_cyc a (b-2) d 0inf 0inf) as H. rewrite Z8 in H.
    refine (ex_intro _ _ (conj _ H)). apply PN1; lia.
Qed.

Lemma step_P1 a s : 22<=a -> 6<=s -> 4*a+74 <= 24*s -> exists c', P c' /\ cP1 a s -[tm]->+ c'.
Proof.
  intros Ha Hs Hi.
  assert (E: s = 6+(s-6)) by lia. rewrite E.
  pose proof (p1_r a (s-6) 0inf 0inf) as H. rewrite Z6 in H.
  refine (ex_intro _ _ (conj _ H)). apply PN1; lia.
Qed.

Lemma step_P2 a b s : 23<=a -> 7<=b -> 6<=s -> 4*a+81 <= 5*b+24*s -> exists c', P c' /\ cP2 a b s -[tm]->+ c'.
Proof.
  intros Ha Hb Hs Hi.
  assert (E: s = 6+(s-6)) by lia. assert (E2: b = 6+(b-6)) by lia. rewrite E, E2.
  pose proof (p2_r a (b-6) (s-6) 0inf 0inf) as H. rewrite Z2 in H.
  refine (ex_intro _ _ (conj _ H)). apply PN1; lia.
Qed.

Lemma step_T0 a s : 28<=a -> 16<=s -> 2*a+22 <= 5*s -> exists c', P c' /\ cT0 a s -[tm]->+ c'.
Proof.
  intros Ha Hs Hi.
  assert (E: s = 8+(s-8)) by lia. assert (E2: a = 14+(a-14)) by lia. rewrite E, E2.
  pose proof (t0_r (a-14) (s-8) 0inf 0inf) as H. rewrite Z12 in H.
  refine (ex_intro _ _ (conj _ H)). apply PLC; lia.
Qed.

Lemma step_T1 a b c d : 24<=a -> 7<=b -> 6<=c -> 6<=d -> 2*a+22 <= 5*d -> 8*a+702 <= 50*c+65*d ->
    676 <= 40*b+26*c+17*d+49*a -> 261 <= 15*d+2*a -> 4*a+29 <= 5*b+12*c+24*d ->
    exists c', P c' /\ cT1 a b c d -[tm]->+ c'.
Proof.
  intros Ha Hb Hc Hd H1 H2 H3 H4 H5.
  assert (E1: a = 9+(a-9)) by lia. assert (E2: b = 7+(b-7)) by lia.
  assert (E3: c = 6+(c-6)) by lia. assert (E4: d = 6+(d-6)) by lia. rewrite E1, E2, E3, E4.
  pose proof (t1_r (a-9) (b-7) (c-6) (d-6) 0inf 0inf) as H. rewrite Z4 in H.
  refine (ex_intro _ _ (conj _ H)). apply PLC; lia.
Qed.

Lemma step_LC x y z Z c d : 1<=z -> 6<=y -> 8<=Z -> 7<=c -> 2*z+18 <= 5*d -> 40*x+8*z+606 <= 50*c+65*d ->
    32*x+649 <= 40*Z+26*c+17*d+49*z -> 4*x <= 5*y+12*Z+37 -> 235 <= 10*x+15*d+2*z ->
    4*x <= 5*y+5*Z+12*c+9 -> exists c', P c' /\ cLC x y z Z c d -[tm]->+ c'.
Proof.
  intros Hz Hy HZ Hc H1 H2 H3 H4 H5 H6.
  assert (E1: y = 6+(y-6)) by lia. assert (E2: Z = 8+(Z-8)) by lia.
  assert (E3: c = 7+(c-7)) by lia. assert (E4: d = 4+(d-4)) by lia.
  destruct z as [|[|[|[|[|[|z]]]]]]; [lia| | | | | |].
  - rewrite E1, E2, E3, E4.
    pose proof (lc_z1 x (y-6) (Z-8) (c-7) (d-4) 0inf 0inf) as H. rewrite Z4 in H.
    refine (ex_intro _ _ (conj _ H)). apply PN3; lia.
  - rewrite E1, E2, E3, E4.
    pose proof (lc_z2 x (y-6) (Z-8) (c-7) (d-4) 0inf 0inf) as H. rewrite Z4 in H.
    refine (ex_intro _ _ (conj _ H)). apply PN3; lia.
  - rewrite E1, E2, E3, E4.
    pose proof (lc_z3 x (y-6) (Z-8) (c-7) (d-4) 0inf 0inf) as H. rewrite Z8, LCm_eq in H.
    refine (ex_intro _ _ (conj _ H)). apply PLH; lia.
  - rewrite E1, E2, E3, E4.
    pose proof (lc_z4 x (y-6) (Z-8) (c-7) (d-4) 0inf 0inf) as H. rewrite Z8, LCm_eq in H.
    refine (ex_intro _ _ (conj _ H)). apply PLH; lia.
  - rewrite E1, E2, E3, E4.
    pose proof (lc_z5 x (y-6) (Z-8) (c-7) (d-4) 0inf 0inf) as H. rewrite Z8, LCm_eq in H.
    refine (ex_intro _ _ (conj _ H)). apply PLH; lia.
  - rewrite E1, E2, E3, E4.
    pose proof (lc_cyc x (y-6) z (Z-8) (c-7) (d-4) 0inf 0inf) as H. rewrite Z8 in H.
    refine (ex_intro _ _ (conj _ H)). apply PLC; lia.
Qed.

Lemma step_LH x y c d : 9<=y -> 7<=c -> 43 <= 2*x+3*d -> 8*x+118 <= 10*c+13*d -> 4*x <= 5*y+12*c+2 ->
    exists c', P c' /\ cLC x y 0 0 c d -[tm]->+ c'.
Proof.
  intros Hy Hc H1 H2 H3.
  assert (E1: y = 6+(y-6)) by lia. assert (E3: c = 7+(c-7)) by lia. rewrite E1, E3.
  pose proof (lh_r x (y-6) (c-7) d 0inf 0inf) as H. rewrite Z2 in H.
  refine (ex_intro _ _ (conj _ H)). apply PN2; lia.
Qed.

Lemma step_N2 a b c d : 8<=b -> 11<=c -> 45 <= 2*a+3*d -> 8*a+150 <= 10*c+13*d -> 4*a+37 <= 5*b+12*c ->
    exists c', P c' /\ cN2 a b c d -[tm]->+ c'.
Proof.
  intros Hb Hc H1 H2 H3.
  destruct d as [|[|[|[|d]]]].
  - destruct a as [|k]; [lia|].
    assert (E1: b = 8+(b-8)) by lia.
    destruct (Nat.Even_or_Odd c) as [[t Ht]|[t Ht]].
    + assert (E: c = 4+(6+(t-5)*2)) by lia. rewrite E1, E.
      refine (ex_intro _ _ (conj _ (n2e0_even k (b-8) (t-5)))). apply PT1; lia.
    + assert (E: c = 4+(7+(t-5)*2)) by lia. rewrite E1, E.
      refine (ex_intro _ _ (conj _ (n2e0_odd k (b-8) (t-5)))). apply PP2; lia.
  - destruct a as [|k]; [lia|].
    assert (E1: b = 8+(b-8)) by lia.
    destruct (Nat.Even_or_Odd c) as [[t Ht]|[t Ht]].
    + assert (E: c = 5+(5+(t-5)*2)) by lia. rewrite E1, E.
      refine (ex_intro _ _ (conj _ (n2e1_even k (b-8) (t-5)))). apply PT1; lia.
    + assert (E: c = 5+(6+(t-5)*2)) by lia. rewrite E1, E.
      refine (ex_intro _ _ (conj _ (n2e1_odd k (b-8) (t-5)))). apply PP2; lia.
  - assert (E1: b = 6+(b-6)) by lia. assert (E3: c = 7+(c-7)) by lia. rewrite E1, E3.
    pose proof (n2_d2 a (b-6) (c-7) 0inf 0inf) as H. rewrite Z6 in H.
    refine (ex_intro _ _ (conj _ H)). apply PLH; lia.
  - assert (E1: b = 6+(b-6)) by lia. assert (E3: c = 7+(c-7)) by lia. rewrite E1, E3.
    pose proof (n2_d3 a (b-6) (c-7) 0inf 0inf) as H. rewrite Z6 in H.
    refine (ex_intro _ _ (conj _ H)). apply PLH; lia.
  - assert (E1: b = 6+(b-6)) by lia. assert (E3: c = 7+(c-7)) by lia. rewrite E1, E3.
    pose proof (n2_cyc a (b-6) (c-7) d 0inf 0inf) as H. rewrite Z6 in H.
    refine (ex_intro _ _ (conj _ H)). apply PLH; lia.
Qed.

Lemma step_N3 a b z c d : 6<=b -> 9<=z -> 7<=c -> 45 <= 2*a+3*d -> 8*a+73 <= 10*c+13*d ->
    32*a+623 <= 40*z+26*c+17*d -> 4*a <= 5*b+12*z+37 -> exists c', P c' /\ cN3 a b z c d -[tm]->+ c'.
Proof.
  intros Hb Hz Hc H1 H2 H3 H4.
  assert (Eb: b = 6+(b-6)) by lia.
  destruct d as [|[|[|[|d]]]].
  - assert (Ez: z = 9+(z-9)) by lia.
    destruct (Nat.Even_or_Odd c) as [[t Ht]|[t Ht]].
    + assert (E: c = 7+(1+(t-4)*2)) by lia.
      assert (Ea: a = 10+(a-10)) by lia. rewrite Ea, Eb, Ez, E.
      pose proof (n3e0_even (a-10) (b-6) (z-9) (t-4)) as H. rewrite LCc_eq in H.
      refine (ex_intro _ _ (conj _ H)). apply PLC; lia.
    + assert (E: c = 7+(t-3)*2) by lia.
      destruct a as [|k]; [lia|]. rewrite Eb, Ez, E.
      refine (ex_intro _ _ (conj _ (n3e0_odd k (b-6) (z-9) (t-3)))). apply PLH; lia.
  - assert (Ez: z = 9+(z-9)) by lia.
    destruct (Nat.Even_or_Odd c) as [[t Ht]|[t Ht]].
    + assert (E: c = 7+(1+(t-4)*2)) by lia.
      assert (Ea: a = 10+(a-10)) by lia. rewrite Ea, Eb, Ez, E.
      pose proof (n3e1_even (a-10) (b-6) (z-9) (t-4)) as H. rewrite LCc_eq in H.
      refine (ex_intro _ _ (conj _ H)). apply PLC; lia.
    + assert (E: c = 7+(t-3)*2) by lia.
      destruct a as [|k]; [lia|]. rewrite Eb, Ez, E.
      refine (ex_intro _ _ (conj _ (n3e1_odd k (b-6) (z-9) (t-3)))). apply PLH; lia.
  - assert (Ez: z = 6+(z-6)) by lia. assert (E: c = 7+(c-7)) by lia. rewrite Eb, Ez, E.
    pose proof (n3_d2 a (b-6) (z-6) (c-7) 0inf 0inf) as H. rewrite Z8 in H.
    refine (ex_intro _ _ (conj _ H)). apply PN3; lia.
  - assert (Ez: z = 6+(z-6)) by lia. assert (E: c = 7+(c-7)) by lia. rewrite Eb, Ez, E.
    pose proof (n3_d3 a (b-6) (z-6) (c-7) 0inf 0inf) as H. rewrite Z8 in H.
    refine (ex_intro _ _ (conj _ H)). apply PN3; lia.
  - assert (Ez: z = 6+(z-6)) by lia. assert (E: c = 7+(c-7)) by lia. rewrite Eb, Ez, E.
    pose proof (n3_cyc a (b-6) (z-6) (c-7) d 0inf 0inf) as H. rewrite Z8 in H.
    refine (ex_intro _ _ (conj _ H)). apply PN3; lia.
Qed.

Lemma step_P : forall c, P c -> exists c', P c' /\ c -[tm]->+ c'.
Proof.
  intros c Hc. destruct Hc.
  - apply step_N1; assumption.
  - apply step_P1; assumption.
  - apply step_P2; assumption.
  - apply step_T0; assumption.
  - apply step_T1; assumption.
  - apply step_LC; assumption.
  - apply step_LH; assumption.
  - apply step_N2; assumption.
  - apply step_N3; assumption.
Qed.

Lemma init : c0 -[tm]->* cN1 24 73 3.
Proof. unfold N1. esx. Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [ apply init | ].
  apply progress_nonhalt with (P:=P); [ exact step_P | ].
  apply PN1; lia.
Qed.
Print Assumptions nonhalt.

End TM1.
