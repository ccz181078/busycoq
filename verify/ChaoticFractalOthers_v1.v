From BusyCoq Require Import Individual62 ES_v2.
Require Import String List Lia ZifyNat PeanoNat.
Import ListNotations.

(* Chaotic-fractal-others TM1--3. Shared block semantics and a closed
   union of normal, entry, recovery and high-cleanup domains prove
   nonhalting. TM3 is defined using the mirror of its original table. *)
Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1RC0RA_1RD0RF_0LE---_1LB1LA_1LD1RA").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Definition S l r a b c d := l <* <[0;1]^^a <{{B}}
  [1] *> [0;1;1;0;1;0]^^b *> [1;0]^^c *> [0] *> [1;0;0]^^d *> r.
Lemma edge1 l r b c:
  l <* <[0;1] <{{B}} [1] *> [0;1;1;0;1;0]^^b *> [1;0]^^c *> [0;1;0] *> r -->*
  l <{{C}} [0;1;0;1] *> [0;0;1;1;0;1]^^b *> [0;1]^^(1+c) *> r.
Proof. es. Qed.
Lemma edge2 l r b c:
  l <* <[0;1]^^2 <{{B}} [1] *> [0;1;1;0;1;0]^^b *> [1;0]^^c *> [0;1;0;0] *> r -->*
  l <{{B}} [1] *> [0;1;1;0;1;0]^^(1+b) *> [1;0]^^(1+c) *> r.
Proof. es. Qed.
Lemma Inc1 l r a b c d: S l r (2+a) b c (2+d) -->* S l r a (1+b) (2+c) d.
Proof. unfold S; es. Qed.
Lemma Incs1 l r a b c d n: S l r (n*2+a) b c (n*2+d) -->* S l r a (n+b) (n*2+c) d.
Proof. gen l r a b c d; ind n Inc1. Qed.
Lemma pass_011 l r n:
  l <* <[0;1;1]^^n <{{C}} [0;1] *> r -->*
  l <{{C}} [0;1] *> [0;1;0]^^n *> r.
Proof. es. Qed.

(* All blank-right returns. P is deliberately restricted to its proved
   parameter chain; the gaps have different output words and return heads.
   The same rules transfer to TM2/TM3 under the checked state bijections. *)
Definition P a := forall l, l <* <[0;1]^^a {{B}}> 0inf -->*
  l <{{C}} [0;1] *> [0;1;0]^^a *> 0inf.
Definition PP a := forall l, l <* <[0;1]^^a {{B}}> 0inf -->*
  l <{{E}} [0;1;1] *> [0;1;0]^^a *> 0inf.
Lemma P0: P 0. Proof. unfold P; es. Qed.
Lemma P3: P 3. Proof. unfold P; es. Qed.
Lemma return_one l: l <* <[0;1] {{B}}> 0inf -->* l <{{B}} [1;0;1;1] *> 0inf.
Proof. es. Qed.
Lemma return_two: PP 2. Proof. unfold PP; es. Qed.
Lemma close l a b:
  [1;1;0]^^(a*2) *> [1] *> l <{{C}} [0;1] *> [0;1;0]^^b *> 0inf -->*
  l <{{E}} [0;1;1] *> [0;1;0]^^(a*2+b) *> 0inf.
Proof. es. Qed.
Lemma close_odd l a b:
  [1;1;0]^^(1+a*2) *> l <{{C}} [0;1] *> [0;1;0]^^b *> 0inf -->*
  l <{{C}} [0;1] *> [0;1;0]^^(1+a*2+b) *> 0inf.
Proof. es. Qed.
Lemma P_S b: P (1+b*2) -> P ((1+b*2)+(3+b*2)).
Proof.
  unfold P; intros HP l.
  rewrite (lpow_add _ (1+b*2) (3+b*2)),Str_app_assoc; follow HP.
  mid (S l 0inf (b*2+2) 1 0 (b*2+0)); [unfold S; es|].
  follow Incs1; unfold S.
  mid ([1;0]^^(1+b*2) *> [1;1;0]^^(3+b*2) *> l {{B}}> 0inf); [es|].
  follow HP; applys_eq (close_odd l (1+b) (1+b*2)); flia.
Qed.
Lemma P_S' b: P (2+b*2) -> P ((2+b*2)+(5+b*2)).
Proof.
  unfold P; intros HP l.
  rewrite (lpow_add _ (2+b*2) (5+b*2)),Str_app_assoc; follow HP.
  mid (S l 0inf (b*2+4) 1 0 (b*2+1)); [unfold S; es|].
  follow Incs1; unfold S.
  mid ([1;0]^^(2+b*2) *> [1;1;0]^^(5+b*2) *> l {{B}}> 0inf); [es|].
  follow HP; applys_eq (close_odd l (2+b) (2+b*2)); flia.
Qed.
Lemma return_odd l b d: P (1+b*2+d) ->
  l <* <[0;1]^^((1+b*2+d)+(1+b*2)) {{B}}> 0inf -->*
  l <{{B}} [1] *> [0;1;1;0;1;0]^^(1+b) *> [1;0]^^(b*2) *>
    [0] *> [1;0;0]^^d *> 0inf.
Proof.
  unfold P; intro HP.
  rewrite (lpow_add _ (1+b*2+d) (1+b*2)),Str_app_assoc; follow HP.
  mid (S l 0inf (b*2) 1 0 (b*2+d)); [unfold S; es|].
  applys_eq (Incs1 l 0inf 0 1 0 d b); unfold S; flia.
Qed.
Lemma return_even l b d: P (2+b*2+d) ->
  l <* <[0;1]^^((2+b*2+d)+(2+b*2)) {{B}}> 0inf -->*
  l <{{C}} [0;1;0;1] *> [0;0;1;1;0;1]^^(1+b) *> [0;1]^^(1+b*2) *>
    [0] *> [1;0;0]^^d *> 0inf.
Proof.
  unfold P; intro HP.
  rewrite (lpow_add _ (2+b*2+d) (2+b*2)),Str_app_assoc; follow HP.
  mid (S l 0inf (b*2+1) 1 0 (b*2+1+d)); [unfold S; es|].
  mid (S l 0inf 1 (1+b) (b*2) (1+d)).
  1: applys_eq (Incs1 l 0inf 1 1 0 (1+d) b); flia.
  unfold S; follow edge1; finish.
Qed.
Lemma return_last l b: P (2+b*2) ->
  l <* <[0;1]^^((2+b*2)+(3+b*2)) {{B}}> 0inf -->*
  l <{{B}} [1] *> [0;1;1;0;1;0]^^(2+b) *> [1;0]^^(1+b*2) *> 0inf.
Proof.
  unfold P; intro HP.
  rewrite (lpow_add _ (2+b*2) (3+b*2)),Str_app_assoc; follow HP.
  mid (S l 0inf (b*2+2) 1 0 (b*2+1)); [unfold S; es|].
  follow Incs1; unfold S; follow edge2; finish.
Qed.
Lemma pred_odd b: P (1+b*2) -> PP ((1+b*2)+(2+b*2)).
Proof.
  unfold P,PP; intros HP l.
  rewrite (lpow_add _ (1+b*2) (2+b*2)),Str_app_assoc; follow HP.
  mid (S l 0inf (b*2+1) 1 0 (b*2+0)); [unfold S; es|].
  follow Incs1; unfold S.
  mid ([1;0]^^(1+b*2) *> [1;1;0]^^(2+b*2) *> [1] *> l {{B}}> 0inf); [es|].
  follow HP; applys_eq (close l (1+b) (1+b*2)); flia.
Qed.
Lemma pred_even b: P (2+b*2) -> PP ((2+b*2)+(4+b*2)).
Proof.
  unfold P,PP; intros HP l.
  rewrite (lpow_add _ (2+b*2) (4+b*2)),Str_app_assoc; follow HP.
  mid (S l 0inf (b*2+3) 1 0 (b*2+1)); [unfold S; es|].
  follow Incs1; unfold S.
  mid ([1;0]^^(2+b*2) *> [1;1;0]^^(4+b*2) *> [1] *> l {{B}}> 0inf); [es|].
  follow HP; applys_eq (close l (2+b) (2+b*2)); flia.
Qed.

(* A middle word is not unchanged on each individual scan. Moving its
   trailing 10 to the front gives x; the forward scan makes y; the return
   restores w. This interface is closed under arbitrary concatenation. *)
Definition Word w x y :=
  w++[1;0]=[1;0]++x /\
  (forall l r, l {{B}}> x *> r -->* l <* rev y {{B}}> r) /\
  (forall l r, l <* rev y <{{A}} r -->* l <{{A}} w *> r).
Lemma Word_nil: Word [] [] [].
Proof. repeat split; intros; finish. Qed.
Lemma Word_U: Word [1;0] [1;0] [0;1].
Proof. repeat split; intros; try reflexivity; es. Qed.
Lemma Word_Y: Word [1;0;0;1] [0;1;1;0] [1;0;1;1].
Proof. repeat split; intros; try reflexivity; es. Qed.
Lemma Word_V: Word [1;0;1;0;0;1] [1;0;0;1;1;0] [0;1;1;0;1;1].
Proof. repeat split; intros; try reflexivity; es. Qed.
Lemma Word_app w1 x1 y1 w2 x2 y2:
  Word w1 x1 y1 -> Word w2 x2 y2 -> Word (w1++w2) (x1++x2) (y1++y2).
Proof.
  intros [E1 [R1 L1]] [E2 [R2 L2]]; repeat split.
  - rewrite <-app_assoc,E2,!app_assoc,E1; reflexivity.
  - intros l r; rewrite !rev_app_distr,!Str_app_assoc.
    follow R1; follow R2; finish.
  - intros l r; rewrite !rev_app_distr,!Str_app_assoc.
    follow L2; follow L1; finish.
Qed.
Lemma Word_pow w x y n: Word w x y -> Word (w^^n) (x^^n) (y^^n).
Proof. intro H; induction n; cbn; auto using Word_nil,Word_app. Qed.
Definition rootW r a w c d := 0inf <{{A}}
  [1;0]^^(1+a) *> w *> [1;0]^^c *> [1;0;1] *> [0;1;0]^^d *> r.
Lemma rootW_step r a w x y c d: Word w x y ->
  rootW r a w c (2+d) -->* rootW r (2+a) w (2+c) d.
Proof.
  intros [E [HR HL]].
  mid ([1;0]^^(2+a) *> 0inf {{B}}>
    (w++[1;0]) *> [1;0]^^(2+c) *> [0;1;0]^^(1+d) *> r).
  1: unfold rootW; rewrite Str_app_assoc; es.
  rewrite E,Str_app_assoc; es; follow HR; es; follow HL; unfold rootW; es.
Qed.
Definition crossW l r a w c d := l <* <[0;1]^^a <{{B}}
  [1;0;1] *> w *> [1;0]^^c *> [1;0;1] *> [0;1;0]^^d *> r.
Lemma crossW_step l r a w x y c d: Word w x y ->
  crossW l r (2+a) w c (2+d) -->*
  crossW l r a ([1;0;1;0;0;1]++w) (2+c) d.
Proof.
  intros [E [HR HL]].
  mid ([0;1;1;0;1;1;0] *> [1;0]^^a *> l {{F}}>
    (w++[1;0]) *> [1;0]^^(2+c) *> [0;1;0]^^(1+d) *> r).
  1: unfold crossW; rewrite !Str_app_assoc; es.
  rewrite E,Str_app_assoc; es; follow HR; es; follow HL; unfold crossW; es.
Qed.
Lemma rootsW r a w x y c d n: Word w x y ->
  rootW r a w c (n*2+d) -->* rootW r (n*2+a) w (n*2+c) d.
Proof.
  intro H; gen a c d; induction n; intros a c d; [finish|].
  follow (rootW_step r a w x y c (n*2+d) H); applys_eq IHn; flia.
Qed.
Lemma root_end0 a b c:
  rootW 0inf a ([1;0;1;0;0;1]^^(1+b)) c 0 -->*
  0inf <* <[0;1]^^(3+a) <* <[0;1;1]^^(2+b*2)
    <* <[0;1]^^(1+c) {{B}}> 0inf.
Proof. unfold rootW; es. Qed.
Lemma root_end1 a b c:
  rootW 0inf a ([1;0;1;0;0;1]^^(1+b)) c 1 -->*
  0inf <* <[0;1]^^(3+a) <* <[0;1;1]^^(2+b*2)
    <* <[0;1]^^(2+c) {{B}}> 0inf.
Proof. unfold rootW; es. Qed.
Lemma crossesW l r a w x y c d n: Word w x y ->
  crossW l r (n*2+a) w c (n*2+d) -->*
  crossW l r a ([1;0;1;0;0;1]^^n++w) (n*2+c) d.
Proof.
  intro H; gen a c d; induction n; intros a c d; [finish|].
  mid (crossW l r (2+a) ([1;0;1;0;0;1]^^n++w) (n*2+c) (2+d)).
  1: applys_eq IHn; flia.
  applys_eq (crossW_step l r a _ _ _ (n*2+c) d
    (Word_app _ _ _ _ _ _ (Word_pow _ _ _ n Word_V) H)); flia.
Qed.
(* The exceptional internal 0 has a two-round cycle. Three U words
   before it keep both scans in the displayed phase. Smaller c is left
   to the other rules; no stronger closure claim is made here. *)
Definition crossZ l r a b c e := l <* <[0;1]^^a <{{B}}
  [1;0;1] *> [1;0;1;0;0;1]^^b *> [1;0]^^c *> [0] *> [1;0]^^e *> r.
Lemma crossZ_step l r a b c e:
  crossZ l r (4+a) b (3+c) (2+e) -->* crossZ l r a (2+b) (3+c) e.
Proof. unfold crossZ; es. Qed.
Lemma crossesZ l r a b c e n:
  crossZ l r (n*4+a) b (3+c) (n*2+e) -->* crossZ l r a (n*2+b) (3+c) e.
Proof. gen l r a b c e; ind n crossZ_step. Qed.
Definition rootZ r a b c e := 0inf <{{A}}
  [1;0]^^(1+a) *> [1;0;1;0;0;1]^^b *> [1;0]^^c *> [0] *> [1;0]^^e *> r.
Lemma rootZ_step r a b c e:
  rootZ r a b (3+c) (2+e) -->* rootZ r (4+a) b (3+c) e.
Proof. unfold rootZ; es. Qed.
Lemma rootsZ r a b c e n:
  rootZ r a b (3+c) (n*2+e) -->* rootZ r (n*4+a) b (3+c) e.
Proof. gen r a b c e; ind n rootZ_step. Qed.
Definition crossV l r a b c e := l <* <[0;1]^^a <{{B}}
  [1;0;1] *> [1;0;1;0;0;1]^^b *> [1;0]^^c *> [0;1;0;0;1] *> [1;0;1;0;0;1]^^e *> r.
Lemma crossV_step l r a b c e:
  crossV l r (4+a) b (3+c) (1+e) -->* crossV l r a (2+b) (4+c) e.
Proof. unfold crossV; es. Qed.
Lemma crossesV l r a b c e n:
  crossV l r (n*4+a) b (3+c) (n+e) -->* crossV l r a (n*2+b) (3+(n+c)) e.
Proof. gen l r a b c e; ind n crossV_step. Qed.
Definition rootV r a b c e := 0inf <{{A}}
  [1;0]^^(1+a) *> [1;0;1;0;0;1]^^b *> [1;0]^^c *> [0;1;0;0;1] *> [1;0;1;0;0;1]^^e *> r.
Lemma rootV_step r a b c e:
  rootV r a b (3+c) (1+e) -->* rootV r (4+a) b (4+c) e.
Proof. unfold rootV; es. Qed.
Lemma rootsV r a b c e n:
  rootV r a b (3+c) (n+e) -->* rootV r (n*4+a) b (3+(n+c)) e.
Proof. gen r a b c e; ind n rootV_step. Qed.

(* The last unary block of a normal list traversal. The unread 010
   suffix includes its final implicit zero; it must not be shortened. *)
Lemma normal_odd_root a d:
  0inf <* <[0;1]^^(3+a*2) <{{C}}
    [0;1] *> [0;1;0]^^(3+a*2+d*2) *> 0inf -->*
  rootW 0inf 2 ([1;0;1;0;0;1]^^(1+a)) (1+a*2) (1+d*2).
Proof.
  mid (S 0inf 0inf (a*2+2) 1 0 (a*2+(2+d*2))).
  1: unfold S; es.
  mid (S 0inf 0inf 2 (a+1) (a*2) (2+d*2)).
  1: applys_eq (Incs1 0inf 0inf 2 1 0 (2+d*2) a); flia.
  follow Inc1; unfold S,rootW; es.
Qed.
Lemma normal_odd a d:
  0inf <* <[0;1]^^(3+a*2) <{{C}}
    [0;1] *> [0;1;0]^^(3+a*2+d*2) *> 0inf -->*
  0inf <* <[0;1]^^(5+d*2) <* <[0;1;1]^^(2+a*2)
    <* <[0;1]^^(3+d*2+a*2) {{B}}> 0inf.
Proof.
  follow normal_odd_root.
  mid (rootW 0inf (2+d*2) ([1;0;1;0;0;1]^^(1+a)) (1+a*2+d*2) 1).
  1: applys_eq (rootsW 0inf 2 _ _ _ (1+a*2) 1 d
      (Word_pow _ _ _ (1+a) Word_V)); flia.
  applys_eq root_end1; flia.
Qed.
Lemma normal_even_root a d:
  0inf <* <[0;1]^^(3+a*2) <{{C}}
    [0;1] *> [0;1;0]^^(2+a*2+d*2) *> 0inf -->*
  rootW 0inf 2 ([1;0;1;0;0;1]^^(1+a)) (1+a*2) (d*2).
Proof.
  mid (S 0inf 0inf (a*2+2) 1 0 (a*2+(1+d*2))).
  1: unfold S; es.
  mid (S 0inf 0inf 2 (a+1) (a*2) (1+d*2)).
  1: applys_eq (Incs1 0inf 0inf 2 1 0 (1+d*2) a); flia.
  destruct d; unfold S,rootW; es.
Qed.
Lemma normal_even a d:
  0inf <* <[0;1]^^(3+a*2) <{{C}}
    [0;1] *> [0;1;0]^^(2+a*2+d*2) *> 0inf -->*
  0inf <* <[0;1]^^(5+d*2) <* <[0;1;1]^^(2+a*2)
    <* <[0;1]^^(2+d*2+a*2) {{B}}> 0inf.
Proof.
  follow normal_even_root.
  mid (rootW 0inf (2+d*2) ([1;0;1;0;0;1]^^(1+a)) (1+a*2+d*2) 0).
  1: applys_eq (rootsW 0inf 2 _ _ _ (1+a*2) 0 d
      (Word_pow _ _ _ (1+a) Word_V)); flia.
  applys_eq root_end0; flia.
Qed.

(* The even left unary block, including its residual-capacity zero case. *)
Lemma even_root a d:
  S 0inf 0inf 1 (1+a) (a*2) (1+d) -->*
  rootW 0inf 0 ([1;0;1;0;0;1]^^(1+a)) (1+a*2) d.
Proof. unfold S,rootW; es. Qed.
Lemma even_end a:
  S 0inf 0inf 1 (1+a) (a*2) 0 -->*
  0inf <* <[0;1] <* <[0;1;1]^^(2+a*2) <* <[0;1]^^(1+a*2) {{B}}> 0inf.
Proof. unfold S; es. Qed.
Lemma even_left_even a d:
  0inf <* <[0;1]^^(2+a*2) <{{C}} [0;1] *> [0;1;0]^^(2+a*2+d*2) *> 0inf -->*
  0inf <* <[0;1]^^(3+d*2) <* <[0;1;1]^^(2+a*2)
    <* <[0;1]^^(2+a*2+d*2) {{B}}> 0inf.
Proof.
  mid (S 0inf 0inf (a*2+1) 1 0 (a*2+(1+d*2))); [unfold S; es|].
  mid (S 0inf 0inf 1 (1+a) (a*2) (1+d*2)).
  1: applys_eq (Incs1 0inf 0inf 1 1 0 (1+d*2) a); flia.
  follow even_root.
  mid (rootW 0inf (d*2) ([1;0;1;0;0;1]^^(1+a)) (1+a*2+d*2) 0).
  1: applys_eq (rootsW 0inf 0 _ _ _ (1+a*2) 0 d (Word_pow _ _ _ (1+a) Word_V)); flia.
  applys_eq root_end0; flia.
Qed.
Lemma even_left_odd a d:
  0inf <* <[0;1]^^(2+a*2) <{{C}} [0;1] *> [0;1;0]^^(1+a*2+d*2) *> 0inf -->*
  0inf <* <[0;1]^^(1+d*2) <* <[0;1;1]^^(2+a*2)
    <* <[0;1]^^(1+a*2+d*2) {{B}}> 0inf.
Proof.
  mid (S 0inf 0inf (a*2+1) 1 0 (a*2+d*2)); [unfold S; es|].
  mid (S 0inf 0inf 1 (1+a) (a*2) (d*2)).
  1: applys_eq (Incs1 0inf 0inf 1 1 0 (d*2) a); flia.
  destruct d; [applys_eq even_end; flia|].
  follow even_root.
  mid (rootW 0inf (d*2) ([1;0;1;0;0;1]^^(1+a)) (1+a*2+d*2) 1).
  1: applys_eq (rootsW 0inf 0 _ _ _ (1+a*2) 1 d (Word_pow _ _ _ (1+a) Word_V)); fold Nat.mul; flia.
  applys_eq root_end1; fold Nat.mul; flia.
Qed.

(* An overflowing unary block returns before reading the left context. *)
Lemma left_overflow0 l a:
  l <* <[0;1]^^(3+a) <{{C}} [0;1] *> 0inf -->*
  l <* <[0;1]^^a <* <[0;1;1]^^3 {{B}}> 0inf.
Proof. es. Qed.
Lemma left_overflow_odd l a d:
  l <* <[0;1]^^(3+d*2+a) <{{C}} [0;1] *> [0;1;0]^^(1+d*2) *> 0inf -->*
  l <* <[0;1]^^a <* <[0;1;1]^^(3+d*2) <* <[0;1]^^(1+d*2) {{B}}> 0inf.
Proof.
  mid (S l 0inf (d*2+(2+a)) 1 0 (d*2)); [unfold S; es|].
  mid (S l 0inf (2+a) (1+d) (d*2) 0).
  1: applys_eq (Incs1 l 0inf (2+a) 1 0 0 d); flia.
  unfold S; es.
Qed.
Lemma left_overflow_even l a d:
  l <* <[0;1]^^(5+d*2+a) <{{C}} [0;1] *> [0;1;0]^^(2+d*2) *> 0inf -->*
  l <* <[0;1]^^a <* <[0;1;1]^^(5+d*2) <* <[0;1]^^(2+d*2) {{B}}> 0inf.
Proof.
  mid (S l 0inf (d*2+(4+a)) 1 0 (d*2+1)); [unfold S; es|].
  mid (S l 0inf (4+a) (1+d) (d*2) 1).
  1: applys_eq (Incs1 l 0inf (4+a) 1 0 1 d); flia.
  unfold S; es.
Qed.

(* An odd 011 block after an odd-gap return. The left blank boundary is
   essential: these rules do not allow an arbitrary unread left context. *)
Definition seed a b c d := 0inf <{{A}}
  [1;0]^^(2+a) *> [0;1;1;0;1;0]^^(1+b) *> [1;0]^^(c*2) *> [0] *> [1;0;0]^^d *> 0inf.
Lemma odd_seed a b c d:
  0inf <* <[0;1]^^c <* <[0;1;1]^^(1+b*2) <{{B}}
    [1] *> [0;1;1;0;1;0]^^(1+a) *> [1;0]^^(a*2) *> [0] *> [1;0;0]^^d *> 0inf -->*
  seed c (b+a) a d.
Proof. unfold seed; es. Qed.
Lemma seed_root a b c d:
  seed a b c (1+d) -->* rootW 0inf (1+a) ([1;0;1;0;0;1]^^(1+b)) (1+c*2) d.
Proof. unfold seed,rootW; es. Qed.
Lemma seed_zero a b c:
  seed a b c 0 -->* 0inf <* <[0;1]^^(2+a) <* <[0;1;1]^^(2+b*2)
    <* <[0;1]^^(1+c*2) {{B}}> 0inf.
Proof. unfold seed; es. Qed.
Lemma seed_odd a b c d:
  seed a b c (1+d*2) -->*
  0inf <* <[0;1]^^(4+a+d*2) <* <[0;1;1]^^(2+b*2)
    <* <[0;1]^^(2+c*2+d*2) {{B}}> 0inf.
Proof.
  follow seed_root.
  mid (rootW 0inf (1+a+d*2) ([1;0;1;0;0;1]^^(1+b)) (1+c*2+d*2) 0).
  1: applys_eq (rootsW 0inf (1+a) _ _ _ (1+c*2) 0 d
      (Word_pow _ _ _ (1+b) Word_V)); flia.
  applys_eq root_end0; flia.
Qed.
Lemma seed_even a b c d:
  seed a b c (2+d*2) -->*
  0inf <* <[0;1]^^(4+a+d*2) <* <[0;1;1]^^(2+b*2)
    <* <[0;1]^^(3+c*2+d*2) {{B}}> 0inf.
Proof.
  follow seed_root.
  mid (rootW 0inf (1+a+d*2) ([1;0;1;0;0;1]^^(1+b)) (1+c*2+d*2) 1).
  1: applys_eq (rootsW 0inf (1+a) _ _ _ (1+c*2) 1 d
      (Word_pow _ _ _ (1+b) Word_V)); flia.
  applys_eq root_end1; flia.
Qed.
(* The capacity -1 boundary has a real lone 1 between two 011 blocks.
   Do not erase it: two complete returns restore a three-block section.
   The hypothesis P restricts the initial counter to its proved chain. *)
Lemma even_exit l a:
  S l 0inf 1 (1+a) (a*2) 0 -->*
  l <* <[1] <* <[0;1;1]^^(2+a*2) <* <[0;1]^^(1+a*2) {{B}}> 0inf.
Proof. unfold S; es. Qed.
Lemma border l a:
  l <* <[0;1]^^(2+a*2) <{{C}} [0;1] *> [0;1;0]^^(1+a*2) *> 0inf -->*
  l <* <[1] <* <[0;1;1]^^(2+a*2) <* <[0;1]^^(1+a*2) {{B}}> 0inf.
Proof.
  mid (S l 0inf (a*2+1) 1 0 (a*2)); [unfold S; es|].
  mid (S l 0inf 1 (1+a) (a*2) 0).
  1: applys_eq (Incs1 l 0inf 1 1 0 0 a); flia.
  follow even_exit; finish.
Qed.
Lemma odd_c_root b c d:
  S 0inf 0inf 1 (1+b) (1+c*2) (1+d) -->*
  rootW 0inf 0 ([1;0;1;0;0;1]^^(1+b)) (2+c*2) d.
Proof. unfold S,rootW; es. Qed.

Definition repair_start a :=
  0inf <* <[0;1]^^(29+a*4) <* <[0;1;1]^^14 <* <[0;1]^^(22+a*2)
    <* <[0;1;1]^^2 <* <[0;1]^^(19+a*2) {{B}}> 0inf.
Definition repair_mid a :=
  0inf <* <[0;1]^^(29+a*4) <* <[0;1;1]^^14 <* <[1]
    <* <[0;1;1]^^(22+a*2) <* <[0;1]^^(21+a*2) {{B}}> 0inf.
Definition repair_tail a := [1;0;0;1;1;0;1;0;1;0] *> [1;0;0]^^(17+a*2) *> 0inf.
Lemma lone_one b l r:
  l <* <[0;1] <* <[0;1;1]^^(b*2) <* <[1] <{{C}} [0;1] *> r -->*
  l <{{C}} [0] *> [1;0;1;0;0;1]^^b *> [1;0]^^2 *> r.
Proof. es. Qed.
Lemma repair_entry a: P (19+a*2) -> repair_mid a -->*
  S 0inf (repair_tail a) (27+a*4) 8 0 (22+a*2).
Proof.
  intro HP; unfold repair_mid.
  mid (0inf <* <[0;1]^^(29+a*4) <* <[0;1;1]^^14 <* <[1]
    <* <[0;1;1]^^(22+a*2) <{{C}} [0;1;0;1] *> [0;0;1;1;0;1] *>
    [0;1] *> [0] *> [1;0;0]^^(17+a*2) *> 0inf).
  1: applys_eq (return_even
    (0inf <* <[0;1]^^(29+a*4) <* <[0;1;1]^^14 <* <[1] <* <[0;1;1]^^(22+a*2))
    0 (17+a*2) HP); flia.
  follow pass_011; follow (lone_one 7).
  unfold S,repair_tail; es.
Qed.
Lemma cross_to_Z l r a b c:
  crossW l ([0;1;1;0;1;0;1;0] *> r) (2+a) ([1;0;1;0;0;1]^^b) (3+c) 0 -->*
  crossZ l r a (1+b) (5+c) 2.
Proof. unfold crossW,crossZ; es. Qed.
Lemma repair_cross a:
  S 0inf (repair_tail a) (5+a*2) (19+a) (22+a*2) 0 -->*
  crossZ 0inf ([1;0;0]^^(17+a*2) *> 0inf)
    (1+a*2) (20+a) (25+a*2) 2.
Proof.
  mid (crossW 0inf ([0;1;1;0;1;0;1;0] *> [1;0;0]^^(17+a*2) *> 0inf)
    (5+a*2) ([1;0;1;0;0;1]^^(18+a)) (21+a*2) 2).
  1: unfold S,repair_tail,crossW; st; simpl_rotate; finish; flia.
  mid (crossW 0inf ([0;1;1;0;1;0;1;0] *> [1;0;0]^^(17+a*2) *> 0inf)
    (3+a*2) ([1;0;1;0;0;1]^^(19+a)) (23+a*2) 0).
  1: applys_eq (crossW_step 0inf ([0;1;1;0;1;0;1;0] *> [1;0;0]^^(17+a*2) *> 0inf)
    (3+a*2) _ _ _ (21+a*2) 0 (Word_pow _ _ _ (18+a) Word_V)); flia.
  applys_eq (cross_to_Z 0inf ([1;0;0]^^(17+a*2) *> 0inf)
    (1+a*2) (19+a) (20+a*2)); flia.
Qed.
Lemma repair_root a:
  crossZ 0inf ([1;0;0]^^(21+a*2) *> 0inf)
    (5+a*2) (22+a) (29+a*2) 2 -->*
  rootW 0inf 0 ([1;0;1;0;0;1]^^(25+a*2)) (28+a*4) 20.
Proof.
  mid (crossZ 0inf ([1;0;0]^^(21+a*2) *> 0inf)
    (1+a*2) (24+a) (29+a*2) 0).
  1: applys_eq (crossZ_step 0inf ([1;0;0]^^(21+a*2) *> 0inf)
    (1+a*2) (22+a) (26+a*2) 0); flia.
  mid (S 0inf 0inf (1+a*2) (25+a) (27+a*2) (21+a*2)).
  1: unfold crossZ,S; st; simpl_rotate; finish; flia.
  mid (S 0inf 0inf 1 (25+a*2) (27+a*4) 21).
  1: applys_eq (Incs1 0inf 0inf 1 (25+a) (27+a*2) 21 a); flia.
  applys_eq (odd_c_root (24+a*2) (13+a*2) 20); flia.
Qed.
Lemma repair_first a: P (19+a*2) -> repair_start a -->* repair_mid a.
Proof.
  unfold P,repair_start,repair_mid; intro HP.
  follow HP; follow pass_011.
  applys_eq (border (0inf <* <[0;1]^^(29+a*4) <* <[0;1;1]^^14) (10+a)); flia.
Qed.
Lemma crossZ_one r b c:
  crossZ 0inf r 1 b (3+c) 2 -->* rootZ r 2 (1+b) (3+c) 0.
Proof. unfold crossZ,rootZ; es. Qed.
Lemma crossZ_three r b c:
  crossZ 0inf r 3 b (3+c) 2 -->* rootZ r 0 (2+b) (3+c) 0.
Proof. unfold crossZ,rootZ; es. Qed.
Definition repair_end a :=
  0inf <* <[0;1]^^23 <* <[0;1;1]^^(42+a*4) <* <[0;1]^^(41+a*4) {{B}}> 0inf.
Lemma repair_exit a:
  crossZ 0inf ([1;0;0]^^(17+a*2) *> 0inf)
    (1+a*2) (20+a) (25+a*2) 2 -->* repair_end a.
Proof.
  mid (rootW 0inf 20 ([1;0;1;0;0;1]^^(21+a*2)) (40+a*4) 0).
  - destruct a as [|[|a]].
    + follow (crossZ_one ([1;0;0]^^17 *> 0inf) 20 22).
      mid (rootW 0inf 2 ([1;0;1;0;0;1]^^21) 22 18).
      1: unfold rootZ,rootW; st; simpl_rotate; finish.
      applys_eq (rootsW 0inf 2 _ _ _ 22 0 9 (Word_pow _ _ _ 21 Word_V)); flia.
    + follow (crossZ_three ([1;0;0]^^19 *> 0inf) 21 24).
      mid (rootW 0inf 0 ([1;0;1;0;0;1]^^23) 24 20).
      1: unfold rootZ,rootW; st; simpl_rotate; finish.
      applys_eq (rootsW 0inf 0 _ _ _ 24 0 10 (Word_pow _ _ _ 23 Word_V)); flia.
    + mid (rootW 0inf 0 ([1;0;1;0;0;1]^^(25+a*2)) (28+a*4) 20).
      1: applys_eq (repair_root a); flia.
      applys_eq (rootsW 0inf 0 _ _ _ (28+a*4) 0 10
        (Word_pow _ _ _ (25+a*2) Word_V)); flia.
  - unfold repair_end; applys_eq (root_end0 20 (20+a*2) (40+a*4)); flia.
Qed.
Lemma repair_second a: P (19+a*2) -> repair_mid a -->* repair_end a.
Proof.
  intro HP; follow (repair_entry a HP).
  mid (S 0inf (repair_tail a) (5+a*2) (19+a) (22+a*2) 0).
  1: applys_eq (Incs1 0inf (repair_tail a) (5+a*2) 8 0 0 (11+a)); flia.
  follow repair_cross; apply repair_exit.
Qed.
Lemma repair a: P (19+a*2) -> repair_start a -->* repair_end a.
Proof. intro HP; follow (repair_first a HP); apply repair_second,HP. Qed.

(* Negative-capacity exits. Early returns preserve the arbitrary unread
   left context; they must not be confused with a complete traversal. *)
Lemma odd_block l r b:
  l <* <[0;1;1]^^(1+b*2) <{{B}}
    [1] *> r -->*
  l <{{A}} [1;0]^^2 *> [0;1;1;0;1;0]^^b *> r.
Proof. es. Qed.

Lemma even_block l r b:
  l <* <[0;1;1]^^(b*2) <{{B}} [1] *> r -->*
  l <{{B}} [1] *> [0;1;1;0;1;0]^^b *> r.
Proof. es. Qed.

Lemma S_exit0 l a b c:
  S l 0inf (2+a) (1+b) c 0 -->*
  l <* <[0;1]^^a <* <[0;1;1]^^(3+b*2) <* <[0;1]^^(1+c) {{B}}> 0inf.
Proof. unfold S; es. Qed.
Lemma S_exit1 l a b c:
  S l 0inf (4+a) (1+b) c 1 -->*
  l <* <[0;1]^^a <* <[0;1;1]^^(5+b*2) <* <[0;1]^^(2+c) {{B}}> 0inf.
Proof. unfold S; es. Qed.
Lemma S_root1 b c d:
  S 0inf 0inf 1 (1+b) c (1+d) -->*
  rootW 0inf 0 ([1;0;1;0;0;1]^^(1+b)) (1+c) d.
Proof. unfold S,rootW; es. Qed.

Lemma into_S l r a d:
  l <* <[0;1]^^(1+a) <{{C}} [0;1] *> [0;1;0]^^(1+d) *> [0;1] *> r -->*
  S l ([1] *> r) a 1 0 d.
Proof. unfold S; es. Qed.
Definition special r := [1;0;0;1;1;0;1;0;1;0] *> r.
Lemma bridge4 l r a b c:
  S l (special r) (4+a) (1+b) (2+c) 0 -->* crossZ l r a (2+b) (5+c) 2.
Proof.
  mid (crossW l ([0;1;1;0;1;0;1;0] *> r) (4+a) ([1;0;1;0;0;1]^^b) (1+c) 2).
  1: unfold S,special,crossW; st; simpl_rotate; finish; flia.
  mid (crossW l ([0;1;1;0;1;0;1;0] *> r) (2+a) ([1;0;1;0;0;1]^^(1+b)) (3+c) 0).
  1: applys_eq (crossW_step l ([0;1;1;0;1;0;1;0] *> r) (2+a) _ _ _ (1+c) 0
    (Word_pow _ _ _ b Word_V)); flia.
  apply cross_to_Z.
Qed.
Lemma bridge8 l r a b c d:
  S l (special ([1;0;0]^^d *> r)) (8+a) (1+b) (2+c) 0 -->*
  S l r a (5+b) (3+c) d.
Proof.
  follow bridge4.
  mid (crossZ l ([1;0;0]^^d *> r) a (4+b) (5+c) 0).
  1: applys_eq (crossZ_step l ([1;0;0]^^d *> r) a (2+b) (2+c) 0); flia.
  unfold crossZ,S; st; simpl_rotate; finish; flia.
Qed.

Lemma negative_first l a d: P (3+a*2) ->
  l <* <[0;1]^^(8+a*2+d*2) <* <[0;1;1]^^2 <* <[0;1]^^(3+a*2) {{B}}> 0inf -->*
  l <* <[0;1]^^(1+d*2) <* <[0;1;1]^^(7+a*2) <* <[0;1]^^(5+a*2) {{B}}> 0inf.
Proof.
  unfold P; intro HP; follow HP; follow pass_011.
  applys_eq (left_overflow_odd l (1+d*2) (2+a)); flia.
Qed.
Definition negative_mid l a d :=
  l <* <[0;1]^^(1+d*2) <* <[0;1;1]^^(7+a*2) <* <[0;1]^^(5+a*2) {{B}}> 0inf.
Lemma negative_entry l a d: P (3+a*2) -> negative_mid l a d -->*
  S l (special ([1;0;0]^^(1+a*2) *> 0inf)) (d*2) 1 0 (6+a*2).
Proof.
  intro HP; unfold negative_mid.
  mid (l <* <[0;1]^^(1+d*2) <* <[0;1;1]^^(7+a*2) <{{C}}
    [0;1;0;1] *> [0;0;1;1;0;1] *> [0;1;0] *> [1;0;0]^^(1+a*2) *> 0inf).
  1: applys_eq (return_even (l <* <[0;1]^^(1+d*2) <* <[0;1;1]^^(7+a*2))
    0 (1+a*2) HP); flia.
  follow pass_011; unfold special; applys_eq (into_S l
    ([0;0;1;1;0;1;0;1;0] *> [1;0;0]^^(1+a*2) *> 0inf) (d*2) (6+a*2)); flia.
Qed.
Lemma negative_early l a k: P (3+a*2) ->
  negative_mid l a (9+a*2+k) -->*
  l <* <[0;1]^^(k*2) <* <[0;1;1]^^(19+a*4) <* <[0;1]^^(9+a*4) {{B}}> 0inf.
Proof.
  intro HP; follow (negative_entry l a (9+a*2+k) HP).
  mid (S l (special ([1;0;0]^^(1+a*2) *> 0inf)) (12+a*2+k*2) (4+a) (6+a*2) 0).
  1: applys_eq (Incs1 l (special ([1;0;0]^^(1+a*2) *> 0inf)) (12+a*2+k*2) 1 0 0 (3+a)); flia.
  mid (S l 0inf (4+a*2+k*2) (8+a) (7+a*2) (1+a*2)).
  1: applys_eq (bridge8 l 0inf (4+a*2+k*2) (3+a) (4+a*2) (1+a*2)); flia.
  mid (S l 0inf (4+k*2) (8+a*2) (7+a*4) 1).
  1: applys_eq (Incs1 l 0inf (4+k*2) (8+a) (7+a*2) 1 a); flia.
  applys_eq (S_exit1 l (k*2) (7+a*2) (7+a*4)); flia.
Qed.

Lemma S_even_block l r b c d e:
  S (l <* <[0;1;1]^^(e*2)) r 0 b c d -->*
  S l r 0 (e+b) c d.
Proof. unfold S; follow even_block; rewrite lpow_add,Str_app_assoc; finish. Qed.

Lemma negative_bounded a b d j u t:
  P (3+a*2) -> a+3=d+j -> d*2=b+3+u -> t+b*2=13+a*4+d*2 ->
  negative_mid (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2)) a d -->*
  0inf <* <[0;1]^^(1+u*2) <* <[0;1;1]^^(19+a*4+b*2)
    <* <[0;1]^^(9+a*4) {{B}}> 0inf.
Proof.
  intros HP E1 E2 E3;
    follow (negative_entry (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2)) a d HP).
  mid (S (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2))
    (special ([1;0;0]^^(1+a*2) *> 0inf)) 0 (1+d) (d*2) (j*2)).
  1: applys_eq (Incs1 (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2))
    (special ([1;0;0]^^(1+a*2) *> 0inf)) 0 1 0 (j*2) d); flia.
  follow S_even_block.
  mid (S 0inf (special ([1;0;0]^^(1+a*2) *> 0inf)) t (b+(1+d)) (d*2) (j*2)).
  1: unfold S; finish.
  mid (S 0inf (special ([1;0;0]^^(1+a*2) *> 0inf))
    (13+a*2+u*2) (4+a+b) (6+a*2) 0).
  1: applys_eq (Incs1 0inf (special ([1;0;0]^^(1+a*2) *> 0inf))
    (13+a*2+u*2) (b+(1+d)) (d*2) 0 j); flia.
  mid (S 0inf 0inf (5+a*2+u*2) (8+a+b) (7+a*2) (1+a*2)).
  1: applys_eq (bridge8 0inf 0inf (5+a*2+u*2) (3+a+b) (4+a*2) (1+a*2)); flia.
  mid (S 0inf 0inf (5+u*2) (8+a*2+b) (7+a*4) 1).
  1: applys_eq (Incs1 0inf 0inf (5+u*2) (8+a+b) (7+a*2) 1 a); flia.
  applys_eq (S_exit1 0inf (1+u*2) (7+a*2+b) (7+a*4)); flia.
Qed.

(* A variable first 011 block produces a variable short tail. The two
   existing internal cycles consume it in bulk, including even P layers. *)

Definition specialN n r :=
  [1] *> [0;0;1;1;0;1]^^(1+n) *> [0;1]^^(1+n*2) *> [0] *> r.

Lemma crossV_end l r a b c e:
  crossV l ([1;0]^^(1+e) *> r) (4+a) b (3+c) 0 -->*
  crossZ l r a (2+b) (4+c) e.
Proof. unfold crossV,crossZ; es. Qed.

Lemma cross_to_V l r a b c n:
  crossW l ([0;1;1] *> [0;1;0;0;1;1]^^(1+n) *>
    [0;1]^^(4+n*2) *> [0] *> r)
    (2+a) ([1;0;1;0;0;1]^^b) (3+c) 0 -->*
  crossV l ([1;0]^^(5+n*2) *> r) a (1+b) (5+c) n.
Proof. unfold crossW,crossV; es. Qed.

Lemma bridgeV l r a b c n:
  S l (specialN (1+n) r) (4+a) (1+b) (2+c) 0 -->*
  crossV l ([1;0]^^(5+n*2) *> r) a (2+b) (5+c) n.
Proof.
  mid (crossW l ([0;1;1] *> [0;1;0;0;1;1]^^(1+n) *>
    [0;1]^^(4+n*2) *> [0] *> r)
    (4+a) ([1;0;1;0;0;1]^^b) (1+c) 2).
  1: unfold S,specialN,crossW; st; simpl_rotate; finish; flia.
  mid (crossW l ([0;1;1] *> [0;1;0;0;1;1]^^(1+n) *>
    [0;1]^^(4+n*2) *> [0] *> r)
    (2+a) ([1;0;1;0;0;1]^^(1+b)) (3+c) 0).
  1: applys_eq (crossW_step l ([0;1;1] *> [0;1;0;0;1;1]^^(1+n) *>
    [0;1]^^(4+n*2) *> [0] *> r) (2+a) _ _ _ (1+c) 0
    (Word_pow _ _ _ b Word_V)); flia.
  apply cross_to_V.
Qed.

Lemma bridges l r a b c d n:
  S l (specialN n ([1;0;0]^^d *> r)) (8+n*8+a) (1+b) (2+c) 0 -->*
  S l r a (5+n*4+b) (3+n+c) d.
Proof.
  destruct n as [|n].
  - change (S l (special ([1;0;0]^^d *> r)) (8+a) (1+b) (2+c) 0 -->*
      S l r a (5+b) (3+c) d); apply bridge8.
  - mid (crossV l ([1;0]^^(5+n*2) *> [1;0;0]^^d *> r)
      (12+n*8+a) (2+b) (5+c) n).
    1: applys_eq (bridgeV l ([1;0;0]^^d *> r) (12+n*8+a) b c n); flia.
    mid (crossV l ([1;0]^^(5+n*2) *> [1;0;0]^^d *> r)
      (12+n*4+a) (2+n*2+b) (5+n+c) 0).
    1: applys_eq (crossesV l ([1;0]^^(5+n*2) *> [1;0;0]^^d *> r)
      (12+n*4+a) (2+b) (2+c) 0 n); flia.
    mid (crossZ l ([1;0;0]^^d *> r) (8+n*4+a) (4+n*2+b) (6+n+c) (4+n*2)).
    1: applys_eq (crossV_end l ([1;0;0]^^d *> r)
      (8+n*4+a) (2+n*2+b) (2+n+c) (4+n*2)); flia.
    mid (crossZ l ([1;0;0]^^d *> r) a (8+n*4+b) (6+n+c) 0).
    1: applys_eq (crossesZ l ([1;0;0]^^d *> r) a (4+n*2+b) (3+n+c) 0 (2+n)); flia.
    unfold crossZ,S; st; simpl_rotate; finish; flia.
Qed.

Definition negativeN l p n d e := l <* <[0;1]^^(1+d*2)
  <* <[0;1;1]^^(p+4+n*2+e) <* <[0;1]^^(p+2+n*2) {{B}}> 0inf.
Lemma negativeN_first_odd l a n d: P (3+a*2) ->
  l <* <[0;1]^^(8+a*2+n*2+d*2) <* <[0;1;1]^^(2+n*2)
    <* <[0;1]^^(3+a*2) {{B}}> 0inf -->*
  negativeN l (3+a*2) n d 0.
Proof.
  intro HP; unfold P in HP; follow HP; follow pass_011; unfold negativeN.
  mid (l <* <[0;1]^^(8+a*2+n*2+d*2) <{{C}}
    [0;1] *> [0;1;0]^^((2+n*2)+(3+a*2)) *> 0inf).
  1: rewrite (lpow_add _ (2+n*2) (3+a*2)),Str_app_assoc; finish.
  applys_eq (left_overflow_odd l (1+d*2) (2+a+n)); flia.
Qed.
Lemma negativeN_first_even l a n d: P (2+a*2) ->
  l <* <[0;1]^^(8+a*2+n*2+d*2) <* <[0;1;1]^^(2+n*2)
    <* <[0;1]^^(2+a*2) {{B}}> 0inf -->*
  negativeN l (2+a*2) n d 1.
Proof.
  intro HP; unfold P in HP; follow HP; follow pass_011; unfold negativeN.
  mid (l <* <[0;1]^^(8+a*2+n*2+d*2) <{{C}}
    [0;1] *> [0;1;0]^^((2+n*2)+(2+a*2)) *> 0inf).
  1: rewrite (lpow_add _ (2+n*2) (2+a*2)),Str_app_assoc; finish.
  applys_eq (left_overflow_even l (1+d*2) (1+a+n)); flia.
Qed.
Lemma negativeN_entry l p n d e d0:
  P p -> p=2+n*2+d0 -> negativeN l p n d e -->*
  S l (specialN n ([1;0;0]^^d0 *> 0inf)) (d*2) 1 0 (p+3+n*2+e).
Proof.
  intros HP E; unfold negativeN.
  mid (l <* <[0;1]^^(1+d*2) <* <[0;1;1]^^(p+4+n*2+e) <{{C}}
    [0;1;0;1] *> [0;0;1;1;0;1]^^(1+n) *> [0;1]^^(1+n*2) *>
    [0] *> [1;0;0]^^d0 *> 0inf).
  1: rewrite E in HP; applys_eq (return_even
    (l <* <[0;1]^^(1+d*2) <* <[0;1;1]^^(p+4+n*2+e)) n d0 HP); flia.
  follow pass_011; unfold specialN; applys_eq (into_S l
    ([0;0;1;1;0;1]^^(1+n) *> [0;1]^^(1+n*2) *> [0] *>
      [1;0;0]^^d0 *> 0inf) (d*2) (p+3+n*2+e)); flia.
Qed.
Lemma negativeN_cross p n d e d0 b j a:
  P p -> p=2+n*2+d0 -> p+3+n*2+e=d*2+j*2 ->
  negativeN (0inf <* <[0;1]^^(j*2+8+n*8+a) <* <[0;1;1]^^(b*2)) p n d e -->*
  S 0inf 0inf a (5+n*4+b+d+j) (1+n+d*2+j*2) d0.
Proof.
  intros HP E1 E2.
  follow (negativeN_entry (0inf <* <[0;1]^^(j*2+8+n*8+a) <* <[0;1;1]^^(b*2))
    p n d e d0 HP E1).
  mid (S (0inf <* <[0;1]^^(j*2+8+n*8+a) <* <[0;1;1]^^(b*2))
    (specialN n ([1;0;0]^^d0 *> 0inf)) 0 (1+d) (d*2) (j*2)).
  1: applys_eq (Incs1 (0inf <* <[0;1]^^(j*2+8+n*8+a) <* <[0;1;1]^^(b*2))
    (specialN n ([1;0;0]^^d0 *> 0inf)) 0 1 0 (j*2) d); flia.
  follow S_even_block.
  mid (S 0inf (specialN n ([1;0;0]^^d0 *> 0inf)) (j*2+8+n*8+a)
    (b+(1+d)) (d*2) (j*2)).
  1: unfold S; finish.
  mid (S 0inf (specialN n ([1;0;0]^^d0 *> 0inf)) (8+n*8+a)
    (1+b+d+j) (d*2+j*2) 0).
  1: applys_eq (Incs1 0inf (specialN n ([1;0;0]^^d0 *> 0inf))
    (8+n*8+a) (b+(1+d)) (d*2) 0 j); flia.
  applys_eq (bridges 0inf 0inf a (b+d+j) (d*2+j*2-2) d0 n); flia.
Qed.

Lemma negativeN_bounded_odd a n d b j r u t:
  P (3+a*2) -> a=n+r -> a+n+3=d+j ->
  d*2=b+n*4+3+u -> t+b*2=13+a*4+d*2 ->
  negativeN (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2)) (3+a*2) n d 0 -->*
  0inf <* <[0;1]^^(1+u*2) <* <[0;1;1]^^(19+a*4+n*8+b*2)
    <* <[0;1]^^(9+a*4+n) {{B}}> 0inf.
Proof.
  intros HP E1 E2 E3 E4.
  mid (S 0inf 0inf (5+r*2+u*2) (8+a+n*5+b) (7+a*2+n*3) (1+r*2)).
  1: applys_eq (negativeN_cross (3+a*2) n d 0 (1+r*2) b j (5+r*2+u*2) HP); flia.
  mid (S 0inf 0inf (5+u*2) (8+a*2+n*4+b) (7+a*4+n) 1).
  1: applys_eq (Incs1 0inf 0inf (5+u*2) (8+a+n*5+b) (7+a*2+n*3) 1 r); flia.
  applys_eq (S_exit1 0inf (1+u*2) (7+a*2+n*4+b) (7+a*4+n)); flia.
Qed.
Lemma negativeN_bounded_even a n d b j r u t:
  P (2+a*2) -> a=n+r -> a+n+3=d+j ->
  d*2=b+n*4+2+u -> t+b*2=13+a*4+d*2 ->
  negativeN (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2)) (2+a*2) n d 1 -->*
  0inf <* <[0;1]^^(1+u*2) <* <[0;1;1]^^(17+a*4+n*8+b*2)
    <* <[0;1]^^(8+a*4+n) {{B}}> 0inf.
Proof.
  intros HP E1 E2 E3 E4.
  mid (S 0inf 0inf (3+r*2+u*2) (8+a+n*5+b) (7+a*2+n*3) (r*2)).
  1: applys_eq (negativeN_cross (2+a*2) n d 1 (r*2) b j (3+r*2+u*2) HP); flia.
  mid (S 0inf 0inf (3+u*2) (8+a*2+n*4+b) (7+a*4+n) 0).
  1: applys_eq (Incs1 0inf 0inf (3+u*2) (8+a+n*5+b) (7+a*2+n*3) 0 r); flia.
  applys_eq (S_exit0 0inf (1+u*2) (7+a*2+n*4+b) (7+a*4+n)); flia.
Qed.

Lemma S_root_exit0 b c v w:
  S 0inf 0inf (1+v*2) (1+b) c (1+v*2+w*2) -->*
  0inf <* <[0;1]^^(3+w*2) <* <[0;1;1]^^(2+b*2+v*2)
    <* <[0;1]^^(2+c+v*2+w*2) {{B}}> 0inf.
Proof.
  mid (S 0inf 0inf 1 (1+b+v) (c+v*2) (1+w*2)).
  1: applys_eq (Incs1 0inf 0inf 1 (1+b) c (1+w*2) v); flia.
  follow S_root1.
  mid (rootW 0inf (w*2) ([1;0;1;0;0;1]^^(1+(b+v))) (1+(c+v*2)+w*2) 0).
  1: applys_eq (rootsW 0inf 0 _ _ _ (1+(c+v*2)) 0 w
    (Word_pow _ _ _ (1+(b+v)) Word_V)); flia.
  applys_eq (root_end0 (w*2) (b+v) (1+(c+v*2)+w*2)); flia.
Qed.
Lemma S_root_exit1 b c v w:
  S 0inf 0inf (1+v*2) (1+b) c (2+v*2+w*2) -->*
  0inf <* <[0;1]^^(3+w*2) <* <[0;1;1]^^(2+b*2+v*2)
    <* <[0;1]^^(3+c+v*2+w*2) {{B}}> 0inf.
Proof.
  mid (S 0inf 0inf 1 (1+b+v) (c+v*2) (2+w*2)).
  1: applys_eq (Incs1 0inf 0inf 1 (1+b) c (2+w*2) v); flia.
  follow S_root1.
  mid (rootW 0inf (w*2) ([1;0;1;0;0;1]^^(1+(b+v))) (1+(c+v*2)+w*2) 1).
  1: applys_eq (rootsW 0inf 0 _ _ _ (1+(c+v*2)) 1 w
    (Word_pow _ _ _ (1+(b+v)) Word_V)); flia.
  applys_eq (root_end1 (w*2) (b+v) (1+(c+v*2)+w*2)); flia.
Qed.

Lemma negativeN_positive_odd a n d b j u v t:
  P (3+a*2) -> a=n+u+v -> a+n+3=d+j ->
  b+n*4+1=d*2+u -> t+b*2=13+a*4+d*2 ->
  negativeN (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2)) (3+a*2) n d 0 -->*
  0inf <* <[0;1]^^(3+u*2) <* <[0;1;1]^^(14+a*4+d*4)
    <* <[0;1]^^(9+a*4+n) {{B}}> 0inf.
Proof.
  intros HP E1 E2 E3 E4.
  mid (S 0inf 0inf (1+v*2) (8+a+n*5+b) (7+a*2+n*3) (1+v*2+u*2)).
  1: applys_eq (negativeN_cross (3+a*2) n d 0 (1+v*2+u*2) b j (1+v*2) HP); flia.
  applys_eq (S_root_exit0 (7+a+n*5+b) (7+a*2+n*3) v u); flia.
Qed.
Lemma negativeN_positive_even a n d b j u v t:
  P (2+a*2) -> a=1+n+u+v -> a+n+3=d+j ->
  b+n*4=d*2+u -> t+b*2=13+a*4+d*2 ->
  negativeN (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2)) (2+a*2) n d 1 -->*
  0inf <* <[0;1]^^(3+u*2) <* <[0;1;1]^^(14+a*4+d*4)
    <* <[0;1]^^(8+a*4+n) {{B}}> 0inf.
Proof.
  intros HP E1 E2 E3 E4.
  mid (S 0inf 0inf (1+v*2) (8+a+n*5+b) (7+a*2+n*3) (2+v*2+u*2)).
  1: applys_eq (negativeN_cross (2+a*2) n d 1 (2+v*2+u*2) b j (1+v*2) HP); flia.
  applys_eq (S_root_exit1 (7+a+n*5+b) (7+a*2+n*3) v u); flia.
Qed.

Lemma S_short1 l b c:
  S l 0inf 3 (1+b) c 1 -->*
  l <* <[1] <* <[0;1;1]^^(4+b*2) <* <[0;1]^^(2+c) {{B}}> 0inf.
Proof. unfold S; es. Qed.
Lemma border_even l a:
  l <* <[0;1]^^(4+a*2) <{{C}} [0;1] *> [0;1;0]^^(2+a*2) *> 0inf -->*
  l <* <[1] <* <[0;1;1]^^(4+a*2) <* <[0;1]^^(2+a*2) {{B}}> 0inf.
Proof.
  mid (S l 0inf (3+a*2) 1 0 (1+a*2)); [unfold S; es|].
  mid (S l 0inf 3 (1+a) (a*2) 1).
  1: applys_eq (Incs1 l 0inf 3 1 0 1 a); flia.
  apply S_short1.
Qed.
Lemma lone_S l r a b m:
  l <* <[0;1]^^(1+a) <{{C}} [0] *> [1;0;1;0;0;1]^^b *>
    [1;0]^^2 *> [0;1;0]^^m *> [0;1] *> r -->*
  S l ([1] *> r) a (1+b) 0 m.
Proof. unfold S; es. Qed.

Definition loneN l p n e := l <* <[1] <* <[0;1;1]^^(p+3+n*2+e)
  <* <[0;1]^^(p+2+n*2) {{B}}> 0inf.
Lemma loneN_first_odd l a n: P (3+a*2) ->
  l <* <[0;1]^^(6+a*2+n*2) <* <[0;1;1]^^(2+n*2)
    <* <[0;1]^^(3+a*2) {{B}}> 0inf -->* loneN l (3+a*2) n 0.
Proof.
  intro HP; unfold P in HP; follow HP; follow pass_011; unfold loneN.
  mid (l <* <[0;1]^^(6+a*2+n*2) <{{C}}
    [0;1] *> [0;1;0]^^((2+n*2)+(3+a*2)) *> 0inf).
  1: rewrite (lpow_add _ (2+n*2) (3+a*2)),Str_app_assoc; finish.
  applys_eq (border l (2+a+n)); flia.
Qed.
Lemma loneN_first_even l a n: P (2+a*2) ->
  l <* <[0;1]^^(6+a*2+n*2) <* <[0;1;1]^^(2+n*2)
    <* <[0;1]^^(2+a*2) {{B}}> 0inf -->* loneN l (2+a*2) n 1.
Proof.
  intro HP; unfold P in HP; follow HP; follow pass_011; unfold loneN.
  mid (l <* <[0;1]^^(6+a*2+n*2) <{{C}}
    [0;1] *> [0;1;0]^^((2+n*2)+(2+a*2)) *> 0inf).
  1: rewrite (lpow_add _ (2+n*2) (2+a*2)),Str_app_assoc; finish.
  applys_eq (border_even l (1+a+n)); flia.
Qed.
Lemma loneN_entry p n e d0 b t:
  P p -> p=2+n*2+d0 ->
  loneN (0inf <* <[0;1]^^(2+t) <* <[0;1;1]^^(b*2)) p n e -->*
  S 0inf (specialN n ([1;0;0]^^d0 *> 0inf)) t (1+b) 0 (p+3+n*2+e).
Proof.
  intros HP E; unfold loneN.
  mid (0inf <* <[0;1]^^(2+t) <* <[0;1;1]^^(b*2) <* <[1]
    <* <[0;1;1]^^(p+3+n*2+e) <{{C}}
    [0;1;0;1] *> [0;0;1;1;0;1]^^(1+n) *> [0;1]^^(1+n*2) *>
    [0] *> [1;0;0]^^d0 *> 0inf).
  1: rewrite E in HP; applys_eq (return_even
    (0inf <* <[0;1]^^(2+t) <* <[0;1;1]^^(b*2) <* <[1]
      <* <[0;1;1]^^(p+3+n*2+e)) n d0 HP); flia.
  follow pass_011; follow (lone_one b); unfold specialN.
  applys_eq (lone_S 0inf ([0;0;1;1;0;1]^^(1+n) *> [0;1]^^(1+n*2) *>
    [0] *> [1;0;0]^^d0 *> 0inf) t b (p+3+n*2+e)); flia.
Qed.
Lemma loneN_cross p n e d0 b h a:
  P p -> p=2+n*2+d0 -> p+3+n*2+e=h*2 ->
  loneN (0inf <* <[0;1]^^(10+h*2+n*8+a) <* <[0;1;1]^^(b*2)) p n e -->*
  S 0inf 0inf a (5+n*4+b+h) (1+n+h*2) d0.
Proof.
  intros HP E1 E2.
  mid (S 0inf (specialN n ([1;0;0]^^d0 *> 0inf)) (8+h*2+n*8+a) (1+b) 0 (h*2)).
  1: applys_eq (loneN_entry p n e d0 b (8+h*2+n*8+a) HP E1); flia.
  mid (S 0inf (specialN n ([1;0;0]^^d0 *> 0inf)) (8+n*8+a) (1+b+h) (h*2) 0).
  1: applys_eq (Incs1 0inf (specialN n ([1;0;0]^^d0 *> 0inf)) (8+n*8+a) (1+b) 0 0 h); flia.
  applys_eq (bridges 0inf 0inf a (b+h) (h*2-2) d0 n); flia.
Qed.
Lemma loneN_odd a n b v t:
  P (3+a*2) -> a=3+n*5+b+v -> t+b*2=11+a*4 ->
  loneN (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2)) (3+a*2) n 0 -->*
  0inf <* <[0;1]^^(9+n*8+b*2) <* <[0;1;1]^^(10+a*4)
    <* <[0;1]^^(9+a*4+n) {{B}}> 0inf.
Proof.
  intros HP E1 E2.
  mid (S 0inf 0inf (1+v*2) (8+a+n*5+b) (7+a*2+n*3) (1+v*2+(3+n*4+b)*2)).
  1: applys_eq (loneN_cross (3+a*2) n 0 (1+v*2+(3+n*4+b)*2) b (a+n+3) (1+v*2) HP); flia.
  applys_eq (S_root_exit0 (7+a+n*5+b) (7+a*2+n*3) v (3+n*4+b)); flia.
Qed.
Lemma loneN_even a n b v t:
  P (2+a*2) -> a=3+n*5+b+v -> t+b*2=11+a*4 ->
  loneN (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2)) (2+a*2) n 1 -->*
  0inf <* <[0;1]^^(7+n*8+b*2) <* <[0;1;1]^^(10+a*4)
    <* <[0;1]^^(8+a*4+n) {{B}}> 0inf.
Proof.
  intros HP E1 E2.
  mid (S 0inf 0inf (1+v*2) (8+a+n*5+b) (7+a*2+n*3) (2+v*2+(2+n*4+b)*2)).
  1: applys_eq (loneN_cross (2+a*2) n 1 (2+v*2+(2+n*4+b)*2) b (a+n+3) (1+v*2) HP); flia.
  applys_eq (S_root_exit1 (7+a+n*5+b) (7+a*2+n*3) v (2+n*4+b)); flia.
Qed.

(* Composable traversal through a variable short tail, including arrival
   at the left blank boundary before the tail has been consumed. *)
Lemma crossW_one r b c d:
  crossW 0inf r 1 ([1;0;1;0;0;1]^^b) c (2+d) -->*
  rootW r 0 ([1;0;1;0;0;1]^^(1+b)) (2+c) d.
Proof. unfold crossW,rootW; es. Qed.
Lemma root_to_Z r a b c:
  rootW ([0;1;1;0;1;0;1;0] *> r) a ([1;0;1;0;0;1]^^b) (3+c) 0 -->*
  rootZ r (2+a) b (5+c) 2.
Proof. unfold rootW,rootZ; es. Qed.
Lemma cross_to_Z_one r b c:
  crossW 0inf ([0;1;1;0;1;0;1;0] *> r) 1 ([1;0;1;0;0;1]^^b) (3+c) 0 -->*
  rootZ r 0 (1+b) (5+c) 2.
Proof. unfold crossW,rootZ; es. Qed.
Lemma root_to_V r a b c n:
  rootW ([0;1;1] *> [0;1;0;0;1;1]^^(1+n) *> [0;1]^^(4+n*2) *> [0] *> r)
    a ([1;0;1;0;0;1]^^b) (3+c) 0 -->*
  rootV ([1;0]^^(5+n*2) *> r) (2+a) b (5+c) n.
Proof. unfold rootW,rootV; es. Qed.
Lemma cross_to_V_one r b c n:
  crossW 0inf ([0;1;1] *> [0;1;0;0;1;1]^^(1+n) *> [0;1]^^(4+n*2) *> [0] *> r)
    1 ([1;0;1;0;0;1]^^b) (3+c) 0 -->*
  rootV ([1;0]^^(5+n*2) *> r) 0 (1+b) (5+c) n.
Proof. unfold crossW,rootV; es. Qed.
Lemma rootV_end r a b c e:
  rootV ([1;0]^^(1+e) *> r) a b (3+c) 0 -->*
  rootZ r (4+a) b (4+c) e.
Proof. unfold rootV,rootZ; es. Qed.
Lemma crossV_one r b c e:
  crossV 0inf r 1 b (3+c) (1+e) -->* rootV r 2 (1+b) (4+c) e.
Proof. unfold crossV,rootV; es. Qed.
Lemma crossV_three r b c e:
  crossV 0inf r 3 b (3+c) (1+e) -->* rootV r 0 (2+b) (4+c) e.
Proof. unfold crossV,rootV; es. Qed.
Lemma crossVend_one r b c e:
  crossV 0inf ([1;0]^^(1+e) *> r) 1 b (3+c) 0 -->* rootZ r 2 (1+b) (4+c) e.
Proof. unfold crossV,rootZ; es. Qed.
Lemma crossVend_three r b c e:
  crossV 0inf ([1;0]^^(1+e) *> r) 3 b (3+c) 0 -->* rootZ r 0 (2+b) (4+c) e.
Proof. unfold crossV,rootZ; es. Qed.
Lemma crossZ_one' r b c e:
  crossZ 0inf r 1 b (3+c) (2+e) -->* rootZ r 2 (1+b) (3+c) e.
Proof. unfold crossZ,rootZ; es. Qed.
Lemma crossZ_three' r b c e:
  crossZ 0inf r 3 b (3+c) (2+e) -->* rootZ r 0 (2+b) (3+c) e.
Proof. unfold crossZ,rootZ; es. Qed.
Lemma rootZ_end r a b c d:
  rootZ ([1;0;0]^^d *> r) a b (3+c) 0 -->*
  rootW ([0] *> r) a ([1;0;1;0;0;1]^^b) c (1+d).
Proof. unfold rootZ,rootW; st; simpl_rotate; finish. Qed.
Lemma S_root1' r b c d:
  S 0inf r 1 (1+b) c (1+d) -->*
  rootW ([0] *> r) 0 ([1;0;1;0;0;1]^^(1+b)) (1+c) d.
Proof. unfold S,rootW; es. Qed.

(* A compositional budget for a block: spending 2n copies of 01 either
   stays away from the left edge, or crosses it after an odd remainder.
   The root branch retains the same 011 counter and grows its prefix. *)
Record Flow (C:side->nat->nat->Q*tape) (R:nat->nat->Q*tape)
  (D:side->nat->nat->Q*tape) (T:nat->nat->Q*tape) n : Prop := {
  flow_cross: forall l a b, C l (n*2+a) b -->* D l a (n+b);
  flow_root: forall a b, R a b -->* T (n*2+a) b;
  flow_border: forall s v b, s+v+1=n ->
    C 0inf (1+s*2) b -->* T (v*2) (1+s+b)
}.
Lemma Flow_id C R: Flow C R C R 0.
Proof. constructor; intros; try finish; lia. Qed.
Lemma Flow_trans C R D T F U n m:
  Flow C R D T n -> Flow D T F U m -> Flow C R F U (n+m).
Proof.
  intros [HC HR HB] [KC KR KB]; constructor; intros.
  - mid (D l (m*2+a) (n+b)); [applys_eq HC; flia|applys_eq KC; flia].
  - follow HR; applys_eq KR; flia.
  - destruct (Nat.le_gt_cases n s).
    + mid (D 0inf (1+(s-n)*2) (n+b)); [applys_eq HC; flia|].
      applys_eq (KB (s-n) v (n+b)); flia.
    + mid (T ((n-s-1)*2) (1+s+b)); [apply HB; flia|].
      applys_eq KR; flia.
Qed.
Lemma Flow_W r c d:
  Flow (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b) c (2+d))
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b) c (2+d))
    (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b) (2+c) d)
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b) (2+c) d) 1.
Proof.
  constructor; intros; cbn beta.
  - apply (crossW_step l r a _ _ _ c d (Word_pow _ _ _ b Word_V)).
  - apply (rootW_step r a _ _ _ c d (Word_pow _ _ _ b Word_V)).
  - assert (s=0%nat /\ v=0%nat) as [-> ->] by lia; apply crossW_one.
Qed.
Lemma Flow_to_Z r c:
  Flow (fun l a b=>crossW l ([0;1;1;0;1;0;1;0] *> r) a ([1;0;1;0;0;1]^^b) (3+c) 0)
    (fun a b=>rootW ([0;1;1;0;1;0;1;0] *> r) a ([1;0;1;0;0;1]^^b) (3+c) 0)
    (fun l a b=>crossZ l r a b (5+c) 2)
    (fun a b=>rootZ r a b (5+c) 2) 1.
Proof.
  constructor; intros; cbn beta; try apply cross_to_Z; try apply root_to_Z.
  assert (s=0%nat /\ v=0%nat) as [-> ->] by lia; apply cross_to_Z_one.
Qed.
Lemma Flow_to_V r c n:
  Flow (fun l a b=>crossW l ([0;1;1] *> [0;1;0;0;1;1]^^(1+n) *>
    [0;1]^^(4+n*2) *> [0] *> r) a ([1;0;1;0;0;1]^^b) (3+c) 0)
    (fun a b=>rootW ([0;1;1] *> [0;1;0;0;1;1]^^(1+n) *>
    [0;1]^^(4+n*2) *> [0] *> r) a ([1;0;1;0;0;1]^^b) (3+c) 0)
    (fun l a b=>crossV l ([1;0]^^(5+n*2) *> r) a b (5+c) n)
    (fun a b=>rootV ([1;0]^^(5+n*2) *> r) a b (5+c) n) 1.
Proof.
  constructor; intros; cbn beta; try apply cross_to_V; try apply root_to_V.
  assert (s=0%nat /\ v=0%nat) as [-> ->] by lia; apply cross_to_V_one.
Qed.
Lemma Flow_V r c e:
  Flow (fun l a b=>crossV l r a b (3+c) (1+e))
    (fun a b=>rootV r a b (3+c) (1+e))
    (fun l a b=>crossV l r a b (4+c) e)
    (fun a b=>rootV r a b (4+c) e) 2.
Proof.
  constructor; intros; cbn beta; try apply crossV_step; try apply rootV_step.
  destruct s as [|[|s]]; try lia;
    [assert (v=1%nat) as -> by lia; apply crossV_one|
     assert (v=0%nat) as -> by lia; apply crossV_three].
Qed.
Lemma Flow_Z r c e:
  Flow (fun l a b=>crossZ l r a b (3+c) (2+e))
    (fun a b=>rootZ r a b (3+c) (2+e))
    (fun l a b=>crossZ l r a b (3+c) e)
    (fun a b=>rootZ r a b (3+c) e) 2.
Proof.
  constructor; intros; cbn beta; try apply crossZ_step; try apply rootZ_step.
  destruct s as [|[|s]]; try lia;
    [assert (v=1%nat) as -> by lia; apply crossZ_one'|
     assert (v=0%nat) as -> by lia; apply crossZ_three'].
Qed.
Lemma Flow_V_end r c e:
  Flow (fun l a b=>crossV l ([1;0]^^(1+e) *> r) a b (3+c) 0)
    (fun a b=>rootV ([1;0]^^(1+e) *> r) a b (3+c) 0)
    (fun l a b=>crossZ l r a b (4+c) e)
    (fun a b=>rootZ r a b (4+c) e) 2.
Proof.
  constructor; intros; cbn beta; try apply crossV_end; try apply rootV_end.
  destruct s as [|[|s]]; try lia;
    [assert (v=1%nat) as -> by lia; apply crossVend_one|
     assert (v=0%nat) as -> by lia; apply crossVend_three].
Qed.

Lemma Flow_Vs r c e n:
  Flow (fun l a b=>crossV l r a b (3+c) (e+n))
    (fun a b=>rootV r a b (3+c) (e+n))
    (fun l a b=>crossV l r a b (3+c+n) e)
    (fun a b=>rootV r a b (3+c+n) e) (n*2).
Proof.
  gen c e; induction n; intros.
  - rewrite !Nat.add_0_r; apply Flow_id.
  - rewrite !Nat.add_succ_r.
    eapply Flow_trans with (n:=2%nat) (m:=n*2); [apply Flow_V|apply IHn].
Qed.
Lemma Flow_Zs r c e n:
  Flow (fun l a b=>crossZ l r a b (3+c) (e+n*2))
    (fun a b=>rootZ r a b (3+c) (e+n*2))
    (fun l a b=>crossZ l r a b (3+c) e)
    (fun a b=>rootZ r a b (3+c) e) (n*2).
Proof.
  induction n.
  - rewrite !Nat.add_0_r; apply Flow_id.
  - cbn [Nat.mul]; try rewrite !Nat.add_succ_r.
    replace (e+(2+n*2)) with (2+(e+n*2)) by lia.
    eapply Flow_trans with (n:=2%nat) (m:=n*2); [apply Flow_Z|apply IHn].
Qed.
Definition flow_tail n r := [0;1;1] *> [0;1;0;0;1;1]^^n *>
  [0;1]^^(2+n*2) *> [0] *> r.
Lemma Flow_tail r c n:
  Flow (fun l a b=>crossW l (flow_tail n r) a ([1;0;1;0;0;1]^^b) (1+c) 2)
    (fun a b=>rootW (flow_tail n r) a ([1;0;1;0;0;1]^^b) (1+c) 2)
    (fun l a b=>crossZ l r a b (5+c+n) 0)
    (fun a b=>rootZ r a b (5+c+n) 0) (4+n*4).
Proof.
  eapply Flow_trans with (n:=1%nat) (m:=3+n*4); [apply Flow_W|].
  destruct n as [|n].
  - rewrite !Nat.add_0_r; unfold flow_tail.
    eapply Flow_trans with (n:=1%nat) (m:=2%nat); [apply Flow_to_Z|].
    apply (Flow_Z r (2+c) 0).
  - rewrite !Nat.add_succ_r.
    replace (3+Datatypes.S n*4)%nat with (1+(n*2+(2+(2+n)*2)))%nat by lia.
    unfold flow_tail.
    eapply Flow_trans with (n:=1%nat) (m:=n*2+(2+(2+n)*2)); [apply Flow_to_V|].
    eapply Flow_trans with (n:=n*2) (m:=2+(2+n)*2); [apply (Flow_Vs _ (2+c) 0 n)|].
    eapply Flow_trans with (n:=2%nat) (m:=(2+n)*2); [apply Flow_V_end|].
    applys_eq (Flow_Zs r (3+c+n) 0 (2+n)); flia.
Qed.
Lemma bridges_root n s v b c d:
  s+v=3+n*4 ->
  S 0inf (specialN n ([1;0;0]^^d *> 0inf)) (1+s*2) (1+b) (2+c) 0 -->*
  rootW 0inf (v*2) ([1;0;1;0;0;1]^^(1+s+b)) (2+c+n) (1+d).
Proof.
  intro E.
  mid (crossW 0inf (flow_tail n ([1;0;0]^^d *> 0inf))
    (1+s*2) ([1;0;1;0;0;1]^^b) (1+c) 2).
  1: unfold S,specialN,crossW,flow_tail; st; simpl_rotate; finish; flia.
  mid (rootZ ([1;0;0]^^d *> 0inf) (v*2) (1+s+b) (5+c+n) 0).
  1: apply (flow_border _ _ _ _ _ (Flow_tail _ c n)); flia.
  applys_eq (rootZ_end 0inf (v*2) (1+s+b) (2+c+n) d); flia.
  solve_const0_eq.
Qed.

Lemma root_tail_entry n r a b c:
  rootW ([0] *> specialN n r) a ([1;0;1;0;0;1]^^b) c 1 -->*
  rootW (flow_tail n r) a ([1;0;1;0;0;1]^^b) c 2.
Proof. unfold rootW,specialN,flow_tail; st; simpl_rotate; finish. Qed.

Lemma S_tail_root n s v b c j d:
  1<=c+j -> s+v+1=j+4+n*4 ->
  S 0inf (specialN n ([1;0;0]^^d *> 0inf)) (1+s*2) (1+b) (c*2) (j*2) -->*
  rootW 0inf (v*2) ([1;0;1;0;0;1]^^(1+b+s)) ((c+j)*2+n) (1+d).
Proof.
  intros E1 E2; destruct (Nat.le_gt_cases j s).
  - mid (S 0inf (specialN n ([1;0;0]^^d *> 0inf))
      (1+(s-j)*2) (1+b+j) ((c+j)*2) 0).
    1: applys_eq (Incs1 0inf (specialN n ([1;0;0]^^d *> 0inf))
      (1+(s-j)*2) (1+b) (c*2) 0 j); flia.
    applys_eq (bridges_root n (s-j) v (b+j) ((c+j)*2-2) d); flia.
  - mid (rootW ([0] *> specialN n ([1;0;0]^^d *> 0inf))
      ((j-s-1)*2) ([1;0;1;0;0;1]^^(1+b+s)) ((c+j)*2-1) 1).
    + mid (S 0inf (specialN n ([1;0;0]^^d *> 0inf))
        1 (1+b+s) ((c+s)*2) (2+(j-s-1)*2)).
      1: applys_eq (Incs1 0inf (specialN n ([1;0;0]^^d *> 0inf))
        1 (1+b) (c*2) (2+(j-s-1)*2) s); flia.
      follow S_root1'.
      applys_eq (rootsW ([0] *> specialN n ([1;0;0]^^d *> 0inf)) 0 _ _ _ (1+(c+s)*2) 1 (j-s-1)
        (Word_pow _ _ _ (1+b+s) Word_V)); flia.
    + follow root_tail_entry.
      mid (rootZ ([1;0;0]^^d *> 0inf) (v*2) (1+b+s) (3+(c+j)*2+n) 0).
      1: applys_eq (flow_root _ _ _ _ _ (Flow_tail ([1;0;0]^^d *> 0inf) ((c+j)*2-2) n)
        ((j-s-1)*2) (1+b+s)); flia.
      applys_eq (rootZ_end 0inf (v*2) (1+b+s) ((c+j)*2+n) d); flia.
      solve_const0_eq.
Qed.

Lemma negativeN_absorb p n d e d0 b j t:
  P p -> p=2+n*2+d0 -> p+3+n*2+e=d*2+j*2 ->
  negativeN (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2)) p n d e -->*
  S 0inf (specialN n ([1;0;0]^^d0 *> 0inf)) t (1+b+d) (d*2) (j*2).
Proof.
  intros HP E1 E2; follow (negativeN_entry
    (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2)) p n d e d0 HP E1).
  mid (S (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2))
    (specialN n ([1;0;0]^^d0 *> 0inf)) 0 (1+d) (d*2) (j*2)).
  1: applys_eq (Incs1 (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2))
    (specialN n ([1;0;0]^^d0 *> 0inf)) 0 1 0 (j*2) d); flia.
  follow S_even_block; unfold S; finish; flia.
Qed.
Lemma negativeN_root p n d e d0 b j s v:
  P p -> p=2+n*2+d0 -> p+3+n*2+e=d*2+j*2 -> 1<=d+j ->
  s+v+1=j+4+n*4 ->
  negativeN (0inf <* <[0;1]^^(1+s*2) <* <[0;1;1]^^(b*2)) p n d e -->*
  rootW 0inf (v*2) ([1;0;1;0;0;1]^^(1+b+d+s)) ((d+j)*2+n) (1+d0).
Proof.
  intros HP E1 E2 E3 E4; follow (negativeN_absorb p n d e d0 b j (1+s*2) HP E1 E2).
  applys_eq (S_tail_root n s v (b+d) d j d0); flia.
Qed.
Lemma negativeN_root_odd a n d b j r s v:
  P (3+a*2) -> a=n+r -> a+n+3=d+j -> s+b=6+a*2+d -> s+v+1=j+4+n*4 ->
  negativeN (0inf <* <[0;1]^^(1+s*2) <* <[0;1;1]^^(b*2)) (3+a*2) n d 0 -->*
  0inf <* <[0;1]^^(5+v*2+r*2) <* <[0;1;1]^^(14+a*4+d*4)
    <* <[0;1]^^(9+a*4+n) {{B}}> 0inf.
Proof.
  intros HP E1 E2 E3 E4.
  mid (rootW 0inf (v*2) ([1;0;1;0;0;1]^^(1+b+d+s)) ((d+j)*2+n) (2+r*2)).
  1: applys_eq (negativeN_root (3+a*2) n d 0 (1+r*2) b j s v HP); flia.
  mid (rootW 0inf (2+v*2+r*2) ([1;0;1;0;0;1]^^(1+b+d+s))
    (2+(d+j)*2+n+r*2) 0).
  1: applys_eq (rootsW 0inf (v*2) _ _ _ ((d+j)*2+n) 0 (1+r)
    (Word_pow _ _ _ (1+b+d+s) Word_V)); flia.
  applys_eq (root_end0 (2+v*2+r*2) (b+d+s) (2+(d+j)*2+n+r*2)); flia.
Qed.
Lemma negativeN_root_even a n d b j r s v:
  P (2+a*2) -> a=n+r -> a+n+3=d+j -> s+b=6+a*2+d -> s+v+1=j+4+n*4 ->
  negativeN (0inf <* <[0;1]^^(1+s*2) <* <[0;1;1]^^(b*2)) (2+a*2) n d 1 -->*
  0inf <* <[0;1]^^(3+v*2+r*2) <* <[0;1;1]^^(14+a*4+d*4)
    <* <[0;1]^^(8+a*4+n) {{B}}> 0inf.
Proof.
  intros HP E1 E2 E3 E4.
  mid (rootW 0inf (v*2) ([1;0;1;0;0;1]^^(1+b+d+s)) ((d+j)*2+n) (1+r*2)).
  1: applys_eq (negativeN_root (2+a*2) n d 1 (r*2) b j s v HP); flia.
  mid (rootW 0inf (v*2+r*2) ([1;0;1;0;0;1]^^(1+b+d+s)) ((d+j)*2+n+r*2) 1).
  1: applys_eq (rootsW 0inf (v*2) _ _ _ ((d+j)*2+n) 1 r
    (Word_pow _ _ _ (1+b+d+s) Word_V)); flia.
  applys_eq (root_end1 (v*2+r*2) (b+d+s) ((d+j)*2+n+r*2)); flia.
Qed.

Lemma loneN_root p n e d0 b h s v:
  P p -> p=2+n*2+d0 -> p+3+n*2+e=h*2 -> 1<=h ->
  s+v+1=h+4+n*4 ->
  loneN (0inf <* <[0;1]^^(3+s*2) <* <[0;1;1]^^(b*2)) p n e -->*
  rootW 0inf (v*2) ([1;0;1;0;0;1]^^(1+b+s)) (h*2+n) (1+d0).
Proof.
  intros HP E1 E2 E3 E4.
  mid (S 0inf (specialN n ([1;0;0]^^d0 *> 0inf)) (1+s*2) (1+b) 0 (h*2)).
  1: applys_eq (loneN_entry p n e d0 b (1+s*2) HP E1); flia.
  applys_eq (S_tail_root n s v b 0 h d0); flia.
Qed.
Lemma loneN_root_odd a n b r s v:
  P (3+a*2) -> a=n+r -> s+b=4+a*2 -> s+v+1=a+n+7+n*4 ->
  loneN (0inf <* <[0;1]^^(3+s*2) <* <[0;1;1]^^(b*2)) (3+a*2) n 0 -->*
  0inf <* <[0;1]^^(5+v*2+r*2) <* <[0;1;1]^^(10+a*4)
    <* <[0;1]^^(9+a*4+n) {{B}}> 0inf.
Proof.
  intros HP E1 E2 E3.
  mid (rootW 0inf (v*2) ([1;0;1;0;0;1]^^(1+b+s)) ((a+n+3)*2+n) (2+r*2)).
  1: applys_eq (loneN_root (3+a*2) n 0 (1+r*2) b (a+n+3) s v HP); flia.
  mid (rootW 0inf (2+v*2+r*2) ([1;0;1;0;0;1]^^(1+b+s))
    (2+(a+n+3)*2+n+r*2) 0).
  1: applys_eq (rootsW 0inf (v*2) _ _ _ ((a+n+3)*2+n) 0 (1+r)
    (Word_pow _ _ _ (1+b+s) Word_V)); flia.
  applys_eq (root_end0 (2+v*2+r*2) (b+s) (2+(a+n+3)*2+n+r*2)); flia.
Qed.
Lemma loneN_root_even a n b r s v:
  P (2+a*2) -> a=n+r -> s+b=4+a*2 -> s+v+1=a+n+7+n*4 ->
  loneN (0inf <* <[0;1]^^(3+s*2) <* <[0;1;1]^^(b*2)) (2+a*2) n 1 -->*
  0inf <* <[0;1]^^(3+v*2+r*2) <* <[0;1;1]^^(10+a*4)
    <* <[0;1]^^(8+a*4+n) {{B}}> 0inf.
Proof.
  intros HP E1 E2 E3.
  mid (rootW 0inf (v*2) ([1;0;1;0;0;1]^^(1+b+s)) ((a+n+3)*2+n) (1+r*2)).
  1: applys_eq (loneN_root (2+a*2) n 1 (r*2) b (a+n+3) s v HP); flia.
  mid (rootW 0inf (v*2+r*2) ([1;0;1;0;0;1]^^(1+b+s)) ((a+n+3)*2+n+r*2) 1).
  1: applys_eq (rootsW 0inf (v*2) _ _ _ ((a+n+3)*2+n) 1 r
    (Word_pow _ _ _ (1+b+s) Word_V)); flia.
  applys_eq (root_end1 (v*2+r*2) (b+s) ((a+n+3)*2+n+r*2)); flia.
Qed.

Lemma S_short0 l b c:
  S l 0inf 1 (1+b) c 0 -->*
  l <* <[1] <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(1+c) {{B}}> 0inf.
Proof. unfold S; es. Qed.
Lemma negativeN_one_odd a n d b j r t:
  P (3+a*2) -> a=n+r -> a+n+3=d+j -> b+n*4+2=d*2 -> t+b*2=13+a*4+d*2 ->
  negativeN (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2)) (3+a*2) n d 0 -->*
  0inf <* <[0;1] <* <[0;1;1]^^(14+a*4+d*4) <* <[0;1]^^(9+a*4+n) {{B}}> 0inf.
Proof.
  intros HP E1 E2 E3 E4.
  mid (S 0inf 0inf (3+r*2) (8+a+n*5+b) (7+a*2+n*3) (1+r*2)).
  1: applys_eq (negativeN_cross (3+a*2) n d 0 (1+r*2) b j (3+r*2) HP); flia.
  mid (S 0inf 0inf 3 (8+a+n*5+b+r) (7+a*2+n*3+r*2) 1).
  1: applys_eq (Incs1 0inf 0inf 3 (8+a+n*5+b) (7+a*2+n*3) 1 r); flia.
  replace (0inf <* <[0;1]) with (0inf <* <[1]) by solve_const0_eq.
  applys_eq (S_short1 0inf (7+a+n*5+b+r) (7+a*2+n*3+r*2)); flia.
Qed.
Lemma negativeN_one_even a n d b j r t:
  P (2+a*2) -> a=n+r -> a+n+3=d+j -> b+n*4+1=d*2 -> t+b*2=13+a*4+d*2 ->
  negativeN (0inf <* <[0;1]^^t <* <[0;1;1]^^(b*2)) (2+a*2) n d 1 -->*
  0inf <* <[0;1] <* <[0;1;1]^^(14+a*4+d*4) <* <[0;1]^^(8+a*4+n) {{B}}> 0inf.
Proof.
  intros HP E1 E2 E3 E4.
  mid (S 0inf 0inf (1+r*2) (8+a+n*5+b) (7+a*2+n*3) (r*2)).
  1: applys_eq (negativeN_cross (2+a*2) n d 1 (r*2) b j (1+r*2) HP); flia.
  mid (S 0inf 0inf 1 (8+a+n*5+b+r) (7+a*2+n*3+r*2) 0).
  1: applys_eq (Incs1 0inf 0inf 1 (8+a+n*5+b) (7+a*2+n*3) 0 r); flia.
  replace (0inf <* <[0;1]) with (0inf <* <[1]) by solve_const0_eq.
  applys_eq (S_short0 0inf (7+a+n*5+b+r) (7+a*2+n*3+r*2)); flia.
Qed.

(* Traversal with an intervening even 011 block. *)
Lemma crossW_block l r B b c d:
  crossW (l <* <[0;1;1]^^(B*2)) r 0 ([1;0;1;0;0;1]^^b) c d -->*
  crossW l r 0 ([1;0;1;0;0;1]^^(B+b)) c d.
Proof. unfold crossW; follow even_block; st; simpl_rotate; finish; flia. Qed.
Lemma crossV_block l r B b c e:
  crossV (l <* <[0;1;1]^^(B*2)) r 0 b c e -->* crossV l r 0 (B+b) c e.
Proof. unfold crossV; follow even_block; st; simpl_rotate; finish; flia. Qed.
Lemma crossZ_block l r B b c e:
  crossZ (l <* <[0;1;1]^^(B*2)) r 0 b c e -->* crossZ l r 0 (B+b) c e.
Proof. unfold crossZ; follow even_block; st; simpl_rotate; finish; flia. Qed.

Lemma crossV_step_block l r a B b c e:
  crossV (l <* <[0;1]^^(2+a) <* <[0;1;1]^^(B*2)) r 2 b (3+c) (1+e) -->*
  crossV l r a (2+B+b) (4+c) e.
Proof. unfold crossV; es. Qed.
Lemma crossZ_step_block l r a B b c e:
  crossZ (l <* <[0;1]^^(2+a) <* <[0;1;1]^^(B*2)) r 2 b (3+c) (2+e) -->*
  crossZ l r a (2+B+b) (3+c) e.
Proof. unfold crossZ; es. Qed.
Lemma crossVend_block l r a B b c e:
  crossV (l <* <[0;1]^^(2+a) <* <[0;1;1]^^(B*2))
    ([1;0]^^(1+e) *> r) 2 b (3+c) 0 -->* crossZ l r a (2+B+b) (4+c) e.
Proof. unfold crossV,crossZ; es. Qed.

Lemma crossV_step_block_root r B b c e:
  crossV (0inf <* <[0;1] <* <[0;1;1]^^(B*2)) r 2 b (3+c) (1+e) -->*
  rootV r 0 (2+B+b) (4+c) e.
Proof. unfold crossV,rootV; es. Qed.
Lemma crossZ_step_block_root r B b c e:
  crossZ (0inf <* <[0;1] <* <[0;1;1]^^(B*2)) r 2 b (3+c) (2+e) -->*
  rootZ r 0 (2+B+b) (3+c) e.
Proof. unfold crossZ,rootZ; es. Qed.
Lemma crossVend_block_root r B b c e:
  crossV (0inf <* <[0;1] <* <[0;1;1]^^(B*2))
    ([1;0]^^(1+e) *> r) 2 b (3+c) 0 -->* rootZ r 0 (2+B+b) (4+c) e.
Proof. unfold crossV,rootZ; es. Qed.

Lemma crossW_absorb l r a B b c d:
  crossW (l <* <[0;1]^^a <* <[0;1;1]^^(B*2)) r 0 ([1;0;1;0;0;1]^^b) c d -->*
  crossW l r a ([1;0;1;0;0;1]^^(B+b)) c d.
Proof. follow crossW_block; unfold crossW; st; finish. Qed.
Lemma crossV_absorb l r a B b c e:
  crossV (l <* <[0;1]^^a <* <[0;1;1]^^(B*2)) r 0 b c e -->* crossV l r a (B+b) c e.
Proof. follow crossV_block; unfold crossV; st; finish. Qed.
Lemma crossZ_absorb l r a B b c e:
  crossZ (l <* <[0;1]^^a <* <[0;1;1]^^(B*2)) r 0 b c e -->* crossZ l r a (B+b) c e.
Proof. follow crossZ_block; unfold crossZ; st; finish. Qed.

(* The even 011 block is consumed exactly once, when reached. The budget
   counts only 01 pairs; B contributes to the output counter, not time. *)
Record BlockFlow (C:side->nat->nat->Q*tape) (R:nat->nat->Q*tape)
  (D:side->nat->nat->Q*tape) (T:nat->nat->Q*tape) n : Prop := {
  block_flow: Flow C R D T n;
  block_cross: forall l a B b s v, s+v+1=n ->
    C (l <* <[0;1]^^(2+v*2+a) <* <[0;1;1]^^(B*2)) (s*2) b -->*
    D l a (n+B+b);
  block_border: forall B b s t v, s+t+v+1=n ->
    C (0inf <* <[0;1]^^(1+t*2) <* <[0;1;1]^^(B*2)) (s*2) b -->*
    T (v*2) (1+s+t+B+b)
}.
Lemma BlockFlow_id C R: BlockFlow C R C R 0.
Proof. constructor; [apply Flow_id| |]; intros; lia. Qed.
Lemma BlockFlow_trans C R D T F U n m:
  BlockFlow C R D T n -> BlockFlow D T F U m -> BlockFlow C R F U (n+m).
Proof.
  intros [H HC HB] [K KC KB]; constructor; [eapply Flow_trans; eauto| |].
  - intros l a B b s v E; destruct (Nat.le_gt_cases n s).
    + mid (D (l <* <[0;1]^^(2+v*2+a) <* <[0;1;1]^^(B*2)) ((s-n)*2) (n+b)).
      1: applys_eq (flow_cross _ _ _ _ _ H); flia.
      applys_eq (KC l a B (n+b) (s-n) v); flia.
    + mid (D l (m*2+a) (n+B+b)).
      1: applys_eq (HC l (m*2+a) B b s (n-s-1)); flia.
      applys_eq (flow_cross _ _ _ _ _ K); flia.
  - intros B b s t v E; destruct (Nat.le_gt_cases n s).
    + mid (D (0inf <* <[0;1]^^(1+t*2) <* <[0;1;1]^^(B*2)) ((s-n)*2) (n+b)).
      1: applys_eq (flow_cross _ _ _ _ _ H); flia.
      applys_eq (KB B (n+b) (s-n) t v); flia.
    + destruct (Nat.le_gt_cases n (s+t)).
      * mid (D 0inf (1+(s+t-n)*2) (n+B+b)).
        1: applys_eq (HC 0inf (1+(s+t-n)*2) B b s (n-s-1)); flia.
        applys_eq (flow_border _ _ _ _ _ K (s+t-n) v (n+B+b)); flia.
      * mid (T ((n-s-t-1)*2) (1+s+t+B+b)).
        1: apply HB; flia.
        applys_eq (flow_root _ _ _ _ _ K); flia.
Qed.

Lemma BlockFlow_one C R D T:
  Flow C R D T 1 ->
  (forall l a B b, C (l <* <[0;1]^^a <* <[0;1;1]^^(B*2)) 0%nat b -->* C l a (B+b)) ->
  BlockFlow C R D T 1.
Proof.
  intros H Hblock; constructor; [exact H| |].
  - intros l a B b s v E; assert (s=0%nat /\ v=0%nat) as [-> ->] by lia.
    follow Hblock; applys_eq (flow_cross _ _ _ _ _ H l a (B+b)); flia.
  - intros B b s t v E; assert (s=0%nat /\ t=0%nat /\ v=0%nat) as [-> [-> ->]] by lia.
    follow Hblock; applys_eq (flow_border _ _ _ _ _ H 0 0 (B+b)); flia.
Qed.
Lemma BlockFlow_two C R D T:
  Flow C R D T 2 ->
  (forall l a B b, C (l <* <[0;1]^^a <* <[0;1;1]^^(B*2)) 0%nat b -->* C l a (B+b)) ->
  (forall l a B b, C (l <* <[0;1]^^(2+a) <* <[0;1;1]^^(B*2)) 2%nat b -->*
    D l a (2+B+b)) ->
  (forall B b, C (0inf <* <[0;1] <* <[0;1;1]^^(B*2)) 2%nat b -->*
    T 0%nat (2+B+b)) ->
  BlockFlow C R D T 2.
Proof.
  intros H Hblock HC HB; constructor; [exact H| |].
  - intros l a B b s v E; destruct s as [|[|s]]; try lia.
    + follow Hblock; applys_eq (flow_cross _ _ _ _ _ H l a (B+b)); flia.
    + assert (v=0%nat) as -> by lia; apply HC.
  - intros B b s t v E; destruct s as [|[|s]]; try lia.
    + follow Hblock; applys_eq (flow_border _ _ _ _ _ H t v (B+b)); flia.
    + assert (t=0%nat /\ v=0%nat) as [-> ->] by lia; apply HB.
Qed.

Lemma BlockFlow_W r c d:
  BlockFlow (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b) c (2+d))
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b) c (2+d))
    (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b) (2+c) d)
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b) (2+c) d) 1.
Proof. apply BlockFlow_one; [apply Flow_W|intros; apply crossW_absorb]. Qed.
Lemma BlockFlow_to_Z r c:
  BlockFlow (fun l a b=>crossW l ([0;1;1;0;1;0;1;0] *> r) a ([1;0;1;0;0;1]^^b) (3+c) 0)
    (fun a b=>rootW ([0;1;1;0;1;0;1;0] *> r) a ([1;0;1;0;0;1]^^b) (3+c) 0)
    (fun l a b=>crossZ l r a b (5+c) 2)
    (fun a b=>rootZ r a b (5+c) 2) 1.
Proof. apply BlockFlow_one; [apply Flow_to_Z|intros; apply crossW_absorb]. Qed.
Lemma BlockFlow_to_V r c n:
  BlockFlow (fun l a b=>crossW l ([0;1;1] *> [0;1;0;0;1;1]^^(1+n) *>
    [0;1]^^(4+n*2) *> [0] *> r) a ([1;0;1;0;0;1]^^b) (3+c) 0)
    (fun a b=>rootW ([0;1;1] *> [0;1;0;0;1;1]^^(1+n) *>
    [0;1]^^(4+n*2) *> [0] *> r) a ([1;0;1;0;0;1]^^b) (3+c) 0)
    (fun l a b=>crossV l ([1;0]^^(5+n*2) *> r) a b (5+c) n)
    (fun a b=>rootV ([1;0]^^(5+n*2) *> r) a b (5+c) n) 1.
Proof. apply BlockFlow_one; [apply Flow_to_V|intros; apply crossW_absorb]. Qed.
Lemma BlockFlow_V r c e:
  BlockFlow (fun l a b=>crossV l r a b (3+c) (1+e))
    (fun a b=>rootV r a b (3+c) (1+e))
    (fun l a b=>crossV l r a b (4+c) e)
    (fun a b=>rootV r a b (4+c) e) 2.
Proof. apply BlockFlow_two; intros; auto using Flow_V,crossV_absorb,crossV_step_block,crossV_step_block_root. Qed.
Lemma BlockFlow_Z r c e:
  BlockFlow (fun l a b=>crossZ l r a b (3+c) (2+e))
    (fun a b=>rootZ r a b (3+c) (2+e))
    (fun l a b=>crossZ l r a b (3+c) e)
    (fun a b=>rootZ r a b (3+c) e) 2.
Proof. apply BlockFlow_two; intros; auto using Flow_Z,crossZ_absorb,crossZ_step_block,crossZ_step_block_root. Qed.
Lemma BlockFlow_V_end r c e:
  BlockFlow (fun l a b=>crossV l ([1;0]^^(1+e) *> r) a b (3+c) 0)
    (fun a b=>rootV ([1;0]^^(1+e) *> r) a b (3+c) 0)
    (fun l a b=>crossZ l r a b (4+c) e)
    (fun a b=>rootZ r a b (4+c) e) 2.
Proof. apply BlockFlow_two; intros; auto using Flow_V_end,crossV_absorb,crossVend_block,crossVend_block_root. Qed.

Lemma BlockFlow_Vs r c e n:
  BlockFlow (fun l a b=>crossV l r a b (3+c) (e+n))
    (fun a b=>rootV r a b (3+c) (e+n))
    (fun l a b=>crossV l r a b (3+c+n) e)
    (fun a b=>rootV r a b (3+c+n) e) (n*2).
Proof.
  gen c e; induction n; intros.
  - rewrite !Nat.add_0_r; apply BlockFlow_id.
  - rewrite !Nat.add_succ_r.
    eapply BlockFlow_trans with (n:=2%nat) (m:=n*2); [apply BlockFlow_V|apply IHn].
Qed.
Lemma BlockFlow_Zs r c e n:
  BlockFlow (fun l a b=>crossZ l r a b (3+c) (e+n*2))
    (fun a b=>rootZ r a b (3+c) (e+n*2))
    (fun l a b=>crossZ l r a b (3+c) e)
    (fun a b=>rootZ r a b (3+c) e) (n*2).
Proof.
  induction n.
  - rewrite !Nat.add_0_r; apply BlockFlow_id.
  - cbn [Nat.mul]; try rewrite !Nat.add_succ_r.
    replace (e+(2+n*2)) with (2+(e+n*2)) by lia.
    eapply BlockFlow_trans with (n:=2%nat) (m:=n*2); [apply BlockFlow_Z|apply IHn].
Qed.
Lemma BlockFlow_tail r c n:
  BlockFlow (fun l a b=>crossW l (flow_tail n r) a ([1;0;1;0;0;1]^^b) (1+c) 2)
    (fun a b=>rootW (flow_tail n r) a ([1;0;1;0;0;1]^^b) (1+c) 2)
    (fun l a b=>crossZ l r a b (5+c+n) 0)
    (fun a b=>rootZ r a b (5+c+n) 0) (4+n*4).
Proof.
  eapply BlockFlow_trans with (n:=1%nat) (m:=3+n*4); [apply BlockFlow_W|].
  destruct n as [|n].
  - rewrite !Nat.add_0_r; unfold flow_tail.
    eapply BlockFlow_trans with (n:=1%nat) (m:=2%nat); [apply BlockFlow_to_Z|].
    apply (BlockFlow_Z r (2+c) 0).
  - rewrite !Nat.add_succ_r.
    replace (3+Datatypes.S n*4)%nat with (1+(n*2+(2+(2+n)*2)))%nat by lia.
    unfold flow_tail.
    eapply BlockFlow_trans with (n:=1%nat) (m:=n*2+(2+(2+n)*2)); [apply BlockFlow_to_V|].
    eapply BlockFlow_trans with (n:=n*2) (m:=2+(2+n)*2); [apply (BlockFlow_Vs _ (2+c) 0 n)|].
    eapply BlockFlow_trans with (n:=2%nat) (m:=(2+n)*2); [apply BlockFlow_V_end|].
    applys_eq (BlockFlow_Zs r (3+c+n) 0 (2+n)); flia.
Qed.

Lemma crossW_finish0 l a b c:
  crossW l 0inf (2+a) ([1;0;1;0;0;1]^^b) c 0 -->*
  l <* <[0;1]^^a <* <[0;1;1]^^(3+b*2) <* <[0;1]^^(1+c) {{B}}> 0inf.
Proof. unfold crossW; es. Qed.
Lemma crossW_finish1 l a b c:
  crossW l 0inf (2+a) ([1;0;1;0;0;1]^^b) c 1 -->*
  l <* <[0;1]^^a <* <[0;1;1]^^(3+b*2) <* <[0;1]^^(2+c) {{B}}> 0inf.
Proof. unfold crossW; es. Qed.
Lemma crossW_short0 l b c:
  crossW l 0inf 1 ([1;0;1;0;0;1]^^b) c 0 -->*
  l <* <[1] <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(1+c) {{B}}> 0inf.
Proof. unfold crossW; es. Qed.
Lemma crossW_short1 l b c:
  crossW l 0inf 1 ([1;0;1;0;0;1]^^b) c 1 -->*
  l <* <[1] <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(2+c) {{B}}> 0inf.
Proof. unfold crossW; es. Qed.

Lemma crossW_finish l a b c e: e<=1 ->
  crossW l 0inf (2+a) ([1;0;1;0;0;1]^^b) c e -->*
  l <* <[0;1]^^a <* <[0;1;1]^^(3+b*2) <* <[0;1]^^(1+c+e) {{B}}> 0inf.
Proof.
  destruct e as [|[|e]]; intro E; try lia;
    [applys_eq (crossW_finish0 l a b c)|applys_eq (crossW_finish1 l a b c)]; flia.
Qed.
Lemma crossW_short b c e: e<=1 ->
  crossW 0inf 0inf 1 ([1;0;1;0;0;1]^^b) c e -->*
  0inf <* <[0;1] <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(1+c+e) {{B}}> 0inf.
Proof.
  intro E; replace (0inf <* <[0;1]) with (0inf <* <[1]) by solve_const0_eq.
  destruct e as [|[|e]]; try lia;
    [applys_eq (crossW_short0 0inf b c)|applys_eq (crossW_short1 0inf b c)]; flia.
Qed.
Lemma rootW_finish a b c e: e<=1 ->
  rootW 0inf a ([1;0;1;0;0;1]^^(1+b)) c e -->*
  0inf <* <[0;1]^^(3+a) <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(1+c+e) {{B}}> 0inf.
Proof.
  destruct e as [|[|e]]; intro E; try lia;
    [applys_eq (root_end0 a b c)|applys_eq (root_end1 a b c)]; flia.
Qed.

Lemma crossZ_end r a b c d l:
  crossZ l ([1;0;0]^^d *> r) a b (3+c) 0 -->*
  crossW l ([0] *> r) a ([1;0;1;0;0;1]^^b) c (1+d).
Proof. unfold crossZ,crossW; st; simpl_rotate; finish. Qed.
Lemma BlockFlow_Z_end r c d:
  BlockFlow (fun l a b=>crossZ l ([1;0;0]^^d *> r) a b (3+c) 0)
    (fun a b=>rootZ ([1;0;0]^^d *> r) a b (3+c) 0)
    (fun l a b=>crossW l ([0] *> r) a ([1;0;1;0;0;1]^^b) c (1+d))
    (fun a b=>rootW ([0] *> r) a ([1;0;1;0;0;1]^^b) c (1+d)) 0.
Proof.
  constructor; [constructor; intros; cbn beta; auto using crossZ_end,rootZ_end; lia| |]; intros; lia.
Qed.
Lemma BlockFlow_Ws r c e n:
  BlockFlow (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b) c (e+n*2))
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b) c (e+n*2))
    (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b) (c+n*2) e)
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b) (c+n*2) e) n.
Proof.
  gen c; induction n; intro c.
  - rewrite !Nat.add_0_r; apply BlockFlow_id.
  - cbn [Nat.mul]; replace (e+(2+n*2)) with (2+(e+n*2)) by lia.
    replace (c+(2+n*2)) with ((2+c)+n*2) by lia.
    eapply BlockFlow_trans with (n:=1%nat) (m:=n); [apply BlockFlow_W|apply IHn].
Qed.
Lemma BlockFlow_whole c n d q e: 1+d=e+q*2 ->
  BlockFlow (fun l a b=>crossW l (flow_tail n ([1;0;0]^^d *> 0inf))
      a ([1;0;1;0;0;1]^^b) (1+c) 2)
    (fun a b=>rootW (flow_tail n ([1;0;0]^^d *> 0inf))
      a ([1;0;1;0;0;1]^^b) (1+c) 2)
    (fun l a b=>crossW l 0inf a ([1;0;1;0;0;1]^^b) (2+c+n+q*2) e)
    (fun a b=>rootW 0inf a ([1;0;1;0;0;1]^^b) (2+c+n+q*2) e) (4+n*4+q).
Proof.
  intro E; eapply BlockFlow_trans; [apply BlockFlow_tail|].
  replace q with (0+q)%nat at 1 by lia.
  eapply BlockFlow_trans with (n:=0%nat) (m:=q); [apply BlockFlow_Z_end|].
  rewrite E; replace ([0] *> 0inf) with 0inf by solve_const0_eq.
  apply BlockFlow_Ws.
Qed.

Lemma S_tail_entry l r a b c n:
  S l (specialN n r) a (1+b) (2+c) 0 -->*
  crossW l (flow_tail n r) a ([1;0;1;0;0;1]^^b) (1+c) 2.
Proof. unfold S,specialN,crossW,flow_tail; st; simpl_rotate; finish; flia. Qed.

Lemma negativeN_large_start l p n e h k d0:
  P p -> p=2+n*2+d0 -> p+3+n*2+e=h*2 -> 1<=h ->
  negativeN l p n (h+k) e -->*
  crossW l (flow_tail n ([1;0;0]^^d0 *> 0inf)) (k*2) ([1;0;1;0;0;1]^^h) (h*2-1) 2.
Proof.
  intros HP E1 E2 Hh; follow (negativeN_entry l p n (h+k) e d0 HP E1).
  mid (S l (specialN n ([1;0;0]^^d0 *> 0inf)) (k*2) (1+h) (h*2) 0).
  1: applys_eq (Incs1 l (specialN n ([1;0;0]^^d0 *> 0inf)) (k*2) 1 0 0 h); flia.
  applys_eq (S_tail_entry l ([1;0;0]^^d0 *> 0inf) (k*2) h (h*2-2) n); flia.
Qed.

Lemma negativeN_large_early l p n e h d0 q M u:
  P p -> p=2+n*2+d0 -> p+3+n*2+e=h*2 -> 1<=h -> e<=1 ->
  1+d0=e+q*2 -> M=4+n*4+q ->
  negativeN l p n (h+M+1+u) e -->*
  l <* <[0;1]^^(u*2) <* <[0;1;1]^^(3+(M+h)*2)
    <* <[0;1]^^(1+h*2+n+q*2+e) {{B}}> 0inf.
Proof.
  intros HP E1 E2 Hh He E3 EM.
  mid (crossW l (flow_tail n ([1;0;0]^^d0 *> 0inf))
    ((M+1+u)*2) ([1;0;1;0;0;1]^^h) (h*2-1) 2).
  1: applys_eq (negativeN_large_start l p n e h (M+1+u) d0 HP E1 E2 Hh); flia.
  mid (crossW l 0inf (2+u*2) ([1;0;1;0;0;1]^^(M+h)) (h*2+n+q*2) e).
  1: applys_eq (flow_cross _ _ _ _ _ (block_flow _ _ _ _ _
    (BlockFlow_whole (h*2-2) n d0 q e E3)) l (2+u*2) h); flia.
  applys_eq (crossW_finish l (u*2) (M+h) (h*2+n+q*2) e He); flia.
Qed.

Lemma negativeN_large_cross l p n e h k d0 q M B v a:
  P p -> p=2+n*2+d0 -> p+3+n*2+e=h*2 -> 1<=h ->
  1+d0=e+q*2 -> M=4+n*4+q -> k+v=M ->
  negativeN (l <* <[0;1]^^(v*2+a) <* <[0;1;1]^^(B*2)) p n (h+k) e -->*
  crossW l 0inf a ([1;0;1;0;0;1]^^(M+B+h)) (h*2+n+q*2) e.
Proof.
  intros HP E1 E2 Hh E3 EM EK.
  follow (negativeN_large_start
    (l <* <[0;1]^^(v*2+a) <* <[0;1;1]^^(B*2)) p n e h k d0 HP E1 E2 Hh).
  destruct v as [|v].
  - mid (crossW (l <* <[0;1]^^a <* <[0;1;1]^^(B*2))
      0inf 0 ([1;0;1;0;0;1]^^(M+h)) (h*2+n+q*2) e).
    1: applys_eq (flow_cross _ _ _ _ _ (block_flow _ _ _ _ _
      (BlockFlow_whole (h*2-2) n d0 q e E3))
      (l <* <[0;1]^^a <* <[0;1;1]^^(B*2)) 0 h); flia.
    applys_eq (crossW_absorb l 0inf a B (M+h) (h*2+n+q*2) e); flia.
  - applys_eq (block_cross _ _ _ _ _ (BlockFlow_whole (h*2-2) n d0 q e E3)
      l a B h k v); flia.
Qed.

Lemma negativeN_large_late p n e h k d0 q M B v u:
  P p -> p=2+n*2+d0 -> p+3+n*2+e=h*2 -> 1<=h -> e<=1 ->
  1+d0=e+q*2 -> M=4+n*4+q -> k+v=M ->
  negativeN (0inf <* <[0;1]^^(3+v*2+u*2) <* <[0;1;1]^^(B*2)) p n (h+k) e -->*
  0inf <* <[0;1]^^(1+u*2) <* <[0;1;1]^^(3+(M+B+h)*2)
    <* <[0;1]^^(1+h*2+n+q*2+e) {{B}}> 0inf.
Proof.
  intros HP E1 E2 Hh He E3 EM EK.
  mid (crossW 0inf 0inf (3+u*2) ([1;0;1;0;0;1]^^(M+B+h)) (h*2+n+q*2) e).
  1: applys_eq (negativeN_large_cross 0inf p n e h k d0 q M B v (3+u*2) HP E1 E2 Hh E3 EM EK); flia.
  applys_eq (crossW_finish 0inf (1+u*2) (M+B+h) (h*2+n+q*2) e He); flia.
Qed.
Lemma negativeN_large_short p n e h k d0 q M B v:
  P p -> p=2+n*2+d0 -> p+3+n*2+e=h*2 -> 1<=h -> e<=1 ->
  1+d0=e+q*2 -> M=4+n*4+q -> k+v=M ->
  negativeN (0inf <* <[0;1]^^(1+v*2) <* <[0;1;1]^^(B*2)) p n (h+k) e -->*
  0inf <* <[0;1] <* <[0;1;1]^^(2+(M+B+h)*2)
    <* <[0;1]^^(1+h*2+n+q*2+e) {{B}}> 0inf.
Proof.
  intros HP E1 E2 Hh He E3 EM EK.
  mid (crossW 0inf 0inf 1 ([1;0;1;0;0;1]^^(M+B+h)) (h*2+n+q*2) e).
  1: applys_eq (negativeN_large_cross 0inf p n e h k d0 q M B v 1 HP E1 E2 Hh E3 EM EK); flia.
  applys_eq (crossW_short (M+B+h) (h*2+n+q*2) e He); flia.
Qed.
Lemma negativeN_large_root p n e h k d0 q M B s v:
  P p -> p=2+n*2+d0 -> p+3+n*2+e=h*2 -> 1<=h -> e<=1 ->
  1+d0=e+q*2 -> M=4+n*4+q -> k+s+v+1=M ->
  negativeN (0inf <* <[0;1]^^(1+s*2) <* <[0;1;1]^^(B*2)) p n (h+k) e -->*
  0inf <* <[0;1]^^(3+v*2) <* <[0;1;1]^^(2+(k+s+B+h)*2)
    <* <[0;1]^^(1+h*2+n+q*2+e) {{B}}> 0inf.
Proof.
  intros HP E1 E2 Hh He E3 EM EK.
  follow (negativeN_large_start (0inf <* <[0;1]^^(1+s*2) <* <[0;1;1]^^(B*2))
    p n e h k d0 HP E1 E2 Hh).
  mid (rootW 0inf (v*2) ([1;0;1;0;0;1]^^(1+k+s+B+h)) (h*2+n+q*2) e).
  1: applys_eq (block_border _ _ _ _ _ (BlockFlow_whole (h*2-2) n d0 q e E3) B h k s v); flia.
  applys_eq (rootW_finish (v*2) (k+s+B+h) (h*2+n+q*2) e He); flia.
Qed.


(* Complete terminal sections. Last is a parity-indexed graph, not a
   claim of global list closure. Cleanup and global closure are still open. *)
Lemma rootW_finish_word0 a w x y c: Word w x y ->
  rootW 0inf a w c 0 -->*
  0inf <* <[0;1]^^(3+a) <* rev y <* <[0;1]^^(1+c) {{B}}> 0inf.
Proof.
  intros [E [HR HL]].
  mid (0inf <* <[0;1]^^(2+a) {{B}}> (w++[1;0]) *> [1;0]^^(1+c) *> 0inf).
  1: unfold rootW; rewrite Str_app_assoc; es.
  rewrite E,Str_app_assoc; es; follow HR; es.
Qed.

Lemma crossW_finish_word0 l a w x y c: Word w x y ->
  crossW l 0inf (2+a) w c 0 -->*
  l <* <[0;1]^^a <* <[0;1;1]^^3 <* rev y <* <[0;1]^^(1+c) {{B}}> 0inf.
Proof.
  intros [E [HR HL]].
  mid ([0;1;1;0;1;1;0] *> [1;0]^^a *> l {{F}}>
    (w++[1;0]) *> [1;0]^^(1+c) *> 0inf).
  1: unfold crossW; rewrite Str_app_assoc; es.
  rewrite E,Str_app_assoc; es; follow HR; es.
Qed.
Lemma crossW_finish_word1 l a w x y c: Word w x y ->
  crossW l 0inf (2+a) w c 1 -->*
  l <* <[0;1]^^a <* <[0;1;1]^^3 <* rev y <* <[0;1]^^(2+c) {{B}}> 0inf.
Proof.
  intros [E [HR HL]].
  mid ([0;1;1;0;1;1;0] *> [1;0]^^a *> l {{F}}>
    (w++[1;0]) *> [1;0]^^(2+c) *> 0inf).
  1: unfold crossW; rewrite Str_app_assoc; es.
  rewrite E,Str_app_assoc; es; follow HR; es.
Qed.
Lemma rootW_finish_word1 a w x y c: Word w x y ->
  rootW 0inf a w c 1 -->*
  0inf <* <[0;1]^^(3+a) <* rev y <* <[0;1]^^(2+c) {{B}}> 0inf.
Proof.
  intros [E [HR HL]].
  mid (0inf <* <[0;1]^^(2+a) {{B}}> (w++[1;0]) *> [1;0]^^(2+c) *> 0inf).
  1: unfold rootW; rewrite Str_app_assoc; es.
  rewrite E,Str_app_assoc; es; follow HR; es.
Qed.

Fixpoint section_side (xs:list nat) (u:bool) : side :=
  match xs with []=>0inf | a::xs=>
    (if u then <[0;1] else <[0;1;1])^^a *> section_side xs (negb u) end.
Definition section xs := section_side xs true {{B}}> 0inf.
Definition final_scan t m := 0inf <* <[0;1]^^t <{{C}} [0;1] *> [0;1;0]^^m *> 0inf.

Definition scan_root a d := 0inf <{{A}} [1] *> [0;1]^^a *> [0;1;0]^^d *> 0inf.
Lemma scan_root_step a d: scan_root a (2+d) -->* scan_root (4+a) d.
Proof. unfold scan_root; es. Qed.
Lemma scan_roots a d n: scan_root a (n*2+d) -->* scan_root (n*4+a) d.
Proof. gen a d; ind n scan_root_step. Qed.
Lemma final_zero_even d: final_scan 0 (d*2) -->* section [3+d*4].
Proof.
  mid (scan_root 1 (d*2)); [unfold final_scan,scan_root; es|].
  mid (scan_root (1+d*4) 0); [applys_eq (scan_roots 1 0 d); flia|].
  unfold scan_root,section; cbn[section_side]; es.
Qed.
Lemma final_zero_odd d: final_scan 0 (1+d*2) -->* section [4+d*4].
Proof.
  mid (scan_root 1 (1+d*2)); [unfold final_scan,scan_root; es|].
  mid (scan_root (1+d*4) 1); [applys_eq (scan_roots 1 1 d); flia|].
  unfold scan_root,section; cbn[section_side]; es.
Qed.
Lemma final_one_even d: final_scan 1 (d*2) -->* section [5+d*4].
Proof.
  mid (scan_root 3 (d*2)); [unfold final_scan,scan_root; es|].
  mid (scan_root (3+d*4) 0); [applys_eq (scan_roots 3 0 d); flia|].
  unfold scan_root,section; cbn[section_side]; es.
Qed.
Lemma final_one_odd d: final_scan 1 (1+d*2) -->* section [6+d*4].
Proof.
  mid (scan_root 3 (1+d*2)); [unfold final_scan,scan_root; es|].
  mid (scan_root (3+d*4) 1); [applys_eq (scan_roots 3 1 d); flia|].
  unfold scan_root,section; cbn[section_side]; es.
Qed.

(* The constructors specify the finite parity cases without division or
   truncated subtraction. In particular the even/even short border is
   separate from the ordinary and overflowing cases. *)
Local Open Scope nat_scope.
Inductive Last : nat->nat->list nat->Prop :=
| Last0E d: Last 0 (d*2) [3+d*4]
| Last0O d: Last 0 (1+d*2) [4+d*4]
| Last1E d: Last 1 (d*2) [5+d*4]
| Last1O d: Last 1 (1+d*2) [6+d*4]
| LastEE a d: Last (2+a*2) (2+a*2+d*2) [2+a*2+d*2;2+a*2;3+d*2]
| LastEO a d: Last (2+a*2) (1+a*2+d*2) [1+a*2+d*2;2+a*2;1+d*2]
| LastOE a d: Last (3+a*2) (2+a*2+d*2) [2+a*2+d*2;2+a*2;5+d*2]
| LastOO a d: Last (3+a*2) (3+a*2+d*2) [3+a*2+d*2;2+a*2;5+d*2]
| LastBorder a: Last (4+a*2) (2+a*2) [2+a*2;4+a*2;1]
| LastOverflowO a d: Last (3+d*2+a) (1+d*2) [1+d*2;3+d*2;a]
| LastOverflowE a d: Last (5+d*2+a) (2+d*2) [2+d*2;5+d*2;a].
Local Close Scope nat_scope.

Lemma Last_spec t m xs: Last t m xs -> final_scan t m -->* section xs.
Proof.
  intro H; destruct H; try apply final_zero_even; try apply final_zero_odd;
    try apply final_one_even; try apply final_one_odd;
    unfold final_scan,section; cbn[section_side negb].
  - apply even_left_even.
  - apply even_left_odd.
  - applys_eq (normal_even a d); flia.
  - applys_eq (normal_odd a d); flia.
  - applys_eq (border_even 0inf a); solve_const0_eq.
  - apply left_overflow_odd.
  - apply left_overflow_even.
Qed.

Lemma good_section p b t xs: P p -> Last t (p+b) xs -> section [p;b;t] -->* section xs.
Proof.
  intros HP HL; unfold section at 1; cbn[section_side negb]; unfold P in HP.
  follow HP; follow pass_011.
  mid (final_scan t (b+p)).
  1: unfold final_scan; rewrite (lpow_add _ b p),Str_app_assoc; finish.
  applys_eq (Last_spec t (p+b) xs HL); flia.
Qed.

Local Open Scope nat_scope.
Lemma parity n: exists k, n=k*2 \/ n=1+k*2.
Proof.
  destruct (Nat.Even_or_Odd n) as [[k H]|[k H]];
    exists k; [left|right]; lia.
Qed.
Lemma Last_total t m: 0<m -> exists xs, Last t m xs.
Proof.
  intro Hm; destruct t as [|[|t]].
  - destruct (parity m) as [d [-> | ->]]; eauto using Last0E,Last0O.
  - destruct (parity m) as [d [-> | ->]]; eauto using Last1E,Last1O.
  - destruct m as [|m]; [lia|].
    destruct (parity t) as [a [-> | ->]], (parity m) as [d [-> | ->]].
    + destruct (Nat.le_gt_cases a d).
      * eexists; applys_eq (LastEO a (d-a)); flia.
      * eexists; applys_eq (LastOverflowO (a*2-d*2-1) d); flia.
    + destruct (Nat.le_gt_cases a d).
      * eexists; applys_eq (LastEE a (d-a)); flia.
      * destruct (Nat.eq_dec a (1+d)).
        -- eexists; applys_eq (LastBorder d); flia.
        -- eexists; applys_eq (LastOverflowE (a*2-d*2-3) d); flia.
    + destruct (Nat.lt_ge_cases a d).
      * eexists; applys_eq (LastOO a (d-a-1)); flia.
      * eexists; applys_eq (LastOverflowO ((a-d)*2) d); flia.
    + destruct (Nat.le_gt_cases a d).
      * eexists; applys_eq (LastOE a (d-a)); flia.
      * eexists; applys_eq (LastOverflowE ((a-d-1)*2) d); flia.
Qed.
Lemma unary_section p k xs: P p -> Last k p xs -> section [p+k] -->* section xs.
Proof.
  intros HP HL; unfold section at 1; cbn[section_side]; unfold P in HP.
  rewrite (lpow_add _ p k),Str_app_assoc; follow HP.
  apply Last_spec,HL.
Qed.
Lemma good_section_returns p b t: P p -> 0<p+b ->
  exists xs, section [p;b;t] -->* section xs.
Proof.
  intros HP H; destruct (Last_total t (p+b) H) as [xs HL].
  exists xs; apply good_section; assumption.
Qed.
Local Close Scope nat_scope.

Lemma Last_progress t m xs: Last t m xs -> final_scan t m -[tm]->+ section xs.
Proof. intro H; apply evstep_progress; [apply Last_spec,H|discriminate]. Qed.

Local Open Scope nat_scope.
Definition last_output t m :=
  let e:=1-m mod 2 in let r:=t mod 2 in
  if t<=?1 then [m*2+2+t*2+e] else
  if t+r<=?m+1+e then [m;t-r;m+2+r*3+e-t]
  else [m;m+2+e;t-(m+2+e)].
Lemma Last_output t m xs: Last t m xs -> xs=last_output t m.
Proof.
  intro H; destruct H; unfold last_output.
  all: repeat match goal with |- context[?x mod 2] =>
    let E:=fresh "E" in
    first [assert (E:x mod 2=0) by lia | assert (E:x mod 2=1) by lia];
    rewrite E; clear E end.
  all: cbn zeta.
  all: repeat match goal with |- context[?a<=? ?b] =>
    let E:=fresh "E" in destruct (a<=?b) eqn:E;
    [apply Nat.leb_le in E | apply Nat.leb_gt in E] end;
    try lia; repeat (f_equal; try lia).
Qed.
Lemma Last_functional t m xs ys: Last t m xs -> Last t m ys -> xs=ys.
Proof. intros H1 H2; rewrite (Last_output _ _ _ H1),(Last_output _ _ _ H2); reflexivity. Qed.
Lemma last_output_spec t m: 0<m -> final_scan t m -[tm]->+ section (last_output t m).
Proof.
  intro H; destruct (Last_total t m H) as [xs HL].
  rewrite <-(Last_output _ _ _ HL); apply Last_progress,HL.
Qed.
Lemma good_section_formula p b t: P p -> 0<p+b ->
  section [p;b;t] -[tm]->+ section (last_output t (p+b)).
Proof.
  intros HP H; eapply evstep_progress_trans with (c':=final_scan t (p+b));
    [|apply last_output_spec,H].
  unfold section; cbn[section_side negb]; unfold P in HP.
  follow HP; follow pass_011.
  unfold final_scan; rewrite (Nat.add_comm p b),(lpow_add _ b p),Str_app_assoc; finish.
Qed.
Local Close Scope nat_scope.

Lemma S_short_section1 b c:
  S 0inf 0inf 3 (1+b) c 1 -->* section [2+c;4+b*2;1]%nat.
Proof.
  unfold section; cbn[section_side negb].
  replace (([1;0]%sym)^^1 *> 0inf) with ([1]%sym *> 0inf) by solve_const0_eq.
  apply S_short1.
Qed.

Local Open Scope nat_scope.
Definition S_odd_output b c v d :=
  let edge:=d+2+d mod 2 in
  if 1+v*2 <? edge then [1+c+d;2+b*2+v*2;edge-(1+v*2)]
  else [1+c+d;3+b*2+d+d mod 2;1+v*2-edge].

Ltac decide_ltb := match goal with |- context[Nat.ltb ?x ?y] =>
  let E:=fresh "Ecut" in first
    [assert (E:(x<?y)=true) by (apply Nat.ltb_lt; lia)
    |assert (E:(x<?y)=false) by (apply Nat.ltb_ge; lia)]; rewrite E end.

Lemma S_odd_spec b c v d:
  S 0inf 0inf (1+v*2) (1+b) c d -->* section (S_odd_output b c v d).
Proof.
  destruct (parity d) as [r [-> | ->]]; unfold S_odd_output.
  - assert (E:(r*2) mod 2=0) by lia; rewrite E.
    destruct (Nat.lt_ge_cases v r).
    + decide_ltb.
      unfold section; cbn[section_side negb].
      applys_eq (S_root_exit1 b c v (r-v-1)); flia.
    + destruct (Nat.eq_dec v r) as [->|Hv].
      * decide_ltb.
        replace (r*2+2+0-(1+r*2)) with 1 by lia.
        mid (S 0inf 0inf 1 (1+b+r) (c+r*2) 0).
        1: applys_eq (Incs1 0inf 0inf 1 (1+b) c 0 r); flia.
        unfold section; cbn[section_side negb].
        replace (([1;0]%sym)^^1 *> 0inf) with ([1]%sym *> 0inf) by solve_const0_eq.
        applys_eq (S_short0 0inf (b+r) (c+r*2)); flia.
      * decide_ltb.
        mid (S 0inf 0inf (1+(v-r)*2) (1+b+r) (c+r*2) 0).
        1: applys_eq (Incs1 0inf 0inf (1+(v-r)*2) (1+b) c 0 r); flia.
        unfold section; cbn[section_side negb].
        applys_eq (S_exit0 0inf ((v-r)*2-1) (b+r) (c+r*2)); flia.
  - assert (E:(1+r*2) mod 2=1) by lia; rewrite E.
    destruct (Nat.le_gt_cases v r).
    + decide_ltb.
      unfold section; cbn[section_side negb].
      applys_eq (S_root_exit0 b c v (r-v)); flia.
    + destruct (Nat.eq_dec v (1+r)) as [->|Hv].
      * decide_ltb.
        mid (S 0inf 0inf 3 (1+b+r) (c+r*2) 1).
        1: applys_eq (Incs1 0inf 0inf 3 (1+b) c 1 r); flia.
        applys_eq (S_short_section1 (b+r) (c+r*2)); flia.
      * decide_ltb.
        mid (S 0inf 0inf (1+(v-r)*2) (1+b+r) (c+r*2) 1).
        1: applys_eq (Incs1 0inf 0inf (1+(v-r)*2) (1+b) c 1 r); flia.
        unfold section; cbn[section_side negb].
        applys_eq (S_exit1 0inf ((v-r)*2-3) (b+r) (c+r*2)); flia.
Qed.
Local Close Scope nat_scope.

Lemma S_odd_progress b c v d:
  S 0inf 0inf (1+v*2) (1+b) c d -[tm]->+ section (S_odd_output b c v d).
Proof. apply evstep_progress; [apply S_odd_spec|discriminate]. Qed.

Lemma bare_root a b c:
  0inf <{{A}} [1;0]^^(2+a) *> [0;1;1;0;1;0]^^(1+b) *> [1;0]^^c *> 0inf -->*
  section [1+c;2+b*2;2+a]%nat.
Proof. unfold section; cbn[section_side negb]; es. Qed.

Lemma odd_seed_bare a b c d:
  0inf <* <[0;1]^^a <* <[0;1;1]^^(1+b*2) <{{B}}
    [1] *> [0;1;1;0;1;0]^^(1+c) *> [1;0]^^d *> 0inf -->*
  section [1+d;2+(b+c)*2;2+a]%nat.
Proof.
  follow odd_block.
  mid (0inf <{{A}} [1;0]^^(2+a) *> [0;1;1;0;1;0]^^(1+(b+c)) *> [1;0]^^d *> 0inf).
  1: replace (1+(b+c))%nat with (b+(1+c))%nat by lia;
    rewrite (lpow_add _ b (1+c)),Str_app_assoc; es.
  apply bare_root.
Qed.

Lemma odd_last_odd g j t: P (2+g*2) ->
  section [(2+g*2)+(3+g*2);1+j*2;t]%nat -->*
  section [2+g*2;4+(j+g)*2;2+t]%nat.
Proof.
  intro HP; unfold section at 1; cbn[section_side negb].
  follow (fun l=>return_last l g HP); applys_eq (odd_seed_bare t j (1+g) (1+g*2)); flia.
Qed.

Lemma odd_last_S g j t: P (2+g*2) ->
  section [(2+g*2)+(3+g*2);j*2;t]%nat -->*
  S 0inf 0inf t (2+j+g) (1+g*2) 0.
Proof.
  intro HP; unfold section; cbn[section_side negb].
  follow (fun l=>return_last l g HP); follow even_block.
  unfold S; replace (2+j+g)%nat with (j+(2+g))%nat by lia.
  rewrite (lpow_add _ j (2+g)),Str_app_assoc; finish; try solve_const0_eq.
Qed.

Lemma odd_gap_seed g j t d: P (1+g*2+d) ->
  section [(1+g*2+d)+(1+g*2);1+j*2;t]%nat -->* seed t (j+g) g d.
Proof.
  intro HP; unfold section; cbn[section_side negb].
  follow (fun l=>return_odd l g d HP); apply odd_seed.
Qed.

Lemma odd_gap_S g j t d: P (1+g*2+d) ->
  section [(1+g*2+d)+(1+g*2);j*2;t]%nat -->* S 0inf 0inf t (1+j+g) (g*2) d.
Proof.
  intro HP; unfold section; cbn[section_side negb].
  follow (fun l=>return_odd l g d HP); follow even_block.
  unfold S; replace (1+j+g)%nat with (j+(1+g))%nat by lia.
  rewrite (lpow_add _ j (1+g)),Str_app_assoc; finish.
Qed.

Local Open Scope nat_scope.
Lemma seed_section a b c d:
  seed a b c d -->* section [1+c*2+d;2+b*2;2+a+d+d mod 2].
Proof.
  destruct (parity d) as [r [-> | ->]].
  - assert (E:(r*2) mod 2=0) by lia; rewrite E; destruct r.
    + unfold section; cbn[section_side negb]; applys_eq (seed_zero a b c); flia.
    + unfold section; cbn[section_side negb]; applys_eq (seed_even a b c r); flia.
  - assert (E:(1+r*2) mod 2=1) by lia; rewrite E.
    unfold section; cbn[section_side negb]; applys_eq (seed_odd a b c r); flia.
Qed.
Lemma odd_gap_odd_formula g j t d: P (1+g*2+d) ->
  section [(1+g*2+d)+(1+g*2);1+j*2;t] -->*
  section [1+g*2+d;2+(j+g)*2;2+t+d+d mod 2].
Proof. intro H; follow (odd_gap_seed g j t d H); apply seed_section. Qed.
Lemma odd_gap_even_formula g j v d: P (1+g*2+d) ->
  section [(1+g*2+d)+(1+g*2);j*2;1+v*2] -->*
  section (S_odd_output (j+g) (g*2) v d).
Proof.
  intro H; follow (odd_gap_S g j (1+v*2) d H); applys_eq (S_odd_spec (j+g) (g*2) v d); flia.
Qed.
Lemma odd_last_even_formula g j v: P (2+g*2) ->
  section [(2+g*2)+(3+g*2);j*2;1+v*2] -[tm]->+
  section (S_odd_output (1+j+g) (1+g*2) v 0).
Proof.
  intro H; eapply evstep_progress_trans; [apply odd_last_S,H|].
  applys_eq (S_odd_progress (1+j+g) (1+g*2) v 0); flia.
Qed.
Local Close Scope nat_scope.

Local Open Scope nat_scope.

Lemma unary_progress p k: P p -> 0<p ->
  section [p+k] -[tm]->+ section (last_output k p).
Proof.
  intros HP H; eapply evstep_progress_trans with (c':=final_scan k p);
    [|apply last_output_spec,H].
  unfold section; cbn[section_side]; unfold P in HP.
  rewrite (lpow_add _ p k),Str_app_assoc; apply HP.
Qed.
Lemma Last_predecessor p: 0<p ->
  Last (p+1+(1-p mod 2)) p [p;p+1+(1-p mod 2);1].
Proof.
  intro H; destruct (parity p) as [a [-> | ->]].
  - assert (E:(a*2) mod 2=0) by lia; rewrite E.
    destruct a; [lia|]; applys_eq (LastBorder a); flia.
  - assert (E:(1+a*2) mod 2=1) by lia; rewrite E.
    applys_eq (LastEO a 0); flia.
Qed.
Definition unary_output p k :=
  if k=?p+1+(1-p mod 2) then last_output 1 (p+k) else last_output k p.
Lemma unary_formula p k: P p -> 0<p ->
  section [p+k] -[tm]->+ section (unary_output p k).
Proof.
  intros HP H; unfold unary_output; destruct (k=?p+1+(1-p mod 2)) eqn:E.
  - apply Nat.eqb_eq in E; subst k; eapply evstep_progress_trans.
    + apply unary_section; [exact HP|apply Last_predecessor,H].
    + apply good_section_formula; [exact HP|lia].
  - apply unary_progress; assumption.
Qed.
Local Close Scope nat_scope.

Lemma unary_zero: section [0%nat] -[tm]->+ section [3%nat].
Proof. unfold section; cbn[section_side]; es. Qed.
Lemma unary_one: section [1%nat] -[tm]->+ section [5%nat].
Proof. unfold section; cbn[section_side]; es. Qed.
Lemma unary_two: section [2%nat] -[tm]->+ section [9%nat].
Proof. unfold section; cbn[section_side]; es. Qed.

Lemma init: c0 -->* section [1%nat].
Proof. unfold section; cbn[section_side]; esx. Qed.


(* The predecessor return has a distinct 001 terminal phase. *)

Lemma pred_S a b n:
  0inf <* <[0;1]^^(2+a) <* <[0;1;1]^^(2+b*2) <{{E}}
    [0;1;1] *> [0;1;0]^^n *> 0inf -->*
  S 0inf 0inf a (2+b) 0 n.
Proof. unfold S; es. Qed.

Definition rootT a b c d := 0inf <{{A}} [1;0]^^(1+a) *>
  [1;0;1;0;0;1]^^(1+b) *> [1;0]^^c *> [1;0;1] *> [0;0;1]^^d *> 0inf.
Lemma rootT_step a b c d:
  rootT a b c (2+d) -->* rootT (2+a) b (2+c) d.
Proof. unfold rootT; es. Qed.
Lemma rootTs a b c d n:
  rootT a b c (n*2+d) -->* rootT (n*2+a) b (n*2+c) d.
Proof. gen a b c d; ind n rootT_step. Qed.
Lemma rootT_end0 a b c:
  rootT a b c 0 -->*
  0inf <* <[0;1]^^(3+a) <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(1+c) {{B}}> 0inf.
Proof. unfold rootT; es. Qed.
Lemma rootT_end1 a b c:
  rootT a b c 1 -->*
  0inf <* <[0;1]^^(5+a) <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(2+c) {{B}}> 0inf.
Proof. unfold rootT; es. Qed.
Lemma pred_root b n:
  0inf <* <[0;1] <* <[0;1;1]^^(2+b*2) <{{E}}
    [0;1;1] *> [0;1;0]^^n *> 0inf -->* rootT 0 b 0 n.
Proof. unfold rootT; es. Qed.

Local Open Scope nat_scope.
Definition pred_output n b t :=
  let h:=n+4+n mod 2 in
  if t<?h then [1+n;b+t-1;h-t] else [1+n;b+h-1;t-h].
Lemma pred_root_formula b n:
  rootT 0 b 0 n -->* section [1+n;2+b*2;3+n+n mod 2].
Proof.
  destruct (parity n) as [r [-> | ->]].
  - assert (E:(r*2) mod 2=0) by lia; rewrite E.
    mid (rootT (r*2) b (r*2) 0); [applys_eq (rootTs 0 b 0 0 r); flia|].
    unfold section; cbn[section_side negb]; applys_eq (rootT_end0 (r*2) b (r*2)); flia.
  - assert (E:(1+r*2) mod 2=1) by lia; rewrite E.
    mid (rootT (r*2) b (r*2) 1); [applys_eq (rootTs 0 b 0 1 r); flia|].
    unfold section; cbn[section_side negb]; applys_eq (rootT_end1 (r*2) b (r*2)); flia.
Qed.
Lemma pred_S_formula b v n:
  S_odd_output (1+b) 0 v n=pred_output n (2+b*2) (3+v*2).
Proof.
  unfold S_odd_output,pred_output.
  repeat match goal with |- context[?a<? ?b] =>
    let E:=fresh "E" in destruct (a<?b) eqn:E;
    [apply Nat.ltb_lt in E|apply Nat.ltb_ge in E] end;
    try lia; repeat (f_equal; try lia).
Qed.
Local Close Scope nat_scope.

Lemma pred_terminal n b v:
  0inf <* <[0;1]^^(1+v*2) <* <[0;1;1]^^(2+b*2) <{{E}}
    [0;1;1] *> [0;1;0]^^n *> 0inf -[tm]->+
  section (pred_output n (2+b*2) (1+v*2)).
Proof.
  apply evstep_progress; [|discriminate].
  destruct v as [|v].
  - follow pred_root; unfold pred_output; decide_ltb.
    applys_eq (pred_root_formula b n); flia.
  - mid (S 0inf 0inf (1+v*2) (2+b) 0 n).
    1: applys_eq (pred_S (1+v*2) b n); flia.
    replace (1+Datatypes.S v*2)%nat with (3+v*2)%nat by lia.
    rewrite <-pred_S_formula.
    applys_eq (S_odd_spec (1+b) 0 v n); flia.
Qed.

Lemma pred_section n b v: PP n ->
  section [n;2+b*2;1+v*2]%nat -[tm]->+ section (pred_output n (2+b*2) (1+v*2)).
Proof.
  intros HP; unfold PP in HP.
  eapply evstep_progress_trans; [|apply pred_terminal].
  unfold section; cbn[section_side negb]; apply HP.
Qed.


(* Short tails and the recursive parameter bands. *)
Definition scan_left r a d := 0inf <{{A}} [1] *> [0;1]^^a *> [0;1;0]^^d *> r.
Lemma scan_left_step r a d: scan_left r a (2+d) -->* scan_left r (4+a) d.
Proof. unfold scan_left; es. Qed.
Lemma scan_lefts r a d n: scan_left r a (n*2+d) -->* scan_left r (n*4+a) d.
Proof. gen r a d; ind n scan_left_step. Qed.
Lemma scan_left_entry r d:
  0inf <* <[0;1] <{{C}} [0;1] *> [0;1;0]^^d *> r -->* scan_left r 3 d.
Proof. unfold scan_left; es. Qed.

Definition short_suffix n d := [0;1] *> [0;0;1;1;0;1]^^(1+n) *>
  [0;1]^^(1+n*2) *> [0] *> [1;0;0]^^d *> 0inf.
Lemma short_normalize a n d:
  scan_left (short_suffix n d) (1+a) 0 -->*
  rootW 0inf a ([1;0;1;0;0;1]^^(1+n)) (1+n*2) d.
Proof. unfold scan_left,short_suffix,rootW; st; simpl_rotate; finish. Qed.

Lemma short_root n j d: P (2+n*2+d) ->
  section [(2+n*2+d)+(2+n*2);j*2;1]%nat -->*
  rootW 0inf (2+j*4) ([1;0;1;0;0;1]^^(1+n)) (1+n*2) d.
Proof.
  intro HP; unfold section; cbn[section_side negb].
  follow (fun l=>return_even l n d HP); follow pass_011.
  mid (scan_left (short_suffix n d) 3 (j*2)).
  1: unfold short_suffix; apply scan_left_entry.
  mid (scan_left (short_suffix n d) (3+j*4) 0).
  1: applys_eq (scan_lefts (short_suffix n d) 3 0 j); flia.
  applys_eq (short_normalize (2+j*4) n d); flia.
Qed.
Local Open Scope nat_scope.
Lemma short_section n j d: P (2+n*2+d) ->
  section [(2+n*2+d)+(2+n*2);j*2;1] -[tm]->+
  section [2+n*2+d;2+n*2;5+j*4+d-d mod 2].
Proof.
  intro HP; eapply evstep_progress_trans; [apply short_root,HP|].
  apply evstep_progress; [|discriminate].
  destruct (parity d) as [r [-> | ->]].
  - assert (E:(r*2) mod 2=0) by lia; rewrite E.
    mid (rootW 0inf (2+j*4+r*2) ([1;0;1;0;0;1]%sym^^(1+n)) (1+n*2+r*2) 0).
    1: applys_eq (rootsW 0inf (2+j*4) _ _ _ (1+n*2) 0 r (Word_pow _ _ _ (1+n) Word_V)); flia.
    unfold section; cbn[section_side negb]; applys_eq root_end0; flia.
  - assert (E:(1+r*2) mod 2=1) by lia; rewrite E.
    mid (rootW 0inf (2+j*4+r*2) ([1;0;1;0;0;1]%sym^^(1+n)) (1+n*2+r*2) 1).
    1: applys_eq (rootsW 0inf (2+j*4) _ _ _ (1+n*2) 1 r (Word_pow _ _ _ (1+n) Word_V)); flia.
    unfold section; cbn[section_side negb]; applys_eq root_end1; flia.
Qed.
Local Close Scope nat_scope.

Local Open Scope nat_scope.

Definition next_p p := p*2+2+(1-p mod 2).
Lemma P_next p: 3<=p -> P p -> P (next_p p).
Proof.
  intros H HP; unfold next_p.
  destruct (Nat.Even_or_Odd p) as [[a E]|[a E]]; subst p.
  - assert (E:(2*a) mod 2=0) by lia; rewrite E; destruct a; [lia|].
    applys_eq (P_S' a); [flia|applys_eq HP; flia].
  - assert (E:(2*a+1) mod 2=1) by lia; rewrite E.
    applys_eq (P_S a); [flia|applys_eq HP; flia].
Qed.

Inductive Chain: nat->Prop :=
| Chain0: Chain 3
| ChainS p: Chain p -> Chain (next_p p).
Lemma next_p_grows p: p<next_p p.
Proof. unfold next_p; lia. Qed.
Lemma Chain_spec p: Chain p ->
  3<=p /\ P p /\ (p mod 16=3 \/ p mod 32=8).
Proof.
  intro H; induction H as [|p H [Hp [HP Hm]]].
  - repeat split; auto using P3.
  - split; [pose proof (next_p_grows p); lia|].
    split; [apply P_next; assumption|].
    unfold next_p; destruct Hm; [right|left]; lia.
Qed.

Definition Band p n := Chain p /\ p<=n<next_p p.
Lemma Band_total n: 3<=n -> exists p, Band p n.
Proof.
  induction n as [|n IH]; intro Hn; [lia|].
  destruct (Nat.eq_dec n 2) as [->|Hn2].
  - exists 3; split; [constructor|unfold next_p; cbn; lia].
  - assert (Hn0:3<=n) by lia.
    destruct (IH Hn0) as [p [HP [Hlo Hhi]]].
    destruct (Nat.lt_ge_cases (1+n) (next_p p)).
    + exists p; split; [assumption|lia].
    + exists (next_p p); split; [constructor; assumption|].
      pose proof (next_p_grows (next_p p)); lia.
Qed.

Local Close Scope nat_scope.

(* Segmented counter paths and arbitrary even-column traversals. *)
Local Open Scope nat_scope.
Local Open Scope sym_scope.
Lemma crossW_one_word r w x y c d: Word w x y ->
  crossW 0inf r 1 w c (2+d) -->*
  rootW r 0 ([1;0;1;0;0;1]++w) (2+c) d.
Proof.
  intros [E [HR HL]].
  mid ([0;1;1;0;1] *> 0inf {{F}}>
    (w++[1;0]) *> [1;0]^^(2+c) *> [0;1;0]^^(1+d) *> r).
  1: unfold crossW; rewrite Str_app_assoc; es.
  rewrite E,Str_app_assoc; es; follow HR; es; follow HL; unfold rootW; es.
Qed.

Definition link w c d r := [0;1;0;0;1] *> w *>
  [1;0]^^c *> [1;0;1] *> [0;1;0]^^d *> r.
Lemma crossW_join l r a w c v c' d:
  crossW l (link v c' d r) a w c 0 -->*
  crossW l r a (w++[1;0]^^(1+c)++[1;0;1;0;0;1]++v) c' d.
Proof. unfold crossW,link; st; simpl_rotate; finish. Qed.
Lemma rootW_join r a w c v c' d:
  rootW (link v c' d r) a w c 0 -->*
  rootW r a (w++[1;0]^^(1+c)++[1;0;1;0;0;1]++v) c' d.
Proof. unfold rootW,link; st; simpl_rotate; finish. Qed.

Lemma Flow_W_word r w x y c d: Word w x y ->
  Flow (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b++w) c (2+d))
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b++w) c (2+d))
    (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b++w) (2+c) d)
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b++w) (2+c) d) 1.
Proof.
  intro H.
  assert (HW:forall b, Word ([1;0;1;0;0;1]^^b++w)
    ([1;0;0;1;1;0]^^b++x) ([0;1;1;0;1;1]^^b++y)).
  1: intro b; apply Word_app; auto using Word_pow,Word_V.
  constructor; intros; cbn beta.
  - apply (crossW_step l r a _ _ _ c d (HW b)).
  - apply (rootW_step r a _ _ _ c d (HW b)).
  - assert (s=0%nat /\ v=0%nat) as [-> ->] by lia.
    apply (crossW_one_word r _ _ _ c d (HW b)).
Qed.

Lemma Flow_Ws_word r w x y c d n: Word w x y ->
  Flow (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b++w) c (n*2+d))
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b++w) c (n*2+d))
    (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b++w) (n*2+c) d)
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b++w) (n*2+c) d) n.
Proof.
  intro H; gen c; induction n; intro c; [apply Flow_id|].
  cbn [Nat.mul].
  eapply Flow_trans with (n:=1%nat) (m:=n); [eapply Flow_W_word; exact H|].
  replace (2+n*2+c)%nat with (n*2+(2+c))%nat by lia.
  apply IHn.
Qed.

Lemma Flow_join r w c v c' d:
  Flow (fun l a n=>crossW l (link v c' d r) a ([1;0;1;0;0;1]^^n++w) c 0)
    (fun a n=>rootW (link v c' d r) a ([1;0;1;0;0;1]^^n++w) c 0)
    (fun l a n=>crossW l r a
      ([1;0;1;0;0;1]^^n++w++[1;0]^^(1+c)++[1;0;1;0;0;1]++v) c' d)
    (fun a n=>rootW r a
      ([1;0;1;0;0;1]^^n++w++[1;0]^^(1+c)++[1;0;1;0;0;1]++v) c' d) 0.
Proof.
  constructor; intros; cbn beta; try lia.
  - rewrite app_assoc; apply crossW_join.
  - rewrite app_assoc; apply rootW_join.
Qed.

(* A right payload retains every internal 010 counter. Interior counters
   have even size; the final counter carries the remaining parity. *)
Inductive Route : nat->nat->side->nat->list Sym->nat->nat->side->Prop :=
| Route_done c n e r: Route c (n*2+e) r n [] (n*2+c) e r
| Route_more c n v x y c' d r m w C e R:
    Word v x y -> Route c' d r m w C e R ->
    Route c (n*2) (link v c' d r) (n+m)
      ([1;0]^^(1+n*2+c)++[1;0;1;0;0;1]++v++w) C e R.

Lemma Route_flow c d r n w C e R: Route c d r n w C e R ->
  forall v x y, Word v x y ->
  Flow (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b++v) c d)
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b++v) c d)
    (fun l a b=>crossW l R a ([1;0;1;0;0;1]^^b++v++w) C e)
    (fun a b=>rootW R a ([1;0;1;0;0;1]^^b++v++w) C e) n.
Proof.
  intro H; induction H as [c n e r|c n z X Y c' d r m w C e R Hz HR IH]; intros v x y HW.
  - rewrite !app_nil_r; eapply Flow_Ws_word; exact HW.
  - eapply Flow_trans with (n:=n) (m:=m).
    + applys_eq (Flow_Ws_word (link z c' d r) v x y c 0 n HW);
        rewrite ?Nat.add_0_r; reflexivity.
    + eapply Flow_trans with (n:=0%nat) (m:=m); [apply Flow_join|].
      assert (HV:Word
        (v++[1;0]^^(1+n*2+c)++[1;0;1;0;0;1]++z)
        (x++[1;0]^^(1+n*2+c)++[1;0;0;1;1;0]++X)
        (y++[0;1]^^(1+n*2+c)++[0;1;1;0;1;1]++Y)).
      1: repeat apply Word_app; auto using Word_pow,Word_U,Word_V.
      applys_eq (IH _ _ _ HV); repeat rewrite <-app_assoc;
        repeat rewrite <-Nat.add_assoc; reflexivity.
Qed.

Lemma Route_word c d r n w C e R: Route c d r n w C e R ->
  exists x y, Word w x y.
Proof.
  intro H; induction H as [c n e r|c n v x y c' d r m w C e R HV HR [X [Y HW]]].
  - exists ([]:list Sym),([]:list Sym); apply Word_nil.
  - eexists; eexists; repeat apply Word_app; eauto using Word_pow,Word_U,Word_V.
Qed.

Lemma Route_cut c d r n w C e R: Route c d r n w C e R ->
  forall k, k<=n -> exists c' d' r' u v,
    Route c d r k u c' d' r' /\
    Route c' d' r' (n-k) v C e R /\ w=u++v.
Proof.
  intro H; induction H as [c n e r|c n z X Y c0 d0 r0 m w C e R Hz HR IH]; intros k Hk.
  - exists (k*2+c),((n-k)*2+e),r,([]:list Sym),([]:list Sym); repeat split.
    + applys_eq (Route_done c k ((n-k)*2+e) r); flia.
    + applys_eq (Route_done (k*2+c) (n-k) e r); flia.
  - destruct (Nat.le_gt_cases k n).
    + exists (k*2+c),((n-k)*2),(link z c0 d0 r0),([]:list Sym),
        ([1;0]^^(1+n*2+c)++[1;0;1;0;0;1]++z++w); repeat split.
      * applys_eq (Route_done c k ((n-k)*2) (link z c0 d0 r0)); flia.
      * applys_eq (Route_more (k*2+c) (n-k) z X Y c0 d0 r0 m w C e R Hz HR); flia.
    + destruct (IH (k-n)) as [c' [d' [r' [u [v [HU [HV EW]]]]]]]; [lia|].
      exists c',d',r',([1;0]^^(1+n*2+c)++[1;0;1;0;0;1]++z++u),v.
      split; [applys_eq (Route_more c n z X Y c0 d0 r0 (k-n) u c' d' r' Hz HU); flia|].
      split; [applys_eq HV; flia|].
      rewrite EW; repeat rewrite <-app_assoc; reflexivity.
Qed.

Definition scanW (l:side) r w c d := l <{{C}}
  [0;1;0;1;0;0;1] *> w *> [1;0]^^c *> [1;0;1] *> [0;1;0]^^d *> r.
Lemma crossW_next l r w x y c d: Word w x y ->
  crossW l r 1 w c (2+d) -->* scanW l r w (2+c) d.
Proof.
  intros [E [HR HL]].
  mid ([0;1;1;0;1] *> l {{F}}>
    (w++[1;0]) *> [1;0]^^(2+c) *> [0;1;0]^^(1+d) *> r).
  1: unfold crossW; rewrite Str_app_assoc; es.
  rewrite E,Str_app_assoc; es; follow HR; es; follow HL; unfold scanW; es.
Qed.

Lemma scan_pair l r n d:
  l <* <[0;1]^^(2+n*2) <{{C}} [0;1] *> [0;1;0]^^(2+n*2+d) *> r -->*
  scanW l r ([1;0;1;0;0;1]^^n) (1+n*2) d.
Proof.
  mid (S l ([1;0] *> [0;1;0]^^d *> r) (1+n*2) 1 0 (n*2)).
  1: unfold S; es.
  mid (S l ([1;0] *> [0;1;0]^^d *> r) 1 (1+n) (n*2) 0).
  1: applys_eq (Incs1 l ([1;0] *> [0;1;0]^^d *> r) 1 1 0 0 n); flia.
  unfold S; follow edge1; unfold scanW; st; simpl_rotate; finish.
Qed.

Lemma scanW_entry l r a w c d:
  scanW (l <* <[0;1]^^(1+a)) r w c d -->*
  crossW l r a ([1;0;1;0;0;1]++w) c d.
Proof. unfold scanW,crossW; es. Qed.

Lemma crossW_zero r w c d:
  crossW 0inf r 0 w c d -->* rootW r 2 w c d.
Proof. unfold crossW,rootW; es. Qed.

Lemma scanW_join l r v c w c' d:
  scanW l (link w c' d r) v c 0 -->*
  scanW l r (v++[1;0]^^(1+c)++[1;0;1;0;0;1]++w) c' d.
Proof. unfold scanW,link; st; simpl_rotate; finish. Qed.

Lemma Word_link v x y c z X Y: Word v x y -> Word z X Y ->
  Word (v++[1;0]^^c++[1;0;1;0;0;1]++z)
    (x++[1;0]^^c++[1;0;0;1;1;0]++X)
    (y++[0;1]^^c++[0;1;1;0;1;1]++Y).
Proof. intros; repeat apply Word_app; auto using Word_pow,Word_U,Word_V. Qed.

Lemma Route_scan_zero c d r n w C e R: Route c d r n w C e R -> n=0%nat ->
  forall l v, scanW l r v c d -->* scanW l R (v++w) C e.
Proof.
  intro H; induction H as [c n e r|c n z X Y c' d r m w C e R Hz HR IH]; intros E l v.
  - subst n; rewrite app_nil_r; finish.
  - assert (n=0%nat /\ m=0%nat) as [-> ->] by lia.
    follow scanW_join.
    applys_eq (IH eq_refl l (v++[1;0]^^(1+c)++[1;0;1;0;0;1]++z));
      repeat rewrite <-app_assoc; reflexivity.
Qed.

Lemma Route_next c d r n w C e R: Route c d r n w C e R -> n=1%nat ->
  forall l v x y, Word v x y ->
  crossW l r 1 v c d -->* scanW l R (v++w) C e.
Proof.
  intro H; induction H as [c n e r|c n z X Y c' d r m w C e R Hz HR IH]; intros E l v x y HW.
  - subst n; rewrite app_nil_r; eapply crossW_next; exact HW.
  - destruct n as [|n].
    + assert (m=1%nat) by lia; follow crossW_join.
      applys_eq (IH H l _ _ _ (Word_link v x y (1+c) z X Y HW Hz));
        repeat rewrite <-app_assoc; reflexivity.
    + assert (n=0%nat /\ m=0%nat) as [-> ->] by lia.
      follow (crossW_next l (link z c' d r) v x y c 0 HW).
      follow scanW_join.
      applys_eq (Route_scan_zero _ _ _ _ _ _ _ _ HR eq_refl l
        (v++[1;0]^^(3+c)++[1;0;1;0;0;1]++z));
        repeat rewrite <-app_assoc; reflexivity.
Qed.

Lemma Route_scan c d r n w C e R: Route c d r n w C e R ->
  forall a l v x y, a<=n -> Word v x y ->
  exists c' d' r' u z,
    Route c' d' r' (n-a) z C e R /\ w=u++z /\
    (exists X Y, Word u X Y) /\
    scanW (l <* <[0;1]^^(a*2)) r v c d -->*
      scanW l r' ([1;0;1;0;0;1]^^a++v++u) c' d'.
Proof.
  intros H a l v x y Ha HW; destruct a as [|a].
  - exists c,d,r,([]:list Sym),w; repeat split; try assumption.
    + rewrite Nat.sub_0_r; exact H.
    + exists ([]:list Sym),([]:list Sym); apply Word_nil.
    + cbn; rewrite app_nil_r; finish.
  - destruct (Route_cut _ _ _ _ _ _ _ _ H a) as
      [c1 [d1 [r1 [u0 [z0 [H0 [H1 E0]]]]]]]; [lia|].
    destruct (Route_cut _ _ _ _ _ _ _ _ H1 1) as
      [c2 [d2 [r2 [u1 [z1 [H2 [H3 E1]]]]]]]; [lia|].
    destruct (Route_word _ _ _ _ _ _ _ _ H0) as [X [Y HU]].
    destruct (Route_word _ _ _ _ _ _ _ _ H2) as [X1 [Y1 HU1]].
    exists c2,d2,r2,(u0++u1),z1; split.
    + applys_eq H3; flia.
    + split; [rewrite E0,E1,app_assoc; reflexivity|].
      split; [exists (X++X1),(Y++Y1); apply Word_app; assumption|].
      assert (HV:Word ([1;0;1;0;0;1]++v) ([1;0;0;1;1;0]++x) ([0;1;1;0;1;1]++y))
        by (apply Word_app; auto using Word_V).
      mid (crossW l r (1+a*2) ([1;0;1;0;0;1]++v) c d).
      1: applys_eq (scanW_entry l r (1+a*2) v c d); flia.
      mid (crossW l r1 1 ([1;0;1;0;0;1]^^a++[1;0;1;0;0;1]++v++u0) c1 d1).
      1: applys_eq (flow_cross _ _ _ _ _ (Route_flow _ _ _ _ _ _ _ _ H0 _ _ _ HV) l 1 0);
        repeat rewrite <-app_assoc; rewrite ?Nat.add_0_r; flia.
      assert (HZ:Word
        ([1;0;1;0;0;1]^^a++[1;0;1;0;0;1]++v++u0)
        ([1;0;0;1;1;0]^^a++[1;0;0;1;1;0]++x++X)
        ([0;1;1;0;1;1]^^a++[0;1;1;0;1;1]++y++Y))
        by (repeat apply Word_app; auto using Word_pow,Word_V).
      follow (Route_next _ _ _ _ _ _ _ _ H2 eq_refl l _ _ _ HZ).
      unfold scanW; st; simpl_rotate; finish.
Qed.

Definition Counter (r:side) n w C e := exists d s,
  r=[0;1;0]^^(2+d) *> s /\ Route 1 d s n w C e 0inf.

Lemma Counter_step l r n w C e a b: Counter r n w C e -> a<=n ->
  exists r', Counter r' (n-a+b)
    ([1;0]^^(2+b*2)++[1;0;1;0;0;1]^^(1+a)++w) C e /\
  l <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(2+a*2) <{{C}} [0;1] *> r -->*
    l <{{C}} [0;1] *> r'.
Proof.
  intros [d [s [-> HR]]] Ha.
  destruct (Route_scan _ _ _ _ _ _ _ _ HR a
    (l <* <[0;1;1]^^(2+b*2)) [] [] [] Ha Word_nil)
    as [c' [d' [s' [u [z [HZ [EW [[X [Y HU]] HS]]]]]]]].
  exists ([0;1;0]^^(2+b*2) *> link ([1;0;1;0;0;1]^^a++u) c' d' s'); split.
  - exists (b*2),(link ([1;0;1;0;0;1]^^a++u) c' d' s'); split; [reflexivity|].
    assert (HV:Word ([1;0;1;0;0;1]^^a++u)
      ([1;0;0;1;1;0]^^a++X) ([0;1;1;0;1;1]^^a++Y))
      by (apply Word_app; auto using Word_pow,Word_V).
    applys_eq (Route_more 1 b _ _ _ c' d' s' (n-a) z C e 0inf HV HZ);
      rewrite ?EW; repeat rewrite <-app_assoc; flia.
  - mid (scanW (l <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(a*2)) s [] 1 d).
    1: applys_eq (scan_pair (l <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(a*2)) s 0 d);
      st; finish; flia.
    follow HS; unfold scanW; follow pass_011; unfold link; finish.
Qed.

Lemma Counter_root r n w C e s: Counter r n w C e -> s<=n ->
  0inf <* <[0;1]^^(3+s*2) <{{C}} [0;1] *> r -->*
    rootW 0inf (2+(n-s)*2) ([1;0;1;0;0;1]^^(1+s)++w) C e.
Proof.
  intros [d [r0 [-> HR]]] Hs.
  destruct (Route_cut _ _ _ _ _ _ _ _ HR s Hs)
    as [c' [d' [r' [u [z [HU [HZ EW]]]]]]].
  destruct (Route_word _ _ _ _ _ _ _ _ HU) as [X [Y HW]].
  mid (scanW (0inf <* <[0;1]^^(1+s*2)) r0 [] 1 d).
  1: applys_eq (scan_pair (0inf <* <[0;1]^^(1+s*2)) r0 0 d); st; finish; flia.
  follow scanW_entry.
  mid (crossW 0inf r' 0 ([1;0;1;0;0;1]^^(1+s)++u) c' d').
  1: applys_eq (flow_cross _ _ _ _ _ (Route_flow _ _ _ _ _ _ _ _ HU _ _ _ Word_V) 0inf 0 0);
    unfold crossW; st; simpl_rotate; try reflexivity; try finish; flia.
  follow crossW_zero.
  assert (HV:Word ([1;0;1;0;0;1]^^(1+s)++u)
    ([1;0;0;1;1;0]^^(1+s)++X) ([0;1;1;0;1;1]^^(1+s)++Y))
    by (apply Word_app; auto using Word_pow,Word_V).
  applys_eq (flow_root _ _ _ _ _ (Route_flow _ _ _ _ _ _ _ _ HZ _ _ _ HV) 2 0);
    rewrite ?EW; repeat rewrite <-app_assoc; flia.
Qed.

Lemma Counter_cross r n w C e s: Counter r n w C e ->
  0inf <* <[0;1]^^(5+n*2+s*2) <{{C}} [0;1] *> r -->*
    crossW 0inf 0inf (2+s*2) ([1;0;1;0;0;1]^^(1+n)++w) C e.
Proof.
  intros [d [r0 [-> HR]]].
  mid (scanW (0inf <* <[0;1]^^(3+n*2+s*2)) r0 [] 1 d).
  1: applys_eq (scan_pair (0inf <* <[0;1]^^(3+n*2+s*2)) r0 0 d); st; finish; flia.
  mid (crossW 0inf r0 (2+n*2+s*2) [1;0;1;0;0;1] 1 d).
  1: applys_eq (scanW_entry 0inf r0 (2+n*2+s*2) [] 1 d); flia.
  applys_eq (flow_cross _ _ _ _ _ (Route_flow _ _ _ _ _ _ _ _ HR _ _ _ Word_V) 0inf (2+s*2) 0);
    unfold crossW; st; simpl_rotate; try reflexivity; try finish; flia.
Qed.

Lemma rootW_terminal a w x y c e: e<=1 -> Word w x y ->
  rootW 0inf a w c e -->*
  0inf <* <[0;1]^^(3+a) <* rev y <* <[0;1]^^(1+c+e) {{B}}> 0inf.
Proof.
  intros He HW; destruct e as [|[|e]]; try lia.
  - applys_eq (rootW_finish_word0 a w x y c HW); flia.
  - applys_eq (rootW_finish_word1 a w x y c HW); flia.
Qed.
Lemma crossW_terminal l a w x y c e: e<=1 -> Word w x y ->
  crossW l 0inf (2+a) w c e -->*
  l <* <[0;1]^^a <* <[0;1;1]^^3 <* rev y <* <[0;1]^^(1+c+e) {{B}}> 0inf.
Proof.
  intros He HW; destruct e as [|[|e]]; try lia.
  - applys_eq (crossW_finish_word0 l a w x y c HW); flia.
  - applys_eq (crossW_finish_word1 l a w x y c HW); flia.
Qed.

Lemma Counter_normal r n w C e s x y:
  Counter r n w C e -> s<=n -> e<=1 -> Word w x y ->
  0inf <* <[0;1]^^(3+s*2) <{{C}} [0;1] *> r -[tm]->+
  0inf <* <[0;1]^^(5+(n-s)*2) <* rev ([0;1;1;0;1;1]^^(1+s)++y)
    <* <[0;1]^^(1+C+e) {{B}}> 0inf.
Proof.
  intros HR Hs He HW; apply evstep_progress; [|discriminate].
  follow (Counter_root r n w C e s HR Hs).
  applys_eq (rootW_terminal (2+(n-s)*2) _ _ _ C e He
    (Word_app _ _ _ _ _ _ (Word_pow _ _ _ (1+s) Word_V) HW)); flia.
Qed.
Lemma Counter_overflow r n w C e s x y:
  Counter r n w C e -> e<=1 -> Word w x y ->
  0inf <* <[0;1]^^(5+n*2+s*2) <{{C}} [0;1] *> r -[tm]->+
  0inf <* <[0;1]^^(s*2) <* <[0;1;1]^^3 <* rev ([0;1;1;0;1;1]^^(1+n)++y)
    <* <[0;1]^^(1+C+e) {{B}}> 0inf.
Proof.
  intros HR He HW; apply evstep_progress; [|discriminate].
  follow (Counter_cross r n w C e s HR).
  apply (crossW_terminal 0inf (s*2) _ _ _ C e He
    (Word_app _ _ _ _ _ _ (Word_pow _ _ _ (1+n) Word_V) HW)).
Qed.

Fixpoint column_side (l:side) (cs:list (nat*nat)) : side :=
  match cs with []=>l | (a,b)::cs=>
    column_side l cs <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(2+a*2) end.
Fixpoint column_word (cs:list (nat*nat)) : list Sym :=
  match cs with []=>[] | (a,b)::cs=>
    column_word cs++[1;0]^^(2+b*2)++[1;0;1;0;0;1]^^(1+a) end.
Fixpoint column_image (cs:list (nat*nat)) : list Sym :=
  match cs with []=>[] | (a,b)::cs=>
    column_image cs++[0;1]^^(2+b*2)++[0;1;1;0;1;1]^^(1+a) end.

Inductive ColumnRun : nat->list (nat*nat)->nat->Prop :=
| Columns_nil n: ColumnRun n [] n
| Columns_cons n a b cs m: a<=n -> ColumnRun (n-a+b) cs m ->
    ColumnRun n ((a,b)::cs) m.

Lemma column_word_spec cs: exists x, Word (column_word cs) x (column_image cs).
Proof.
  induction cs as [|[a b] cs [x HW]]; cbn[column_word column_image].
  - exists ([]:list Sym); apply Word_nil.
  - eexists; repeat apply Word_app; eauto using Word_pow,Word_U,Word_V.
Qed.

Lemma Counter_columns n cs m: ColumnRun n cs m ->
  forall l r w C e, Counter r n w C e -> exists r',
  Counter r' m (column_word cs++w) C e /\
  column_side l cs <{{C}} [0;1] *> r -->* l <{{C}} [0;1] *> r'.
Proof.
  intro H; induction H as [n|n a b cs m Ha H IH]; intros l r w C e HR.
  - exists r; split; [exact HR|finish].
  - destruct (Counter_step (column_side l cs) r n w C e a b HR Ha) as [r1 [H1 HS]].
    destruct (IH l r1 _ C e H1) as [r2 [H2 HT]].
    exists r2; split.
    + cbn[column_word]; repeat rewrite <-app_assoc; exact H2.
    + cbn[column_side]; follow HS; exact HT.
Qed.

Lemma Counter_columns_normal r n w C e cs m s x y:
  Counter r n w C e -> ColumnRun n cs m -> s<=m -> e<=1 ->
  Word (column_word cs++w) x y ->
  column_side (0inf <* <[0;1]^^(3+s*2)) cs <{{C}} [0;1] *> r -[tm]->+
  0inf <* <[0;1]^^(5+(m-s)*2) <* rev ([0;1;1;0;1;1]^^(1+s)++y)
    <* <[0;1]^^(1+C+e) {{B}}> 0inf.
Proof.
  intros HR HC Hs He HW.
  destruct (Counter_columns _ _ _ HC (0inf <* <[0;1]^^(3+s*2)) r w C e HR)
    as [r' [HT HS]].
  eapply evstep_progress_trans; [exact HS|eapply Counter_normal; eauto].
Qed.
Lemma Counter_columns_overflow r n w C e cs m s x y:
  Counter r n w C e -> ColumnRun n cs m -> e<=1 ->
  Word (column_word cs++w) x y ->
  column_side (0inf <* <[0;1]^^(5+m*2+s*2)) cs <{{C}} [0;1] *> r -[tm]->+
  0inf <* <[0;1]^^(s*2) <* <[0;1;1]^^3 <* rev ([0;1;1;0;1;1]^^(1+m)++y)
    <* <[0;1]^^(1+C+e) {{B}}> 0inf.
Proof.
  intros HR HC He HW.
  destruct (Counter_columns _ _ _ HC (0inf <* <[0;1]^^(5+m*2+s*2)) r w C e HR)
    as [r' [HT HS]].
  eapply evstep_progress_trans; [exact HS|eapply Counter_overflow; eauto].
Qed.

Lemma Counter_base n e:
  Counter ([0;1;0]^^(2+n*2+e) *> 0inf) n [] (1+n*2) e.
Proof.
  exists (n*2+e),0inf; split; [flia|].
  applys_eq (Route_done 1 n e 0inf); flia.
Qed.

Lemma Counter_link b v x y c d r n w C e:
  Word v x y -> Route c d r n w C e 0inf ->
  Counter ([0;1;0]^^(2+b*2) *> link v c d r) (b+n)
    ([1;0]^^(2+b*2)++[1;0;1;0;0;1]++v++w) C e.
Proof.
  intros HV HR; exists (b*2),(link v c d r); split; [reflexivity|].
  applys_eq (Route_more 1 b v x y c d r n w C e 0inf HV HR); flia.
Qed.

Lemma Counter_gap g b d e:
  Counter ([0;1;0]^^(2+b*2) *> link ([1;0;1;0;0;1]^^g) (1+g*2) (d*2+e) 0inf)
    (b+d) ([1;0]^^(2+b*2)++[1;0;1;0;0;1]^^(1+g)) (1+g*2+d*2) e.
Proof.
  applys_eq (Counter_link b _ _ _ (1+g*2) (d*2+e) 0inf d [] (d*2+(1+g*2)) e
    (Word_pow _ _ _ g Word_V) (Route_done (1+g*2) d e 0inf));
    rewrite ?app_nil_r; flia.
Qed.

Lemma counter_begin l p b: P p ->
  l <* <[0;1;1]^^b <* <[0;1]^^p {{B}}> 0inf -->*
  l <{{C}} [0;1] *> [0;1;0]^^(p+b) *> 0inf.
Proof.
  unfold P; intro HP; follow HP; follow pass_011;
    rewrite (Nat.add_comm p b),(lpow_add _ b p),Str_app_assoc; finish.
Qed.
Lemma counter_begin_gap l g b d e: P (2+g*2+(d*2+e)) ->
  l <* <[0;1;1]^^(2+b*2) <* <[0;1]^^((2+g*2+(d*2+e))+(2+g*2)) {{B}}> 0inf -->*
  l <{{C}} [0;1] *> [0;1;0]^^(2+b*2) *>
    link ([1;0;1;0;0;1]^^g) (1+g*2) (d*2+e) 0inf.
Proof.
  intro HP; follow (fun l=>return_even l g (d*2+e) HP); follow pass_011.
  unfold link; st; simpl_rotate; finish.
Qed.

Inductive SectionStart (l:side) : nat->list Sym->nat->nat->Q*tape->Prop :=
| Start_good d b e: P (2+d*2+e) ->
    SectionStart l (1+d+b) [] (3+d*2+b*2) e
      (l <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(2+d*2+e) {{B}}> 0inf)
| Start_gap g b d e: P (2+g*2+(d*2+e)) ->
    SectionStart l (b+d) ([1;0]^^(2+b*2)++[1;0;1;0;0;1]^^(1+g))
      (1+g*2+d*2) e
      (l <* <[0;1;1]^^(2+b*2) <* <[0;1]^^((2+g*2+(d*2+e))+(2+g*2)) {{B}}> 0inf).

Lemma SectionStart_spec l n w C e c: SectionStart l n w C e c ->
  exists r, Counter r n w C e /\ c -->* l <{{C}} [0;1] *> r.
Proof.
  intro H; destruct H as [d b e HP|g b d e HP].
  - exists ([0;1;0]^^((2+d*2+e)+(2+b*2)) *> 0inf); split.
    + applys_eq (Counter_base (1+d+b) e); flia.
    + apply counter_begin,HP.
  - eexists; split; [apply Counter_gap|apply counter_begin_gap,HP].
Qed.

Lemma SectionStart_word l n w C e c: SectionStart l n w C e c ->
  exists x y, Word w x y.
Proof.
  intro H; destruct H.
  - exists ([]:list Sym),([]:list Sym); apply Word_nil.
  - eexists; eexists; apply Word_app; auto using Word_pow,Word_U,Word_V.
Qed.

Lemma section_columns_normal n w C e c cs m s x y:
  SectionStart (column_side (0inf <* <[0;1]^^(3+s*2)) cs) n w C e c ->
  ColumnRun n cs m -> s<=m -> e<=1 -> Word (column_word cs++w) x y ->
  c -[tm]->+ 0inf <* <[0;1]^^(5+(m-s)*2) <* rev ([0;1;1;0;1;1]^^(1+s)++y)
    <* <[0;1]^^(1+C+e) {{B}}> 0inf.
Proof.
  intros HS HC Hs He HW; destruct (SectionStart_spec _ _ _ _ _ _ HS) as [r [HR HT]].
  eapply evstep_progress_trans; [exact HT|eapply Counter_columns_normal; eauto].
Qed.
Lemma section_columns_overflow n w C e c cs m s x y:
  SectionStart (column_side (0inf <* <[0;1]^^(5+m*2+s*2)) cs) n w C e c ->
  ColumnRun n cs m -> e<=1 -> Word (column_word cs++w) x y ->
  c -[tm]->+ 0inf <* <[0;1]^^(s*2) <* <[0;1;1]^^3 <* rev ([0;1;1;0;1;1]^^(1+m)++y)
    <* <[0;1]^^(1+C+e) {{B}}> 0inf.
Proof.
  intros HS HC He HW; destruct (SectionStart_spec _ _ _ _ _ _ HS) as [r [HR HT]].
  eapply evstep_progress_trans; [exact HT|eapply Counter_columns_overflow; eauto].
Qed.


Local Close Scope nat_scope.


(* Shaped cleanup paths, including both parities of the left border. *)
Local Open Scope nat_scope.
Local Open Scope sym_scope.
Inductive EraseWord : list Sym->nat->nat->Prop :=
| Erase_nil: EraseWord [] 0 0
| Erase_V n w u v: EraseWord w u v -> EraseWord ([1;0;1;0;0;1]^^n++w) u (n+v)
| Erase_pair j k w u v: EraseWord w u v ->
    EraseWord ([1;0]^^(2+j*2)++[1;0;1;0;0;1]^^(1+k)++w) (1+j+u) (1+k+v).

Lemma crossV_two r b c e:
  crossV 0inf r 2 b (3+c) (1+e) -->* rootV r 4 (1+b) (4+c) e.
Proof. unfold crossV,rootV; es. Qed.


Lemma crossV_zero r b c e:
  crossV 0inf r 0 b c e -->* rootV r 2 b c e.
Proof. unfold crossV,rootV; es. Qed.
Lemma crossZ_zero r b c e:
  crossZ 0inf r 0 b c e -->* rootZ r 2 b c e.
Proof. unfold crossZ,rootZ; es. Qed.
Lemma crossZ_two r b c e:
  crossZ 0inf r 2 b (3+c) (2+e) -->* rootZ r 4 (1+b) (3+c) e.
Proof. unfold crossZ,rootZ; es. Qed.
Lemma crossVend_two r b c e:
  crossV 0inf ([1;0]^^(1+e) *> r) 2 b (3+c) 0 -->* rootZ r 4 (1+b) (4+c) e.
Proof. unfold crossV,rootZ; es. Qed.

Record Pass (C:side->nat->nat->Q*tape) (R:nat->nat->Q*tape)
  (D:side->nat->nat->Q*tape) (T:nat->nat->Q*tape) n : Prop := {
  pass_flow: Flow C R D T n;
  pass_even: forall s v b, s+v+1=n -> C 0inf (2+s*2) b -->* T (2+v*2) (1+s+b)
}.
Lemma Pass_id C R: Pass C R C R 0.
Proof. constructor; [apply Flow_id|intros; lia]. Qed.
Lemma Pass_trans C R D T F U n m:
  Pass C R D T n -> Pass D T F U m -> Pass C R F U (n+m).
Proof.
  intros [HF HE] [KF KE]; constructor; [eapply Flow_trans; eauto|].
  intros s v b H; destruct (Nat.le_gt_cases n s).
  - mid (D 0inf (2+(s-n)*2) (n+b)).
    + applys_eq (flow_cross _ _ _ _ _ HF 0inf (2+(s-n)*2) b); flia.
    + applys_eq (KE (s-n) v (n+b)); flia.
  - mid (T (2+(n-s-1)*2) (1+s+b)); [apply HE; flia|].
    applys_eq (flow_root _ _ _ _ _ KF (2+(n-s-1)*2) (1+s+b)); flia.
Qed.

Lemma Pass_W r c d:
  Pass (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b) c (2+d))
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b) c (2+d))
    (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b) (2+c) d)
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b) (2+c) d) 1.
Proof.
  constructor; [apply Flow_W|]; intros s v b E.
  assert (s=0%nat /\ v=0%nat) as [-> ->] by lia.
  follow (flow_cross _ _ _ _ _ (Flow_W r c d) 0inf 0 b); apply crossW_zero.
Qed.
Lemma Pass_V r c e:
  Pass (fun l a b=>crossV l r a b (3+c) (1+e))
    (fun a b=>rootV r a b (3+c) (1+e))
    (fun l a b=>crossV l r a b (4+c) e)
    (fun a b=>rootV r a b (4+c) e) 2.
Proof.
  constructor; [apply Flow_V|]; intros s v b E.
  destruct s as [|[|s]]; try lia.
  - assert (v=1%nat) as -> by lia; apply crossV_two.
  - assert (v=0%nat) as -> by lia; follow crossV_step; apply crossV_zero.
Qed.
Lemma Pass_Z r c e:
  Pass (fun l a b=>crossZ l r a b (3+c) (2+e))
    (fun a b=>rootZ r a b (3+c) (2+e))
    (fun l a b=>crossZ l r a b (3+c) e)
    (fun a b=>rootZ r a b (3+c) e) 2.
Proof.
  constructor; [apply Flow_Z|]; intros s v b E.
  destruct s as [|[|s]]; try lia.
  - assert (v=1%nat) as -> by lia; apply crossZ_two.
  - assert (v=0%nat) as -> by lia; follow crossZ_step; apply crossZ_zero.
Qed.
Lemma Pass_V_end r c e:
  Pass (fun l a b=>crossV l ([1;0]^^(1+e) *> r) a b (3+c) 0)
    (fun a b=>rootV ([1;0]^^(1+e) *> r) a b (3+c) 0)
    (fun l a b=>crossZ l r a b (4+c) e)
    (fun a b=>rootZ r a b (4+c) e) 2.
Proof.
  constructor; [apply Flow_V_end|]; intros s v b E.
  destruct s as [|[|s]]; try lia.
  - assert (v=1%nat) as -> by lia; apply crossVend_two.
  - assert (v=0%nat) as -> by lia; follow crossV_end; apply crossZ_zero.
Qed.

Lemma Pass_Ws r c d n:
  Pass (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b) c (n*2+d))
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b) c (n*2+d))
    (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b) (n*2+c) d)
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b) (n*2+c) d) n.
Proof.
  gen c; induction n; intro c; [apply Pass_id|].
  cbn [Nat.mul]; eapply Pass_trans with (n:=1%nat) (m:=n); [apply Pass_W|].
  replace (2+n*2+c)%nat with (n*2+(2+c))%nat by lia; apply IHn.
Qed.
Lemma Pass_Vs r c e n:
  Pass (fun l a b=>crossV l r a b (3+c) (e+n))
    (fun a b=>rootV r a b (3+c) (e+n))
    (fun l a b=>crossV l r a b (3+c+n) e)
    (fun a b=>rootV r a b (3+c+n) e) (n*2).
Proof.
  gen c e; induction n; intros; [rewrite !Nat.add_0_r; apply Pass_id|].
  rewrite !Nat.add_succ_r.
  eapply Pass_trans with (n:=2%nat) (m:=n*2); [apply Pass_V|apply IHn].
Qed.
Lemma Pass_Zs r c e n:
  Pass (fun l a b=>crossZ l r a b (3+c) (e+n*2))
    (fun a b=>rootZ r a b (3+c) (e+n*2))
    (fun l a b=>crossZ l r a b (3+c) e)
    (fun a b=>rootZ r a b (3+c) e) (n*2).
Proof.
  induction n; [rewrite !Nat.add_0_r; apply Pass_id|].
  cbn [Nat.mul]; replace (e+(2+n*2)) with (2+(e+n*2)) by lia.
  eapply Pass_trans with (n:=2%nat) (m:=n*2); [apply Pass_Z|apply IHn].
Qed.

Lemma Pass_Z_to_V r c k:
  Pass (fun l a b=>crossZ l ([1;0;1;0;0;1]^^(1+k) *> r) a b (3+c) 1)
    (fun a b=>rootZ ([1;0;1;0;0;1]^^(1+k) *> r) a b (3+c) 1)
    (fun l a b=>crossV l r a b (3+c) k)
    (fun a b=>rootV r a b (3+c) k) 2.
Proof. exact (Pass_Z ([1;0;0;1] *> [1;0;1;0;0;1]^^k *> r) c 0). Qed.

Lemma Pass_Z_back r c d:
  Pass (fun l a b=>crossZ l ([1;0;1] *> [0;1;0]^^(1+d) *> r) a b (4+c) 0)
    (fun a b=>rootZ ([1;0;1] *> [0;1;0]^^(1+d) *> r) a b (4+c) 0)
    (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b) (1+c) (2+d))
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b) (1+c) (2+d)) 2.
Proof.
  applys_eq (Pass_Z ([1;0] *> [0;1;0]^^d *> r) (1+c) 0);
    repeat (apply functional_extensionality; intro);
    unfold crossZ,rootZ,crossW,rootW; st; simpl_rotate; reflexivity.
Qed.


Lemma crossZ_empty l a b c:
  crossZ l ([1;0;1] *> 0inf) (4+a) b (4+c) 0 -->*
  crossW l 0inf a ([1;0;1;0;0;1]^^(2+b)) (2+c) 0.
Proof. unfold crossZ,crossW; es. Qed.
Lemma rootZ_empty a b c:
  rootZ ([1;0;1] *> 0inf) a b (4+c) 0 -->*
  rootW 0inf (4+a) ([1;0;1;0;0;1]^^b) (2+c) 0.
Proof. unfold rootZ,rootW; es. Qed.
Lemma crossZ_empty_one b c:
  crossZ 0inf ([1;0;1] *> 0inf) 1 b (4+c) 0 -->*
  rootW 0inf 2 ([1;0;1;0;0;1]^^(1+b)) (2+c) 0.
Proof. unfold crossZ,rootW; es. Qed.
Lemma crossZ_empty_three b c:
  crossZ 0inf ([1;0;1] *> 0inf) 3 b (4+c) 0 -->*
  rootW 0inf 0 ([1;0;1;0;0;1]^^(2+b)) (2+c) 0.
Proof. unfold crossZ,rootW; es. Qed.
Lemma crossZ_empty_two b c:
  crossZ 0inf ([1;0;1] *> 0inf) 2 b (4+c) 0 -->*
  rootW 0inf 4 ([1;0;1;0;0;1]^^(1+b)) (2+c) 0.
Proof. unfold crossZ,rootW; es. Qed.

Lemma Pass_Z_empty c:
  Pass (fun l a b=>crossZ l ([1;0;1] *> 0inf) a b (4+c) 0)
    (fun a b=>rootZ ([1;0;1] *> 0inf) a b (4+c) 0)
    (fun l a b=>crossW l 0inf a ([1;0;1;0;0;1]^^b) (2+c) 0)
    (fun a b=>rootW 0inf a ([1;0;1;0;0;1]^^b) (2+c) 0) 2.
Proof.
  constructor.
  - constructor; intros; cbn beta; try apply crossZ_empty; try apply rootZ_empty.
    destruct s as [|[|s]]; try lia.
    + assert (v=1%nat) as -> by lia; apply crossZ_empty_one.
    + assert (v=0%nat) as -> by lia; apply crossZ_empty_three.
  - intros s v b E; destruct s as [|[|s]]; try lia.
    + assert (v=1%nat) as -> by lia; apply crossZ_empty_two.
    + assert (v=0%nat) as -> by lia; follow crossZ_empty; apply crossW_zero.
Qed.

Lemma crossW_last_one b c e: e<=1 ->
  crossW 0inf 0inf 1 ([1;0;1;0;0;1]^^b) c e -->*
  0inf <* <[0;1] <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(1+c+e) {{B}}> 0inf.
Proof. intro H; destruct e as [|[|e]]; try lia; unfold crossW; es. Qed.

Local Open Scope nat_scope.
Local Open Scope sym_scope.

Lemma EraseWord_app w u v z x y:
  EraseWord w u v -> EraseWord z x y -> EraseWord (w++z) (u+x) (v+y).
Proof.
  intros H K; induction H; [exact K| |].
  - rewrite <-app_assoc; applys_eq (Erase_V n _ _ _ IHEraseWord); flia.
  - rewrite <-!app_assoc; applys_eq (Erase_pair j k _ _ _ IHEraseWord); flia.
Qed.

Lemma EraseWord_word w u v: EraseWord w u v -> exists x y, Word w x y.
Proof.
  intro H; induction H as [|n w u v H [X [Y HW]]|j k w u v H [X [Y HW]]].
  - exists ([]:list Sym),([]:list Sym); apply Word_nil.
  - eexists; eexists; apply Word_app; eauto using Word_pow,Word_V.
  - eexists; eexists; repeat apply Word_app; eauto using Word_pow,Word_V,Word_U.
Qed.

Inductive RRoute : nat->nat->side->nat->list Sym->nat->nat->side->Prop :=
| RRoute_done j n e r: RRoute (1+j*2) (n*2+e) r n [] (1+(j+n)*2) e r
| RRoute_more j n v u q c' d r m w C e R:
    EraseWord v u q -> RRoute c' d r m w C e R ->
    RRoute (1+j*2) (n*2) (link v c' d r) (n+m)
      ([1;0]^^(2+(j+n)*2)++[1;0;1;0;0;1]++v++w) C e R.

Lemma RRoute_forget c d r n w C e R: RRoute c d r n w C e R ->
  Route c d r n w C e R.
Proof.
  intro H; induction H as [j n e r|j n v u q c' d r m w C e R HV HR IH].
  - applys_eq (Route_done (1+j*2) n e r); flia.
  - destruct (EraseWord_word _ _ _ HV) as [X [Y HW]].
    applys_eq (Route_more (1+j*2) n v X Y c' d r m w C e R HW IH); flia.
Qed.

Lemma RRoute_odd c d r n w C e R: RRoute c d r n w C e R ->
  exists j k, c=1+j*2 /\ C=1+k*2.
Proof. intro H; induction H; [exists j,(j+n); auto|destruct IHRRoute as [x [y [_ E]]]; exists j,y; auto]. Qed.

Lemma RRoute_erase c d r n w C e R: RRoute c d r n w C e R ->
  exists u v, EraseWord w u v.
Proof.
  intro H; induction H as [j n e r|j n z u q c' d r m w C e R HZ HR [x [y HW]]].
  - exists 0%nat,0%nat; constructor.
  - exists (1+(j+n)+(u+x)),(1+(q+y)).
    applys_eq (Erase_pair (j+n) 0 _ _ _ (EraseWord_app _ _ _ _ _ _ HZ HW));
      cbn; rewrite ?app_nil_r; repeat rewrite <-app_assoc; reflexivity.
Qed.

Lemma RRoute_cut c d r n w C e R: RRoute c d r n w C e R ->
  forall k, k<=n -> exists c' d' r' u v,
    RRoute c d r k u c' d' r' /\
    RRoute c' d' r' (n-k) v C e R /\ w=u++v.
Proof.
  intro H; induction H as [j n e r|j n z x y c0 d0 r0 m w C e R HZ HR IH]; intros k Hk.
  - exists (1+(j+k)*2),((n-k)*2+e),r,([]:list Sym),([]:list Sym); repeat split.
    + applys_eq (RRoute_done j k ((n-k)*2+e) r); flia.
    + applys_eq (RRoute_done (j+k) (n-k) e r); flia.
  - destruct (Nat.le_gt_cases k n).
    + exists (1+(j+k)*2),((n-k)*2),(link z c0 d0 r0),([]:list Sym),
        ([1;0]^^(2+(j+n)*2)++[1;0;1;0;0;1]++z++w); repeat split.
      * applys_eq (RRoute_done j k ((n-k)*2) (link z c0 d0 r0)); flia.
      * applys_eq (RRoute_more (j+k) (n-k) z x y c0 d0 r0 m w C e R HZ HR); flia.
    + destruct (IH (k-n)) as [c' [d' [r' [u [v [HU [HV EW]]]]]]]; [lia|].
      exists c',d',r',([1;0]^^(2+(j+n)*2)++[1;0;1;0;0;1]++z++u),v.
      split; [applys_eq (RRoute_more j n z x y c0 d0 r0 (k-n) u c' d' r' HZ HU); flia|].
      split; [applys_eq HV; flia|].
      rewrite EW; repeat rewrite <-app_assoc; reflexivity.
Qed.

Lemma scanW_consume l c d r a u c1 d1 r1 v c2 d2 r2 w x y:
  Route c d r a u c1 d1 r1 -> Route c1 d1 r1 1 v c2 d2 r2 -> Word w x y ->
  scanW (l <* <[0;1]^^(2+a*2)) r w c d -->*
  scanW l r2 ([1;0;1;0;0;1]^^(1+a)++w++u++v) c2 d2.
Proof.
  intros HU HV HW; destruct (Route_word _ _ _ _ _ _ _ _ HU) as [X [Y EU]].
  assert (H1:Word ([1;0;1;0;0;1]++w) ([1;0;0;1;1;0]++x) ([0;1;1;0;1;1]++y))
    by (apply Word_app; auto using Word_V).
  mid (crossW l r (1+a*2) ([1;0;1;0;0;1]++w) c d).
  1: applys_eq (scanW_entry l r (1+a*2) w c d); flia.
  mid (crossW l r1 1 ([1;0;1;0;0;1]^^a++[1;0;1;0;0;1]++w++u) c1 d1).
  1: applys_eq (flow_cross _ _ _ _ _ (Route_flow _ _ _ _ _ _ _ _ HU _ _ _ H1) l 1 0);
    repeat rewrite <-app_assoc; rewrite ?Nat.add_0_r; flia.
  assert (H2:Word ([1;0;1;0;0;1]^^a++[1;0;1;0;0;1]++w++u)
    ([1;0;0;1;1;0]^^a++[1;0;0;1;1;0]++x++X)
    ([0;1;1;0;1;1]^^a++[0;1;1;0;1;1]++y++Y))
    by (repeat apply Word_app; auto using Word_pow,Word_V).
  follow (Route_next _ _ _ _ _ _ _ _ HV eq_refl l _ _ _ H2).
  unfold scanW; st; simpl_rotate; finish.
Qed.

Lemma RRoute_scan c d r n w C e R: RRoute c d r n w C e R ->
  forall a l v x y, a<=n -> Word v x y -> exists c' d' r' u z i j,
    RRoute c' d' r' (n-a) z C e R /\ w=u++z /\ EraseWord u i j /\
    scanW (l <* <[0;1]^^(a*2)) r v c d -->*
      scanW l r' ([1;0;1;0;0;1]^^a++v++u) c' d'.
Proof.
  intros H a l v x y Ha HW; destruct a as [|a].
  - exists c,d,r,([]:list Sym),w; exists (0%nat),(0%nat); split; [rewrite Nat.sub_0_r; exact H|].
    split; [reflexivity|]; split; [constructor|]; cbn; rewrite app_nil_r; finish.
  - destruct (RRoute_cut _ _ _ _ _ _ _ _ H a) as [c1 [d1 [r1 [u0 [z0 [H0 [H1 E0]]]]]]]; [lia|].
    destruct (RRoute_cut _ _ _ _ _ _ _ _ H1 1) as [c2 [d2 [r2 [u1 [z1 [H2 [H3 E1]]]]]]]; [lia|].
    destruct (RRoute_erase _ _ _ _ _ _ _ _ H0) as [i [j EU0]].
    destruct (RRoute_erase _ _ _ _ _ _ _ _ H2) as [k [q EU1]].
    exists c2,d2,r2,(u0++u1),z1; exists (i+k),(j+q); split; [applys_eq H3; flia|].
    split; [rewrite E0,E1,app_assoc; reflexivity|].
    split; [apply EraseWord_app; assumption|].
    applys_eq (scanW_consume l c d r a u0 c1 d1 r1 u1 c2 d2 r2 v x y
      (RRoute_forget _ _ _ _ _ _ _ _ H0) (RRoute_forget _ _ _ _ _ _ _ _ H2) HW);
      repeat rewrite <-app_assoc; flia.
Qed.

Definition RCounter (r:side) n w C e := exists d s,
  r=[0;1;0]^^(2+d) *> s /\ RRoute 1 d s n w C e 0inf.
Lemma RCounter_forget r n w C e: RCounter r n w C e -> Counter r n w C e.
Proof. intros [d [s [E H]]]; exists d,s; split; [exact E|apply RRoute_forget,H]. Qed.

Lemma RCounter_step l r n w C e a b: RCounter r n w C e -> a<=n ->
  exists r', RCounter r' (n-a+b)
    ([1;0]^^(2+b*2)++[1;0;1;0;0;1]^^(1+a)++w) C e /\
    l <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(2+a*2) <{{C}} [0;1] *> r -->*
      l <{{C}} [0;1] *> r'.
Proof.
  intros [d [s [-> HR]]] Ha.
  destruct (RRoute_scan _ _ _ _ _ _ _ _ HR a
    (l <* <[0;1;1]^^(2+b*2)) [] [] [] Ha Word_nil)
    as [c' [d' [s' [u [z [i [j [HZ [EW [HU HS]]]]]]]]]].
  exists ([0;1;0]^^(2+b*2) *> link ([1;0;1;0;0;1]^^a++u) c' d' s'); split.
  - exists (b*2),(link ([1;0;1;0;0;1]^^a++u) c' d' s'); split; [reflexivity|].
    applys_eq (RRoute_more 0 b _ _ _ c' d' s' (n-a) z C e 0inf (Erase_V a _ _ _ HU) HZ);
      rewrite ?EW; repeat rewrite <-app_assoc; flia.
  - mid (scanW (l <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(a*2)) s [] 1 d).
    1: applys_eq (scan_pair (l <* <[0;1;1]^^(2+b*2) <* <[0;1]^^(a*2)) s 0 d); st; finish; flia.
    follow HS; unfold scanW; follow pass_011; unfold link; finish.
Qed.

Lemma RCounter_columns n cs m: ColumnRun n cs m -> forall l r w C e,
  RCounter r n w C e -> exists r', RCounter r' m (column_word cs++w) C e /\
    column_side l cs <{{C}} [0;1] *> r -->* l <{{C}} [0;1] *> r'.
Proof.
  intro H; induction H as [n|n a b cs m Ha H IH]; intros l r w C e HR.
  - exists r; split; [exact HR|finish].
  - destruct (RCounter_step (column_side l cs) r n w C e a b HR Ha) as [r1 [H1 HS]].
    destruct (IH l r1 _ C e H1) as [r2 [H2 HT]].
    exists r2; split.
    + cbn[column_word]; repeat rewrite <-app_assoc; exact H2.
    + cbn[column_side]; follow HS; exact HT.
Qed.

Lemma RCounter_base n e: RCounter ([0;1;0]^^(2+n*2+e) *> 0inf) n [] (1+n*2) e.
Proof. exists (n*2+e),0inf; split; [flia|]; applys_eq (RRoute_done 0 n e 0inf); flia. Qed.
Lemma RCounter_gap g b d e:
  RCounter ([0;1;0]^^(2+b*2) *> link ([1;0;1;0;0;1]^^g) (1+g*2) (d*2+e) 0inf)
    (b+d) ([1;0]^^(2+b*2)++[1;0;1;0;0;1]^^(1+g)) (1+g*2+d*2) e.
Proof.
  exists (b*2),(link ([1;0;1;0;0;1]^^g) (1+g*2) (d*2+e) 0inf); split; [reflexivity|].
  applys_eq (RRoute_more 0 b _ _ _ (1+g*2) (d*2+e) 0inf d [] (1+(g+d)*2) e 0inf
    (Erase_V g [] 0 0 Erase_nil) (RRoute_done g d e 0inf));
    rewrite ?app_nil_r; flia.
Qed.
Lemma SectionStart_Rspec l n w C e c: SectionStart l n w C e c ->
  exists r, RCounter r n w C e /\ c -->* l <{{C}} [0;1] *> r.
Proof.
  intro H; destruct H as [d b e HP|g b d e HP].
  - exists ([0;1;0]^^((2+d*2+e)+(2+b*2)) *> 0inf); split.
    + applys_eq (RCounter_base (1+d+b) e); flia.
    + apply counter_begin,HP.
  - eexists; split; [apply RCounter_gap|apply counter_begin_gap,HP].
Qed.


Lemma Pass_erase_pair r c j k:
  Pass (fun l a b=>crossV l ([1;0]^^(2+j*2) *> [1;0;1;0;0;1]^^(1+k) *> r) a b (3+c) 0)
    (fun a b=>rootV ([1;0]^^(2+j*2) *> [1;0;1;0;0;1]^^(1+k) *> r) a b (3+c) 0)
    (fun l a b=>crossV l r a b (4+c+k) 0)
    (fun a b=>rootV r a b (4+c+k) 0) ((2+j+k)*2).
Proof.
  replace ((2+j+k)*2)%nat with (2+(j*2+(2+k*2)))%nat by lia.
  eapply Pass_trans with (n:=2%nat) (m:=j*2+(2+k*2)); [apply Pass_V_end|].
  eapply Pass_trans with (n:=j*2) (m:=2+k*2); [apply (Pass_Zs _ (1+c) 1 j)|].
  eapply Pass_trans with (n:=2%nat) (m:=k*2); [apply Pass_Z_to_V|].
  apply (Pass_Vs r (1+c) 0 k).
Qed.

Lemma EraseWord_pass w u v: EraseWord w u v -> forall r c,
  Pass (fun l a b=>crossV l (w *> r) a b (3+c) 0)
    (fun a b=>rootV (w *> r) a b (3+c) 0)
    (fun l a b=>crossV l r a b (3+c+v) 0)
    (fun a b=>rootV r a b (3+c+v) 0) ((u+v)*2).
Proof.
  intro H; induction H as [|n w u v H IH|j k w u v H IH]; intros r c.
  - rewrite Nat.add_0_r; apply Pass_id.
  - rewrite Str_app_assoc.
    replace ((u+(n+v))*2)%nat with (n*2+(u+v)*2)%nat by lia.
    eapply Pass_trans with (n:=n*2) (m:=(u+v)*2); [apply (Pass_Vs _ c 0 n)|].
    replace (3+c+(n+v))%nat with (3+(c+n)+v)%nat by lia.
    replace (3+c+n)%nat with (3+(c+n))%nat by lia; apply IH.
  - rewrite !Str_app_assoc.
    replace (((1+j+u)+(1+k+v))*2)%nat with ((2+j+k)*2+(u+v)*2)%nat by lia.
    eapply Pass_trans with (n:=(2+j+k)*2) (m:=(u+v)*2); [apply Pass_erase_pair|].
    replace (3+c+(1+k+v))%nat with (3+(1+c+k)+v)%nat by lia.
    replace (4+c+k)%nat with (3+(1+c+k))%nat by lia; apply IH.
Qed.

Lemma Pass_odd_join r c w c' d:
  Pass (fun l a b=>crossW l (link w c' d r) a ([1;0;1;0;0;1]^^b) c 1)
    (fun a b=>rootW (link w c' d r) a ([1;0;1;0;0;1]^^b) c 1)
    (fun l a b=>crossV l (w *> [1;0]^^c' *> [1;0;1] *> [0;1;0]^^d *> r) a b (3+c) 0)
    (fun a b=>rootV (w *> [1;0]^^c' *> [1;0;1] *> [0;1;0]^^d *> r) a b (3+c) 0) 0.
Proof.
  applys_eq (Pass_id
    (fun l a b=>crossV l (w *> [1;0]^^c' *> [1;0;1] *> [0;1;0]^^d *> r) a b (3+c) 0)
    (fun a b=>rootV (w *> [1;0]^^c' *> [1;0;1] *> [0;1;0]^^d *> r) a b (3+c) 0));
    repeat (apply functional_extensionality; intro);
    unfold crossW,rootW,crossV,rootV,link; st; simpl_rotate; reflexivity.
Qed.

Lemma Pass_clean_tail j n e k: e<=1 -> exists C E, E<=1 /\ C+E=2+k+n*2+e /\
  Pass (fun l a b=>crossV l ([1;0]^^(1+j*2) *> [1;0;1] *> [0;1;0]^^(n*2+e) *> 0inf) a b (3+k) 0)
    (fun a b=>rootV ([1;0]^^(1+j*2) *> [1;0;1] *> [0;1;0]^^(n*2+e) *> 0inf) a b (3+k) 0)
    (fun l a b=>crossW l 0inf a ([1;0;1;0;0;1]^^b) C E)
    (fun a b=>rootW 0inf a ([1;0;1;0;0;1]^^b) C E) (4+j*2+n+e).
Proof.
  intro He; destruct e as [|[|e]]; try lia.
  - destruct n as [|n].
    + exists (2+k),0%nat; split; [lia|]; split; [lia|].
      replace (4+j*2+0+0)%nat with (2+(j*2+2))%nat by lia.
      eapply Pass_trans with (n:=2%nat) (m:=j*2+2); [apply Pass_V_end|].
      eapply Pass_trans with (n:=j*2) (m:=2%nat); [apply (Pass_Zs _ (1+k) 0 j)|].
      apply Pass_Z_empty.
    + exists (3+k+n*2),1%nat; split; [lia|]; split; [lia|].
      replace (4+j*2+Datatypes.S n+0)%nat with (2+(j*2+(2+(1+n))))%nat by lia.
      replace (Datatypes.S n*2+0)%nat with (2+n*2)%nat by lia.
      eapply Pass_trans with (n:=2%nat) (m:=j*2+(2+(1+n))); [apply Pass_V_end|].
      eapply Pass_trans with (n:=j*2) (m:=2+(1+n)); [apply (Pass_Zs _ (1+k) 0 j)|].
      eapply Pass_trans with (n:=2%nat) (m:=1+n); [apply (Pass_Z_back 0inf k (1+n*2))|].
      replace (3+k+n*2)%nat with ((1+n)*2+(1+k))%nat by lia.
      replace (2+(1+n*2))%nat with ((1+n)*2+1)%nat by lia; apply Pass_Ws.
  - exists (3+k+n*2),0%nat; split; [lia|]; split; [lia|].
    replace (4+j*2+n+1)%nat with (2+(j*2+(2+(1+n))))%nat by lia.
    replace (n*2+1)%nat with (1+n*2)%nat by lia.
    eapply Pass_trans with (n:=2%nat) (m:=j*2+(2+(1+n))); [apply Pass_V_end|].
    eapply Pass_trans with (n:=j*2) (m:=2+(1+n)); [apply (Pass_Zs _ (1+k) 0 j)|].
    eapply Pass_trans with (n:=2%nat) (m:=1+n); [apply (Pass_Z_back 0inf k (n*2))|].
    replace (3+k+n*2)%nat with ((1+n)*2+(1+k))%nat by lia.
    replace (2+n*2)%nat with ((1+n)*2+0)%nat by lia.
    apply (Pass_Ws 0inf (1+k) 0 (1+n)).
Qed.

Definition clean_input c d r := [1;0]^^c *> [1;0;1] *> [0;1;0]^^d *> r.

Lemma Pass_clean_link j n z u v c d r k: EraseWord z u v ->
  Pass (fun l a b=>crossV l (clean_input (1+j*2) (n*2) (link z c d r)) a b (3+k) 0)
    (fun a b=>rootV (clean_input (1+j*2) (n*2) (link z c d r)) a b (3+k) 0)
    (fun l a b=>crossV l (clean_input c d r) a b (4+k+n*2+v) 0)
    (fun a b=>rootV (clean_input c d r) a b (4+k+n*2+v) 0) (4+j*2+n+(u+v)*2).
Proof.
  intro HZ; destruct n as [|n].
  - cbn [Nat.mul].
    assert (E:clean_input (1+j*2) 0 (link z c d r)=
      [1;0]^^(2+j*2) *> [1;0;1;0;0;1] *> z *> clean_input c d r).
    1: unfold clean_input,link; st; simpl_rotate; reflexivity.
    rewrite E; rewrite !Nat.add_0_r.
    replace (4+j*2+(u+v)*2)%nat with ((2+j)*2+(u+v)*2)%nat by lia.
    eapply Pass_trans with (n:=(2+j)*2) (m:=(u+v)*2).
    + applys_eq (Pass_erase_pair (z *> clean_input c d r) k j 0); rewrite ?Nat.add_0_r; reflexivity.
    + rewrite !Nat.add_0_r.
      replace (4+k)%nat with (3+(1+k))%nat by lia; apply (EraseWord_pass _ _ _ HZ).
  - unfold clean_input.
    replace (4+j*2+Datatypes.S n+(u+v)*2)%nat
      with (2+(j*2+(2+((1+n)+(0+(u+v)*2)))))%nat by lia.
    replace (4+k+Datatypes.S n*2+v)%nat with (3+((1+n)*2+(1+k))+v)%nat by lia.
    eapply Pass_trans with (n:=2%nat) (m:=j*2+(2+((1+n)+(0+(u+v)*2)))); [apply Pass_V_end|].
    eapply Pass_trans with (n:=j*2) (m:=2+((1+n)+(0+(u+v)*2))); [apply (Pass_Zs _ (1+k) 0 j)|].
    eapply Pass_trans with (n:=2%nat) (m:=(1+n)+(0+(u+v)*2)); [apply (Pass_Z_back _ k (1+n*2))|].
    replace (2+(1+n*2))%nat with ((1+n)*2+1)%nat by lia.
    eapply Pass_trans with (n:=1+n) (m:=0+(u+v)*2); [apply Pass_Ws|].
    eapply Pass_trans with (n:=0%nat) (m:=(u+v)*2); [apply Pass_odd_join|].
    apply (EraseWord_pass _ _ _ HZ).
Qed.

Local Open Scope nat_scope.
Local Open Scope sym_scope.

Lemma reverse_power {A} (w:list A) n: rev (w^^n)=(rev w)^^n.
Proof. induction n; cbn[lpow]; [reflexivity|rewrite rev_app_distr,IHn; apply lpow_shift]. Qed.
Lemma root_plain_terminal a b c e: e<=1 ->
  rootW 0inf a ([1;0;1;0;0;1]^^b) c e -->*
  0inf <* <[0;1]^^(3+a) <* <[0;1;1]^^(b*2) <* <[0;1]^^(1+c+e) {{B}}> 0inf.
Proof.
  intro He; applys_eq (rootW_terminal a _ _ _ c e He (Word_pow _ _ _ b Word_V));
    rewrite reverse_power; st; simpl_rotate; reflexivity.
Qed.
Lemma cross_plain_terminal l a b c e: e<=1 ->
  crossW l 0inf (2+a) ([1;0;1;0;0;1]^^b) c e -->*
  l <* <[0;1]^^a <* <[0;1;1]^^(3+b*2) <* <[0;1]^^(1+c+e) {{B}}> 0inf.
Proof.
  intro He; applys_eq (crossW_terminal l a _ _ _ c e He (Word_pow _ _ _ b Word_V));
    rewrite reverse_power; st; simpl_rotate; reflexivity.
Qed.

Lemma scan_left_zero r d:
  0inf <{{C}} [0;1] *> [0;1;0]^^d *> r -->* scan_left r 1 d.
Proof. unfold scan_left; es. Qed.
Lemma scanW_zero r w c d:
  scanW 0inf r w c d -->* rootW r 0 ([1;0;1;0;0;1]++w) c d.
Proof. unfold scanW,rootW; es. Qed.
Lemma cleanup_start0 r d:
  0inf <{{C}} [0;1] *> [0;1;0]^^(2+d) *> r -->* rootW r 2 [] 1 d.
Proof. follow scan_left_zero; follow scan_left_step; unfold scan_left,rootW; st; simpl_rotate; finish. Qed.
Lemma cleanup_start1 r d:
  0inf <* <[0;1] <{{C}} [0;1] *> [0;1;0]^^(2+d) *> r -->* rootW r 4 [] 1 d.
Proof. follow scan_left_entry; follow scan_left_step; unfold scan_left,rootW; st; simpl_rotate; finish. Qed.
Lemma cleanup_start2 r d:
  0inf <* <[0;1]^^2 <{{C}} [0;1] *> [0;1;0]^^(2+d) *> r -->*
  rootW r 0 [1;0;1;0;0;1] 1 d.
Proof. follow (scan_pair 0inf r 0 d); apply scanW_zero. Qed.
Lemma cleanup_start l a r d:
  l <* <[0;1]^^(3+a) <{{C}} [0;1] *> [0;1;0]^^(2+d) *> r -->*
  crossW l r a [1;0;1;0;0;1] 1 d.
Proof.
  mid (scanW (l <* <[0;1]^^(1+a)) r [] 1 d).
  1: applys_eq (scan_pair (l <* <[0;1]^^(1+a)) r 0 d); st; finish; flia.
  apply scanW_entry.
Qed.

Definition Cleanup (r:side) N X := exists d s c e,
  r=[0;1;0]^^(2+d) *> s /\ e<=1 /\ X=1+c+e /\
  Pass (fun l a b=>crossW l s a ([1;0;1;0;0;1]^^b) 1 d)
    (fun a b=>rootW s a ([1;0;1;0;0;1]^^b) 1 d)
    (fun l a b=>crossW l 0inf a ([1;0;1;0;0;1]^^b) c e)
    (fun a b=>rootW 0inf a ([1;0;1;0;0;1]^^b) c e) N.

Local Open Scope nat_scope.
Inductive CleanLast (N X:nat) : nat->list nat->Prop :=
| Clean0: CleanLast N X 0 [X+5+N*2]
| Clean1: CleanLast N X 1 [X+7+N*2]
| CleanEven s: s<=N -> CleanLast N X (2+s*2) [X;2+s*2;3+(N-s)*2]
| CleanOdd s: s<=N -> CleanLast N X (3+s*2) [X;2+s*2;5+(N-s)*2]
| CleanBorder: CleanLast N X (4+N*2) [X;4+N*2;1]
| CleanOver a: CleanLast N X (5+N*2+a) [X;5+N*2;a].
Local Open Scope sym_scope.

Lemma Cleanup_spec r N X t xs: Cleanup r N X -> CleanLast N X t xs ->
  0inf <* <[0;1]^^t <{{C}} [0;1] *> r -[tm]->+ section xs.
Proof.
  intros [d [r0 [c [e [-> [He [-> [HF HE]]]]]]]] HL.
  apply evstep_progress; [|discriminate].
  destruct HL as [| |s Hs|s Hs| |a].
  - follow cleanup_start0; follow (flow_root _ _ _ _ _ HF 2 0).
    unfold section; cbn[section_side]; applys_eq (root_plain_terminal (N*2+2) 0 c e He); st; simpl_rotate; flia.
  - follow cleanup_start1; follow (flow_root _ _ _ _ _ HF 4 0).
    unfold section; cbn[section_side]; applys_eq (root_plain_terminal (N*2+4) 0 c e He); st; simpl_rotate; flia.
  - destruct s as [|s].
    + follow cleanup_start2; follow (flow_root _ _ _ _ _ HF 0 1).
      unfold section; cbn[section_side negb]; applys_eq (root_plain_terminal (N*2+0) 1 c e He); flia.
    + mid (crossW 0inf r0 (1+s*2) [1;0;1;0;0;1] 1 d).
      1: applys_eq (cleanup_start 0inf (1+s*2) r0 d); flia.
      mid (rootW 0inf ((N-s-1)*2) ([1;0;1;0;0;1]^^(2+s)) c e).
      1: applys_eq (flow_border _ _ _ _ _ HF s (N-s-1) 1); flia.
      unfold section; cbn[section_side negb]; applys_eq (root_plain_terminal ((N-s-1)*2) (2+s) c e He); flia.
  - destruct s as [|s].
    + follow (cleanup_start 0inf 0 r0 d); follow crossW_zero.
      follow (flow_root _ _ _ _ _ HF 2 1).
      unfold section; cbn[section_side negb]; applys_eq (root_plain_terminal (N*2+2) 1 c e He); flia.
    + mid (crossW 0inf r0 (2+s*2) [1;0;1;0;0;1] 1 d).
      1: applys_eq (cleanup_start 0inf (2+s*2) r0 d); flia.
      mid (rootW 0inf (2+(N-s-1)*2) ([1;0;1;0;0;1]^^(2+s)) c e).
      1: applys_eq (HE s (N-s-1) 1%nat); flia.
      unfold section; cbn[section_side negb]; applys_eq (root_plain_terminal (2+(N-s-1)*2) (2+s) c e He); flia.
  - mid (crossW 0inf r0 (1+N*2) [1;0;1;0;0;1] 1 d).
    1: applys_eq (cleanup_start 0inf (1+N*2) r0 d); flia.
    mid (crossW 0inf 0inf 1 ([1;0;1;0;0;1]^^(1+N)) c e).
    1: applys_eq (flow_cross _ _ _ _ _ HF 0inf 1 1); flia.
    unfold section; cbn[section_side negb]; applys_eq (crossW_last_one (1+N) c e He); flia.
  - mid (crossW 0inf r0 (2+N*2+a) [1;0;1;0;0;1] 1 d).
    1: applys_eq (cleanup_start 0inf (2+N*2+a) r0 d); flia.
    mid (crossW 0inf 0inf (2+a) ([1;0;1;0;0;1]^^(1+N)) c e).
    1: applys_eq (flow_cross _ _ _ _ _ HF 0inf (2+a) 1); flia.
    unfold section; cbn[section_side negb]; applys_eq (cross_plain_terminal 0inf a (1+N) c e He); flia.
Qed.

Local Open Scope nat_scope.
Local Open Scope sym_scope.

Lemma RRoute_clean c d r n w C e R: RRoute c d r n w C e R -> R=0inf -> e<=1 ->
  exists u v, EraseWord w u v /\ forall k, exists N C' E,
    E<=1 /\ N+n=(u+v)*2+3+C+e /\ C'+E=2+k+v+n*2+e /\
    Pass (fun l a b=>crossV l (clean_input c d r) a b (3+k) 0)
      (fun a b=>rootV (clean_input c d r) a b (3+k) 0)
      (fun l a b=>crossW l 0inf a ([1;0;1;0;0;1]^^b) C' E)
      (fun a b=>rootW 0inf a ([1;0;1;0;0;1]^^b) C' E) N.
Proof.
  intro H; induction H as [j n e r|j n z x y c' d r m w C e R HZ HR IH]; intros ER He.
  - subst r; exists 0%nat,0%nat; split; [constructor|]; intro k.
    destruct (Pass_clean_tail j n e k He) as [C' [E [HE [HC HP]]]].
    exists (4+j*2+n+e),C',E; split; [exact HE|]; split; [lia|]; split; [lia|exact HP].
  - destruct (IH ER He) as [u [v [HW IHk]]].
    exists (1+(j+n)+x+u),(1+y+v); split.
    + applys_eq (Erase_pair (j+n) 0 _ _ _ (EraseWord_app _ _ _ _ _ _ HZ HW));
        cbn; repeat rewrite <-app_assoc; flia.
    + intro k; destruct (IHk (1+k+n*2+y)) as [N [C0 [E [HE [HN [HC HP]]]]]].
      exists (4+j*2+n+(x+y)*2+N),C0,E; split; [exact HE|].
      split; [lia|]; split; [lia|].
      eapply Pass_trans with (n:=4+j*2+n+(x+y)*2) (m:=N); [apply Pass_clean_link,HZ|].
      replace (4+k+n*2+y) with (3+(1+k+n*2+y)) by lia; exact HP.
Qed.

Lemma RRoute_cleanup b z i j c d r n w C e:
  EraseWord z i j -> RRoute c d r n w C e 0inf -> e<=1 ->
  exists u v N X, EraseWord w u v /\
    N+n=b+(i+j+u+v)*2+3+C+e /\ X=4+b*2+j+v+n*2+e /\
    Cleanup ([0;1;0]^^(3+b*2) *> link z c d r) N X.
Proof.
  intros HZ HR He; destruct (RRoute_clean _ _ _ _ _ _ _ _ HR eq_refl He)
    as [u [v [HW HK]]].
  destruct (HK (1+b*2+j)) as [N [c' [e' [He' [HN [HX HP]]]]]].
  exists u,v,(b+(i+j)*2+N),(1+c'+e'); split; [exact HW|].
  split; [lia|]; split; [lia|].
  exists (1+b*2),(link z c d r),c',e'; split; [reflexivity|].
  split; [exact He'|]; split; [reflexivity|].
  replace (b+(i+j)*2+N) with (b+(0+((i+j)*2+N))) by lia.
  replace (1+b*2) with (b*2+1) by lia.
  eapply Pass_trans with (n:=b) (m:=0+((i+j)*2+N)); [apply Pass_Ws|].
  eapply Pass_trans with (n:=0%nat) (m:=(i+j)*2+N); [apply Pass_odd_join|].
  eapply Pass_trans with (n:=(i+j)*2) (m:=N); [apply (EraseWord_pass _ _ _ HZ)|].
  replace (3+(b*2+1)+j) with (3+(1+b*2+j)) by lia; exact HP.
Qed.

Lemma EraseWord_size w u v: EraseWord w u v -> List.length w=u*4+v*6.
Proof.
  intro H; induction H; repeat rewrite List.length_app;
    repeat rewrite lpow_length; cbn[List.length]; unfold Sym in *; lia.
Qed.

Lemma Cleanup_triple g b d e: e<=1 ->
  Cleanup ([0;1;0]^^(3+b*2) *> link ([1;0;1;0;0;1]^^g) (1+g*2) (d*2+e) 0inf)
    (4+b+g*4+d+e) (4+b*2+g+d*2+e).
Proof.
  intro He; destruct (RRoute_cleanup b ([1;0;1;0;0;1]^^g) 0 g (1+g*2) (d*2+e)
    0inf d [] (1+(g+d)*2) e) as [u [v [N [X [HW [HN [HX HC]]]]]]].
  - applys_eq (Erase_V g [] 0 0 Erase_nil); rewrite ?app_nil_r; flia.
  - apply RRoute_done.
  - exact He.
  - assert (u=0%nat /\ v=0%nat) as [-> ->] by (pose proof (EraseWord_size _ _ _ HW); cbn in *; lia).
    applys_eq HC; flia.
Qed.

Lemma cleanup_triple_section g b d e t xs:
  P (2+g*2+(d*2+e)) -> e<=1 ->
  CleanLast (4+b+g*4+d+e) (4+b*2+g+d*2+e) t xs ->
  section [(2+g*2+(d*2+e))+(2+g*2);3+b*2;t] -[tm]->+ section xs.
Proof.
  intros HP He HL; unfold section at 1; cbn[section_side negb].
  eapply evstep_progress_trans.
  - follow (fun l=>return_even l g (d*2+e) HP); follow pass_011.
    unfold link; st; simpl_rotate; finish.
  - applys_eq (Cleanup_spec _ _ _ _ _ (Cleanup_triple g b d e He) HL);
      unfold link; st; simpl_rotate; reflexivity.
Qed.

Lemma RCounter_cleanup l r n w C e a b: RCounter r n w C e -> a<=n -> e<=1 ->
  exists u v N X r', EraseWord w u v /\
    N+n=b+a*3+(u+v)*2+3+C+e /\ X+a=4+b*2+v+n*2+e /\ Cleanup r' N X /\
    l <* <[0;1;1]^^(3+b*2) <* <[0;1]^^(2+a*2) <{{C}} [0;1] *> r -->*
      l <{{C}} [0;1] *> r'.
Proof.
  intros [d [s [-> HR]]] Ha He.
  destruct (RRoute_scan _ _ _ _ _ _ _ _ HR a
    (l <* <[0;1;1]^^(3+b*2)) [] [] [] Ha Word_nil)
    as [c' [d' [s' [u [z [i [j [HZ [EW [HU HS]]]]]]]]]].
  destruct (RRoute_cleanup b ([1;0;1;0;0;1]^^a++u) i (a+j) c' d' s' (n-a) z C e
    (Erase_V a _ _ _ HU) HZ He) as [x [y [N [X [HW [HN [HX HC]]]]]]].
  exists (i+x),(j+y),N,X,([0;1;0]^^(3+b*2) *> link ([1;0;1;0;0;1]^^a++u) c' d' s').
  split; [rewrite EW; apply EraseWord_app; assumption|].
  split; [lia|]; split; [lia|]; split; [exact HC|].
  mid (scanW (l <* <[0;1;1]^^(3+b*2) <* <[0;1]^^(a*2)) s [] 1 d).
  1: applys_eq (scan_pair (l <* <[0;1;1]^^(3+b*2) <* <[0;1]^^(a*2)) s 0 d); st; finish; flia.
  follow HS; unfold scanW; follow pass_011; unfold link; finish.
Qed.

Local Open Scope nat_scope.
Lemma CleanLast_total N X t: exists xs, CleanLast N X t xs.
Proof.
  destruct t as [|[|t]].
  - eexists; apply Clean0.
  - eexists; apply Clean1.
  - destruct (parity t) as [s [-> | ->]].
    + destruct (Nat.le_gt_cases s N).
      * eexists; applys_eq (CleanEven N X s H); flia.
      * destruct (Nat.eq_dec s (N+1)).
        -- eexists; applys_eq (CleanBorder N X); flia.
        -- eexists; applys_eq (CleanOver N X (2+s*2-(5+N*2))); flia.
    + destruct (Nat.le_gt_cases s N).
      * eexists; applys_eq (CleanOdd N X s H); flia.
      * eexists; applys_eq (CleanOver N X (3+s*2-(5+N*2))); flia.
Qed.
Local Open Scope sym_scope.
Lemma Cleanup_total r N X t: Cleanup r N X -> exists xs,
  0inf <* <[0;1]^^t <{{C}} [0;1] *> r -[tm]->+ section xs.
Proof. intro H; destruct (CleanLast_total N X t) as [xs HX]; exists xs; apply (Cleanup_spec _ _ _ _ _ H HX). Qed.

Local Close Scope nat_scope.

(* All odd cleanup fronts and exact counts of restored columns. *)
Local Open Scope nat_scope.
Local Open Scope sym_scope.


Lemma cleanup_one_entry l a r:
  l <* <[0;1]^^(1+a) <{{C}} [0;1;0;1;0;0;1;0;0;1] *> r -->*
  crossV l r a 0 2 0.
Proof. unfold crossV; es. Qed.
Lemma cleanup_one_zero r:
  0inf <{{C}} [0;1;0;1;0;0;1;0;0;1] *> r -->* rootV r 0 0 2 0.
Proof. unfold rootV; es. Qed.

Lemma crossV_low l r a b e:
  crossV l r (4+a) b 2 (1+e) -->* crossV l r a (2+b) 3 e.
Proof. unfold crossV; es. Qed.
Lemma rootV_low r a b e:
  rootV r a b 2 (1+e) -->* rootV r (4+a) b 3 e.
Proof. unfold rootV; es. Qed.
Lemma crossV_low_one r b e:
  crossV 0inf r 1 b 2 (1+e) -->* rootV r 2 (1+b) 3 e.
Proof. unfold crossV,rootV; es. Qed.
Lemma crossV_low_three r b e:
  crossV 0inf r 3 b 2 (1+e) -->* rootV r 0 (2+b) 3 e.
Proof. unfold crossV,rootV; es. Qed.
Lemma crossV_low_two r b e:
  crossV 0inf r 2 b 2 (1+e) -->* rootV r 4 (1+b) 3 e.
Proof. unfold crossV,rootV; es. Qed.

Lemma crossVend_low l r a b e:
  crossV l ([1;0]^^(1+e) *> r) (4+a) b 2 0 -->* crossZ l r a (2+b) 3 e.
Proof. unfold crossV,crossZ; es. Qed.
Lemma rootVend_low r a b e:
  rootV ([1;0]^^(1+e) *> r) a b 2 0 -->* rootZ r (4+a) b 3 e.
Proof. unfold rootV,rootZ; es. Qed.
Lemma crossVend_low_one r b e:
  crossV 0inf ([1;0]^^(1+e) *> r) 1 b 2 0 -->* rootZ r 2 (1+b) 3 e.
Proof. unfold crossV,rootZ; es. Qed.
Lemma crossVend_low_three r b e:
  crossV 0inf ([1;0]^^(1+e) *> r) 3 b 2 0 -->* rootZ r 0 (2+b) 3 e.
Proof. unfold crossV,rootZ; es. Qed.
Lemma crossVend_low_two r b e:
  crossV 0inf ([1;0]^^(1+e) *> r) 2 b 2 0 -->* rootZ r 4 (1+b) 3 e.
Proof. unfold crossV,rootZ; es. Qed.

Lemma crossZ_empty_low l a b:
  crossZ l ([1;0;1] *> 0inf) (4+a) b 3 0 -->*
  crossW l 0inf a ([1;0;1;0;0;1]^^(2+b)) 1 0.
Proof. unfold crossZ,crossW; es. Qed.
Lemma rootZ_empty_low a b:
  rootZ ([1;0;1] *> 0inf) a b 3 0 -->*
  rootW 0inf (4+a) ([1;0;1;0;0;1]^^b) 1 0.
Proof. unfold rootZ,rootW; es. Qed.
Lemma crossZ_empty_low_one b:
  crossZ 0inf ([1;0;1] *> 0inf) 1 b 3 0 -->*
  rootW 0inf 2 ([1;0;1;0;0;1]^^(1+b)) 1 0.
Proof. unfold crossZ,rootW; es. Qed.
Lemma crossZ_empty_low_three b:
  crossZ 0inf ([1;0;1] *> 0inf) 3 b 3 0 -->*
  rootW 0inf 0 ([1;0;1;0;0;1]^^(2+b)) 1 0.
Proof. unfold crossZ,rootW; es. Qed.
Lemma crossZ_empty_low_two b:
  crossZ 0inf ([1;0;1] *> 0inf) 2 b 3 0 -->*
  rootW 0inf 4 ([1;0;1;0;0;1]^^(1+b)) 1 0.
Proof. unfold crossZ,rootW; es. Qed.


Lemma Pass_V_low r e:
  Pass (fun l a b=>crossV l r a b 2 (1+e)) (fun a b=>rootV r a b 2 (1+e))
    (fun l a b=>crossV l r a b 3 e) (fun a b=>rootV r a b 3 e) 2.
Proof.
  constructor.
  - constructor; intros; cbn beta; try apply crossV_low; try apply rootV_low.
    destruct s as [|[|s]]; try lia.
    + assert (v=1%nat) as -> by lia; apply crossV_low_one.
    + assert (v=0%nat) as -> by lia; apply crossV_low_three.
  - intros s v b E; destruct s as [|[|s]]; try lia.
    + assert (v=1%nat) as -> by lia; apply crossV_low_two.
    + assert (v=0%nat) as -> by lia; follow crossV_low; apply crossV_zero.
Qed.
Lemma Pass_Vend_low r e:
  Pass (fun l a b=>crossV l ([1;0]^^(1+e) *> r) a b 2 0)
    (fun a b=>rootV ([1;0]^^(1+e) *> r) a b 2 0)
    (fun l a b=>crossZ l r a b 3 e) (fun a b=>rootZ r a b 3 e) 2.
Proof.
  constructor.
  - constructor; intros; cbn beta; try apply crossVend_low; try apply rootVend_low.
    destruct s as [|[|s]]; try lia.
    + assert (v=1%nat) as -> by lia; apply crossVend_low_one.
    + assert (v=0%nat) as -> by lia; apply crossVend_low_three.
  - intros s v b E; destruct s as [|[|s]]; try lia.
    + assert (v=1%nat) as -> by lia; apply crossVend_low_two.
    + assert (v=0%nat) as -> by lia; follow crossVend_low; apply crossZ_zero.
Qed.
Lemma Pass_Z_empty_low:
  Pass (fun l a b=>crossZ l ([1;0;1] *> 0inf) a b 3 0)
    (fun a b=>rootZ ([1;0;1] *> 0inf) a b 3 0)
    (fun l a b=>crossW l 0inf a ([1;0;1;0;0;1]^^b) 1 0)
    (fun a b=>rootW 0inf a ([1;0;1;0;0;1]^^b) 1 0) 2.
Proof.
  constructor.
  - constructor; intros; cbn beta; try apply crossZ_empty_low; try apply rootZ_empty_low.
    destruct s as [|[|s]]; try lia.
    + assert (v=1%nat) as -> by lia; apply crossZ_empty_low_one.
    + assert (v=0%nat) as -> by lia; apply crossZ_empty_low_three.
  - intros s v b E; destruct s as [|[|s]]; try lia.
    + assert (v=1%nat) as -> by lia; apply crossZ_empty_low_two.
    + assert (v=0%nat) as -> by lia; follow crossZ_empty_low; apply crossW_zero.
Qed.
Lemma Pass_Z_back_low r d:
  Pass (fun l a b=>crossZ l ([1;0;1] *> [0;1;0]^^(1+d) *> r) a b 3 0)
    (fun a b=>rootZ ([1;0;1] *> [0;1;0]^^(1+d) *> r) a b 3 0)
    (fun l a b=>crossW l r a ([1;0;1;0;0;1]^^b) 0 (2+d))
    (fun a b=>rootW r a ([1;0;1;0;0;1]^^b) 0 (2+d)) 2.
Proof.
  applys_eq (Pass_Z ([1;0] *> [0;1;0]^^d *> r) 0 0);
    repeat (apply functional_extensionality; intro);
    unfold crossZ,rootZ,crossW,rootW; st; simpl_rotate; reflexivity.
Qed.

Lemma Pass_clean_tail_low j n e: e<=1 -> exists C E, E<=1 /\ C+E=1+n*2+e /\
  Pass (fun l a b=>crossV l ([1;0]^^(1+j*2) *> [1;0;1] *> [0;1;0]^^(n*2+e) *> 0inf) a b 2 0)
    (fun a b=>rootV ([1;0]^^(1+j*2) *> [1;0;1] *> [0;1;0]^^(n*2+e) *> 0inf) a b 2 0)
    (fun l a b=>crossW l 0inf a ([1;0;1;0;0;1]^^b) C E)
    (fun a b=>rootW 0inf a ([1;0;1;0;0;1]^^b) C E) (4+j*2+n+e).
Proof.
  intro He; destruct e as [|[|e]]; try lia.
  - destruct n as [|n].
    + exists 1%nat,0%nat; split; [lia|]; split; [lia|].
      replace (4+j*2+0+0)%nat with (2+(j*2+2))%nat by lia.
      eapply Pass_trans with (n:=2%nat) (m:=j*2+2); [apply Pass_Vend_low|].
      eapply Pass_trans with (n:=j*2) (m:=2%nat); [apply (Pass_Zs _ 0 0 j)|].
      apply Pass_Z_empty_low.
    + exists (2+n*2),1%nat; split; [lia|]; split; [lia|].
      replace (4+j*2+Datatypes.S n+0)%nat with (2+(j*2+(2+(1+n))))%nat by lia.
      replace (Datatypes.S n*2+0)%nat with (2+n*2)%nat by lia.
      eapply Pass_trans with (n:=2%nat) (m:=j*2+(2+(1+n))); [apply Pass_Vend_low|].
      eapply Pass_trans with (n:=j*2) (m:=2+(1+n)); [apply (Pass_Zs _ 0 0 j)|].
      eapply Pass_trans with (n:=2%nat) (m:=1+n); [apply (Pass_Z_back_low 0inf (1+n*2))|].
      replace (2+n*2) with ((1+n)*2+0) by lia.
      replace (2+(1+n*2)) with ((1+n)*2+1) by lia; apply Pass_Ws.
  - exists (2+n*2),0%nat; split; [lia|]; split; [lia|].
    replace (4+j*2+n+1)%nat with (2+(j*2+(2+(1+n))))%nat by lia.
    replace (n*2+1)%nat with (1+n*2)%nat by lia.
    eapply Pass_trans with (n:=2%nat) (m:=j*2+(2+(1+n))); [apply Pass_Vend_low|].
    eapply Pass_trans with (n:=j*2) (m:=2+(1+n)); [apply (Pass_Zs _ 0 0 j)|].
    eapply Pass_trans with (n:=2%nat) (m:=1+n); [apply (Pass_Z_back_low 0inf (n*2))|].
    replace (2+n*2) with ((1+n)*2+0) by lia; apply Pass_Ws.
Qed.

Definition OneCleanup r N X := exists c e, e<=1 /\ X=1+c+e /\
  Pass (fun l a b=>crossV l r a b 2 0) (fun a b=>rootV r a b 2 0)
    (fun l a b=>crossW l 0inf a ([1;0;1;0;0;1]^^b) c e)
    (fun a b=>rootW 0inf a ([1;0;1;0;0;1]^^b) c e) (1+N).

Lemma OneCleanup_spec r N X t xs: OneCleanup r N X -> CleanLast N X t xs ->
  0inf <* <[0;1]^^t <{{C}} [0;1;0;1;0;0;1;0;0;1] *> r -[tm]->+ section xs.
Proof.
  intros [c [e [He [-> [HF HE]]]]] HL.
  apply evstep_progress; [|discriminate].
  destruct HL as [| |s Hs|s Hs| |a].
  - follow cleanup_one_zero; follow (flow_root _ _ _ _ _ HF 0 0).
    unfold section; cbn[section_side]; applys_eq (root_plain_terminal ((1+N)*2) 0 c e He); st; simpl_rotate; flia.
  - follow (cleanup_one_entry 0inf 0); follow crossV_zero; follow (flow_root _ _ _ _ _ HF 2 0).
    unfold section; cbn[section_side]; applys_eq (root_plain_terminal ((1+N)*2+2) 0 c e He); st; simpl_rotate; flia.
  - follow (cleanup_one_entry 0inf (1+s*2)).
    follow (flow_border _ _ _ _ _ HF s (N-s) 0 (ltac:(lia))).
    unfold section; cbn[section_side negb]; applys_eq (root_plain_terminal ((N-s)*2) (1+s) c e He); flia.
  - follow (cleanup_one_entry 0inf (2+s*2)).
    follow (HE s (N-s) 0%nat (ltac:(lia))).
    unfold section; cbn[section_side negb]; applys_eq (root_plain_terminal (2+(N-s)*2) (1+s) c e He); flia.
  - follow (cleanup_one_entry 0inf (3+N*2)).
    mid (crossW 0inf 0inf 1 ([1;0;1;0;0;1]^^(1+N)) c e).
    1: applys_eq (flow_cross _ _ _ _ _ HF 0inf 1 0); flia.
    unfold section; cbn[section_side negb]; applys_eq (crossW_last_one (1+N) c e He); flia.
  - mid (crossV 0inf r (4+N*2+a) 0 2 0).
    1: applys_eq (cleanup_one_entry 0inf (4+N*2+a) r); flia.
    mid (crossW 0inf 0inf (2+a) ([1;0;1;0;0;1]^^(1+N)) c e).
    1: applys_eq (flow_cross _ _ _ _ _ HF 0inf (2+a) 0); flia.
    unfold section; cbn[section_side negb]; applys_eq (cross_plain_terminal 0inf a (1+N) c e He); flia.
Qed.

Lemma OneCleanup_triple g d e: e<=1 ->
  OneCleanup ([1;0;1;0;0;1]^^g *> [1;0]^^(1+g*2) *> [1;0;1] *> [0;1;0]^^(d*2+e) *> 0inf)
    (3+g*4+d+e) (2+g+d*2+e).
Proof.
  intro He; destruct g as [|g].
  - destruct (Pass_clean_tail_low 0 d e He) as [C [E [HE [HC HP]]]].
    exists C,E; split; [exact HE|]; split; [lia|].
    applys_eq HP; flia.
  - destruct (Pass_clean_tail (1+g) d e g He) as [C [E [HE [HC HP]]]].
    exists C,E; split; [exact HE|]; split; [lia|].
    change (Pass
      (fun l a b=>crossV l ([1;0]^^(1+(1+g)*2) *> [1;0;1] *> [0;1;0]^^(d*2+e) *> 0inf) a b 2 (1+g))
      (fun a b=>rootV ([1;0]^^(1+(1+g)*2) *> [1;0;1] *> [0;1;0]^^(d*2+e) *> 0inf) a b 2 (1+g))
      (fun l a b=>crossW l 0inf a ([1;0;1;0;0;1]^^b) C E)
      (fun a b=>rootW 0inf a ([1;0;1;0;0;1]^^b) C E) (1+(3+(1+g)*4+d+e))).
    replace (1+(3+(1+g)*4+d+e)) with (2+(g*2+(4+(1+g)*2+d+e))) by lia.
    eapply Pass_trans with (n:=2%nat) (m:=g*2+(4+(1+g)*2+d+e)); [apply Pass_V_low|].
    eapply Pass_trans with (n:=g*2) (m:=4+(1+g)*2+d+e); [apply (Pass_Vs _ 0 0 g)|].
    exact HP.
Qed.

Lemma cleanup_triple_one_section g d e t xs:
  P (2+g*2+(d*2+e)) -> e<=1 ->
  CleanLast (3+g*4+d+e) (2+g+d*2+e) t xs ->
  section [(2+g*2+(d*2+e))+(2+g*2);1%nat;t] -[tm]->+ section xs.
Proof.
  intros HP He HL; unfold section at 1; cbn[section_side negb].
  eapply evstep_progress_trans.
  - follow (fun l=>return_even l g (d*2+e) HP); follow pass_011.
    st; simpl_rotate; finish.
  - applys_eq (OneCleanup_spec _ _ _ _ _ (OneCleanup_triple g d e He) HL);
      st; simpl_rotate; reflexivity.
Qed.

Lemma cleanup_odd_triple_section g b d e t xs:
  P (2+g*2+(d*2+e)) -> e<=1 ->
  CleanLast (3+b+g*4+d+e) (2+b*2+g+d*2+e) t xs ->
  section [(2+g*2+(d*2+e))+(2+g*2);1+b*2;t] -[tm]->+ section xs.
Proof.
  intros HP He HL; destruct b.
  - exact (cleanup_triple_one_section g d e t xs HP He HL).
  - exact (cleanup_triple_section g b d e t xs HP He HL).
Qed.

Lemma OneCleanup_total r N X t: OneCleanup r N X -> exists xs,
  0inf <* <[0;1]^^t <{{C}} [0;1;0;1;0;0;1;0;0;1] *> r -[tm]->+ section xs.
Proof.
  intro H; destruct (CleanLast_total N X t) as [xs HL].
  exists xs; apply (OneCleanup_spec _ _ _ _ _ H HL).
Qed.


Fixpoint count00 (p:Sym) (w:list Sym) : nat :=
  match w with []=>0%nat | x::w=>
    (match p,x with S0,S0=>1%nat | _,_=>0%nat end)+count00 x w end.
Lemma count00_U n w k: (forall p, count00 p w=k) ->
  forall p, count00 p ([1;0]^^n++w)=k.
Proof. intro H; induction n; intros []; cbn[lpow app count00 Nat.add]; auto. Qed.
Lemma count00_V n w k: (forall p, count00 p w=k) ->
  forall p, count00 p ([1;0;1;0;0;1]^^n++w)=n+k.
Proof. intro H; induction n; intros []; cbn[lpow app count00 Nat.add]; auto; rewrite IHn; lia. Qed.
Lemma EraseWord_count00 w u v: EraseWord w u v -> forall p, count00 p w=v.
Proof.
  intro H; induction H; intros p; [reflexivity|apply count00_V; exact IHEraseWord|].
  apply count00_U; intros; apply count00_V; exact IHEraseWord.
Qed.
Lemma EraseWord_unique w u v u' v':
  EraseWord w u v -> EraseWord w u' v' -> u=u' /\ v=v'.
Proof.
  intros H K; pose proof (EraseWord_count00 _ _ _ H S1);
    pose proof (EraseWord_count00 _ _ _ K S1);
    pose proof (EraseWord_size _ _ _ H); pose proof (EraseWord_size _ _ _ K); lia.
Qed.

Fixpoint column_U (cs:list (nat*nat)) :=
  match cs with []=>0%nat | (a,b)::cs=>1+b+column_U cs end.
Fixpoint column_V (cs:list (nat*nat)) :=
  match cs with []=>0%nat | (a,b)::cs=>1+a+column_V cs end.
Lemma column_word_erase cs: EraseWord (column_word cs) (column_U cs) (column_V cs).
Proof.
  induction cs as [|[a b] cs IH]; cbn[column_word column_U column_V]; [constructor|].
  applys_eq (EraseWord_app _ _ _ _ _ _ IH (Erase_pair b a [] 0 0 Erase_nil));
    rewrite ?app_nil_r; flia.
Qed.
Lemma ColumnRun_balance n cs m: ColumnRun n cs m -> m+column_V cs=n+column_U cs.
Proof. intro H; induction H; cbn[column_U column_V] in *; lia. Qed.

Lemma RCounter_columns_cleanup l r n w C e cs m a b u v:
  RCounter r n w C e -> EraseWord w u v -> ColumnRun n cs m -> a<=m -> e<=1 ->
  exists N X r', N+m=b+a*3+(column_U cs+column_V cs+u+v)*2+3+C+e /\
    X+a=4+b*2+column_V cs+v+m*2+e /\ Cleanup r' N X /\
    column_side (l <* <[0;1;1]^^(3+b*2) <* <[0;1]^^(2+a*2)) cs
      <{{C}} [0;1] *> r -[tm]->* l <{{C}} [0;1] *> r'.
Proof.
  intros HR HW HS Ha He.
  destruct (RCounter_columns _ _ _ HS
    (l <* <[0;1;1]^^(3+b*2) <* <[0;1]^^(2+a*2)) r w C e HR)
    as [r0 [H0 T0]].
  destruct (RCounter_cleanup l r0 m _ C e a b H0 Ha He)
    as [i [j [N [X [r1 [H1 [HN [HX [HC T1]]]]]]]]].
  destruct (EraseWord_unique _ _ _ _ _ H1
    (EraseWord_app _ _ _ _ _ _ (column_word_erase cs) HW)) as [-> ->].
  exists N,X,r1; split; [lia|]; split; [lia|]; split; [exact HC|].
  eapply evstep_trans; eauto.
Qed.

Lemma RCounter_columns_cleanup_section r n w C e cs m a b u v t:
  RCounter r n w C e -> EraseWord w u v -> ColumnRun n cs m -> a<=m -> e<=1 ->
  exists N X xs, N+m=b+a*3+(column_U cs+column_V cs+u+v)*2+3+C+e /\
    X+a=4+b*2+column_V cs+v+m*2+e /\ CleanLast N X t xs /\
    column_side (0inf <* <[0;1]^^t <* <[0;1;1]^^(3+b*2) <* <[0;1]^^(2+a*2)) cs
      <{{C}} [0;1] *> r -[tm]->+ section xs.
Proof.
  intros HR HW HS Ha He.
  destruct (RCounter_columns_cleanup (0inf <* <[0;1]^^t) r n w C e cs m a b u v HR HW HS Ha He)
    as [N [X [r' [HN [HX [HC HT]]]]]].
  destruct (CleanLast_total N X t) as [xs HL].
  exists N,X,xs; split; [exact HN|]; split; [exact HX|]; split; [exact HL|].
  eapply evstep_progress_trans; [exact HT|apply (Cleanup_spec _ _ _ _ _ HC HL)].
Qed.


Lemma Pass_erase_pair_low r j k:
  Pass (fun l a b=>crossV l ([1;0]^^(2+j*2) *> [1;0;1;0;0;1]^^(1+k) *> r) a b 2 0)
    (fun a b=>rootV ([1;0]^^(2+j*2) *> [1;0;1;0;0;1]^^(1+k) *> r) a b 2 0)
    (fun l a b=>crossV l r a b (3+k) 0)
    (fun a b=>rootV r a b (3+k) 0) ((2+j+k)*2).
Proof.
  replace ((2+j+k)*2)%nat with (2+(j*2+(2+k*2)))%nat by lia.
  eapply Pass_trans with (n:=2%nat) (m:=j*2+(2+k*2)); [apply Pass_Vend_low|].
  eapply Pass_trans with (n:=j*2) (m:=2+k*2); [apply (Pass_Zs _ 0 1 j)|].
  eapply Pass_trans with (n:=2%nat) (m:=k*2); [apply Pass_Z_to_V|].
  apply (Pass_Vs r 0 0 k).
Qed.

Lemma Pass_Vs_low r e n:
  Pass (fun l a b=>crossV l r a b 2 (e+n)) (fun a b=>rootV r a b 2 (e+n))
    (fun l a b=>crossV l r a b (2+n) e) (fun a b=>rootV r a b (2+n) e) (n*2).
Proof.
  destruct n; [rewrite !Nat.add_0_r; apply Pass_id|].
  rewrite Nat.add_succ_r; eapply Pass_trans with (n:=2%nat) (m:=n*2).
  - apply Pass_V_low.
  - exact (Pass_Vs r 0 e n).
Qed.

Lemma EraseWord_pass_low w u v: EraseWord w u v -> forall r,
  Pass (fun l a b=>crossV l (w *> r) a b 2 0) (fun a b=>rootV (w *> r) a b 2 0)
    (fun l a b=>crossV l r a b (2+v) 0) (fun a b=>rootV r a b (2+v) 0) ((u+v)*2).
Proof.
  intro H; induction H as [|n w u v H IH|j k w u v H IH]; intro r.
  - apply Pass_id.
  - destruct n as [|n]; [exact (IH r)|].
    rewrite Str_app_assoc.
    replace ((u+(Datatypes.S n+v))*2)%nat with ((1+n)*2+(u+v)*2)%nat by lia.
    replace (2+(Datatypes.S n+v))%nat with (3+n+v)%nat by lia.
    eapply Pass_trans with (n:=(1+n)*2) (m:=(u+v)*2).
    + apply (Pass_Vs_low (w *> r) 0 (1+n)).
    + exact (EraseWord_pass _ _ _ H r n).
  - rewrite !Str_app_assoc.
    replace ((1+j+u+(1+k+v))*2)%nat with ((2+j+k)*2+(u+v)*2)%nat by lia.
    replace (2+(1+k+v))%nat with (3+k+v)%nat by lia.
    eapply Pass_trans with (n:=(2+j+k)*2) (m:=(u+v)*2).
    + apply Pass_erase_pair_low.
    + exact (EraseWord_pass _ _ _ H r k).
Qed.

Lemma Pass_clean_link_low j n z u v c d r: EraseWord z u v ->
  Pass (fun l a b=>crossV l (clean_input (1+j*2) (n*2) (link z c d r)) a b 2 0)
    (fun a b=>rootV (clean_input (1+j*2) (n*2) (link z c d r)) a b 2 0)
    (fun l a b=>crossV l (clean_input c d r) a b (3+n*2+v) 0)
    (fun a b=>rootV (clean_input c d r) a b (3+n*2+v) 0) (4+j*2+n+(u+v)*2).
Proof.
  intro HZ; destruct n as [|n].
  - cbn [Nat.mul].
    assert (E:clean_input (1+j*2) 0 (link z c d r)=
      [1;0]^^(2+j*2) *> [1;0;1;0;0;1] *> z *> clean_input c d r).
    1: unfold clean_input,link; st; simpl_rotate; reflexivity.
    rewrite E; rewrite !Nat.add_0_r.
    replace (4+j*2+(u+v)*2)%nat with ((2+j)*2+(u+v)*2)%nat by lia.
    eapply Pass_trans with (n:=(2+j)*2) (m:=(u+v)*2).
    + applys_eq (Pass_erase_pair_low (z *> clean_input c d r) j 0); rewrite ?Nat.add_0_r; reflexivity.
    + apply (EraseWord_pass _ _ _ HZ _ 0).
  - unfold clean_input.
    replace (4+j*2+Datatypes.S n+(u+v)*2)%nat
      with (2+(j*2+(2+((1+n)+(0+(u+v)*2)))))%nat by lia.
    replace (3+Datatypes.S n*2+v)%nat with (3+((1+n)*2+0)+v)%nat by lia.
    eapply Pass_trans with (n:=2%nat) (m:=j*2+(2+((1+n)+(0+(u+v)*2)))); [apply Pass_Vend_low|].
    eapply Pass_trans with (n:=j*2) (m:=2+((1+n)+(0+(u+v)*2))); [apply (Pass_Zs _ 0 0 j)|].
    eapply Pass_trans with (n:=2%nat) (m:=(1+n)+(0+(u+v)*2)); [apply (Pass_Z_back_low _ (1+n*2))|].
    replace (2+(1+n*2))%nat with ((1+n)*2+1)%nat by lia.
    eapply Pass_trans with (n:=1+n) (m:=0+(u+v)*2); [apply Pass_Ws|].
    eapply Pass_trans with (n:=0%nat) (m:=(u+v)*2); [apply Pass_odd_join|].
    apply (EraseWord_pass _ _ _ HZ).
Qed.

Lemma RRoute_clean_low c d r n w C e: RRoute c d r n w C e 0inf -> e<=1 ->
  exists u v N C' E, EraseWord w u v /\ E<=1 /\
    N+n=(u+v)*2+3+C+e /\ C'+E=1+v+n*2+e /\
    Pass (fun l a b=>crossV l (clean_input c d r) a b 2 0)
      (fun a b=>rootV (clean_input c d r) a b 2 0)
      (fun l a b=>crossW l 0inf a ([1;0;1;0;0;1]^^b) C' E)
      (fun a b=>rootW 0inf a ([1;0;1;0;0;1]^^b) C' E) N.
Proof.
  intros HR He; remember 0inf as R eqn:ER.
  destruct HR as [j n e r|j n z x y c' d r m w C e R HZ HR].
  - subst r; destruct (Pass_clean_tail_low j n e He) as [C' [E [HE [HC HP]]]].
    exists 0%nat,0%nat,(4+j*2+n+e),C',E; split; [constructor|].
    split; [exact HE|]; split; [lia|]; split; [lia|exact HP].
  - subst R; destruct (RRoute_clean _ _ _ _ _ _ _ _ HR eq_refl He)
      as [u [v [HW HK]]].
    destruct (HK (n*2+y)) as [N [C' [E [HE [HN [HC HP]]]]]].
    exists (1+(j+n)+x+u),(1+y+v),(4+j*2+n+(x+y)*2+N),C',E.
    split.
    + applys_eq (Erase_pair (j+n) 0 _ _ _ (EraseWord_app _ _ _ _ _ _ HZ HW));
        cbn; repeat rewrite <-app_assoc; flia.
    + split; [exact HE|]; split; [lia|]; split; [lia|].
      eapply Pass_trans with (n:=4+j*2+n+(x+y)*2) (m:=N); [apply Pass_clean_link_low,HZ|].
      replace (3+n*2+y) with (3+(n*2+y)) by lia; exact HP.
Qed.

Lemma RRoute_clean_at2 c d r n w C e u v k:
  RRoute c d r n w C e 0inf -> EraseWord w u v -> e<=1 ->
  exists N C' E, E<=1 /\ N+n=(u+v)*2+3+C+e /\ C'+E=1+k+v+n*2+e /\
    Pass (fun l a b=>crossV l (clean_input c d r) a b (2+k) 0)
      (fun a b=>rootV (clean_input c d r) a b (2+k) 0)
      (fun l a b=>crossW l 0inf a ([1;0;1;0;0;1]^^b) C' E)
      (fun a b=>rootW 0inf a ([1;0;1;0;0;1]^^b) C' E) N.
Proof.
  intros HR HW He; destruct k as [|k].
  - destruct (RRoute_clean_low _ _ _ _ _ _ _ HR He)
      as [x [y [N [C' [E [HZ [HE [HN [HC HP]]]]]]]]].
    destruct (EraseWord_unique _ _ _ _ _ HZ HW) as [-> ->].
    exists N,C',E; auto.
  - destruct (RRoute_clean _ _ _ _ _ _ _ _ HR eq_refl He) as [x [y [HZ HK]]].
    destruct (EraseWord_unique _ _ _ _ _ HZ HW) as [-> ->]; exact (HK k).
Qed.

Lemma RRoute_capacity_bound c d r n w C e R:
  RRoute c d r n w C e R -> forall u v, EraseWord w u v -> n<=u+C.
Proof.
  intro HR; induction HR as [j n e r|j n z x y c' d r m w C e R HZ HR IH]; intros u v HW.
  - lia.
  - destruct (RRoute_erase _ _ _ _ _ _ _ _ HR) as [i [k HK]].
    specialize (IH _ _ HK).
    assert (HT:EraseWord ([1;0]^^(2+(j+n)*2)++[1;0;1;0;0;1]++z++w)
      (1+(j+n)+x+i) (1+y+k)).
    { applys_eq (Erase_pair (j+n) 0 _ _ _ (EraseWord_app _ _ _ _ _ _ HZ HK));
        cbn; repeat rewrite <-app_assoc; flia. }
    destruct (EraseWord_unique _ _ _ _ _ HW HT); lia.
Qed.

Lemma RRoute_one_cleanup z i j c d r n w C e:
  EraseWord z i j -> RRoute c d r n w C e 0inf -> e<=1 ->
  exists u v N X, EraseWord w u v /\
    N+n=(i+j+u+v)*2+2+C+e /\ X=2+j+v+n*2+e /\
    OneCleanup (z *> clean_input c d r) N X.
Proof.
  intros HZ HR He; destruct (RRoute_erase _ _ _ _ _ _ _ _ HR) as [u [v HW]].
  destruct (RRoute_clean_at2 _ _ _ _ _ _ _ _ _ j HR HW He)
    as [N [C' [E [HE [HN [HC HP]]]]]].
  assert (0<N) by (pose proof (RRoute_capacity_bound _ _ _ _ _ _ _ _ HR _ _ HW); lia).
  exists u,v,((i+j)*2+N-1),(1+C'+E); split; [exact HW|].
  split; [lia|]; split; [lia|].
  exists C',E; split; [exact HE|]; split; [reflexivity|].
  replace (1+((i+j)*2+N-1)) with ((i+j)*2+N) by lia.
  eapply Pass_trans with (n:=(i+j)*2) (m:=N); [apply EraseWord_pass_low,HZ|exact HP].
Qed.

Lemma RCounter_one_cleanup l r n w C e a: RCounter r n w C e -> a<=n -> e<=1 ->
  exists u v N X r', EraseWord w u v /\
    N+n=a*3+(u+v)*2+2+C+e /\ X+a=2+v+n*2+e /\ OneCleanup r' N X /\
    l <* <[0;1;1] <* <[0;1]^^(2+a*2) <{{C}} [0;1] *> r -[tm]->*
      l <{{C}} [0;1;0;1;0;0;1;0;0;1] *> r'.
Proof.
  intros [d [s [-> HR]]] Ha He.
  destruct (RRoute_scan _ _ _ _ _ _ _ _ HR a
    (l <* <[0;1;1]) [] [] [] Ha Word_nil)
    as [c' [d' [s' [u [z [i [j [HZ [EW [HU HS]]]]]]]]]].
  destruct (RRoute_one_cleanup ([1;0;1;0;0;1]^^a++u) i (a+j) c' d' s' (n-a) z C e
    (Erase_V a _ _ _ HU) HZ He) as [x [y [N [X [HW [HN [HX HC]]]]]]].
  exists (i+x),(j+y),N,X,(([1;0;1;0;0;1]^^a++u) *> clean_input c' d' s').
  split; [rewrite EW; apply EraseWord_app; assumption|].
  split; [lia|]; split; [lia|]; split; [exact HC|].
  mid (scanW (l <* <[0;1;1] <* <[0;1]^^(a*2)) s [] 1 d).
  1: applys_eq (scan_pair (l <* <[0;1;1] <* <[0;1]^^(a*2)) s 0 d); st; finish; flia.
  follow HS; unfold scanW; follow (fun r=>pass_011 l r 1).
  unfold clean_input; finish.
Qed.

Definition CleanRight r N X := forall t xs, CleanLast N X t xs ->
  0inf <* <[0;1]^^t <{{C}} [0;1] *> r -[tm]->+ section xs.
Lemma Cleanup_right r N X: Cleanup r N X -> CleanRight r N X.
Proof. intros H t xs HL; apply (Cleanup_spec _ _ _ _ _ H HL). Qed.
Lemma OneCleanup_right r N X: OneCleanup r N X ->
  CleanRight ([0;1;0;0;1;0;0;1] *> r) N X.
Proof. intros H t xs HL; apply (OneCleanup_spec _ _ _ _ _ H HL). Qed.

Lemma RCounter_odd_cleanup l r n w C e a b: RCounter r n w C e -> a<=n -> e<=1 ->
  exists u v N X r', EraseWord w u v /\
    N+n=b+a*3+(u+v)*2+2+C+e /\ X+a=2+b*2+v+n*2+e /\ CleanRight r' N X /\
    l <* <[0;1;1]^^(1+b*2) <* <[0;1]^^(2+a*2) <{{C}} [0;1] *> r -[tm]->*
      l <{{C}} [0;1] *> r'.
Proof.
  intros HR Ha He; destruct b as [|b].
  - destruct (RCounter_one_cleanup l r n w C e a HR Ha He)
      as [u [v [N [X [r' [HW [HN [HX [HC HT]]]]]]]]].
    exists u,v,N,X,([0;1;0;0;1;0;0;1] *> r');
      repeat split; auto using OneCleanup_right.
  - destruct (RCounter_cleanup l r n w C e a b HR Ha He)
      as [u [v [N [X [r' [HW [HN [HX [HC HT]]]]]]]]].
    exists u,v,N,X,r'; split; [exact HW|]; split; [lia|]; split; [lia|].
    split; [apply Cleanup_right,HC|exact HT].
Qed.

Lemma CleanRight_total r N X t: CleanRight r N X -> exists xs,
  0inf <* <[0;1]^^t <{{C}} [0;1] *> r -[tm]->+ section xs.
Proof.
  intro H; destruct (CleanLast_total N X t) as [xs HL]; exists xs; apply H,HL.
Qed.

Local Close Scope nat_scope.

(* Exact flat-list sections, preserving every intermediate capacity guard. *)
Local Open Scope nat_scope.
Local Open Scope sym_scope.

Fixpoint column_list (cs:list (nat*nat)) : list nat :=
  match cs with []=>[] | (a,b)::cs=>(2+a*2)::(2+b*2)::column_list cs end.

Lemma column_list_side cs xs:
  section_side (column_list cs++xs) true=column_side (section_side xs true) cs.
Proof.
  induction cs as [|[a b] cs IH]; cbn[column_list app section_side column_side negb];
    rewrite ?IH; reflexivity.
Qed.

Lemma column_image_side cs xs:
  section_side (column_list cs++xs) false=rev (column_image cs) *> section_side xs false.
Proof.
  induction cs as [|[a b] cs IH]; cbn[column_list app section_side column_image negb];
    [reflexivity|].
  rewrite IH, !rev_app_distr, !Str_app_assoc, !reverse_power.
  st; simpl_rotate; reflexivity.
Qed.

Lemma restored_section p g b cs a t:
  section (p::(2+g*2)::b::column_list cs++[a;t])=
  0inf <* <[0;1]^^t <* <[0;1;1]^^a
    <* rev (column_image cs++[0;1]^^b++[0;1;1;0;1;1]^^(1+g))
    <* <[0;1]^^p {{B}}> 0inf.
Proof.
  unfold section; cbn[section_side negb]; rewrite column_image_side.
  cbn[section_side negb]; rewrite !rev_app_distr, !Str_app_assoc, !reverse_power.
  st; simpl_rotate; reflexivity.
Qed.

Lemma restored_section_good p cs a t:
  section (p::column_list cs++[a;t])=
  0inf <* <[0;1]^^t <* <[0;1;1]^^a <* rev (column_image cs) <* <[0;1]^^p {{B}}> 0inf.
Proof.
  unfold section; cbn[section_side negb]; rewrite column_image_side.
  cbn[section_side negb]; reflexivity.
Qed.

Lemma gap_column_word g b cs: exists x,
  Word (column_word cs++([1;0]^^(2+b*2)++[1;0;1;0;0;1]^^(1+g))) x
    (column_image cs++([0;1]^^(2+b*2)++[0;1;1;0;1;1]^^(1+g))).
Proof.
  destruct (column_word_spec cs) as [x HX]; eexists; apply Word_app; [exact HX|].
  apply Word_app; auto using Word_pow,Word_U,Word_V.
Qed.

Lemma gap_normal_section g b d e cs m s:
  P (2+g*2+(d*2+e)) -> ColumnRun (b+d) cs m -> s<=m -> e<=1 ->
  section (((2+g*2+(d*2+e))+(2+g*2))::(2+b*2)::column_list cs++[3+s*2]) -[tm]->+
  section ((2+g*2+(d*2+e))::(2+g*2)::(2+b*2)::column_list cs++[2+s*2;5+(m-s)*2]).
Proof.
  intros HP HC Hs He; destruct (gap_column_word g b cs) as [x HW].
  rewrite restored_section; unfold section; cbn[section_side negb];
    rewrite column_list_side; cbn[section_side].
  applys_eq (section_columns_normal _ _ _ _ _ cs m s _ _
    (Start_gap (column_side (0inf <* <[0;1]^^(3+s*2)) cs) g b d e HP) HC Hs He HW);
    rewrite !rev_app_distr, !Str_app_assoc, !reverse_power; st; simpl_rotate; flia.
Qed.

Lemma gap_overflow_section g b d e cs m s:
  P (2+g*2+(d*2+e)) -> ColumnRun (b+d) cs m -> e<=1 ->
  section (((2+g*2+(d*2+e))+(2+g*2))::(2+b*2)::column_list cs++[5+m*2+s*2]) -[tm]->+
  section ((2+g*2+(d*2+e))::(2+g*2)::(2+b*2)::column_list cs++[5+m*2;s*2]).
Proof.
  intros HP HC He; destruct (gap_column_word g b cs) as [x HW].
  rewrite restored_section; unfold section; cbn[section_side negb];
    rewrite column_list_side; cbn[section_side].
  applys_eq (section_columns_overflow _ _ _ _ _ cs m s _ _
    (Start_gap (column_side (0inf <* <[0;1]^^(5+m*2+s*2)) cs) g b d e HP) HC He HW);
    rewrite !rev_app_distr, !Str_app_assoc, !reverse_power; st; simpl_rotate; flia.
Qed.

Lemma good_normal_section d b e cs m s:
  P (2+d*2+e) -> ColumnRun (1+d+b) cs m -> s<=m -> e<=1 ->
  section ((2+d*2+e)::(2+b*2)::column_list cs++[3+s*2]) -[tm]->+
  section ((4+d*2+b*2+e)::column_list cs++[2+s*2;5+(m-s)*2]).
Proof.
  intros HP HC Hs He; destruct (column_word_spec cs) as [x HW].
  rewrite restored_section_good; unfold section; cbn[section_side negb];
    rewrite column_list_side; cbn[section_side].
  rewrite <-app_nil_r with (l:=column_word cs) in HW.
  applys_eq (section_columns_normal _ _ _ _ _ cs m s _ _
    (Start_good (column_side (0inf <* <[0;1]^^(3+s*2)) cs) d b e HP) HC Hs He HW);
    rewrite !rev_app_distr, !Str_app_assoc, !reverse_power; st; simpl_rotate; flia.
Qed.

Lemma good_overflow_section d b e cs m s:
  P (2+d*2+e) -> ColumnRun (1+d+b) cs m -> e<=1 ->
  section ((2+d*2+e)::(2+b*2)::column_list cs++[5+m*2+s*2]) -[tm]->+
  section ((4+d*2+b*2+e)::column_list cs++[5+m*2;s*2]).
Proof.
  intros HP HC He; destruct (column_word_spec cs) as [x HW].
  rewrite restored_section_good; unfold section; cbn[section_side negb];
    rewrite column_list_side; cbn[section_side].
  rewrite <-app_nil_r with (l:=column_word cs) in HW.
  applys_eq (section_columns_overflow _ _ _ _ _ cs m s _ _
    (Start_good (column_side (0inf <* <[0;1]^^(5+m*2+s*2)) cs) d b e HP) HC He HW);
    rewrite !rev_app_distr, !Str_app_assoc, !reverse_power; st; simpl_rotate; flia.
Qed.

Local Close Scope nat_scope.

(* Flat cleanup and bounded-capacity normal phases. *)

Local Open Scope nat_scope.
Local Open Scope sym_scope.

Lemma section_columns_cleanup n w C e c cs m a b u v t:
  SectionStart (column_side
    (0inf <* <[0;1]^^t <* <[0;1;1]^^(1+b*2) <* <[0;1]^^(2+a*2)) cs) n w C e c ->
  EraseWord w u v -> ColumnRun n cs m -> a<=m -> e<=1 ->
  exists N X, N+m=b+a*3+(column_U cs+column_V cs+u+v)*2+2+C+e /\
    X+a=2+b*2+column_V cs+v+m*2+e /\
    forall xs, CleanLast N X t xs -> c -[tm]->+ section xs.
Proof.
  intros HStart HW HCols Ha He.
  destruct (SectionStart_Rspec _ _ _ _ _ _ HStart) as [r [HR T0]].
  destruct (RCounter_columns _ _ _ HCols
    (0inf <* <[0;1]^^t <* <[0;1;1]^^(1+b*2) <* <[0;1]^^(2+a*2)) r w C e HR)
    as [r0 [H0 T1]].
  destruct (RCounter_odd_cleanup (0inf <* <[0;1]^^t) r0 m _ C e a b H0 Ha He)
    as [i [j [N [X [r1 [H1 [HN [HX [HC T2]]]]]]]]].
  destruct (EraseWord_unique _ _ _ _ _ H1
    (EraseWord_app _ _ _ _ _ _ (column_word_erase cs) HW)) as [-> ->].
  exists N,X; split; [lia|]; split; [lia|]; intros xs HL.
  eapply evstep_progress_trans; [exact T0|].
  eapply evstep_progress_trans; [exact T1|].
  eapply evstep_progress_trans; [exact T2|apply HC,HL].
Qed.

Lemma gap_cleanup_section g b0 d e cs m a b t N X xs:
  P (2+g*2+(d*2+e)) -> ColumnRun (b0+d) cs m -> a<=m -> e<=1 ->
  N+m=b+a*3+(column_U cs+column_V cs+(1+b0)+(1+g))*2+3+g*2+d*2+e ->
  X+a=3+b*2+column_V cs+g+m*2+e -> CleanLast N X t xs ->
  section (((2+g*2+(d*2+e))+(2+g*2))::(2+b0*2)::column_list cs++[2+a*2;1+b*2;t])
    -[tm]->+ section xs.
Proof.
  intros HP HCols Ha He HN HX HL.
  assert (HW:EraseWord ([1;0]^^(2+b0*2)++[1;0;1;0;0;1]^^(1+g)) (1+b0) (1+g)).
  1: applys_eq (Erase_pair b0 g [] 0 0 Erase_nil); rewrite ?app_nil_r; flia.
  destruct (section_columns_cleanup _ _ _ _ _ cs m a b _ _ t
    (Start_gap (column_side
      (0inf <* <[0;1]^^t <* <[0;1;1]^^(1+b*2) <* <[0;1]^^(2+a*2)) cs) g b0 d e HP)
    HW HCols Ha He) as [N0 [X0 [HN0 [HX0 HT]]]].
  assert (N0=N /\ X0=X) as [-> ->] by lia.
  unfold section at 1; cbn[section_side negb]; rewrite column_list_side; cbn[section_side negb].
  apply HT,HL.
Qed.

Lemma good_cleanup_section d b0 e cs m a b t N X xs:
  P (2+d*2+e) -> ColumnRun (1+d+b0) cs m -> a<=m -> e<=1 ->
  N+m=b+a*3+(column_U cs+column_V cs)*2+5+d*2+b0*2+e ->
  X+a=2+b*2+column_V cs+m*2+e -> CleanLast N X t xs ->
  section ((2+d*2+e)::(2+b0*2)::column_list cs++[2+a*2;1+b*2;t]) -[tm]->+ section xs.
Proof.
  intros HP HCols Ha He HN HX HL.
  destruct (section_columns_cleanup _ _ _ _ _ cs m a b _ _ t
    (Start_good (column_side
      (0inf <* <[0;1]^^t <* <[0;1;1]^^(1+b*2) <* <[0;1]^^(2+a*2)) cs) d b0 e HP)
    Erase_nil HCols Ha He) as [N0 [X0 [HN0 [HX0 HT]]]].
  assert (N0=N /\ X0=X) as [-> ->] by lia.
  unfold section at 1; cbn[section_side negb]; rewrite column_list_side; cbn[section_side negb].
  apply HT,HL.
Qed.

Local Open Scope nat_scope.

Inductive BoundedRun h: nat->list (nat*nat)->nat->Prop :=
| Bounded_nil n: n<=h -> BoundedRun h n [] n
| Bounded_cons n a b cs m: n<=h -> a<=n -> BoundedRun h (n-a+b) cs m ->
    BoundedRun h n ((a,b)::cs) m.
Lemma Bounded_forget h n cs m: BoundedRun h n cs m -> ColumnRun n cs m.
Proof. intro H; induction H; constructor; auto. Qed.
Lemma Bounded_ends h n cs m: BoundedRun h n cs m -> n<=h /\ m<=h.
Proof. intro H; induction H; lia. Qed.

Fixpoint flip_columns (b:nat) (cs:list (nat*nat)) (s:nat) : list (nat*nat) := match cs with
  []=>[(b,s)] | (a,b')::cs=>(b,a)::flip_columns b' cs s end.
Fixpoint flip_front (b:nat) (cs:list (nat*nat)) : list (nat*nat) := match cs with
  []=>[] | (a,b')::cs=>(b,a)::flip_front b' cs end.
Fixpoint last_column (b:nat) (cs:list (nat*nat)) : nat := match cs with
  []=>b | (_,b')::cs=>last_column b' cs end.
Lemma flip_columns_list b cs s:
  column_list (flip_columns b cs s)=(2+b*2)::column_list cs++[2+s*2].
Proof. gen b; induction cs as [|[a b'] cs IH]; intro b; cbn; rewrite ?IH; reflexivity. Qed.
Lemma flip_columns_last b cs s:
  flip_columns b cs s=flip_front b cs++[(last_column b cs,s)].
Proof. gen b; induction cs as [|[a b'] cs IH]; intro b; cbn; rewrite ?IH; reflexivity. Qed.
Lemma flip_front_list b cs xs:
  column_list (flip_front b cs)++(2+last_column b cs*2)::xs=
    (2+b*2)::column_list cs++xs.
Proof. gen b; induction cs as [|[a b'] cs IH]; intro b; cbn; rewrite ?IH; reflexivity. Qed.
Lemma flip_front_counts b cs:
  column_U (flip_front b cs)=column_V cs /\
  column_V (flip_front b cs)+last_column b cs=b+column_U cs.
Proof. gen b; induction cs as [|[a b'] cs IH]; intro b; cbn; [lia|specialize (IH b'); lia]. Qed.

Lemma Bounded_flip h n cs m: BoundedRun h n cs m -> forall b r s,
  b<=n -> r+n=h+b -> s<=m -> BoundedRun h r (flip_columns b cs s) (h-m+s).
Proof.
  intro H; induction H as [n Hn|n a b' cs m Hn Ha H IH]; intros b r s Hb Hr Hs; cbn.
  - apply Bounded_cons; [lia|lia|].
    applys_eq (Bounded_nil h (h-n+s)); lia.
  - apply Bounded_cons; [lia|lia|]; apply IH; lia.
Qed.
Lemma Bounded_flip_front h n cs m: BoundedRun h n cs m -> forall b r,
  b<=n -> r+n=h+b -> exists q,
    BoundedRun h r (flip_front b cs) q /\ last_column b cs<=q /\ q+m=h+last_column b cs.
Proof.
  intro H; induction H as [n Hn|n a b' cs m Hn Ha H IH]; intros b r Hb Hr; cbn.
  - exists r; split; [constructor; lia|lia].
  - destruct (IH b' (r-b+a)) as [q [HQ [HL HE]]]; [lia|lia|].
    exists q; split; [apply Bounded_cons; try lia; exact HQ|auto].
Qed.

Inductive Stair (p e:nat) : list nat->Prop :=
| Stair_good d b cs m s: p=2+d*2+e ->
    BoundedRun (p-1-e) (1+d+b) cs m -> m+s=p-e ->
    Stair p e (p::(2+b*2)::column_list cs++[3+s*2])
| Stair_gap g b d cs m s: p=2+g*2+(d*2+e) ->
    BoundedRun (p-1-e) (b+d) cs m -> m+s=p-e ->
    Stair p e ((p+(2+g*2))::(2+b*2)::column_list cs++[3+s*2]).

Lemma stair_gap_normal g b d e cs m s: e<=1 ->
  BoundedRun ((2+g*2+(d*2+e))-1-e) (b+d) cs m ->
  m+s=(2+g*2+(d*2+e))-e -> s<=m ->
  Stair (2+g*2+(d*2+e)) e
    ((2+g*2+(d*2+e))::(2+g*2)::(2+b*2)::column_list cs++[2+s*2;5+(m-s)*2]).
Proof.
  intros He HR HS Hs; pose proof (Bounded_ends _ _ _ _ HR) as [Hn Hm].
  applys_eq (Stair_good (2+g*2+(d*2+e)) e (g+d) g (flip_columns b cs s)
    ((2+g*2+(d*2+e))-1-e-m+s) (1+m-s));
    rewrite ?flip_columns_list; cbn[column_list app]; repeat rewrite <-app_assoc; cbn[app]; try solve [flia].
  eapply Bounded_flip; [exact HR|lia|lia|exact Hs].
Qed.

Lemma stair_good_normal d b e cs m s: e<=1 ->
  BoundedRun ((2+d*2+e)-1-e) (1+d+b) cs m ->
  m+s=(2+d*2+e)-e -> s<=m ->
  Stair (2+d*2+e) e ((4+d*2+b*2+e)::column_list cs++[2+s*2;5+(m-s)*2]).
Proof.
  intros He HR HS Hs; pose proof (Bounded_ends _ _ _ _ HR) as [Hn Hm].
  assert (Hb:b<=d) by lia.
  destruct cs as [|[a b'] cs].
  - inversion HR; subst.
    applys_eq (Stair_gap (2+d*2+e) e b s (d-b) [] (s+(d-b)) (1+(1+d+b)-s));
      cbn[column_list app]; try solve [flia]; constructor; lia.
  - inversion HR as [|n a0 b0 cs0 m0 Hn' Ha HT]; subst.
    applys_eq (Stair_gap (2+d*2+e) e b a (d-b) (flip_columns b' cs s)
      ((2+d*2+e)-1-e-m+s) (1+m-s));
      rewrite ?flip_columns_list; cbn[column_list app]; repeat rewrite <-app_assoc; cbn[app]; try solve [flia].
    eapply Bounded_flip; [exact HT|lia|lia|exact Hs].
Qed.

Local Open Scope nat_scope.

Lemma clean_after_gap g b d e cs m t xs: P (2+g*2+(d*2+e)) -> e<=1 ->
  BoundedRun ((2+g*2+(d*2+e))-1-e) (b+d) cs m ->
  CleanLast ((2+g*2+(d*2+e))+(1+b+column_U cs)*4)
    ((2+g*2+(d*2+e))*2+3-e+(1+b+column_U cs)) t xs ->
  section ((2+g*2+(d*2+e))::(2+g*2)::(2+b*2)::column_list cs++[5+m*2;t])
    -[tm]->+ section xs.
Proof.
  intros HP He HR HC.
  destruct (Bounded_flip_front _ _ _ _ HR b (1+g*2+d)) as [q [HQ [HL HE]]]; [lia|lia|].
  pose proof (ColumnRun_balance _ _ _ (Bounded_forget _ _ _ _ HR)) as HB.
  destruct (flip_front_counts b cs) as [HU HV].
  assert (HP':P (2+(g+d)*2+e)) by (applys_eq HP; flia).
  replace (1+g*2+d) with (1+(g+d)+g) in HQ by lia.
  applys_eq (good_cleanup_section (g+d) g e (flip_front b cs) q (last_column b cs)
    (2+m) t ((2+g*2+(d*2+e))+(1+b+column_U cs)*4)
    ((2+g*2+(d*2+e))*2+3-e+(1+b+column_U cs)) xs HP' (Bounded_forget _ _ _ _ HQ) HL He);
    rewrite ?flip_front_list; cbn[app]; try solve [flia]; eauto.
Qed.

Lemma clean_after_good d b e cs m t xs: P (2+d*2+e) -> e<=1 ->
  BoundedRun ((2+d*2+e)-1-e) (1+d+b) cs m ->
  CleanLast ((2+d*2+e)+(1+b+column_U cs)*4)
    ((2+d*2+e)*2+3-e+(1+b+column_U cs)) t xs ->
  section ((4+d*2+b*2+e)::column_list cs++[5+m*2;t]) -[tm]->+ section xs.
Proof.
  intros HP He HR HC; pose proof (Bounded_ends _ _ _ _ HR) as [Hn Hm].
  assert (Hb:b<=d) by lia; destruct cs as [|[a b'] cs].
  - inversion HR; subst; cbn[column_list column_U app] in *.
    applys_eq (cleanup_odd_triple_section b (2+(1+d+b)) (d-b) e t xs);
      try solve [flia]; first [applys_eq HP; flia|applys_eq HC; flia].
  - inversion HR as [|n a0 b0 cs0 m0 Hn' Ha HT]; subst.
    destruct (Bounded_flip_front _ _ _ _ HT b' (a+(d-b))) as [q [HQ [HL HE]]]; [lia|lia|].
    pose proof (ColumnRun_balance _ _ _ (Bounded_forget _ _ _ _ HT)) as HB.
    destruct (flip_front_counts b' cs) as [HU HV].
    assert (HP':P (2+b*2+((d-b)*2+e))) by (applys_eq HP; flia).
    applys_eq (gap_cleanup_section b a (d-b) e (flip_front b' cs) q (last_column b' cs)
      (2+m) t ((2+d*2+e)+(1+b+column_U ((a,b')::cs))*4)
      ((2+d*2+e)*2+3-e+(1+b+column_U ((a,b')::cs))) xs HP' (Bounded_forget _ _ _ _ HQ) HL He);
      rewrite ?flip_front_list; cbn[column_list column_U app] in *; try solve [flia]; eauto.
Qed.

Local Open Scope nat_scope.

Lemma Band_offset p k: Chain p -> exists q, p<=q /\ Band q (p+k).
Proof.
  intro HP; induction k as [|k [q [Hpq [HQ [Hlo Hhi]]]]].
  - exists p; split; [lia|]; split; [exact HP|pose proof (next_p_grows p); lia].
  - destruct (Nat.lt_ge_cases (p+(1+k)) (next_p q)).
    + exists q; split; [exact Hpq|]; split; [exact HQ|lia].
    + exists (next_p q); split; [pose proof (next_p_grows q); lia|].
      split; [constructor; exact HQ|pose proof (next_p_grows (next_p q)); lia].
Qed.
Lemma Band_above p n: Chain p -> p<=n -> exists q, p<=q /\ Band q n.
Proof.
  intros HP Hn; destruct (Band_offset p (n-p) HP) as [q [HQ HB]].
  exists q; split; [exact HQ|applys_eq HB; flia].
Qed.

Inductive CoreEntry: list nat->Prop :=
| Entry_unary n: CoreEntry [n]
| Entry_small p n b t: Band p n -> 2<=b -> b mod 2=0 -> 1<=t -> t mod 2=1 ->
    b<=p -> b+t<=n*8 -> CoreEntry [n;b;t].

Lemma next_p_parity p e: e<=1 -> p mod 2=e -> next_p p=p*2+3-e.
Proof. intros He HP; unfold next_p; rewrite HP; lia. Qed.
Lemma Stair_parity p e xs: e<=1 -> Stair p e xs -> p mod 2=e.
Proof. intros He H; destruct H; lia. Qed.

Lemma core_even_exit p e f r: Chain p -> e<=1 -> p mod 2=e -> 1<=f -> r<=p-1-e ->
  exists xs, CleanLast (p+f*4) (next_p p+f) (r*2) xs /\ CoreEntry xs.
Proof.
  intros HP He Hpar Hf Hr; pose proof (Chain_spec _ HP) as [Hp _].
  pose proof (next_p_parity _ _ He Hpar) as Hnext.
  destruct r as [|r].
  - eexists; split; [apply Clean0|constructor].
  - exists [next_p p+f;2+r*2;3+(p+f*4-r)*2]; split.
    + apply CleanEven; lia.
    + destruct (Band_above (next_p p) (next_p p+f) (ChainS p HP) (ltac:(lia)))
        as [q [Hq HB]].
      apply (Entry_small q); try lia; exact HB.
Qed.

Local Open Scope nat_scope.

Lemma Stair_progress p e xs: Chain p -> e<=1 -> Stair p e xs -> exists ys,
  section xs -[tm]->+ section ys /\ (Stair p e ys \/ CoreEntry ys).
Proof.
  intros HChain He HStair.
  pose proof (Chain_spec _ HChain) as [Hp [HP _]].
  pose proof (Stair_parity _ _ _ He HStair) as Hpar.
  pose proof (next_p_parity _ _ He Hpar) as Hnext.
  destruct HStair as [d b cs m s EP HR HS|g b d cs m s EP HR HS]; subst p.
  - destruct (Nat.le_gt_cases s m) as [Hs|Hs].
    + exists ((4+d*2+b*2+e)::column_list cs++[2+s*2;5+(m-s)*2]); split.
      * exact (good_normal_section d b e cs m s HP (Bounded_forget _ _ _ _ HR) Hs He).
      * left; apply stair_good_normal; assumption.
    + destruct (core_even_exit (2+d*2+e) e (1+b+column_U cs) (s-m-1)
        HChain He Hpar (ltac:(lia)) (ltac:(lia))) as [ys [HC HY]].
      exists ys; split; [|right; exact HY].
      eapply progress_trans with (c':=section ((4+d*2+b*2+e)::column_list cs++[5+m*2;(s-m-1)*2])).
      * applys_eq (good_overflow_section d b e cs m (s-m-1) HP (Bounded_forget _ _ _ _ HR) He); flia.
      * rewrite Hnext in HC; apply (clean_after_good d b e cs m ((s-m-1)*2) ys HP He HR HC).
  - destruct (Nat.le_gt_cases s m) as [Hs|Hs].
    + exists ((2+g*2+(d*2+e))::(2+g*2)::(2+b*2)::column_list cs++[2+s*2;5+(m-s)*2]); split.
      * exact (gap_normal_section g b d e cs m s HP (Bounded_forget _ _ _ _ HR) Hs He).
      * left; apply stair_gap_normal; assumption.
    + destruct (core_even_exit (2+g*2+(d*2+e)) e (1+b+column_U cs) (s-m-1)
        HChain He Hpar (ltac:(lia)) (ltac:(lia))) as [ys [HC HY]].
      exists ys; split; [|right; exact HY].
      eapply progress_trans with (c':=section
        ((2+g*2+(d*2+e))::(2+g*2)::(2+b*2)::column_list cs++[5+m*2;(s-m-1)*2])).
      * applys_eq (gap_overflow_section g b d e cs m (s-m-1) HP (Bounded_forget _ _ _ _ HR) He); flia.
      * rewrite Hnext in HC; apply (clean_after_gap g b d e cs m ((s-m-1)*2) ys HP He HR HC).
Qed.

Local Close Scope nat_scope.

Local Open Scope nat_scope.

Lemma good_relation p b t xs: P p -> 0<p+b -> Last t (p+b) xs ->
  section [p;b;t] -[tm]->+ section xs.
Proof.
  intros HP H HL; rewrite (Last_output _ _ _ HL); apply good_section_formula; assumption.
Qed.

Lemma odd_gap_odd_progress g j t d: P (1+g*2+d) ->
  section [(1+g*2+d)+(1+g*2);1+j*2;t] -[tm]->+
  section [1+g*2+d;2+(j+g)*2;2+t+d+d mod 2].
Proof.
  intro HP; eapply evstep_progress_trans; [apply odd_gap_seed,HP|].
  apply evstep_progress; [apply seed_section|discriminate].
Qed.
Lemma odd_gap_even_progress g j v d: P (1+g*2+d) ->
  section [(1+g*2+d)+(1+g*2);j*2;1+v*2] -[tm]->+
  section (S_odd_output (j+g) (g*2) v d).
Proof.
  intro HP; eapply evstep_progress_trans; [apply odd_gap_S,HP|].
  applys_eq (S_odd_progress (j+g) (g*2) v d); flia.
Qed.
Lemma odd_last_odd_progress g j t: P (2+g*2) ->
  section [(2+g*2)+(3+g*2);1+j*2;t] -[tm]->+
  section [2+g*2;4+(j+g)*2;2+t].
Proof.
  intro HP; unfold section at 1; cbn[section_side negb].
  follow (fun l=>return_last l g HP); follow odd_block.
  mid01 (0inf <{{A}} [1;0]%sym^^(2+t) *>
    [0;1;1;0;1;0]%sym^^(2+j+g) *> [1;0]%sym^^(1+g*2) *> 0inf).
  1: replace (2+j+g) with (j+(2+g)) by lia;
    rewrite (lpow_add _ j (2+g)),Str_app_assoc; es.
  apply evstep_progress; [applys_eq (bare_root t (1+j+g) (1+g*2)); flia|discriminate].
Qed.

Definition odd_output p e k b t :=
  if t <? p+2+e-k then [p;b+k+t;p+2+e-k-t]
  else [p;p+b+2+e;t-(p+2+e-k)].

Lemma odd_odd_section p e k b t:
  P p -> 3<=p -> e<=1 -> p mod 2+e=1 ->
  k mod 2=1 -> k<=p+e -> b mod 2=1 ->
  section [p+k;b;t] -[tm]->+ section [p;b+k;t+p+2+e-k].
Proof.
  intros HP Hp He Hpar Hk Hkp Hb.
  destruct (parity k) as [g [-> | ->]], (parity b) as [j [-> | ->]]; try lia.
  destruct (Nat.le_gt_cases (1+g*2) p) as [Hle|Hgt].
  - assert (HD:(p-(1+g*2)) mod 2=e) by lia.
    applys_eq (odd_gap_odd_progress g j t (p-(1+g*2)));
      rewrite ?HD; try solve [flia]; applys_eq HP; flia.
  - destruct g as [|g]; [lia|].
    applys_eq (odd_last_odd_progress g j t);
      try solve [flia]; applys_eq HP; flia.
Qed.

Lemma odd_even_section p e k b t:
  P p -> 3<=p -> e<=1 -> p mod 2+e=1 ->
  k mod 2=1 -> k<=p+e -> b mod 2=0 -> t mod 2=1 ->
  section [p+k;b;t] -[tm]->+ section (odd_output p e k b t).
Proof.
  intros HP Hp He Hpar Hk Hkp Hb Ht.
  destruct (parity k) as [g [-> | ->]], (parity b) as [j [-> | ->]],
    (parity t) as [v [-> | ->]]; try lia.
  destruct (Nat.le_gt_cases (1+g*2) p) as [Hle|Hgt].
  - assert (HD:(p-(1+g*2)) mod 2=e) by lia.
    assert (E:odd_output p e (1+g*2) (j*2) (1+v*2)=
      S_odd_output (j+g) (g*2) v (p-(1+g*2))).
    { unfold odd_output,S_odd_output; rewrite HD.
      replace (p-(1+g*2)+2+e) with (p+2+e-(1+g*2)) by lia.
      destruct (1+v*2 <? p+2+e-(1+g*2)); repeat (f_equal; try lia). }
    rewrite E; applys_eq (odd_gap_even_progress g j v (p-(1+g*2)));
      try solve [flia]; applys_eq HP; flia.
  - destruct g as [|g]; [lia|].
    assert (E:odd_output p e (1+(1+g)*2) (j*2) (1+v*2)=
      S_odd_output (1+j+g) (1+g*2) v 0).
    { unfold odd_output,S_odd_output; replace (0 mod 2) with 0 by reflexivity.
      replace (0+2+0) with 2 by lia.
      replace (p+2+e-(1+(1+g)*2)) with 2 by lia.
      destruct (1+v*2 <? 2); repeat (f_equal; try lia). }
    change (section [p+(1+(1+g)*2);j*2;1+v*2] -[tm]->+
      section (odd_output p e (1+(1+g)*2) (j*2) (1+v*2))).
    rewrite E; applys_eq (odd_last_even_formula g j v);
      try solve [flia]; applys_eq HP; flia.
Qed.

Lemma predecessor_P p: Chain p -> PP (next_p p-1).
Proof.
  intro H; destruct (Chain_spec _ H) as [Hp [HP _]].
  destruct (parity p) as [a [-> | ->]]; unfold next_p.
  - destruct a as [|a]; [lia|].
    applys_eq (pred_even a); try solve [flia]; applys_eq HP; flia.
  - applys_eq (pred_odd a); try solve [flia]; exact HP.
Qed.

Lemma predecessor_section p b t: Chain p -> 2<=b -> b mod 2=0 -> t mod 2=1 ->
  section [next_p p-1;b;t] -[tm]->+ section (pred_output (next_p p-1) b t).
Proof.
  intros HP Hb Hbp Htp.
  destruct (parity b) as [a [-> | ->]], (parity t) as [v [-> | ->]]; try lia.
  destruct a as [|a]; [lia|].
  applys_eq (pred_section (next_p p-1) a v (predecessor_P _ HP)); flia.
Qed.

Lemma even_odd_section p e k b t xs:
  P p -> e<=1 -> p mod 2=e -> 2<=k -> k<=p -> k mod 2=0 -> b mod 2=1 ->
  CleanLast ((p+k*3+b+e-2)/2) (p+b-k/2) t xs ->
  section [p+k;b;t] -[tm]->+ section xs.
Proof.
  intros HP He Hpar Hk Hkp Hke Hb HC.
  destruct (parity k) as [g [-> | ->]], (parity b) as [j [-> | ->]]; try lia.
  destruct g as [|g]; [lia|].
  assert (Hd:exists d,p=2+g*2+(d*2+e)).
  { exists ((p-2-g*2-e)/2); lia. }
  destruct Hd as [d ->].
  apply (cleanup_odd_triple_section g j d e t xs HP He).
  applys_eq HC; flia.
Qed.

Lemma even_normal_stair g b d e s:
  P (2+g*2+(d*2+e)) -> e<=1 -> b<=1+g*2+d -> s<=b+d ->
  exists ys, section [(2+g*2+(d*2+e))+(2+g*2);2+b*2;3+s*2] -[tm]->+ section ys /\
    Stair (2+g*2+(d*2+e)) e ys.
Proof.
  intros HP He Hb Hs.
  exists [2+g*2+(d*2+e);2+g*2;2+b*2;2+s*2;5+(b+d-s)*2]; split.
  - applys_eq (gap_normal_section g b d e [] (b+d) s HP); cbn[column_list app];
      try solve [flia]; constructor.
  - applys_eq (Stair_good (2+g*2+(d*2+e)) e (g+d) g [(b,s)]
      (1+g*2+d-b+s) (1+b+d-s)); cbn[column_list app]; try solve [flia].
    apply Bounded_cons; try lia.
    applys_eq (Bounded_nil (2+g*2+(d*2+e)-1-e) (1+g*2+d-b+s)); flia.
Qed.

Lemma even_overflow_clean g b d e r xs:
  P (2+g*2+(d*2+e)) -> e<=1 -> b<=1+g*2+d ->
  CleanLast ((2+g*2+(d*2+e))+(1+b)*4)
    ((2+g*2+(d*2+e))*2+3-e+(1+b)) (r*2) xs ->
  section [(2+g*2+(d*2+e))+(2+g*2);2+b*2;5+(b+d)*2+r*2] -[tm]->+ section xs.
Proof.
  intros HP He Hb HC.
  eapply progress_trans with (c':=section [2+g*2+(d*2+e);2+g*2;2+b*2;5+(b+d)*2;r*2]).
  - applys_eq (gap_overflow_section g b d e [] (b+d) r HP); cbn[column_list app];
      try solve [flia]; constructor.
  - assert (HR:BoundedRun (2+g*2+(d*2+e)-1-e) (b+d) [] (b+d)).
    { apply Bounded_nil; lia. }
    applys_eq (clean_after_gap g b d e [] (b+d) (r*2) xs HP He HR);
      cbn[column_list column_U app]; rewrite ?Nat.add_0_r; try solve [flia]; try exact HC.
Qed.

Lemma even_parameters p e k b:
  e<=1 -> p mod 2+e=1 -> 2<=k -> k<=p -> k mod 2=0 -> 2<=b -> b mod 2=0 ->
  exists g j d, k=2+g*2 /\ b=2+j*2 /\ p=2+g*2+(d*2+(1-e)).
Proof.
  intros; exists ((k-2)/2),((b-2)/2),((p-k-(1-e))/2); repeat split; lia.
Qed.

Lemma even_normal_section p e k b t:
  P p -> e<=1 -> p mod 2+e=1 -> 2<=k -> k<=p -> k mod 2=0 ->
  2<=b -> b mod 2=0 -> 3<=t -> t mod 2=1 ->
  b<=p+k -> t+k<=p+b+e ->
  exists ys, section [p+k;b;t] -[tm]->+ section ys /\ Stair p (1-e) ys.
Proof.
  intros HP He Hpar Hk Hkp Hke Hb Hbe Ht Hte Hbn Hcap.
  destruct (even_parameters _ _ _ _ He Hpar Hk Hkp Hke Hb Hbe)
    as [g [j [d [-> [-> ->]]]]].
  assert (Et:t=3+((t-3)/2)*2) by lia; rewrite Et.
  apply even_normal_stair; try assumption; lia.
Qed.

Lemma even_overflow_section p e k b t xs:
  P p -> e<=1 -> p mod 2+e=1 -> 2<=k -> k<=p -> k mod 2=0 ->
  2<=b -> b mod 2=0 -> t mod 2=1 -> b<=p+k -> p+b+e<t+k ->
  CleanLast (p+b*2) (next_p p+b/2) (t+k-(p+b+2+e)) xs ->
  section [p+k;b;t] -[tm]->+ section xs.
Proof.
  intros HP He Hpar Hk Hkp Hke Hb Hbe Hte Hbn Hcap HC.
  destruct (even_parameters _ _ _ _ He Hpar Hk Hkp Hke Hb Hbe)
    as [g [j [d [-> [-> ->]]]]].
  assert (Hr:exists r,t=5+(j+d)*2+r*2).
  { exists ((t-(5+(j+d)*2))/2); lia. }
  destruct Hr as [r ->].
  apply (even_overflow_clean g j d (1-e) r xs HP); try lia.
  unfold next_p in HC; applys_eq HC; flia.
Qed.

Lemma even_short_section p e k b:
  P p -> e<=1 -> p mod 2+e=1 -> 2<=k -> k<=p -> k mod 2=0 -> b mod 2=0 ->
  section [p+k;b;1] -[tm]->+ section [p;k;p+b*2+4+e-k].
Proof.
  intros HP He Hpar Hk Hkp Hke Hb.
  destruct (parity k) as [g [-> | ->]], (parity b) as [j [-> | ->]]; try lia.
  destruct g as [|g]; [lia|].
  applys_eq (short_section g j (p-(2+g*2))); try solve [flia]; applys_eq HP; flia.
Qed.

Local Open Scope nat_scope.

Definition Diagonal n b t := 2<=b /\ b mod 2=0 /\ 1<=t /\ t mod 2=1 /\
  (b+t=n+2+(1-n mod 2) \/ (5<=t /\ b+t=n+4+(1-n mod 2))).
Inductive Core: list nat->Prop :=
| Core_entry xs: CoreEntry xs -> Core xs
| Core_diagonal n b t: 3<=n -> Diagonal n b t -> Core [n;b;t].

Lemma Last_core t m xs: 3<=m -> t<=m+1+(1-m mod 2) -> Last t m xs -> Core xs.
Proof.
  intros Hm Ht HL; destruct HL; try (apply Core_entry; constructor).
  all: try (apply Core_diagonal; [lia|unfold Diagonal; repeat split; try lia;
    first [left; lia|right; split; lia]]).
  all: lia.
Qed.

Lemma unary_core_progress n: exists ys, section [n] -[tm]->+ section ys /\ Core ys.
Proof.
  destruct (Nat.lt_ge_cases n 3) as [Hn|Hn].
  - destruct n as [|[|[|n]]]; try lia;
      eexists; split; first [apply unary_zero|apply unary_one|apply unary_two|
        apply Core_entry; constructor].
  - destruct (Band_total n Hn) as [p [HP [Hlo Hhi]]].
    destruct (Chain_spec _ HP) as [Hp [HP' _]].
    destruct (Last_total (n-p) p (ltac:(lia))) as [ys HL].
    exists ys; split.
    + rewrite (Last_output _ _ _ HL); applys_eq (unary_progress p (n-p) HP' (ltac:(lia))); flia.
    + apply (Last_core (n-p) p); try assumption; unfold next_p in Hhi; lia.
Qed.

Lemma good_core_or_overflow p b t: Chain p -> 1<=b ->
  exists ys, section [p;b;t] -[tm]->+ section ys /\
    (Core ys \/ exists u, ys=[p+b;p+b+2+(1-(p+b) mod 2);u] /\
      t=p+b+2+(1-(p+b) mod 2)+u).
Proof.
  intros HChain Hb; destruct (Chain_spec _ HChain) as [Hp [HP _]].
  destruct (Last_total t (p+b) (ltac:(lia))) as [ys HL].
  exists ys; split.
  - rewrite (Last_output _ _ _ HL); apply good_section_formula; auto; lia.
  - destruct (Nat.le_gt_cases t (p+b+1+(1-(p+b) mod 2))) as [Ht|Ht].
    + left; apply (Last_core t (p+b)); auto; lia.
    + destruct HL; try lia;
        right; eexists; split; repeat (f_equal; try lia).
Qed.

Lemma good_bounded_core p b t: Chain p -> t<=p+b+1+(1-(p+b) mod 2) ->
  exists ys, section [p;b;t] -[tm]->+ section ys /\ Core ys.
Proof.
  intros HChain Ht; destruct (Chain_spec _ HChain) as [Hp [HP _]].
  destruct (Last_total t (p+b) (ltac:(lia))) as [ys HL].
  exists ys; split; [apply good_relation; auto; lia|apply (Last_core t (p+b)); auto; lia].
Qed.

Lemma odd_even_core p e k b t:
  Chain p -> e<=1 -> p mod 2+e=1 -> k mod 2=1 -> k<=p+e ->
  2<=b -> b mod 2=0 -> t mod 2=1 -> t+k<=p+b+e ->
  exists ys, section [p+k;b;t] -[tm]->+ section ys /\ Core ys.
Proof.
  intros HChain He Hpar Hk Hkp Hb Hbe Hte Hcap.
  destruct (Chain_spec _ HChain) as [Hp [HP _]].
  pose proof (odd_even_section p e k b t HP Hp He Hpar Hk Hkp Hbe Hte) as Hstep.
  unfold odd_output in Hstep; destruct (t <? p+2+e-k) eqn:E.
  - apply Nat.ltb_lt in E.
    destruct (good_bounded_core p (b+k+t) (p+2+e-k-t) HChain (ltac:(lia)))
      as [ys [HT HY]].
    exists ys; split; [eapply progress_trans; eauto|exact HY].
  - apply Nat.ltb_ge in E.
    destruct (good_bounded_core p (p+b+2+e) (t-(p+2+e-k)) HChain (ltac:(lia)))
      as [ys [HT HY]].
    exists ys; split; [eapply progress_trans; eauto|exact HY].
Qed.

Lemma even_short_core p e k b:
  Chain p -> e<=1 -> p mod 2+e=1 -> 2<=k -> k<=p -> k mod 2=0 -> b mod 2=0 -> b<k ->
  exists ys, section [p+k;b;1] -[tm]->+ section ys /\ Core ys.
Proof.
  intros HChain He Hpar Hk Hkp Hke Hbe Hb.
  destruct (Chain_spec _ HChain) as [Hp [HP _]].
  destruct (good_bounded_core p k (p+b*2+4+e-k) HChain (ltac:(lia))) as [ys [HT HY]].
  exists ys; split; [|exact HY].
  eapply progress_trans; [apply even_short_section; eauto|exact HT].
Qed.

Lemma odd_recovery_core p e k b t:
  Chain p -> e<=1 -> p mod 2+e=1 -> 1<=k -> k*4<=p -> k mod 2=1 ->
  b mod 2=1 -> 1<=t -> t mod 2=1 -> p+k*8+2+e<=b -> b+t+4<=p*3 ->
  exists ys, section [p+k;b;t] -[tm]->+ section ys /\ Core ys.
Proof.
  intros HChain He Hpar Hk Hkp Hke Hbe Ht Hte Hb Hsum.
  destruct (Chain_spec _ HChain) as [Hp [HP _]].
  pose proof (odd_odd_section p e k b t HP Hp He Hpar Hke (ltac:(lia)) Hbe) as Hfirst.
  destruct (good_core_or_overflow p (b+k) (t+p+2+e-k) HChain (ltac:(lia)))
    as [zs [Hsecond [HZ|[u [-> HU]]]]].
  - exists zs; split; [eapply progress_trans; eauto|exact HZ].
  - set (P:=next_p p).
    assert (HC:Chain P) by (apply ChainS,HChain).
    assert (EP:P=p*2+2+e) by (unfold P,next_p; lia).
    assert (HPpar:P mod 2+(1-e)=1) by lia.
    destruct (Chain_spec _ HC) as [HPlo [HPP _]].
    set (j:=p+(b+k)-P).
    assert (j mod 2=1 /\ j<=P+(1-e)) as [Hje Hj] by (unfold j; lia).
    assert (ET:section [p+(b+k);p+(b+k)+2+(1-(p+(b+k)) mod 2);u] -[tm]->+
      section [P;p+(b+k)+2+e+j;u+P+2+(1-e)-j]).
    { applys_eq (odd_odd_section P (1-e) j (p+(b+k)+2+e) u HPP HPlo
        (ltac:(lia)) HPpar Hje Hj (ltac:(lia))); unfold j; flia. }
    destruct (good_bounded_core P (p+(b+k)+2+e+j) (u+P+2+(1-e)-j) HC
      (ltac:(unfold j; lia))) as [ys [Hlast HY]].
    exists ys; split; [|exact HY].
    eapply progress_trans; [exact Hfirst|].
    eapply progress_trans; [exact Hsecond|].
    eapply progress_trans; [exact ET|exact Hlast].
Qed.

Lemma even_recovery_core p e k b t:
  Chain p -> e<=1 -> p mod 2+e=1 -> 1<=k -> k*4<=p -> k mod 2=0 ->
  b mod 2=1 -> 1<=t -> t mod 2=1 -> p+k*8+2+e<=b -> b+t+4<=p*3 ->
  exists ys, section [p+k;b;t] -[tm]->+ section ys /\ Core ys.
Proof.
  intros HChain He Hpar Hk Hkp Hke Hbe Ht Hte Hb Hsum.
  destruct (Chain_spec _ HChain) as [Hp [HP _]].
  set (N:=(p+k*3+b+(1-e)-2)/2).
  set (X:=p+b-k/2).
  set (P:=next_p p).
  assert (HN:N*2+5=p+k*3+b+3-e) by (unfold N; lia).
  assert (EP:P=p*2+2+e) by (unfold P,next_p; lia).
  assert (HPpar:P mod 2+(1-e)=1) by lia.
  assert (EX:Band P X).
  { split; [apply ChainS,HChain|unfold X,next_p; lia]. }
  destruct (CleanLast_total N X t) as [ys HC].
  exists ys; split.
  - apply (even_odd_section p (1-e) k b t ys HP); try lia; exact HC.
  - destruct HC; try lia; apply Core_entry; try constructor.
    apply (Entry_small P); try assumption; unfold X; lia.
Qed.

Lemma recovery_core p k b t:
  Chain p -> 1<=k -> k*4<=p -> b mod 2=1 -> 1<=t -> t mod 2=1 ->
  p+k*8+2+(1-p mod 2)<=b -> b+t+4<=p*3 ->
  exists ys, section [p+k;b;t] -[tm]->+ section ys /\ Core ys.
Proof.
  intros; destruct (parity k) as [a [-> | ->]].
  - apply (even_recovery_core p (1-p mod 2)); auto; lia.
  - apply (odd_recovery_core p (1-p mod 2)); auto; lia.
Qed.

Local Open Scope nat_scope.

Lemma negative_positive_small a n e d b t u:
  P (3+a*2-e) -> e<=1 -> n<=a -> d<=a+n+3 ->
  b+n*4+2=d*2+e+u -> t+b*2=13+a*4+d*2 ->
  negativeN (0inf <* <[0;1]%sym^^t <* <[0;1;1]%sym^^(b*2)) (3+a*2-e) n d e
    -[tm]->* section [9+a*4+n-e;14+a*4+d*4;1+u*2].
Proof.
  intros HP He Hn Hd Hu Ht.
  unfold section; cbn[section_side negb].
  destruct u as [|u].
  - destruct e as [|[|e]]; try lia.
    + applys_eq (negativeN_one_odd a n d b (a+n+3-d) (a-n) t);
        try solve [flia]; applys_eq HP; flia.
    + applys_eq (negativeN_one_even a n d b (a+n+3-d) (a-n) t);
        try solve [flia]; applys_eq HP; flia.
  - destruct (Nat.le_gt_cases (u+e+n) a) as [Hcross|Hroot].
    + destruct e as [|[|e]]; try lia.
      * applys_eq (negativeN_positive_odd a n d b (a+n+3-d) u (a-n-u) t);
          try solve [flia]; applys_eq HP; flia.
      * applys_eq (negativeN_positive_even a n d b (a+n+3-d) u (a-1-n-u) t);
          try solve [flia]; applys_eq HP; flia.
    + destruct e as [|[|e]]; try lia.
      * applys_eq (negativeN_root_odd a n d b (a+n+3-d) (a-n) ((t-1)/2) (u-(a-n)-1));
          try solve [flia]; applys_eq HP; flia.
      * applys_eq (negativeN_root_even a n d b (a+n+3-d) (a-n) ((t-1)/2) (u-(a-n)));
          try solve [flia]; applys_eq HP; flia.
Qed.

Lemma negative_negative_small a n e d b t u:
  P (3+a*2-e) -> e<=1 -> n<=a -> d<=a+n+3 ->
  d*2+e=b+n*4+3+u -> t+b*2=13+a*4+d*2 ->
  negativeN (0inf <* <[0;1]%sym^^t <* <[0;1;1]%sym^^(b*2)) (3+a*2-e) n d e
    -[tm]->* section [9+a*4+n-e;19+a*4+n*8+b*2-e*2;1+u*2].
Proof.
  intros HP He Hn Hd Hu Ht; unfold section; cbn[section_side negb].
  destruct e as [|[|e]]; try lia.
  - applys_eq (negativeN_bounded_odd a n d b (a+n+3-d) (a-n) u t);
      try solve [flia]; applys_eq HP; flia.
  - applys_eq (negativeN_bounded_even a n d b (a+n+3-d) (a-n) u t);
      try solve [flia]; applys_eq HP; flia.
Qed.

Lemma negative_positive_large a n e k b t u:
  P (3+a*2-e) -> e<=1 -> n<=a -> k<=5+n*3+a-e ->
  b+n*4+2=(a+n+3+k)*2+e+u -> t+b*2=13+a*4+(a+n+3+k)*2 ->
  negativeN (0inf <* <[0;1]%sym^^t <* <[0;1;1]%sym^^(b*2))
    (3+a*2-e) n (a+n+3+k) e
    -[tm]->* section [9+a*4+n-e;14+a*4+(a+n+3+k)*4;1+u*2].
Proof.
  intros HP He Hn Hk Hu Ht; unfold section; cbn[section_side negb].
  destruct u as [|u].
  - applys_eq (negativeN_large_short (3+a*2-e) n e (a+n+3) k
      (3+a*2-e-(2+n*2)) (1+a-n-e) (5+n*3+a-e) b ((t-1)/2));
      try solve [flia]; exact HP.
  - applys_eq (negativeN_large_root (3+a*2-e) n e (a+n+3) k
      (3+a*2-e-(2+n*2)) (1+a-n-e) (5+n*3+a-e) b ((t-1)/2) u);
      try solve [flia]; exact HP.
Qed.

Lemma negative_negative_large a n e k b t u:
  P (3+a*2-e) -> e<=1 -> n<=a -> k<=5+n*3+a-e ->
  (a+n+3+k)*2+e=b+n*4+3+u -> t+b*2=13+a*4+(a+n+3+k)*2 ->
  negativeN (0inf <* <[0;1]%sym^^t <* <[0;1;1]%sym^^(b*2))
    (3+a*2-e) n (a+n+3+k) e
    -[tm]->* section [9+a*4+n-e;19+a*4+n*8+b*2-e*2;1+u*2].
Proof.
  intros HP He Hn Hk Hu Ht; unfold section; cbn[section_side negb].
  applys_eq (negativeN_large_late (3+a*2-e) n e (a+n+3) k
    (3+a*2-e-(2+n*2)) (1+a-n-e) (5+n*3+a-e) b ((5+n*3+a-e)-k) u);
    try solve [flia]; exact HP.
Qed.

Lemma lone_positive a n e b t:
  P (3+a*2-e) -> e<=1 -> n<=a -> 3<=t -> t+b*2=11+a*4 ->
  loneN (0inf <* <[0;1]%sym^^t <* <[0;1;1]%sym^^(b*2)) (3+a*2-e) n e
    -[tm]->* section [9+a*4+n-e;10+a*4;9+n*8+b*2-e*2].
Proof.
  intros HP He Hn Ht HE; unfold section; cbn[section_side negb].
  destruct (Nat.le_gt_cases (3+n*5+b) a) as [Hcross|Hroot].
  - destruct e as [|[|e]]; try lia.
    + applys_eq (loneN_odd a n b (a-3-n*5-b) t);
        try solve [flia]; applys_eq HP; flia.
    + applys_eq (loneN_even a n b (a-3-n*5-b) t);
        try solve [flia]; applys_eq HP; flia.
  - destruct e as [|[|e]]; try lia.
    + applys_eq (loneN_root_odd a n b (a-n) ((t-3)/2) (n*5+b+2-a));
        try solve [flia]; applys_eq HP; flia.
    + applys_eq (loneN_root_even a n b (a-n) ((t-3)/2) (n*5+b+2-a));
        try solve [flia]; applys_eq HP; flia.
Qed.

Inductive Repair (p e A delta B:nat): list nat->Prop :=
| Repair_positive x: 1<=x -> x+delta*2=B+A*4+3 ->
    Repair p e A delta B [next_p p+A/2;p*2+delta*2+2;x]
| Repair_negative x: 1<=x -> B+A*4+3+x=delta*2 ->
    Repair p e A delta B [next_p p+A/2;p*2+A*4+B+5;x].

Lemma wide_section p e A delta B t xs:
  P p -> 3<=p -> e<=1 -> p mod 2+e=1 ->
  2<=A -> A<=p -> A mod 2=0 -> 2<=B -> B mod 2=0 ->
  1+e<=delta -> (delta+e) mod 2=1 -> delta<p*2+A*4+7+e ->
  t+B=p*2+4+e+delta -> (delta=1+e -> 3<=t) -> Repair p e A delta B xs ->
  section [p;A;p+A+delta;B;t] -[tm]->* section xs.
Proof.
  intros HP Hp He Hpar HA HAp HAe HB HBe HD HDe HDhi Hbal Hlone HR.
  assert (exists a n b,p=3+a*2-e /\ A=2+n*2 /\ B=b*2 /\ n<=a)
    as [a [n [b [-> [-> [-> Hn]]]]]].
  { exists ((p+e-3)/2),((A-2)/2),(B/2); repeat split; lia. }
  destruct (Nat.eq_dec delta (1+e)) as [->|Hdelta].
  - mid (loneN (0inf <* <[0;1]%sym^^t <* <[0;1;1]%sym^^(b*2)) (3+a*2-e) n e).
    + unfold section; cbn[section_side negb]; destruct e as [|[|e]]; try lia.
      * applys_eq (loneN_first_odd (0inf <* <[0;1]%sym^^t <* <[0;1;1]%sym^^(b*2)) a n);
          try solve [flia]; applys_eq HP; flia.
      * applys_eq (loneN_first_even (0inf <* <[0;1]%sym^^t <* <[0;1;1]%sym^^(b*2)) a n);
          try solve [flia]; applys_eq HP; flia.
    + destruct HR; try lia; unfold next_p.
      applys_eq (lone_positive a n e b t HP He Hn); flia.
  - assert (exists d,delta=3+e+d*2) as [d ->].
    { exists ((delta-3-e)/2); lia. }
    mid (negativeN (0inf <* <[0;1]%sym^^t <* <[0;1;1]%sym^^(b*2)) (3+a*2-e) n d e).
    + unfold section; cbn[section_side negb]; destruct e as [|[|e]]; try lia.
      * applys_eq (negativeN_first_odd (0inf <* <[0;1]%sym^^t <* <[0;1;1]%sym^^(b*2)) a n d);
          try solve [flia]; applys_eq HP; flia.
      * applys_eq (negativeN_first_even (0inf <* <[0;1]%sym^^t <* <[0;1;1]%sym^^(b*2)) a n d);
          try solve [flia]; applys_eq HP; flia.
    + destruct HR as [x Hx Hex|x Hx Hex]; unfold next_p;
        assert (Ex:x=1+((x-1)/2)*2) by lia;
        destruct (Nat.le_gt_cases d (a+n+3)) as [Hsmall|Hlarge].
      * applys_eq (negative_positive_small a n e d b t ((x-1)/2) HP He Hn); flia.
      * applys_eq (negative_positive_large a n e (d-(a+n+3)) b t ((x-1)/2) HP He Hn); flia.
      * applys_eq (negative_negative_small a n e d b t ((x-1)/2) HP He Hn); flia.
      * applys_eq (negative_negative_large a n e (d-(a+n+3)) b t ((x-1)/2) HP He Hn); flia.
Qed.

Lemma Repair_total p e A delta B: B mod 2=0 ->
  exists xs, Repair p e A delta B xs.
Proof.
  intro HB; destruct (Nat.le_gt_cases (delta*2) (B+A*4+3)).
  - eexists; apply Repair_positive with (x:=B+A*4+3-delta*2); lia.
  - eexists; apply Repair_negative with (x:=delta*2-(B+A*4+3)); lia.
Qed.

Lemma wide_triple p e k b t xs:
  P p -> 3<=p -> e<=1 -> p mod 2+e=1 -> 2<=k -> k<=p -> k mod 2=0 ->
  2<=b -> b mod 2=0 -> 3<=t -> t mod 2=1 -> p+k<b -> t+k<=p+b+e ->
  b-(p+k)<p*2+k*4+7+e ->
  Repair p e k (b-(p+k)) (t-1) xs -> section [p+k;b;t] -[tm]->+ section xs.
Proof.
  intros HP Hp He Hpar Hk Hkp Hke Hb Hbe Ht Hte Hbn Hcap Hdelta HR.
  destruct (even_parameters _ _ _ _ He Hpar Hk Hkp Hke Hb Hbe)
    as [g [j [d [Ek [Eb Ep]]]]].
  assert (Ett:t=3+((t-3)/2)*2) by lia.
  eapply progress_evstep_trans with (c':=section [p;k;b;t-1;p+b+5+e-k-t]).
  - rewrite Ek,Eb,Ep,Ett.
    applys_eq (gap_normal_section g j d (1-e) [] (j+d) ((t-3)/2));
      cbn[column_list app]; try solve [flia]; first [constructor|applys_eq HP; flia].
  - applys_eq (wide_section p e k (b-(p+k)) (t-1) (p+b+5+e-k-t) xs HP Hp He Hpar);
      try solve [flia]; exact HR.
Qed.

Local Open Scope nat_scope.

Lemma short_overflow_output p e k b:
  3<=p -> e<=1 -> p mod 2+e=1 -> 2<=k -> k<=p -> k mod 2=0 -> k<=b ->
  last_output (p+b*2+4+e-k) (p+k)=[p+k;p+k+2+e;(b-k)*2+2].
Proof.
  intros Hp He Hpar Hk Hkp Hke Hb.
  unfold last_output; assert (E:1-(p+k) mod 2=e) by lia; rewrite E.
  assert (Et:(p+b*2+4+e-k) mod 2=1) by lia; rewrite Et.
  repeat match goal with |- context[?a<=? ?b] =>
    let E:=fresh "E" in destruct (a<=?b) eqn:E;
    [apply Nat.leb_le in E|apply Nat.leb_gt in E] end;
    try lia; repeat (f_equal; try lia).
Qed.

Lemma even_short_clean p e k b xs:
  Chain p -> e<=1 -> p mod 2+e=1 -> 2<=k -> k<=p -> k mod 2=0 ->
  b mod 2=0 -> k<=b ->
  CleanLast (p+k*2) (next_p p+k/2) ((b-k)*2+2) xs ->
  section [p+k;b;1] -[tm]->+ section xs.
Proof.
  intros HChain He Hpar Hk Hkp Hke Hb Hbk HC.
  destruct (Chain_spec _ HChain) as [Hp [HP _]].
  eapply progress_trans; [apply even_short_section; eauto|].
  eapply progress_trans with (c':=section [p+k;p+k+2+e;(b-k)*2+2]).
  - rewrite <-(short_overflow_output p e k b Hp He Hpar Hk Hkp Hke Hbk).
    apply good_section_formula; auto; lia.
  - apply (even_odd_section p (1-e) k (p+k+2+e) ((b-k)*2+2) xs HP);
      try lia; unfold next_p in HC; applys_eq HC; flia.
Qed.

Lemma short_repair p e k b xs:
  Chain p -> e<=1 -> p mod 2+e=1 -> 2<=k -> k<=p -> k mod 2=0 ->
  b mod 2=0 -> p+k<b -> Repair p e k (b-(p+k)) 0 xs ->
  section [p+k;b;1] -[tm]->+ section xs.
Proof.
  intros HChain He Hpar Hk Hkp Hke Hb Hbn HR.
  destruct (Chain_spec _ HChain) as [Hp [HP _]].
  apply (even_short_clean p e k b xs HChain He Hpar Hk Hkp Hke Hb (ltac:(lia))).
  destruct HR as [x Hx HE|x Hx HE]; unfold next_p in *.
  - destruct (Nat.eq_dec x 1) as [->|Hx1].
    + applys_eq (CleanBorder (p+k*2) (p*2+2+(1-p mod 2)+k/2)); flia.
    + applys_eq (CleanEven (p+k*2) (p*2+2+(1-p mod 2)+k/2) (b-k)); flia.
  - applys_eq (CleanOver (p+k*2) (p*2+2+(1-p mod 2)+k/2) x); flia.
Qed.

Lemma halving_step p e k d t xs:
  Chain p -> e<=1 -> p mod 2+e=1 -> 2<=k -> k*4<=p -> k mod 2=0 ->
  1<=d -> d<=p*2 -> (p+d) mod 2=0 -> 1<=t -> t mod 2=1 -> t<=p*2+d+e ->
  Repair p e k d (t-1) xs ->
  section [p+k;p+k+d;t] -[tm]->+ section xs.
Proof.
  intros HChain He Hpar Hk Hkp Hke Hd Hdp Hde Ht Hte Hcap HR.
  destruct (Chain_spec _ HChain) as [Hp [HP _]].
  destruct (Nat.eq_dec t 1) as [->|Ht1].
  - apply (short_repair p e k (p+k+d) xs HChain He Hpar Hk (ltac:(lia)) Hke);
      try lia; applys_eq HR; flia.
  - apply (wide_triple p e k (p+k+d) t xs HP Hp He Hpar Hk (ltac:(lia)) Hke);
      try lia; applys_eq HR; flia.
Qed.

Inductive Safe: list nat->Prop :=
| Safe_core xs: Core xs -> Safe xs
| Safe_stair p e xs: Chain p -> e<=1 -> Stair p e xs -> Safe xs
| Safe_half p k d t: Chain p -> 2<=k -> k*4<=p -> k mod 2=0 ->
    1<=d -> d<=p*2 -> (p+d) mod 2=0 -> 1<=t -> t mod 2=1 ->
    t<=p*2+d+(1-p mod 2) -> Safe [p+k;p+k+d;t].

Lemma near_core p e k b t:
  Chain p -> e<=1 -> p mod 2+e=1 -> 1<=k -> k*4<=p ->
  p<b -> b<=p+k -> b mod 2=0 -> 1<=t -> t mod 2=1 -> t+k<=p+b+e ->
  exists ys, section [p+k;b;t] -[tm]->+ section ys /\ Safe ys.
Proof.
  intros HChain He Hpar Hk Hkp Hb Hbn Hbe Ht Hte Hcap.
  destruct (Chain_spec _ HChain) as [Hp [HP _]].
  destruct (Nat.eq_dec (k mod 2) 1) as [Hko|Hke].
  - destruct (odd_even_core p e k b t HChain He Hpar Hko (ltac:(lia))
      (ltac:(lia)) Hbe Hte Hcap) as [ys [HT HY]].
    exists ys; split; [exact HT|apply Safe_core,HY].
  - assert (Hk0:k mod 2=0) by lia.
    destruct (Nat.eq_dec t 1) as [->|Ht1].
    + exists [next_p p+k/2;(b-k)*2+2;3+(p+k*2-(b-k))*2]; split.
      * apply (even_short_clean p e k b _ HChain He Hpar (ltac:(lia))
          (ltac:(lia)) Hk0 Hbe (ltac:(lia))).
        applys_eq (CleanEven (p+k*2) (next_p p+k/2) (b-k)); flia.
      * apply Safe_core,Core_entry,(Entry_small (next_p p)); unfold next_p; try lia.
        split; [apply ChainS,HChain|unfold next_p; lia].
    + destruct (even_normal_section p e k b t HP He Hpar (ltac:(lia))
        (ltac:(lia)) Hk0 (ltac:(lia)) Hbe (ltac:(lia)) Hte Hbn Hcap) as [ys [HT HY]].
      exists ys; split; [exact HT|exact (Safe_stair p (1-e) ys HChain (ltac:(lia)) HY)].
Qed.

Lemma halving_progress p k d t:
  Chain p -> 2<=k -> k*4<=p -> k mod 2=0 -> 1<=d -> d<=p*2 ->
  (p+d) mod 2=0 -> 1<=t -> t mod 2=1 -> t<=p*2+d+(1-p mod 2) ->
  exists ys, section [p+k;p+k+d;t] -[tm]->+ section ys /\ Safe ys.
Proof.
  intros HChain Hk Hkp Hke Hd Hdp Hde Ht Hte Hcap.
  destruct (Chain_spec _ HChain) as [Hp [HP _]].
  set (e:=1-p mod 2).
  assert (e<=1 /\ p mod 2+e=1) as [He Hpar] by (unfold e; lia).
  destruct (Repair_total p e k d (t-1) (ltac:(lia))) as [xs HR].
  pose proof (halving_step p e k d t xs HChain He Hpar Hk Hkp Hke Hd Hdp Hde Ht Hte Hcap HR) as HT.
  set (P:=next_p p); set (K:=k/2).
  assert (EP:P=p*2+2+e) by (unfold P,next_p,e; lia).
  assert (HPpar:P mod 2+(1-e)=1) by lia.
  assert (HC:Chain P) by (apply ChainS,HChain).
  assert (1<=K /\ K*4<=P /\ k=K*2) as [HK [HKP EK]] by (unfold K; lia).
  destruct HR as [x Hx Hex|x Hx Hex].
  - set (B:=p*2+d*2+2).
    assert (HBe:B mod 2=0) by (unfold B; lia).
    assert (x mod 2=1 /\ x+K<=P+B+(1-e)) as [HX Hcap'] by (unfold B; lia).
    destruct (Nat.eq_dec (K mod 2) 1) as [Hko|Hke'].
    + destruct (odd_even_core P (1-e) K B x HC (ltac:(lia)) HPpar Hko
        (ltac:(lia)) (ltac:(unfold B; lia)) HBe HX Hcap') as [ys [HY HZ]].
      exists ys; split; [eapply progress_trans; eauto|apply Safe_core,HZ].
    + assert (HK0:K mod 2=0) by lia.
      destruct (Nat.le_gt_cases B (P+K)) as [Hnear|Hfar].
      * destruct (near_core P (1-e) K B x HC (ltac:(lia)) HPpar HK HKP
          (ltac:(unfold B; lia)) Hnear HBe Hx HX Hcap') as [ys [HY HZ]].
        exists ys; split; [eapply progress_trans; eauto|exact HZ].
      * exists [P+K;B;x]; split; [exact HT|].
        applys_eq (Safe_half P K (B-(P+K)) x HC); unfold B,next_p,e in *; flia.
  - assert (HX:x mod 2=1) by lia.
    destruct (recovery_core P K (p*2+k*4+(t-1)+5) x HC HK HKP
      (ltac:(lia)) Hx HX (ltac:(unfold next_p; lia)) (ltac:(lia))) as [ys [HY HZ]].
    exists ys; split; [eapply progress_trans; eauto|apply Safe_core,HZ].
Qed.

Lemma Safe_progress:
  (forall xs, Core xs -> exists ys, section xs -[tm]->+ section ys /\ Safe ys) ->
  forall xs, Safe xs -> exists ys, section xs -[tm]->+ section ys /\ Safe ys.
Proof.
  intros Hcore xs H; destruct H as [xs H|p e xs HP He H|p k d t HP Hk Hkp Hke Hd Hdp Hde Ht Hte Hcap].
  - apply Hcore,H.
  - destruct (Stair_progress p e xs HP He H) as [ys [HT [HY|HY]]]; exists ys;
      split; [exact HT|exact (Safe_stair p e ys HP He HY)|exact HT|apply Safe_core,Core_entry,HY].
  - apply halving_progress; assumption.
Qed.

Local Open Scope nat_scope.

Lemma clean_small_core p X N t: Chain p -> p<=X -> t mod 2=0 -> t<=p ->
  t<N*2+5 -> N*2+5<=X*8 ->
  exists xs, CleanLast N X t xs /\ Core xs.
Proof.
  intros HP HX Hte Htp Ht HN.
  destruct (Band_above p X HP HX) as [q [Hq HQ]].
  destruct (CleanLast_total N X t) as [xs HC].
  exists xs; split; [exact HC|].
  destruct HC; try lia; apply Core_entry; try constructor;
    apply (Entry_small q); auto; lia.
Qed.

Lemma even_overflow_core p e k b t:
  Chain p -> e<=1 -> p mod 2+e=1 -> 2<=k -> k<=p -> k mod 2=0 ->
  2<=b -> b mod 2=0 -> t mod 2=1 -> b<=p+k -> p+b+e<t+k ->
  t+k<=p+b+2+e+next_p p ->
  exists ys, section [p+k;b;t] -[tm]->+ section ys /\ Core ys.
Proof.
  intros HChain He Hpar Hk Hkp Hke Hb Hbe Hte Hbn Hcap Hmax.
  destruct (Chain_spec _ HChain) as [Hp [HP _]].
  destruct (clean_small_core (next_p p) (next_p p+b/2) (p+b*2)
    (t+k-(p+b+2+e)) (ChainS _ HChain)) as [ys [HC HY]]; try (unfold next_p in *; lia).
  exists ys; split; [apply (even_overflow_section p e k b t ys); assumption|exact HY].
Qed.

Lemma odd_even_bounded_core p e k b t:
  Chain p -> e<=1 -> p mod 2+e=1 -> k mod 2=1 -> k<=p+e ->
  2<=b -> b mod 2=0 -> t mod 2=1 -> t+k<=p*3+b+6+e ->
  exists ys, section [p+k;b;t] -[tm]->+ section ys /\ Core ys.
Proof.
  intros HChain He Hpar Hk Hkp Hb Hbe Hte Hcap.
  destruct (Chain_spec _ HChain) as [Hp [HP _]].
  pose proof (odd_even_section p e k b t HP Hp He Hpar Hk Hkp Hbe Hte) as Hstep.
  unfold odd_output in Hstep; destruct (t <? p+2+e-k) eqn:E.
  - apply Nat.ltb_lt in E.
    destruct (good_bounded_core p (b+k+t) (p+2+e-k-t) HChain (ltac:(lia)))
      as [ys [HT HY]].
    exists ys; split; [eapply progress_trans; eauto|exact HY].
  - apply Nat.ltb_ge in E.
    destruct (good_bounded_core p (p+b+2+e) (t-(p+2+e-k)) HChain (ltac:(lia)))
      as [ys [HT HY]].
    exists ys; split; [eapply progress_trans; eauto|exact HY].
Qed.

Lemma bounded_small_advance p e k b t:
  Chain p -> e<=1 -> p mod 2+e=1 -> 1<=k -> k*4<=p -> p<b -> b<=p+3 ->
  b mod 2=0 -> 1<=t -> t mod 2=1 -> t<=k*8+1 ->
  exists ys, section [p+k;b;t] -[tm]->+ section ys /\ Safe ys.
Proof.
  intros HChain He Hpar Hk Hkp Hb Hbhi Hbe Ht Hte Hthi.
  destruct (Chain_spec _ HChain) as [Hp [HP _]].
  destruct (Nat.eq_dec (k mod 2) 1) as [Hko|Hke].
  - destruct (odd_even_bounded_core p e k b t HChain He Hpar Hko (ltac:(lia))
      (ltac:(lia)) Hbe Hte (ltac:(lia))) as [ys [HT HY]].
    exists ys; split; [exact HT|apply Safe_core,HY].
  - assert (Hk0:k mod 2=0) by lia.
    destruct (Nat.le_gt_cases b (p+k)) as [Hnear|Hfar].
    + destruct (Nat.le_gt_cases (t+k) (p+b+e)) as [Hcap|Hover].
      * apply (near_core p e k b t HChain He Hpar Hk Hkp Hb Hnear Hbe Ht Hte Hcap).
      * destruct (even_overflow_core p e k b t HChain He Hpar (ltac:(lia))
          (ltac:(lia)) Hk0 (ltac:(lia)) Hbe Hte Hnear Hover
          (ltac:(unfold next_p; lia))) as [ys [HT HY]].
        exists ys; split; [exact HT|apply Safe_core,HY].
    + replace b with (p+k+(b-(p+k))) by lia.
      apply halving_progress; auto; lia.
Qed.

Lemma short_diagonal_safe p e k:
  Chain p -> e<=1 -> p mod 2+e=1 -> 2<=k -> k<=p -> k mod 2=0 ->
  exists ys, section [p+k;p+k+1+e;1] -[tm]->+ section ys /\ Safe ys.
Proof.
  intros HChain He Hpar Hk Hkp Hke.
  destruct (Chain_spec _ HChain) as [Hp [HP _]].
  set (P:=next_p p); set (K:=k/2).
  assert (EP:P=p*2+2+e) by (unfold P,next_p; lia).
  assert (HC:Chain P) by (apply ChainS,HChain).
  assert (ET:section [p+k;p+k+1+e;1] -[tm]->+ section [P+K;P+2+e;k*4+1-e*2]).
  { apply (even_short_clean p e k (p+k+1+e) _ HChain He Hpar Hk Hkp Hke
      (ltac:(lia)) (ltac:(lia))).
    applys_eq (CleanEven (p+k*2) (next_p p+k/2) (p+1+e)); unfold P,K; flia. }
  destruct (bounded_small_advance P (1-e) K (P+2+e) (k*4+1-e*2) HC)
    as [ys [HT HY]]; try (unfold K; lia).
  exists ys; split; [eapply progress_trans; eauto|exact HY].
Qed.

Lemma predecessor_core p b t: Chain p -> 2<=b -> b mod 2=0 -> 1<=t -> t mod 2=1 ->
  t<next_p p+3+(1-next_p p mod 2) ->
  exists ys, section [next_p p-1;b;t] -[tm]->+ section ys /\ Core ys.
Proof.
  intros HChain Hb Hbe Ht Hte Hhi.
  pose proof (next_p_grows p) as HP.
  pose proof (predecessor_section p b t HChain Hb Hbe Hte) as HT.
  unfold pred_output in HT.
  replace (next_p p-1+4+(next_p p-1) mod 2) with (next_p p+3+(1-next_p p mod 2)) in HT by lia.
  assert (E:(t <? next_p p+3+(1-next_p p mod 2))=true) by (apply Nat.ltb_lt; lia).
  rewrite E in HT.
  replace (1+(next_p p-1)) with (next_p p) in HT by lia.
  destruct (good_bounded_core (next_p p) (b+t-1) (next_p p+3+(1-next_p p mod 2)-t)
    (ChainS _ HChain) (ltac:(lia))) as [ys [HY HZ]].
  exists ys; split; [eapply progress_trans; eauto|exact HZ].
Qed.

Lemma diagonal_progress n b t: 3<=n -> Diagonal n b t ->
  exists ys, section [n;b;t] -[tm]->+ section ys /\ Safe ys.
Proof.
  intros Hn [Hb [Hbe [Ht [Hte Hsum]]]].
  destruct (Band_total n Hn) as [p [HChain [Hlo Hhi]]].
  destruct (Chain_spec _ HChain) as [Hp [HP _]].
  set (e:=1-p mod 2); set (k:=n-p).
  assert (e<=1 /\ p mod 2+e=1) as [He Hpar] by (unfold e; lia).
  assert (En:n=p+k) by (unfold k; lia).
  clearbody k.
  destruct (Nat.eq_dec k 0) as [Hk0|Hk0].
  - assert (Enp:n=p) by lia; rewrite Enp.
    destruct (good_bounded_core p b t HChain (ltac:(lia))) as [ys [HT HY]].
    exists ys; split; [exact HT|apply Safe_core,HY].
  - destruct (Nat.eq_dec n (next_p p-1)) as [Enp|Enp].
    + rewrite Enp.
      destruct (predecessor_core p b t HChain Hb Hbe Ht Hte
        (ltac:(unfold next_p in *; lia))) as [ys [HT HY]].
      exists ys; split; [exact HT|apply Safe_core,HY].
    + rewrite En; unfold next_p in Hhi.
      destruct (Nat.eq_dec (k mod 2) 1) as [Hko|Hke].
      * destruct (odd_even_bounded_core p e k b t HChain He Hpar Hko (ltac:(unfold next_p in Enp; lia))
          Hb Hbe Hte (ltac:(lia))) as [ys [HT HY]].
        exists ys; split; [exact HT|apply Safe_core,HY].
      * assert (2<=k /\ k<=p /\ k mod 2=0) as [Hk [Hkp Hke0]]
          by (unfold next_p in Enp; lia).
        destruct (Nat.eq_dec t 1) as [->|Ht1].
        -- replace b with (p+k+1+e) by lia.
           apply short_diagonal_safe; assumption.
        -- assert (Hbn:b<=p+k) by lia.
           destruct (Nat.le_gt_cases (t+k) (p+b+e)) as [Hcap|Hover].
           ++ destruct (even_normal_section p e k b t HP He Hpar Hk Hkp Hke0 Hb Hbe
                (ltac:(lia)) Hte Hbn Hcap) as [ys [HT HY]].
              exists ys; split; [exact HT|exact (Safe_stair p (1-e) ys HChain (ltac:(lia)) HY)].
           ++ destruct (even_overflow_core p e k b t HChain He Hpar Hk Hkp Hke0 Hb Hbe Hte Hbn Hover
                (ltac:(unfold next_p; lia))) as [ys [HT HY]].
              exists ys; split; [exact HT|apply Safe_core,HY].
Qed.


(* The low exit of an even cleanup tail needs no further symbolic search. *)
Lemma small_cleanup_low p k b t:
  Chain p -> 1<=k -> k*4<=p -> 2<=b -> b mod 2=0 ->
  1<=t -> t mod 2=1 -> b+t=p+k*8+2+(1-p mod 2) ->
  exists ys, section [p+k;b;t] -[tm]->* section ys /\ Safe ys.
Proof.
  intros HC Hk Hkp Hb Hbe Ht Hte Hsum.
  destruct (Chain_spec p HC) as [Hp [HP _]].
  set (e:=1-p mod 2).
  assert (e<=1 /\ p mod 2+e=1) as [He Hpe] by (unfold e; lia).
  destruct (Nat.le_gt_cases b p) as [Hsmall|Hlarge].
  - exists [p+k;b;t]; split; [constructor|].
    apply Safe_core,Core_entry,(Entry_small p); try lia.
    split; [exact HC|unfold next_p; lia].
  - destruct (Nat.eq_dec (k mod 2) 1) as [Hko|Hke].
    + destruct (odd_even_bounded_core p e k b t HC He Hpe Hko
        (ltac:(lia)) Hb Hbe Hte (ltac:(unfold e in *; lia))) as [ys [HT HY]].
      exists ys; split; [apply progress_evstep,HT|apply Safe_core,HY].
    + assert (k mod 2=0 /\ 2<=k) as [Hke0 Hk2] by lia.
      destruct (Nat.le_gt_cases b (p+k)) as [Hnear|Hwide].
      * destruct (Nat.le_gt_cases (t+k) (p+b+e)) as [Hcap|Hover].
        -- destruct (near_core p e k b t HC He Hpe Hk Hkp Hlarge Hnear Hbe Ht Hte Hcap)
             as [ys [HT HY]]; exists ys; split; [apply progress_evstep,HT|exact HY].
        -- destruct (even_overflow_core p e k b t HC He Hpe Hk2 (ltac:(lia)) Hke0
             Hb Hbe Hte Hnear Hover (ltac:(unfold next_p,e in *; lia))) as [ys [HT HY]].
           exists ys; split; [apply progress_evstep,HT|apply Safe_core,HY].
      * exists [p+k;b;t]; split; [constructor|].
        applys_eq (Safe_half p k (b-(p+k)) t HC); unfold e in *; flia.
Qed.

Lemma cleanup_low_reaches p k N t xs:
  Chain p -> 1<=k -> k*4<=p ->
  N*2+5=p+k*8+2+(1-p mod 2) -> t mod 2=0 -> t<N*2+5 ->
  CleanLast N (p+k) t xs ->
  exists ys, section xs -[tm]->* section ys /\ Safe ys.
Proof.
  intros HC Hk Hkp Hsum Hte Ht HL; destruct HL; try lia.
  - exists [p+k+5+N*2]; split; [constructor|apply Safe_core,Core_entry,Entry_unary].
  - apply (small_cleanup_low p k); auto; lia.
  - apply (small_cleanup_low p k); auto; lia.
Qed.

(* The remaining high exit is a three-parameter family, not an arbitrary
   triple. No closure claim for this family is made here. *)
Inductive HighExit: list nat->Prop :=
| High_exit p k t:
    Chain p -> 1<=k -> k*4<=p -> 1<=t -> t mod 2=1 ->
    t+k*12+2+(1-p mod 2)<=p*7 ->
    HighExit [p+k;p+k*8+2+(1-p mod 2);t].
Definition EntryExit xs := Safe xs \/ HighExit xs.

Lemma cleanup_entry_exit p k N t xs:
  Chain p -> 1<=k -> k*4<=p ->
  N*2+5=p+k*8+2+(1-p mod 2) -> t mod 2=0 -> t+k*4<=p*8 ->
  CleanLast N (p+k) t xs ->
  exists ys, section xs -[tm]->* section ys /\ EntryExit ys.
Proof.
  intros HC Hk Hkp Hsum Hte Hcap HL.
  destruct (Nat.lt_ge_cases t (N*2+5)) as [Hlow|Hhigh].
  - destruct (cleanup_low_reaches p k N t xs HC Hk Hkp Hsum Hte Hlow HL)
      as [ys [HT HY]]; exists ys; split; [exact HT|left; exact HY].
  - destruct HL; try lia.
    exists [p+k;5+N*2;a]; split; [constructor|right].
    replace (5+N*2) with (p+k*8+2+(1-p mod 2)) by lia.
    apply High_exit; auto; lia.
Qed.

Lemma post_good_cleanup p e b t xs:
  P p -> e<=1 -> p mod 2+e=1 -> 2<=b -> b<=p -> b mod 2=0 ->
  CleanLast (p+b*2) (next_p p+b/2) t xs ->
  section [p+b;p+b+2+e;t] -[tm]->+ section xs.
Proof.
  intros HP He Hpe Hb Hbp Hbe HL.
  apply (even_odd_section p (1-e) b (p+b+2+e) _ xs HP); try lia.
  applys_eq HL; unfold next_p; flia.
Qed.

Lemma good_even_cleanup p e b t xs:
  P p -> 3<=p -> e<=1 -> p mod 2+e=1 ->
  2<=b -> b<=p -> b mod 2=0 -> p+b+1+e<t ->
  CleanLast (p+b*2) (next_p p+b/2) (t-(p+b+2+e)) xs ->
  section [p;b;t] -[tm]->+ section xs.
Proof.
  intros HP Hp He Hpe Hb Hbp Hbe Ht HL.
  pose proof (good_section_formula p b t HP (ltac:(lia))) as HT.
  assert (E:last_output t (p+b)=[p+b;p+b+2+e;t-(p+b+2+e)]).
  { unfold last_output.
    replace (1-(p+b) mod 2) with e by lia.
    repeat match goal with |- context[?a<=? ?b] =>
      let F:=fresh "F" in destruct (a<=?b) eqn:F;
      [apply Nat.leb_le in F|apply Nat.leb_gt in F] end; try lia; reflexivity. }
  rewrite E in HT; eapply progress_trans; [exact HT|].
  apply (post_good_cleanup p e b _ xs HP He Hpe Hb Hbp Hbe HL).
Qed.

Lemma mixed_good_entry p b t:
  Chain p -> 2<=b -> b<=p -> b mod 2=0 -> t mod 2=1 -> b+t<=p*18 ->
  exists ys, section [p;p+b+2+(1-p mod 2);t] -[tm]->+ section ys /\ EntryExit ys.
Proof.
  intros HC Hb Hbp Hbe Hte Hsum.
  destruct (Chain_spec p HC) as [Hp [HP _]].
  set (e:=1-p mod 2); set (q:=next_p p).
  assert (HQ:Chain q) by (apply ChainS,HC).
  destruct (Chain_spec q HQ) as [Hq [HPq _]].
  assert (He:e<=1 /\ p mod 2+e=1 /\ q mod 2=e) by (unfold q,next_p,e; lia).
  destruct (good_core_or_overflow p (p+b+2+e) t HC (ltac:(lia)))
    as [xs [HT [HY|[u [EX EU]]]]].
  - exists xs; split; [exact HT|left; apply Safe_core,HY].
  - subst xs.
    replace (p+(p+b+2+e)) with (q+b) in HT,EU by (unfold q,next_p,e; lia).
    replace (1-(q+b) mod 2) with (1-e) in HT,EU by lia.
    destruct (CleanLast_total (q+b*2) (next_p q+b/2) u) as [zs HL].
    pose proof (post_good_cleanup q (1-e) b u zs HPq (ltac:(lia)) (ltac:(lia))
      Hb (ltac:(unfold q,next_p; lia)) Hbe HL) as HU.
    destruct (cleanup_entry_exit (next_p q) (b/2) (q+b*2) u zs (ChainS q HQ))
      as [ys [HV HY]]; try (unfold q,next_p,e in *; lia); try exact HL.
    exists ys; split; [eapply progress_trans; [exact HT|]; eapply progress_evstep_trans; eauto|exact HY].
Qed.

Lemma odd_entry_exit p k b t:
  Chain p -> k mod 2=1 -> k<=p+(1-p mod 2) ->
  2<=b -> b<=p -> b mod 2=0 -> t mod 2=1 -> b+t<=(p+k)*8 ->
  exists ys, section [p+k;b;t] -[tm]->+ section ys /\ EntryExit ys.
Proof.
  intros HC Hko Hkp Hb Hbp Hbe Hte Hsum.
  destruct (Chain_spec p HC) as [Hp [HP _]].
  set (e:=1-p mod 2).
  assert (e<=1 /\ p mod 2+e=1) as [He Hpe] by (unfold e; lia).
  pose proof (odd_even_section p e k b t HP Hp He Hpe Hko Hkp Hbe Hte) as HT.
  unfold odd_output in HT; destruct (t <? p+2+e-k) eqn:E.
  - apply Nat.ltb_lt in E.
    destruct (good_bounded_core p (b+k+t) (p+2+e-k-t) HC (ltac:(lia))) as [ys [HU HY]].
    exists ys; split; [eapply progress_trans; eauto|left; apply Safe_core,HY].
  - apply Nat.ltb_ge in E.
    destruct (mixed_good_entry p b (t-(p+2+e-k)) HC Hb Hbp Hbe
      (ltac:(lia)) (ltac:(unfold e in *; lia))) as [ys [HU HY]].
    exists ys; split; [eapply progress_trans; eauto|exact HY].
Qed.

Lemma predecessor_entry_exit p b t:
  Chain p -> 2<=b -> b<=p -> b mod 2=0 -> t mod 2=1 -> b+t<=(next_p p-1)*8 ->
  exists ys, section [next_p p-1;b;t] -[tm]->+ section ys /\ EntryExit ys.
Proof.
  intros HC Hb Hbp Hbe Hte Hsum.
  pose proof (predecessor_section p b t HC Hb Hbe Hte) as HT.
  set (q:=next_p p); assert (HQ:Chain q) by (apply ChainS,HC).
  destruct (Chain_spec q HQ) as [Hq [HPq _]].
  fold q in HT,Hsum; unfold pred_output in HT.
  replace (1+(q-1)) with q in HT by lia.
  replace (q-1+4+(q-1) mod 2) with (q+3+(1-q mod 2)) in HT by lia.
  destruct (t <? q+3+(1-q mod 2)) eqn:E.
  - apply Nat.ltb_lt in E.
    destruct (good_bounded_core q (b+t-1) (q+3+(1-q mod 2)-t) HQ (ltac:(lia)))
      as [ys [HU HY]].
    exists ys; split; [eapply progress_trans; eauto|left; apply Safe_core,HY].
  - apply Nat.ltb_ge in E.
    replace (b+(q+3+(1-q mod 2))-1) with (q+b+2+(1-q mod 2)) in HT by lia.
    destruct (mixed_good_entry q b (t-(q+3+(1-q mod 2))) HQ Hb
      (ltac:(unfold q,next_p; lia)) Hbe (ltac:(lia)) (ltac:(lia))) as [ys [HU HY]].
    exists ys; split; [eapply progress_trans; eauto|exact HY].
Qed.

Lemma good_entry_exit p b t:
  Chain p -> 2<=b -> b<=p -> b mod 2=0 -> t mod 2=1 -> b+t<=p*8 ->
  exists ys, section [p;b;t] -[tm]->+ section ys /\ EntryExit ys.
Proof.
  intros HC Hb Hbp Hbe Hte Hsum.
  destruct (Chain_spec p HC) as [Hp [HP _]].
  set (e:=1-p mod 2).
  assert (e<=1 /\ p mod 2+e=1) as [He Hpe] by (unfold e; lia).
  destruct (Nat.le_gt_cases t (p+b+1+e)) as [Hlow|Hhigh].
  - destruct (good_bounded_core p b t HC (ltac:(unfold e in *; lia))) as [ys [HT HY]].
    exists ys; split; [exact HT|left; apply Safe_core,HY].
  - destruct (CleanLast_total (p+b*2) (next_p p+b/2) (t-(p+b+2+e))) as [xs HL].
    pose proof (good_even_cleanup p e b t xs HP Hp He Hpe Hb Hbp Hbe Hhigh HL) as HT.
    destruct (cleanup_entry_exit (next_p p) (b/2) (p+b*2) (t-(p+b+2+e)) xs
      (ChainS p HC)) as [ys [HU HY]]; try (unfold next_p,e in *; lia); try exact HL.
    exists ys; split; [eapply progress_evstep_trans; eauto|exact HY].
Qed.

Lemma even_entry_exit p k b t:
  Chain p -> 2<=k -> k<=p -> k mod 2=0 ->
  2<=b -> b<=p -> b mod 2=0 -> t mod 2=1 -> b+t<=(p+k)*8 ->
  exists ys, section [p+k;b;t] -[tm]->+ section ys /\ EntryExit ys.
Proof.
  intros HC Hk Hkp Hke Hb Hbp Hbe Hte Hsum.
  destruct (Chain_spec p HC) as [Hp [HP _]].
  set (e:=1-p mod 2).
  assert (e<=1 /\ p mod 2+e=1) as [He Hpe] by (unfold e; lia).
  destruct (Nat.eq_dec t 1) as [->|Ht1].
  - destruct (Nat.lt_ge_cases b k) as [Hsmall|Hlarge].
    + destruct (even_short_core p e k b HC He Hpe Hk Hkp Hke Hbe Hsmall)
        as [ys [HT HY]]; exists ys; split; [exact HT|left; apply Safe_core,HY].
    + destruct (CleanLast_total (p+k*2) (next_p p+k/2) ((b-k)*2+2)) as [xs HL].
      pose proof (even_short_clean p e k b xs HC He Hpe Hk Hkp Hke Hbe Hlarge HL) as HT.
      destruct (cleanup_entry_exit (next_p p) (k/2) (p+k*2) ((b-k)*2+2) xs
        (ChainS p HC)) as [ys [HU HY]]; try (unfold next_p,e in *; lia); try exact HL.
      exists ys; split; [eapply progress_evstep_trans; eauto|exact HY].
  - destruct (Nat.le_gt_cases (t+k) (p+b+e)) as [Hnormal|Hover].
    + destruct (even_normal_section p e k b t HP He Hpe Hk Hkp Hke Hb Hbe
        (ltac:(lia)) Hte (ltac:(lia)) Hnormal) as [ys [HT HY]].
      exists ys; split; [exact HT|left; apply (Safe_stair p (1-e)); auto; lia].
    + destruct (CleanLast_total (p+b*2) (next_p p+b/2) (t+k-(p+b+2+e))) as [xs HL].
      pose proof (even_overflow_section p e k b t xs HP He Hpe Hk Hkp Hke Hb Hbe
        Hte (ltac:(lia)) Hover HL) as HT.
      destruct (cleanup_entry_exit (next_p p) (b/2) (p+b*2) (t+k-(p+b+2+e)) xs
        (ChainS p HC)) as [ys [HU HY]]; try (unfold next_p,e in *; lia); try exact HL.
      exists ys; split; [eapply progress_evstep_trans; eauto|exact HY].
Qed.

Lemma entry_exit p n b t:
  Band p n -> 2<=b -> b<=p -> b mod 2=0 -> t mod 2=1 -> b+t<=n*8 ->
  exists ys, section [n;b;t] -[tm]->+ section ys /\ EntryExit ys.
Proof.
  intros [HC [Hpn Hnp]] Hb Hbp Hbe Hte Hsum.
  set (k:=n-p); assert (En:n=p+k) by (unfold k; lia); clearbody k.
  destruct (Nat.eq_dec k 0) as [Hk0|Hk0].
  - replace n with p in * by lia; apply good_entry_exit; assumption.
  - destruct (Nat.eq_dec n (next_p p-1)) as [Hpred|Hpred].
    + rewrite Hpred in Hsum |- *; apply predecessor_entry_exit; assumption.
    + rewrite En; destruct (Nat.eq_dec (k mod 2) 1) as [Hko|Hke].
      * apply odd_entry_exit; auto; unfold next_p in *; lia.
      * apply even_entry_exit; auto; unfold next_p in *; lia.
Qed.

Lemma core_entry_exit xs: Core xs ->
  exists ys, section xs -[tm]->+ section ys /\ EntryExit ys.
Proof.
  intro H; destruct H as [xs H|n b t Hn HD].
  - destruct H as [n|p n b t HB Hb Hbe Ht Hte Hbp Hsum].
    + destruct (unary_core_progress n) as [ys [HT HY]]; exists ys;
        split; [exact HT|left; apply Safe_core,HY].
    + apply (entry_exit p n b t HB Hb Hbp Hbe Hte Hsum).
  - destruct (diagonal_progress n b t Hn HD) as [ys [HT HY]];
      exists ys; split; [exact HT|left; exact HY].
Qed.

Lemma entry_exit_progress:
  (forall xs, HighExit xs -> exists ys, section xs -[tm]->+ section ys /\ EntryExit ys) ->
  forall xs, EntryExit xs -> exists ys, section xs -[tm]->+ section ys /\ EntryExit ys.
Proof.
  intros Hhigh xs [H|H]; [|apply Hhigh,H].
  destruct H as [xs H|p e xs HP He H|p k d t HP Hk Hkp Hke Hd Hdp Hde Ht Hte Hcap].
  - apply core_entry_exit,H.
  - destruct (Stair_progress p e xs HP He H) as [ys [HT [HY|HY]]];
      exists ys; split; try exact HT; left.
    + apply (Safe_stair p e ys HP He HY).
    + apply Safe_core,Core_entry,HY.
  - destruct (halving_progress p k d t HP Hk Hkp Hke Hd Hdp Hde Ht Hte Hcap)
      as [ys [HT HY]]; exists ys; split; [exact HT|left; exact HY].
Qed.

Lemma high_lower_progress p k t:
  Chain p -> 1<=k -> k*4<=p -> 1<=t -> t mod 2=1 ->
  t+k*8+6+(1-p mod 2)<=p*2 ->
  exists ys, section [p+k;p+k*8+2+(1-p mod 2);t] -[tm]->+ section ys /\ Safe ys.
Proof.
  intros HC Hk Hkp Ht Hte Hcap.
  destruct (recovery_core p k (p+k*8+2+(1-p mod 2)) t HC Hk Hkp
    (ltac:(lia)) Ht Hte (ltac:(lia)) (ltac:(lia))) as [ys [HT HY]].
  exists ys; split; [exact HT|apply Safe_core,HY].
Qed.


Lemma odd_post_good_finish p e k t:
  Chain p -> e<=1 -> p mod 2+e=1 -> k mod 2=1 -> k<=p+e ->
  t+e<=p+k*3+2 ->
  exists ys, section [p+k;p+k+2+(1-(p+k) mod 2);t] -[tm]->+ section ys /\ Core ys.
Proof.
  intros HC He Hpe Hko Hkp Hcap.
  destruct (Chain_spec p HC) as [Hp [HP _]].
  pose proof (odd_odd_section p e k (p+k+2+(1-(p+k) mod 2)) t
    HP Hp He Hpe Hko Hkp (ltac:(lia))) as HT.
  destruct (good_bounded_core p (p+k+2+(1-(p+k) mod 2)+k)
    (t+p+2+e-k) HC (ltac:(lia))) as [ys [HU HY]].
  exists ys; split; [eapply progress_trans; eauto|exact HY].
Qed.

Lemma odd_post_good_core p e k t:
  Chain p -> e<=1 -> p mod 2+e=1 -> k mod 2=1 -> k<=p+e -> t<=(p+k)*3 ->
  exists ys, section [p+k;p+k+2+(1-(p+k) mod 2);t] -[tm]->+ section ys /\ Core ys.
Proof.
  intros HC He Hpe Hko Hkp Hcap.
  destruct (Chain_spec p HC) as [Hp [HP _]].
  pose proof (odd_odd_section p e k (p+k+2+(1-(p+k) mod 2)) t
    HP Hp He Hpe Hko Hkp (ltac:(lia))) as HT.
  set (b:=p+k+2+(1-(p+k) mod 2)+k).
  fold b in HT.
  destruct (good_core_or_overflow p b (t+p+2+e-k) HC (ltac:(unfold b; lia)))
    as [xs [HU [HY|[u [EX EU]]]]].
  - exists xs; split; [eapply progress_trans; eauto|exact HY].
  - subst xs; set (q:=next_p p); set (j:=k*2+1-e*2).
    assert (HQ:Chain q) by (apply ChainS,HC).
    assert (E:p+b=q+j) by (unfold b,q,j,next_p; lia).
    rewrite E in HU,EU.
    destruct (odd_post_good_finish q (1-e) j u HQ)
      as [ys [HV HY]]; try (unfold q,j,b,next_p in *; lia).
    exists ys; split; [eapply progress_trans; [exact HT|]; eapply progress_trans; eauto|exact HY].
Qed.

Lemma post_good_even_entry p n t:
  Band p n -> n<>next_p p-1 -> t mod 2=0 -> t<=n*3 ->
  exists ys, section [n;n+2+(1-n mod 2);t] -[tm]->+ section ys /\ EntryExit ys.
Proof.
  intros [HC [Hpn Hnp]] Hpred Hte Hcap.
  destruct (Chain_spec p HC) as [Hp [HP _]].
  set (e:=1-p mod 2); set (k:=n-p).
  assert (e<=1 /\ p mod 2+e=1) as [He Hpe] by (unfold e; lia).
  assert (En:n=p+k) by (unfold k; lia); clearbody k.
  destruct (Nat.eq_dec k 0) as [Hk0|Hk0].
  - replace n with p in * by lia.
    destruct (good_core_or_overflow p (p+2+e) t HC (ltac:(lia)))
      as [xs [HT [HY|[u [EX EU]]]]].
    + exists xs; split; [exact HT|left; apply Safe_core,HY].
    + subst xs; replace (p+(p+2+e)) with (next_p p) in HT,EU by (unfold next_p,e; lia).
      destruct (good_bounded_core (next_p p) (next_p p+2+(1-next_p p mod 2)) u
        (ChainS p HC) (ltac:(unfold next_p in *; lia))) as [ys [HU HY]].
      exists ys; split; [eapply progress_trans; eauto|left; apply Safe_core,HY].
  - rewrite En; destruct (Nat.eq_dec (k mod 2) 1) as [Hko|Hke].
    + destruct (odd_post_good_core p e k t HC He Hpe Hko (ltac:(unfold next_p in *; lia))
        (ltac:(lia))) as [ys [HT HY]].
      exists ys; split; [exact HT|left; apply Safe_core,HY].
    + assert (2<=k /\ k<=p /\ k mod 2=0) as [Hk [Hkp Hke0]] by (unfold next_p in *; lia).
      replace (1-(p+k) mod 2) with e by lia.
      destruct (CleanLast_total (p+k*2) (next_p p+k/2) t) as [xs HL].
      pose proof (post_good_cleanup p e k t xs HP He Hpe Hk Hkp Hke0 HL) as HT.
      destruct (cleanup_entry_exit (next_p p) (k/2) (p+k*2) t xs (ChainS p HC))
        as [ys [HU HY]]; try (unfold next_p,e in *; lia); try exact HL.
      exists ys; split; [eapply progress_evstep_trans; eauto|exact HY].
Qed.

Lemma high_odd_progress p e k t:
  Chain p -> e<=1 -> p mod 2+e=1 -> 1<=k -> k*4<=p -> k mod 2=1 ->
  1<=t -> t mod 2=1 -> t+k*12+2+e<=p*7 ->
  exists ys, section [p+k;p+k*8+2+e;t] -[tm]->+ section ys /\ EntryExit ys.
Proof.
  intros HC He Hpe Hk Hkp Hko Ht Hte Hcap.
  destruct (Chain_spec p HC) as [Hp [HP _]].
  pose proof (odd_odd_section p e k (p+k*8+2+e) t HP Hp He Hpe Hko
    (ltac:(lia)) (ltac:(lia))) as HT.
  destruct (good_core_or_overflow p (p+k*8+2+e+k) (t+p+2+e-k) HC (ltac:(lia)))
    as [xs [HU [HY|[u [EX EU]]]]].
  - exists xs; split; [eapply progress_trans; eauto|left; apply Safe_core,HY].
  - subst xs; set (q:=next_p p).
    assert (HQ:Chain q) by (apply ChainS,HC).
    replace (p+(p+k*8+2+e+k)) with (q+k*9) in HU,EU by (unfold q,next_p; lia).
    assert (u<=(q+k*9)*3 /\ u mod 2=0) as [Hbound Hue] by (unfold q,next_p in *; lia).
    assert (HR:exists r,Band r (q+k*9) /\ q+k*9<>next_p r-1).
    { destruct (Nat.lt_ge_cases (q+k*9) (next_p q)) as [Hlo|Hhi].
      - exists q; split; [split; [exact HQ|unfold q,next_p in *; lia]|unfold q,next_p in *; lia].
      - exists (next_p q); split; [split; [apply ChainS,HQ|unfold q,next_p in *; lia]|unfold q,next_p in *; lia]. }
    destruct HR as [r [HB Hpred]].
    destruct (post_good_even_entry r (q+k*9) u HB Hpred Hue Hbound) as [ys [HV HY]].
    exists ys; split; [eapply progress_trans; [exact HT|]; eapply progress_trans; eauto|exact HY].
Qed.

Lemma small_cleanup_upper p k b t:
  Chain p -> 1<=k -> k*4+2<=p -> 2<=b -> b mod 2=0 ->
  1<=t -> t mod 2=1 -> b+t<=p+k*8+4+(1-p mod 2) ->
  exists ys, section [p+k;b;t] -[tm]->* section ys /\ Safe ys.
Proof.
  intros HC Hk Hkp Hb Hbe Ht Hte Hsum.
  destruct (Chain_spec p HC) as [Hp [HP _]].
  set (e:=1-p mod 2).
  assert (e<=1 /\ p mod 2+e=1) as [He Hpe] by (unfold e; lia).
  destruct (Nat.le_gt_cases b p) as [Hsmall|Hlarge].
  - exists [p+k;b;t]; split; [constructor|].
    apply Safe_core,Core_entry,(Entry_small p); try lia.
    split; [exact HC|unfold next_p; lia].
  - destruct (Nat.eq_dec (k mod 2) 1) as [Hko|Hke].
    + destruct (odd_even_bounded_core p e k b t HC He Hpe Hko
        (ltac:(lia)) Hb Hbe Hte (ltac:(unfold e in *; lia))) as [ys [HT HY]].
      exists ys; split; [apply progress_evstep,HT|apply Safe_core,HY].
    + assert (k mod 2=0 /\ 2<=k) as [Hke0 Hk2] by lia.
      destruct (Nat.le_gt_cases b (p+k)) as [Hnear|Hwide].
      * destruct (Nat.le_gt_cases (t+k) (p+b+e)) as [Hcap|Hover].
        -- destruct (near_core p e k b t HC He Hpe Hk (ltac:(lia)) Hlarge Hnear Hbe Ht Hte Hcap)
             as [ys [HT HY]]; exists ys; split; [apply progress_evstep,HT|exact HY].
        -- destruct (even_overflow_core p e k b t HC He Hpe Hk2 (ltac:(lia)) Hke0
             Hb Hbe Hte Hnear Hover (ltac:(unfold next_p,e in *; lia))) as [ys [HT HY]].
           exists ys; split; [apply progress_evstep,HT|apply Safe_core,HY].
      * exists [p+k;b;t]; split; [constructor|].
        applys_eq (Safe_half p k (b-(p+k)) t HC); unfold e in *; flia.
Qed.

Lemma small_near_reaches p k b t:
  Chain p -> 1<=k -> k*4<=p -> p<b -> b mod 2=0 ->
  1<=t -> t mod 2=1 -> b-(p+k)<=p*2 ->
  t+k<=p+b+2+(1-p mod 2)+next_p p ->
  (b<=p+k \/ t+k<=p+b+(1-p mod 2)) ->
  exists ys, section [p+k;b;t] -[tm]->* section ys /\ Safe ys.
Proof.
  intros HC Hk Hkp Hb Hbe Ht Hte Hdelta Hbound Hcap.
  destruct (Chain_spec p HC) as [Hp [HP _]].
  set (e:=1-p mod 2).
  assert (e<=1 /\ p mod 2+e=1) as [He Hpe] by (unfold e; lia).
  destruct (Nat.eq_dec (k mod 2) 1) as [Hko|Hke].
  - destruct (odd_even_bounded_core p e k b t HC He Hpe Hko (ltac:(lia))
      (ltac:(lia)) Hbe Hte (ltac:(unfold next_p,e in *; lia))) as [ys [HT HY]].
    exists ys; split; [apply progress_evstep,HT|apply Safe_core,HY].
  - assert (k mod 2=0 /\ 2<=k) as [Hke0 Hk2] by lia.
    destruct (Nat.le_gt_cases b (p+k)) as [Hnear|Hwide].
    + destruct (Nat.le_gt_cases (t+k) (p+b+e)) as [Hnormal|Hover].
      * destruct (near_core p e k b t HC He Hpe Hk Hkp Hb Hnear Hbe Ht Hte Hnormal)
          as [ys [HT HY]]; exists ys; split; [apply progress_evstep,HT|exact HY].
      * destruct (even_overflow_core p e k b t HC He Hpe Hk2 (ltac:(lia)) Hke0
          (ltac:(lia)) Hbe Hte Hnear Hover Hbound) as [ys [HT HY]].
        exists ys; split; [apply progress_evstep,HT|apply Safe_core,HY].
    + exists [p+k;b;t]; split; [constructor|].
      applys_eq (Safe_half p k (b-(p+k)) t HC); unfold e in *; flia.
Qed.

Lemma odd_block_short p e k b t:
  Chain p -> e<=1 -> p mod 2+e=1 -> 1<=k -> k*4<=p ->
  p<=b -> b mod 2=1 -> t<=p ->
  exists ys, section [p+k;b;t] -[tm]->+ section ys /\ Core ys.
Proof.
  intros HC He Hpe Hk Hkp Hb Hbo Ht.
  destruct (Chain_spec p HC) as [Hp [HP _]].
  destruct (Nat.eq_dec (k mod 2) 1) as [Hko|Hke].
  - pose proof (odd_odd_section p e k b t HP Hp He Hpe Hko (ltac:(lia)) Hbo) as HT.
    destruct (good_bounded_core p (b+k) (t+p+2+e-k) HC (ltac:(lia))) as [ys [HU HY]].
    exists ys; split; [eapply progress_trans; eauto|exact HY].
  - set (N:=(p+k*3+b+(1-e)-2)/2); set (X:=p+b-k/2).
    destruct (Band_above p X HC (ltac:(unfold X; lia))) as [q [Hq HB]].
    destruct (CleanLast_total N X t) as [ys HL].
    exists ys; split.
    + apply (even_odd_section p (1-e) k b t ys HP); try lia; exact HL.
    + destruct HL; try (unfold N,X in *; lia); apply Core_entry; try constructor;
        apply (Entry_small q); auto; unfold N,X in *; lia.
Qed.

Lemma high_even_low p e j b u:
  Chain p -> e<=1 -> p mod 2+e=1 -> 1<=j -> j*8<=p ->
  2<=b -> b mod 2=0 -> 5<=u -> u mod 2=1 ->
  b+u=p*2+j*22+7 -> b+j*24+3+e<=p*7 ->
  exists ys, section [next_p p+j*15;b;u] -[tm]->* section ys /\ Safe ys.
Proof.
  intros HC He Hpe Hj Hjp Hb Hbe Hu Hue Hsum Hcap.
  destruct (Chain_spec p HC) as [Hp [HP _]].
  set (q:=next_p p); assert (HQ:Chain q) by (apply ChainS,HC).
  destruct (Chain_spec q HQ) as [Hq [HPq _]].
  assert (Hqe:q mod 2=e) by (unfold q,next_p; lia).
  destruct (Nat.le_gt_cases b q) as [Hsmall|Hlarge].
  - exists [q+j*15;b;u]; split; [constructor|].
    apply Safe_core,Core_entry,(Entry_small q); try (unfold q,next_p in *; lia).
    split; [exact HQ|unfold q,next_p; lia].
  - destruct (Nat.eq_dec (j mod 2) 1) as [Hjo|Hje].
    + destruct (odd_even_bounded_core q (1-e) (j*15) b u HQ (ltac:(lia))
        (ltac:(lia)) (ltac:(lia)) (ltac:(unfold q,next_p; lia)) Hb Hbe Hue
        (ltac:(unfold q,next_p in *; lia))) as [ys [HT HY]].
      exists ys; split; [apply progress_evstep,HT|apply Safe_core,HY].
    + assert (Hje0:j mod 2=0) by lia.
      destruct (Nat.le_gt_cases b (q+j*15)) as [Hnear|Hwide].
      * destruct (Nat.le_gt_cases (u+j*15) (q+b+(1-e))) as [Hnormal|Hover].
        -- destruct (even_normal_section q (1-e) (j*15) b u HPq (ltac:(lia))
             (ltac:(lia)) (ltac:(lia)) (ltac:(unfold q,next_p; lia)) (ltac:(lia))
             Hb Hbe (ltac:(lia)) Hue Hnear Hnormal) as [ys [HT HY]].
           exists ys; split; [apply progress_evstep,HT|apply (Safe_stair q e ys HQ He); applys_eq HY; flia].
        -- destruct (even_overflow_core q (1-e) (j*15) b u HQ (ltac:(lia))
             (ltac:(lia)) (ltac:(lia)) (ltac:(unfold q,next_p; lia)) (ltac:(lia))
             Hb Hbe Hue Hnear Hover (ltac:(unfold q,next_p in *; lia))) as [ys [HT HY]].
           exists ys; split; [apply progress_evstep,HT|apply Safe_core,HY].
      * destruct (Repair_total q (1-e) (j*15) (b-(q+j*15)) (u-1) (ltac:(lia))) as [xs HR].
        pose proof (wide_triple q (1-e) (j*15) b u xs HPq Hq (ltac:(lia))
          (ltac:(lia)) (ltac:(lia)) (ltac:(unfold q,next_p; lia)) (ltac:(lia))
          Hb Hbe (ltac:(lia)) Hue Hwide (ltac:(unfold q,next_p in *; lia))
          (ltac:(unfold q,next_p in *; lia)) HR) as HT.
        destruct HR as [x Hx HX|x Hx HX]; try (unfold q,next_p in *; lia).
        destruct (small_near_reaches (next_p q) (j*15/2)
          (q*2+(b-(q+j*15))*2+2) x (ChainS q HQ)) as [ys [HU HY]];
          try (unfold q,next_p in *; lia).
        exists ys; split; [eapply evstep_trans; [apply progress_evstep,HT|exact HU]|exact HY].
Qed.

Lemma high_second_low p e j b u:
  Chain p -> e<=1 -> p mod 2+e=1 -> 1<=j -> j*8<=p -> j mod 2=0 ->
  2<=b -> b mod 2=0 -> 1<=u -> u mod 2=1 ->
  b+u=(next_p p+(j/2)*67)*2+5 -> b+j*46+7+e<=p*5 ->
  exists ys, section [next_p (next_p p)+(j/2)*29;b;u] -[tm]->* section ys /\ Safe ys.
Proof.
  intros HC He Hpe Hj Hjp Hje Hb Hbe Hu Hue Hsum Hcap.
  set (q:=next_p (next_p p)); assert (HQ:Chain q) by (apply ChainS,ChainS,HC).
  destruct (Nat.le_gt_cases b q) as [Hsmall|Hlarge].
  - exists [q+(j/2)*29;b;u]; split; [constructor|].
    apply Safe_core,Core_entry,(Entry_small q); try (unfold q,next_p in *; lia).
    split; [exact HQ|unfold q,next_p in *; lia].
  - apply (small_cleanup_upper q ((j/2)*29) b u HQ); try assumption;
      unfold q,next_p in *; lia.
Qed.

Lemma high_even_high p e j c:
  Chain p -> e<=1 -> p mod 2+e=1 -> 1<=j -> j*8<=p ->
  c mod 2=0 -> c+j*46+7+e<=p*5 ->
  exists ys, section [next_p p+j*15;p*2+j*22+5;c] -[tm]->+ section ys /\ Safe ys.
Proof.
  intros HC He Hpe Hj Hjp Hce Hcap.
  destruct (Chain_spec p HC) as [Hp [HP _]].
  set (q:=next_p p); assert (HQ:Chain q) by (apply ChainS,HC).
  destruct (Chain_spec q HQ) as [Hq [HPq _]].
  assert (Hqe:q mod 2=e) by (unfold q,next_p; lia).
  destruct (Nat.eq_dec (j mod 2) 1) as [Hjo|Hje].
  - pose proof (odd_odd_section q (1-e) (j*15) (p*2+j*22+5) c HPq Hq
      (ltac:(lia)) (ltac:(lia)) (ltac:(lia)) (ltac:(unfold q,next_p; lia)) (ltac:(lia))) as HT.
    destruct (good_core_or_overflow q (p*2+j*22+5+j*15)
      (c+q+2+(1-e)-j*15) HQ (ltac:(lia))) as [xs [HU [HY|[u [EX EU]]]]].
    + exists xs; split; [eapply progress_trans; eauto|apply Safe_core,HY].
    + subst xs; set (r:=next_p q); assert (HR:Chain r) by (apply ChainS,HQ).
      replace (q+(p*2+j*22+5+j*15)) with (r+j*37) in HU,EU by (unfold r,q,next_p; lia).
      destruct (odd_post_good_core r e (j*37) u HR He (ltac:(unfold r,q,next_p; lia))
        (ltac:(lia)) (ltac:(unfold r,q,next_p in *; lia)) (ltac:(unfold r,q,next_p in *; lia)))
        as [ys [HV HY]].
      exists ys; split; [eapply progress_trans; [exact HT|]; eapply progress_trans; eauto|apply Safe_core,HY].
  - assert (Hje0:j mod 2=0) by lia.
    set (N:=q+(j/2)*67); set (X:=next_p q+(j/2)*29).
    destruct (CleanLast_total N X c) as [xs HL].
    assert (HT:section [q+j*15;p*2+j*22+5;c] -[tm]->+ section xs).
    { apply (even_odd_section q e (j*15) (p*2+j*22+5) c xs HPq);
        try (unfold q,next_p in *; lia).
      applys_eq HL; unfold N,X,q,next_p; flia. }
    destruct HL; try lia.
    + eexists; split; [exact HT|apply Safe_core,Core_entry,Entry_unary].
    + destruct (high_second_low p e j (2+s*2) (3+(N-s)*2) HC He Hpe Hj Hjp Hje0)
        as [ys [HU HY]]; try (unfold N,q in *; lia).
      exists ys; split; [eapply progress_evstep_trans; [exact HT|exact HU]|exact HY].
    + destruct (high_second_low p e j (4+N*2) 1 HC He Hpe Hj Hjp Hje0)
        as [ys [HU HY]]; try (unfold N,q in *; lia).
      exists ys; split; [eapply progress_evstep_trans; [exact HT|exact HU]|exact HY].
    + destruct (odd_block_short (next_p q) e ((j/2)*29) (5+N*2) a (ChainS q HQ) He)
        as [ys [HU HY]]; try (unfold N,q,next_p in *; lia).
      exists ys; split; [eapply progress_trans; [exact HT|exact HU]|apply Safe_core,HY].
Qed.

Lemma high_even_progress p e j t:
  Chain p -> e<=1 -> p mod 2+e=1 -> 1<=j -> j*8<=p ->
  1<=t -> t mod 2=1 -> t+j*24+2+e<=p*7 ->
  exists ys, section [p+j*2;p+j*16+2+e;t] -[tm]->+ section ys /\ Safe ys.
Proof.
  intros HC He Hpe Hj Hjp Ht Hte Hcap.
  destruct (Chain_spec p HC) as [Hp [HP _]].
  destruct (CleanLast_total (p+j*11) (next_p p+j*15) t) as [xs HL].
  assert (HT:section [p+j*2;p+j*16+2+e;t] -[tm]->+ section xs).
  { apply (even_odd_section p (1-e) (j*2) (p+j*16+2+e) t xs HP); try lia.
    applys_eq HL; unfold next_p; flia. }
  destruct HL; try lia.
  - eexists; split; [exact HT|apply Safe_core,Core_entry,Entry_unary].
  - destruct (high_even_low p e j (2+s*2) (5+(p+j*11-s)*2) HC He Hpe Hj Hjp)
      as [ys [HU HY]]; try lia.
    exists ys; split; [eapply progress_evstep_trans; eauto|exact HY].
  - destruct (high_even_high p e j a HC He Hpe Hj Hjp (ltac:(lia)) (ltac:(lia)))
      as [ys [HU HY]].
    exists ys; split; [eapply progress_trans; [exact HT|applys_eq HU; flia]|exact HY].
Qed.

Lemma high_exit_progress xs: HighExit xs ->
  exists ys, section xs -[tm]->+ section ys /\ EntryExit ys.
Proof.
  intro H; destruct H as [p k t HC Hk Hkp Ht Hte Hcap].
  destruct (Nat.eq_dec (k mod 2) 1) as [Hko|Hke].
  - apply (high_odd_progress p (1-p mod 2) k t HC); auto; lia.
  - destruct (high_even_progress p (1-p mod 2) (k/2) t HC)
      as [ys [HT HY]]; try lia.
    exists ys; split; [applys_eq HT; flia|left; exact HY].
Qed.

Lemma closed_progress xs: EntryExit xs ->
  exists ys, section xs -[tm]->+ section ys /\ EntryExit ys.
Proof. apply entry_exit_progress,high_exit_progress. Qed.

Lemma section_nonhalt xs: EntryExit xs -> ~halts tm (section xs).
Proof. apply (progress_nonhalt_cond tm _ xs section EntryExit),closed_progress. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  apply section_nonhalt; left; apply Safe_core,Core_entry,Entry_unary.
Qed.

End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0RF_0LC---_1LE1LD_1RE0LA_1RA0RD_1LB1RD").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Definition section xs := TM1.section_side xs true {{E}}> 0inf.
Lemma init: c0 -->* section [2%nat].
Proof. unfold section; cbn[TM1.section_side]; esx. Qed.
Definition from_tm1 q := match q with A=>D|B=>E|C=>A|D=>B|E=>C|F=>F end.
Lemma from_tm1_spec: Perm TM1.tm tm from_tm1.
Proof.
  split.
  - intros [] [] H; cbn in *; congruence.
  - intros [] [] s d q H; inverts H; reflexivity.
Qed.
Lemma transfer l r:
  l {{B}}> 0inf -[TM1.tm]->+ r {{B}}> 0inf ->
  l {{E}}> 0inf -[tm]->+ r {{E}}> 0inf.
Proof.
  intro H; destruct (progress_multistep _ _ _ H) as [n Hn].
  apply multistep_progress with (n:=n).
  exact (perm_multistep _ _ _ from_tm1_spec _ B _ B _ Hn).
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  apply (progress_nonhalt_cond tm _ [2%nat] section TM1.EntryExit).
  - intros xs H; destruct (TM1.closed_progress xs H) as [ys [HT HY]].
    exists ys; split; [unfold section; apply transfer; exact HT|exact HY].
  - left; apply TM1.Safe_core,TM1.Core_entry,TM1.Entry_unary.
Qed.
End TM2.

Module TM3.
Definition tm := Eval compute in (TM_from_str "1LB1RF_0LC---_1LD1LF_1RE0RF_1RB0RA_1RD0LE").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Definition section xs := TM1.section_side xs true {{D}}> 0inf.
Lemma init: c0 -->* section [4%nat].
Proof. unfold section; cbn[TM1.section_side]; esx. Qed.
Definition from_tm1 q := match q with A=>F|B=>D|C=>E|D=>B|E=>C|F=>A end.
Lemma from_tm1_spec: Perm TM1.tm tm from_tm1.
Proof.
  split.
  - intros [] [] H; cbn in *; congruence.
  - intros [] [] s d q H; inverts H; reflexivity.
Qed.
Lemma transfer l r:
  l {{B}}> 0inf -[TM1.tm]->+ r {{B}}> 0inf ->
  l {{D}}> 0inf -[tm]->+ r {{D}}> 0inf.
Proof.
  intro H; destruct (progress_multistep _ _ _ H) as [n Hn].
  apply multistep_progress with (n:=n).
  exact (perm_multistep _ _ _ from_tm1_spec _ B _ B _ Hn).
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  apply (progress_nonhalt_cond tm _ [4%nat] section TM1.EntryExit).
  - intros xs H; destruct (TM1.closed_progress xs H) as [ys [HT HY]].
    exists ys; split; [unfold section; apply transfer; exact HT|exact HY].
  - left; apply TM1.Safe_core,TM1.Core_entry,TM1.Entry_unary.
Qed.
End TM3.
