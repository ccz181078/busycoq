From BusyCoq Require Import Individual62 Longitudinal ES_v3.
Require Import Lia ZArith String List.

Import ListNotations.
Open Scope list.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6);
   [vm_compute; reflexivity | st; reflexivity]).

Module TM11.

Fixpoint multistep_c' tm n1 n2 n3 c :=
  match n1 with
  | O => multistep_c tm n3 c
  | S n1' =>
      match multistep_c tm n2 c with
      | Some c' => multistep_c' tm n1' n2 n3 c'
      | None => None
      end
  end.

Lemma multistep_c'_spec tm n1 n2 n3 c c' :
  multistep_c' tm n1 n2 n3 c = Some c' <->
  c -[tm]->> (n1*n2+n3) / c'.
Proof.
  revert c c'; induction n1; cbn [multistep_c']; intros.
  - apply multistep_c_spec.
  - destruct (multistep_c tm n2 c) eqn:E.
    + apply multistep_c_spec in E. rewrite IHn1.
      replace (S n1*n2+n3) with (n2+(n1*n2+n3)) by lia.
      split; intro H.
      * eapply multistep_trans; eauto.
      * eapply rewind_split in H. destruct H as [c'' [I1 I2]].
        multistep_deterministic; eauto.
    + split; [congruence|].
      replace (S n1*n2+n3) with (n2+(n1*n2+n3)) by lia.
      intro H; eapply rewind_split in H. destruct H as [c'' [I1 I2]].
      apply multistep_c_spec in I1; congruence.
Qed.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC1RF_0LA1RA_0RE0RC_1LE1LB_---0LE").

Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Notation hL := (B,[1;0;0;1;1;1;0;1;1;1]).
Notation hR := (C,[0;0]).
Notation kR := (A,[1;0;0]).
Notation kL := (B,[1;0;0;1;1;1;0;1;1;1]).
Notation hh := [(hR,hL)].
Notation kk := [(kR,kL)].

Notation A3 := [1;1;1].
Notation B4 := [0;1;1;1].
Definition RD n := A3 ++ B4^^n.
Definition RD1 a b := RD a ++ [1] ++ B4^^b.
Notation edge := ([1;1;1;1] *> 0inf).

Inductive Col := CRD (n:nat) | CRD1 (a b:nat).

Definition colword (c:Col) :=
  match c with CRD n => RD n | CRD1 a b => RD1 a b end.

Fixpoint netword (cs:list Col) : side :=
  match cs with [] => edge | c::cs' => colword c *> netword cs' end.

Fixpoint rdcols (ns:list nat) : list Col :=
  match ns with [] => [] | n::ns' => CRD n::rdcols ns' end.

Definition init_ns := [4;9;19;37;73;142;275;529;1016;1949].

(* The four finite left-hand phases. *)
Notation lh0 :=
  (0inf <* <[1;1;1;1;1;1;1;1;1;1;1;1;0;1;0;1;1;0;0;1;1;1;1;1;1;1;0;1;1;0;1;1;1;0;1;1]).
Notation lh1 :=
  (0inf <* <[1;1;1;1;1;1;1;1;1;1;1;1;0;1;0;1;1;1;1;1;1;1;1;1;0;0;1;1;1;1]).
Notation lh2 :=
  (0inf <* <[1;1;1;1;1;1;1;1;1;1;1;1;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;0;1;1]).
Notation lh3 :=
  (0inf <* <[1;1;1;1;1;1;1;1;1;1;1;1;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1]).

Definition Config (cs:list Col) := lh3 {{{(hL,L)}}} netword cs.

Lemma init : c0 -->* Config (rdcols init_ns).
Proof.
  eapply without_counter.
  eapply multistep_c'_spec with (n1:=839) (n2:=10^5) (n3:=62885).
  match goal with |- _ = ?rhs => native_cast_no_check (eq_refl rhs) end.
Qed.

(* The rules in TM11.txt.  The compound signal [#1] is represented by [kk]. *)
Lemma hash_B : segRLs tm hh hh B4 B4.
Proof. apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity. Qed.

Lemma hash_edge : sideRLs tm hh edge edge.
Proof. esc. Qed.

Lemma hash_1 : segRLs tm hh kk [1] [].
Proof. apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity. Qed.

Lemma hash1_BB : segRLs tm kk [] (B4++B4) [1].
Proof. apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity. Qed.

Lemma hash1_BA : segRLs tm kk kk (B4++A3) (A3++B4).
Proof. apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity. Qed.

Lemma hash1_A : segRLs tm kk (kk++hh) A3 (A3++B4++B4).
Proof. apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity. Qed.

Lemma hash1_edge : sideRLs tm kk edge (A3 *> B4 *> edge).
Proof. esc. Qed.

Lemma hash1_B_edge : sideRLs tm kk (B4 *> edge) (A3 *> edge).
Proof. esc. Qed.

(* Aggregate column rules.  [L] is the compound incoming form [#1 0111]:
   its directed head is [kk] and its extra [B4] is part of the input word. *)
Lemma H_RD n : segRLs tm hh (hh^^2) (RD n) (RD (n+2)).
Proof. ut; esx. Qed.

Lemma K_RD0 : segRLs tm kk (kk++hh) (RD 0) (RD 2).
Proof. vm_compute; exact hash1_A. Qed.

Lemma K_RD4 n : segRLs tm kk [] (RD (n+4)) (RD1 2 n).
Proof. ut; esx. Qed.

Lemma H_RD1_4 a b : segRLs tm hh [] (RD1 a (b+4)) (RD1 (a+2) b).
Proof. ut; esx. Qed.

Lemma H_RD1_0 a : segRLs tm hh (kk++hh) (RD1 a 0) (RD (a+2)).
Proof. ut; esx. Qed.

Lemma L_RD2 n : segRLs tm kk [] (B4++RD (n+2)) (RD1 1 n).
Proof. ut; esx. Qed.

Lemma KH_BB : segRLs tm (kk++hh) kk (B4++B4) [].
Proof.
  exact (@segRLs_trans tm kk [] hh kk (B4++B4) [1] []
    hash1_BB hash_1).
Qed.

Lemma K_RD2 : segRLs tm kk kk (RD 2) (RD 2).
Proof.
  change (segRLs tm kk kk (A3++B4++B4) (A3++B4++B4)).
  exact (@segRLs_concat tm kk (kk++hh) kk A3 (A3++B4++B4)
    (B4++B4) [] hash1_A KH_BB).
Qed.

Lemma H_RD1_2 a : segRLs tm hh kk (RD1 a 2) (RD (a+2)).
Proof.
  replace (RD1 a 2) with (RD1 a 0++B4++B4) by
    (unfold RD1; cbn; repeat rewrite app_nil_r;
     rewrite <-app_assoc; reflexivity).
  pose proof (@segRLs_concat tm hh (kk++hh) kk (RD1 a 0) (RD (a+2))
    (B4++B4) [] (H_RD1_0 a) KH_BB) as H.
  rewrite app_nil_r in H. exact H.
Qed.

Lemma RD1_one a : RD1 a 1 = RD1 a 0 ++ B4.
Proof.
  unfold RD1; cbn; repeat rewrite app_nil_r; rewrite <-app_assoc;
    reflexivity.
Qed.

Lemma RD1_three a : RD1 a 3 = RD1 a 2 ++ B4.
Proof.
  unfold RD1; cbn; repeat rewrite app_nil_r; rewrite <-app_assoc;
    reflexivity.
Qed.

Lemma restart0 r :
  lh0 {{{(hL,L)}}} r -->*
  lh1 {{{(hR,R)}}} (A3 *> B4 *> A3 *> B4 *> r).
Proof.
  eapply without_counter with (n:=137).
  apply multistep_c_spec; vm_compute; reflexivity.
Qed.

Lemma restart1 r :
  lh1 {{{(hL,L)}}} r -->*
  lh2 {{{(hR,R)}}} (B4 *> r).
Proof.
  eapply without_counter with (n:=47).
  apply multistep_c_spec; vm_compute; reflexivity.
Qed.

Lemma restart2 r :
  lh2 {{{(hL,L)}}} r -->*
  lh3 {{{(hR,R)}}} (A3 *> B4 *> r).
Proof.
  eapply without_counter with (n:=38).
  apply multistep_c_spec; vm_compute; reflexivity.
Qed.

Lemma restart3 r :
  lh3 {{{(hL,L)}}} r -->*
  lh0 {{{(hR,R)}}} ([1] *> A3 *> A3 *> B4 *> r).
Proof.
  eapply without_counter with (n:=642).
  apply multistep_c_spec; vm_compute; reflexivity.
Qed.

Lemma phase0_prefix :
  segRLs tm hh (kk++hh++hh++hh) ([1]++A3++A3) (RD 2++RD 4).
Proof. ut; esx. Qed.

Lemma phase1_prefix :
  segRLs tm hh (hh^^4) (A3++B4++A3++B4) (RD 3++RD 5).
Proof. ut; esx. Qed.

(* Arithmetic certificate for the reference column stream.  A six-cell
   window advances by [a,b,c,d,e,f |-> b,c,d,e,f,2*f-a]. *)
Record QWin := mkQWin {
  qa : nat; qb : nat; qc : nat; qd : nat; qe : nat; qf : nat
}.

Definition qnext (w:QWin) : nat := 2*qf w-qa w.
Definition qshift (w:QWin) : QWin :=
  mkQWin (qb w) (qc w) (qd w) (qe w) (qf w) (qnext w).

Definition between (p x y:nat) : Prop :=
  25^p*y >= 49^p*x /\ y <= 2^p*x.

Definition QGood (w:QWin) : Prop :=
  between 1 (qa w) (qb w) /\
  between 2 (qa w) (qc w) /\
  between 3 (qa w) (qd w) /\
  between 4 (qa w) (qe w) /\
  between 5 (qa w) (qf w) /\
  between 1 (qb w) (qc w) /\
  between 2 (qb w) (qd w) /\
  between 3 (qb w) (qe w) /\
  between 4 (qb w) (qf w) /\
  between 1 (qc w) (qd w) /\
  between 2 (qc w) (qe w) /\
  between 3 (qc w) (qf w) /\
  between 1 (qd w) (qe w) /\
  between 2 (qd w) (qf w) /\
  between 1 (qe w) (qf w).

Lemma between_cons p x y z :
  between 1 x y -> between p y z -> between (S p) x z.
Proof.
  unfold between. intros [Hxy Uxy] [Hyz Uyz].
  cbn [Nat.pow] in *. split; nia.
Qed.

Lemma QGood_initial : QGood (mkQWin 17 34 68 135 266 523).
Proof.
  assert (H0 : between 1 17 34) by (vm_compute; lia).
  assert (H1 : between 1 34 68) by (vm_compute; lia).
  assert (H2 : between 1 68 135) by (vm_compute; lia).
  assert (H3 : between 1 135 266) by (vm_compute; lia).
  assert (H4 : between 1 266 523) by (vm_compute; lia).
  pose proof (between_cons 1 17 34 68 H0 H1) as H01.
  pose proof (between_cons 1 34 68 135 H1 H2) as H12.
  pose proof (between_cons 1 68 135 266 H2 H3) as H23.
  pose proof (between_cons 1 135 266 523 H3 H4) as H34.
  pose proof (between_cons 2 17 34 135 H0 H12) as H012.
  pose proof (between_cons 2 34 68 266 H1 H23) as H123.
  pose proof (between_cons 2 68 135 523 H2 H34) as H234.
  pose proof (between_cons 3 17 34 266 H0 H123) as H0123.
  pose proof (between_cons 3 34 68 523 H1 H234) as H1234.
  pose proof (between_cons 4 17 34 523 H0 H1234) as H01234.
  cbn [QGood qa qb qc qd qe qf].
  exact (conj H0 (conj H01 (conj H012 (conj H0123 (conj H01234
    (conj H1 (conj H12 (conj H123 (conj H1234 (conj H2
    (conj H23 (conj H234 (conj H3 (conj H34 H4)))))))))))))).
Qed.

Lemma between_next1 a f : between 5 a f -> between 1 f (2*f-a).
Proof. unfold between. cbn [Nat.pow]. lia. Qed.

Lemma between_next2 a e f :
  between 4 a e -> between 1 e f -> between 2 e (2*f-a).
Proof. unfold between. cbn [Nat.pow]. lia. Qed.

Lemma between_next3 a d f :
  between 3 a d -> between 2 d f -> between 3 d (2*f-a).
Proof. unfold between. cbn [Nat.pow]. lia. Qed.

Lemma between_next4 a c f :
  between 2 a c -> between 3 c f -> between 4 c (2*f-a).
Proof. unfold between. cbn [Nat.pow]. lia. Qed.

Lemma between_next5 a b f :
  between 1 a b -> between 4 b f -> between 5 b (2*f-a).
Proof. unfold between. cbn [Nat.pow]. lia. Qed.

Lemma QGood_shift w : QGood w -> QGood (qshift w).
Proof.
  destruct w as [a b c d e f].
  unfold QGood,qshift,qnext; cbn.
  intros (Hab & Hac & Had & Hae & Haf & Hbc & Hbd & Hbe & Hbf &
    Hcd & Hce & Hcf & Hde & Hdf & Hef).
  pose proof (between_next5 a b f Hab Hbf) as H5.
  pose proof (between_next4 a c f Hac Hcf) as H4.
  pose proof (between_next3 a d f Had Hdf) as H3.
  pose proof (between_next2 a e f Hae Hef) as H2.
  pose proof (between_next1 a f Haf) as H1.
  exact (conj Hbc (conj Hbd (conj Hbe (conj Hbf (conj H5
    (conj Hcd (conj Hce (conj Hcf (conj H4 (conj Hde
    (conj Hdf (conj H3 (conj Hef (conj H2 H1)))))))))))))).
Qed.

Lemma QGood_next_positive w :
  0 < qa w -> QGood w -> 0 < qa (qshift w).
Proof.
  destruct w as [a b c d e f].
  unfold QGood; cbn. intros Ha (Hab & _).
  unfold between in Hab. cbn [Nat.pow] in Hab. lia.
Qed.

Lemma QGood_six_growth w : QGood w -> 56*qa w <= qnext w.
Proof.
  destruct w as [a b c d e f].
  unfold QGood; cbn. intros (_ & _ & _ & _ & Haf & _).
  unfold between in Haf. cbn [Nat.pow] in Haf.
  destruct Haf as [Hlo Hhi].
  unfold qnext; cbn.
  lia.
Qed.

Lemma between_one_lower x y : between 1 x y -> 49*x <= 25*y.
Proof. unfold between. cbn [Nat.pow]. lia. Qed.

Opaque Nat.pow.

Fixpoint qiter (n:nat) (w:QWin) : QWin :=
  match n with O => w | S n' => qshift (qiter n' w) end.

Definition qwindow n := qiter n (mkQWin 17 34 68 135 266 523).
Definition q n := qa (qwindow n).

Lemma qiter_add a b w : qiter (a+b) w = qiter a (qiter b w).
Proof.
  induction a.
  - reflexivity.
  - cbn [Nat.add qiter]. f_equal. exact IHa.
Qed.

Lemma q_0 : q 0 = 17. Proof. reflexivity. Qed.
Lemma q_1 : q 1 = 34. Proof. reflexivity. Qed.
Lemma q_2 : q 2 = 68. Proof. reflexivity. Qed.
Lemma q_3 : q 3 = 135. Proof. reflexivity. Qed.
Lemma q_4 : q 4 = 266. Proof. reflexivity. Qed.
Lemma q_5 : q 5 = 523. Proof. reflexivity. Qed.
Lemma q_6 : q 6 = 1029. Proof. reflexivity. Qed.
Lemma q_7 : q 7 = 2024. Proof. reflexivity. Qed.

Lemma q_rec n : q (n+6) = 2*q (n+5)-q n.
Proof.
  unfold q,qwindow. replace (n+6) with (6+n) by lia.
  replace (n+5) with (5+n) by lia.
  rewrite !qiter_add. cbn [qiter qshift qnext]. reflexivity.
Qed.

Lemma qwindow_good n : QGood (qwindow n).
Proof. induction n; [exact QGood_initial|cbn [qwindow qiter]; apply QGood_shift,IHn]. Qed.

Lemma q_adjacent n : 49*q n <= 25*q (n+1).
Proof.
  unfold q,qwindow. replace (n+1) with (1+n) by lia.
  rewrite qiter_add. cbn [qiter qshift qa qb].
  apply between_one_lower. exact (proj1 (qwindow_good n)).
Qed.

Lemma q_pos n : 0 < q n.
Proof.
  unfold q. induction n.
  - change (0 < 17). lia.
  - cbn [qwindow qiter].
    apply QGood_next_positive; [exact IHn|apply qwindow_good].
Qed.

Lemma q_rec_Z base j :
  (Z.of_nat (q (base+6+j)) =
    2 * Z.of_nat (q (base+5+j)) - Z.of_nat (q (base+j)))%Z.
Proof.
  pose proof (q_pos (base+j+6)) as Hpos.
  pose proof (q_rec (base+j)) as Hrec.
  replace (base+j+6) with (base+6+j) in Hpos,Hrec by lia.
  replace (base+j+5) with (base+5+j) in Hrec by lia.
  assert (Hle : q (base+j) <= 2*q (base+5+j)) by lia.
  rewrite Hrec, Nat2Z.inj_sub by exact Hle.
  rewrite Nat2Z.inj_mul. cbn. lia.
Qed.

Lemma q_six_growth n : 56*q n <= q (n+6).
Proof.
  unfold q,qwindow. replace (n+6) with (6+n) by lia.
  rewrite qiter_add. cbn [qiter qshift].
  apply QGood_six_growth.
  change (QGood (qwindow n)). apply qwindow_good.
Qed.

(* The eight exceptional columns.  The affine map is the exact error map
   induced by one four-phase cycle; writing all coordinates out keeps the
   final arithmetic proof in Presburger arithmetic. *)
Record Err8 := mkErr8 {
  e0: Z; e1: Z; e2: Z; e3: Z; e4: Z; e5: Z; e6: Z; e7: Z
}.

Definition enext (e:Err8) : Err8 :=
  mkErr8
    (- e0 e)
    (- (2*e0 e+e1 e))
    (- (4*e0 e+2*e1 e+e2 e))
    (- (8*e0 e+4*e1 e+2*e2 e+e3 e))
    (- (16*e0 e+8*e1 e+4*e2 e+2*e3 e+e4 e))
    (- (32*e0 e+16*e1 e+8*e2 e+4*e3 e+2*e4 e+e5 e))
    (- (64*e0 e+32*e1 e+16*e2 e+8*e3 e+4*e4 e+2*e5 e+e6 e))
    (- (128*e0 e+64*e1 e+32*e2 e+16*e3 e+8*e4 e+4*e5 e+2*e6 e+e7 e)-1).

Definition zabs_le_nat (z:Z) (n:nat) : Prop :=
  (-Z.of_nat n < z <= Z.of_nat n)%Z.

Definition ErrGood (base:nat) (e:Err8) : Prop :=
  zabs_le_nat (e0 e) (q base) /\
  zabs_le_nat (e1 e) (q (base+1)) /\
  zabs_le_nat (e2 e) (q (base+2)) /\
  zabs_le_nat (e3 e) (q (base+3)) /\
  zabs_le_nat (e4 e) (q (base+4)) /\
  zabs_le_nat (e5 e) (q (base+5)) /\
  zabs_le_nat (e6 e) (q (base+6)) /\
  zabs_le_nat (e7 e) (q (base+7)).

Definition err_initial := mkErr8 2 3 5 7 9 6 (-13) (-75).

Fixpoint erriter (k:nat) : Err8 :=
  match k with O => err_initial | S k' => enext (erriter k') end.

Definition eget (e:Err8) (j:nat) : Z :=
  match j with
  | O => e0 e | S O => e1 e | S (S O) => e2 e
  | S (S (S O)) => e3 e | S (S (S (S O))) => e4 e
  | S (S (S (S (S O)))) => e5 e
  | S (S (S (S (S (S O))))) => e6 e | _ => e7 e
  end.

Definition eval_col (base j:nat) (e:Err8) : nat :=
  Z.to_nat (Z.of_nat (q (base+j)) + eget e j).

Definition eval_colZ (base j:nat) (e:Err8) : Z :=
  Z.of_nat (q (base+j)) + eget e j.

Definition tail8 base e :=
  [eval_col base 0 e; eval_col base 1 e; eval_col base 2 e;
   eval_col base 3 e; eval_col base 4 e; eval_col base 5 e;
   eval_col base 6 e; eval_col base 7 e].

Definition orbit k :=
  [4;9] ++ map q (seq 0 (6*k)) ++ tail8 (6*k) (erriter k).

Lemma ErrGood_initial : ErrGood 0 err_initial.
Proof.
  unfold ErrGood,zabs_le_nat,err_initial.
  cbn [Nat.add e0 e1 e2 e3 e4 e5 e6 e7].
  rewrite ?q_0, ?q_1, ?q_2, ?q_3, ?q_4, ?q_5, ?q_6, ?q_7.
  repeat split; lia.
Qed.

(* [q] grows by at least 56 in six positions.  Together with the lower
   adjacent ratio 49/25, this dominates every row sum in [enext]. *)
Lemma ErrGood_next base e : ErrGood base e -> ErrGood (base+6) (enext e).
Proof.
  intros H. unfold ErrGood,zabs_le_nat in *. destruct H as
    (H0&H1&H2&H3&H4&H5&H6&H7).
  pose proof (q_adjacent base) as A0.
  pose proof (q_adjacent (base+1)) as A1.
  pose proof (q_adjacent (base+2)) as A2.
  pose proof (q_adjacent (base+3)) as A3'.
  pose proof (q_adjacent (base+4)) as A4.
  pose proof (q_adjacent (base+5)) as A5.
  pose proof (q_adjacent (base+6)) as A6.
  replace (base+1+1) with (base+2) in A1 by lia.
  replace (base+2+1) with (base+3) in A2 by lia.
  replace (base+3+1) with (base+4) in A3' by lia.
  replace (base+4+1) with (base+5) in A4 by lia.
  replace (base+5+1) with (base+6) in A5 by lia.
  replace (base+6+1) with (base+7) in A6 by lia.
  pose proof (q_six_growth base) as G0.
  pose proof (q_six_growth (base+1)) as G1.
  pose proof (q_six_growth (base+2)) as G2.
  pose proof (q_six_growth (base+3)) as G3.
  pose proof (q_six_growth (base+4)) as G4.
  pose proof (q_six_growth (base+5)) as G5.
  pose proof (q_six_growth (base+6)) as G6.
  pose proof (q_six_growth (base+7)) as G7.
  pose proof (q_pos (base+7)) as P7.
  replace (base+6+1) with (base+1+6) by lia.
  replace (base+6+2) with (base+2+6) by lia.
  replace (base+6+3) with (base+3+6) by lia.
  replace (base+6+4) with (base+4+6) by lia.
  replace (base+6+5) with (base+5+6) by lia.
  replace (base+6+6) with (base+6+6) by lia.
  replace (base+6+7) with (base+7+6) by lia.
  unfold enext; cbn [e0 e1 e2 e3 e4 e5 e6 e7].
  repeat split; lia.
Qed.

Lemma erriter_good k : ErrGood (6*k) (erriter k).
Proof.
  induction k.
  - exact ErrGood_initial.
  - cbn [erriter]. replace (6*S k) with (6*k+6) by lia.
    apply ErrGood_next,IHk.
Qed.

Lemma orbit_0 : orbit 0 = init_ns.
Proof. vm_compute. reflexivity. Qed.

(* A small operational semantics for the verified block rules.  [SigL]
   denotes the compound signal [#1 0111]; hence its machine denotation is
   [kk] with one [B4] prepended to the following column word. *)
Inductive Sig := SigH | SigK | SigL.

Definition pref_of (ss:list Sig) : list Sym :=
  match ss with SigL::_ => B4 | _ => [] end.

Inductive Push : list Sig -> list Col -> list Col -> Prop :=
| Push_nil cs : Push [] cs cs
| Push_cons s ss cs cs1 cs2 :
    Push1 s cs cs1 -> Push ss cs1 cs2 -> pref_of ss = [] ->
    Push (s::ss) cs cs2
with Push1 : Sig -> list Col -> list Col -> Prop :=
| Push1_H_RD n cs cs' :
    Push [SigH;SigH] cs cs' ->
    Push1 SigH (CRD n::cs) (CRD (n+2)::cs')
| Push1_K_RD0 cs cs' :
    Push [SigK;SigH] cs cs' ->
    Push1 SigK (CRD 0::cs) (CRD 2::cs')
| Push1_K_RD1 cs cs' :
    Push [SigL;SigH] cs cs' ->
    Push1 SigK (CRD 1::cs) (CRD 2::cs')
| Push1_K_RD2 cs cs' :
    Push [SigK] cs cs' ->
    Push1 SigK (CRD 2::cs) (CRD 2::cs')
| Push1_K_RD3 cs cs' :
    Push [SigL] cs cs' ->
    Push1 SigK (CRD 3::cs) (CRD 2::cs')
| Push1_K_RD4 n cs :
    Push1 SigK (CRD (n+4)::cs) (CRD1 2 n::cs)
| Push1_L_RD0 cs cs' :
    Push [SigK] cs cs' ->
    Push1 SigL (CRD 0::cs) (CRD 1::cs')
| Push1_L_RD1 cs cs' :
    Push [SigL] cs cs' ->
    Push1 SigL (CRD 1::cs) (CRD 1::cs')
| Push1_L_RD2 n cs :
    Push1 SigL (CRD (n+2)::cs) (CRD1 1 n::cs)
| Push1_H_D0 a cs cs' :
    Push [SigK;SigH] cs cs' ->
    Push1 SigH (CRD1 a 0::cs) (CRD (a+2)::cs')
| Push1_H_D1 a cs cs' :
    Push [SigL;SigH] cs cs' ->
    Push1 SigH (CRD1 a 1::cs) (CRD (a+2)::cs')
| Push1_H_D2 a cs cs' :
    Push [SigK] cs cs' ->
    Push1 SigH (CRD1 a 2::cs) (CRD (a+2)::cs')
| Push1_H_D3 a cs cs' :
    Push [SigL] cs cs' ->
    Push1 SigH (CRD1 a 3::cs) (CRD (a+2)::cs')
| Push1_H_D4 a b cs :
    Push1 SigH (CRD1 a (b+4)::cs) (CRD1 (a+2) b::cs)
| Push1_H_edge : Push1 SigH [] []
| Push1_K_edge : Push1 SigK [] [CRD 1]
| Push1_L_edge : Push1 SigL [] [CRD 0].

Scheme Push_ind' := Induction for Push Sort Prop
with Push1_ind' := Induction for Push1 Sort Prop.
Combined Scheme Push_Push1_ind from Push_ind', Push1_ind'.

Inductive Cycle : list Col -> list Col -> Prop :=
| Cycle_intro n n0 n1 n2 n' :
    Push [SigL;SigH;SigH;SigH] n n0 ->
    Push [SigH;SigH;SigH;SigH] (CRD 2::CRD 4::n0) n1 ->
    Push [SigH] (CRD 3::CRD 5::n1) n2 ->
    Push [SigH;SigH] n2 n' ->
    Cycle n (CRD 4::n').

Fixpoint heads_of (ss:list Sig) : list (DH0*DH0) :=
  match ss with
  | [] => []
  | SigH::ss' => hh ++ heads_of ss'
  | SigK::ss' => kk ++ heads_of ss'
  | SigL::ss' => kk ++ heads_of ss'
  end.

Lemma Push_sound :
  (forall ss cs cs' (HP:Push ss cs cs'),
      sideRLs tm (heads_of ss) (pref_of ss *> netword cs) (netword cs')) /\
  (forall s cs cs' (HP:Push1 s cs cs'),
      sideRLs tm (heads_of [s]) (pref_of [s] *> netword cs) (netword cs')).
Proof.
  apply Push_Push1_ind.
  - intros. constructor.
  - intros s ss cs cs1 cs2 H1 IH1 HP IH Htail.
    rewrite Htail in IH. cbn in IH.
    destruct s.
    + cbn [heads_of pref_of] in *. eapply sideRLs_trans; eauto.
    + cbn [heads_of pref_of] in *. eapply sideRLs_trans; eauto.
    + cbn [heads_of pref_of] in *. eapply sideRLs_trans; eauto.
  - intros. cbn [heads_of pref_of netword colword] in *.
    eapply @segRLs_sideRLs_concat with
      (ls1:=hh) (ls2:=hh^^2) (w1:=RD n) (w2:=RD (n+2)).
    + apply H_RD.
    + exact H.
  - intros. cbn [heads_of pref_of netword colword] in *.
    eapply @segRLs_sideRLs_concat with
      (ls1:=kk) (ls2:=kk++hh) (w1:=RD 0) (w2:=RD 2);
      [exact K_RD0|assumption].
  - intros. cbn [heads_of pref_of netword colword] in *.
    eapply @segRLs_sideRLs_concat with
      (ls1:=kk) (ls2:=kk++hh) (w1:=A3) (w2:=A3++B4++B4);
      [exact hash1_A|assumption].
  - intros. cbn [heads_of pref_of netword colword] in *.
    eapply @segRLs_sideRLs_concat with
      (ls1:=kk) (ls2:=kk) (w1:=RD 2) (w2:=RD 2);
      [exact K_RD2|assumption].
  - intros. cbn [heads_of pref_of netword colword] in *.
    eapply @segRLs_sideRLs_concat with
      (ls1:=kk) (ls2:=kk) (w1:=RD 2) (w2:=RD 2);
      [exact K_RD2|assumption].
  - intros. cbn [heads_of pref_of netword colword] in *.
    eapply @segRLs_sideRLs_concat with
      (ls1:=kk) (ls2:=[]) (w1:=RD (n+4)) (w2:=RD1 2 n);
      [apply K_RD4|constructor].
  - intros. cbn [heads_of pref_of netword colword] in *.
    eapply @segRLs_sideRLs_concat with
      (ls1:=kk) (ls2:=kk) (w1:=B4++A3) (w2:=A3++B4);
      [exact hash1_BA|assumption].
  - intros. cbn [heads_of pref_of netword colword] in *.
    eapply @segRLs_sideRLs_concat with
      (ls1:=kk) (ls2:=kk) (w1:=B4++A3) (w2:=A3++B4);
      [exact hash1_BA|assumption].
  - intros. cbn [heads_of pref_of netword colword] in *.
    eapply @segRLs_sideRLs_concat with
      (ls1:=kk) (ls2:=[]) (w1:=B4++RD (n+2)) (w2:=RD1 1 n);
      [apply L_RD2|constructor].
  - intros. cbn [heads_of pref_of netword] in *.
    cbn [colword].
    eapply @segRLs_sideRLs_concat with
      (ls1:=hh) (ls2:=kk++hh) (w1:=RD1 a 0) (w2:=RD (a+2));
      [exact (H_RD1_0 a)|assumption].
  - intros. cbn [heads_of pref_of netword colword] in *.
    rewrite RD1_one, Str_app_assoc.
    eapply @segRLs_sideRLs_concat with
      (ls1:=hh) (ls2:=kk++hh) (w1:=RD1 a 0) (w2:=RD (a+2));
      [exact (H_RD1_0 a)|assumption].
  - intros. cbn [heads_of pref_of netword] in *.
    cbn [colword].
    eapply @segRLs_sideRLs_concat with
      (ls1:=hh) (ls2:=kk) (w1:=RD1 a 2) (w2:=RD (a+2));
      [exact (H_RD1_2 a)|assumption].
  - intros. cbn [heads_of pref_of netword colword] in *.
    rewrite RD1_three, Str_app_assoc.
    eapply @segRLs_sideRLs_concat with
      (ls1:=hh) (ls2:=kk) (w1:=RD1 a 2) (w2:=RD (a+2));
      [exact (H_RD1_2 a)|assumption].
  - intros. cbn [heads_of pref_of netword colword] in *.
    eapply @segRLs_sideRLs_concat with
      (ls1:=hh) (ls2:=[]) (w1:=RD1 a (b+4)) (w2:=RD1 (a+2) b);
      [apply H_RD1_4|constructor].
  - intros. exact hash_edge.
  - intros. exact hash1_edge.
  - intros. exact hash1_B_edge.
Qed.

Lemma Push_sound_main ss cs cs' : Push ss cs cs' ->
  sideRLs tm (heads_of ss) (pref_of ss *> netword cs) (netword cs').
Proof. apply (proj1 Push_sound). Qed.

Lemma Cycle_BigStep cs cs' : Cycle cs cs' -> Config cs -->+ Config cs'.
Proof.
  intro HC. inversion HC as [n n0 n1 n2 n' P0 P1 P2 P3]; subst.
  unfold Config.
  follow restart3.
  pose proof (Push_sound_main _ _ _ P0) as S0.
  cbn [heads_of pref_of] in S0.
  pose proof (segRLs_sideRLs_concat phase0_prefix S0) as F0.
  eapply sideRLs_1 in F0. follow10 F0.
  follow restart0.
  pose proof (Push_sound_main _ _ _ P1) as S1.
  cbn [heads_of pref_of] in S1.
  pose proof (sideRLs_1 _ _ _ _ _
    (segRLs_sideRLs_concat phase1_prefix S1) lh1) as F1.
  eapply evstep_trans with
    (c':=to_DH_config lh1
      ((A3++B4++A3++B4) *> [] *> netword (CRD 2::CRD 4::n0))
      (hR,R)).
  - replace (to_DH_config lh1
      (A3 *> B4 *> A3 *> B4 *> (RD 2 ++ RD 4) *> netword n0) (hR,R))
      with (to_DH_config lh1
        ((A3++B4++A3++B4) *> [] *> netword (CRD 2::CRD 4::n0))
        (hR,R)).
    + apply evstep_refl.
    + unfold RD; cbn [netword colword];
        repeat rewrite Str_app_assoc; reflexivity.
  - eapply evstep_trans with
      (c':=to_DH_config lh1 ((RD 3++RD 5) *> netword n1) (hL,L)).
    + exact (progress_evstep _ _ _ F1).
    + change (lh1 {{{(hL,L)}}} ((RD 3++RD 5) *> netword n1) -->*
        lh3 {{{(hL,L)}}} netword (CRD 4::n')).
      follow restart1.
      pose proof (Push_sound_main _ _ _ P2) as S2.
      cbn [heads_of pref_of] in S2.
      pose proof (sideRLs_1 _ _ _ _ _
        (segRLs_sideRLs_concat hash_B S2) lh2) as F2.
      follow100 F2.
      follow restart2.
      pose proof (Push_sound_main _ _ _ P3) as S3.
      cbn [heads_of pref_of] in S3.
      pose proof (sideRLs_1 _ _ _ _ _
        (segRLs_sideRLs_concat (H_RD 2) S3) lh3) as F3.
      follow100 F3.
      finish.
Qed.

Fixpoint scan (y:nat) (ns:list nat) : list nat :=
  match ns with
  | [] => [y-1]
  | n::ns' => y :: scan (2*y-n) ns'
  end.

Definition transform (ns:list nat) :=
  [4;9;17;34;68] ++ scan 135 ns.

Fixpoint ScanOK (y:nat) (ns:list nat) : Prop :=
  match ns with
  | [] => 0 < y
  | n::ns' => n < 2*y /\ ScanOK (2*y-n) ns'
  end.

(* [sweep y ns] is the state of the column suffix after a signal carrying
   capacity [y] has crossed it.  If the next column is too large, the signal
   is stored in that column as [CRD1]; otherwise it is passed on with the
   updated capacity [2*y-n]. *)
Fixpoint sweep (y:nat) (ns:list nat) : list Col :=
  match ns with
  | [] => [CRD (y-1)]
  | n::ns' =>
      if n <? 2*y then CRD y :: sweep (2*y-n) ns'
      else CRD1 y (n-2*y) :: rdcols ns'
  end.

Lemma Push_single s cs cs' : Push1 s cs cs' -> Push [s] cs cs'.
Proof. intro H; econstructor; [exact H|constructor|reflexivity]. Qed.

Lemma Push_two s t cs cs1 cs2 :
  pref_of [t] = [] -> Push1 s cs cs1 -> Push1 t cs1 cs2 ->
  Push [s;t] cs cs2.
Proof.
  intros E Hs Ht. eapply Push_cons; [exact Hs| |exact E].
  eapply Push_cons; [exact Ht|constructor|reflexivity].
Qed.

(* These three statements are proved together because resolving the stored
   residues 0,1,2,3 emits respectively KH,LH,K,L into the remaining columns. *)
Lemma sweep_rules ns :
  Push1 SigK (rdcols ns) (sweep 2 ns) /\
  Push1 SigL (rdcols ns) (sweep 1 ns) /\
  forall y, 0 < y -> Push1 SigH (sweep y ns) (sweep (y+2) ns).
Proof.
  induction ns as [|n ns IH].
  - split; [constructor|]. split; [constructor|].
    intros y Hy. cbn [rdcols sweep].
    replace (y+2-1) with (y-1+2) by lia.
    apply Push1_H_RD.
    eapply Push_two; [reflexivity|apply Push1_H_edge|apply Push1_H_edge].
  - destruct IH as (IK & IL & IH).
    split.
    + destruct n as [|[|[|[|n]]]]; cbn [rdcols sweep].
      * apply Push1_K_RD0.
        eapply Push_two; [reflexivity|exact IK|apply IH; lia].
      * apply Push1_K_RD1.
        eapply Push_two; [reflexivity|exact IL|apply IH; lia].
      * apply Push1_K_RD2. apply Push_single,IK.
      * apply Push1_K_RD3. apply Push_single,IL.
      * replace (S (S (S (S n))) <? 2*2) with false by
          (symmetry; apply Nat.ltb_ge; lia).
        cbn.
        replace (S (S (S (S n))) - 2 * 2) with n by lia.
        rewrite Nat.sub_0_r.
        replace (S (S (S (S n)))) with (n+4) by lia.
        apply Push1_K_RD4.
    + split.
      * destruct n as [|[|n]]; cbn [rdcols sweep].
        -- apply Push1_L_RD0. apply Push_single,IK.
        -- apply Push1_L_RD1. apply Push_single,IL.
        -- replace (S (S n) <? 2*1) with false by
             (symmetry; apply Nat.ltb_ge; lia).
           cbn.
           replace (S (S n) - 2 * 1) with n by lia.
           rewrite Nat.sub_0_r.
           replace (S (S n)) with (n+2) by lia.
           apply Push1_L_RD2.
      * intros y Hy. cbn [sweep].
        destruct (n <? 2*y) eqn:E.
        -- apply Nat.ltb_lt in E.
           replace (n <? 2*(y+2)) with true by
             (symmetry; apply Nat.ltb_lt; lia).
           cbn.
           replace (y+2+(y+2+0)-n) with (((2*y-n)+2)+2) by lia.
           apply Push1_H_RD.
           eapply Push_two; [reflexivity|exact (IH (2*y-n) (ltac:(lia)))|].
           exact (IH ((2*y-n)+2) (ltac:(lia))).
        -- apply Nat.ltb_ge in E.
           remember (n-2*y) as b eqn:Eb.
           assert (En : n = 2*y+b) by lia. subst n.
           destruct b as [|[|[|[|b]]]].
           ++ replace (2*y+0) with (2*y) by lia.
              replace (2*y <? 2*(y+2)) with true by
                (symmetry; apply Nat.ltb_lt; lia).
              cbn [Nat.add Nat.sub].
              replace (y+2+(y+2+0)-(y+y+0)) with 4 by lia.
              replace (2*(y+2)-2*y) with 4 by lia.
              apply Push1_H_D0.
              eapply Push_two; [reflexivity|exact IK|apply IH; lia].
           ++ replace (2*y+1 <? 2*(y+2)) with true by
                (symmetry; apply Nat.ltb_lt; lia).
              cbn.
              replace (2*(y+2)-(2*y+1)) with 3 by lia.
              replace (y+2+(y+2+0)-(y+(y+0)+1)) with 3 by lia.
              apply Push1_H_D1.
              eapply Push_two; [reflexivity|exact IL|apply IH; lia].
           ++ replace (2*y+2 <? 2*(y+2)) with true by
                (symmetry; apply Nat.ltb_lt; lia).
              cbn.
              replace (2*(y+2)-(2*y+2)) with 2 by lia.
              replace (y+2+(y+2+0)-(y+(y+0)+2)) with 2 by lia.
              apply Push1_H_D2. apply Push_single,IK.
           ++ replace (2*y+3 <? 2*(y+2)) with true by
                (symmetry; apply Nat.ltb_lt; lia).
              cbn.
              assert (Eone : y+2+(y+2+0)-(y+(y+0)+3) = 1%nat).
              { nia. }
              rewrite Eone.
              apply Push1_H_D3. apply Push_single,IL.
           ++ replace (2*y+(b+4) <? 2*(y+2)) with false by
                (symmetry; apply Nat.ltb_ge; lia).
              cbn.
              replace (2*y+(b+4)-2*(y+2)) with b by lia.
              replace (y+(y+0)+S (S (S (S b)))-
                (y+2+(y+2+0))) with b by nia.
              replace (S (S (S (S b)))) with (b+4) by lia.
              destruct (match y+2+(y+2+0) with
                | O => false
                | S m' => y+(y+0)+(b+4) <=? m'
                end) eqn:Eu.
              { exfalso.
                assert (F : (match y+2+(y+2+0) with
                  | O => false
                  | S m' => y+(y+0)+(b+4) <=? m'
                  end) = false).
                { replace (y+2+(y+2+0)) with
                    (S (y+(y+0)+3)) by lia.
                  cbn. apply Nat.leb_gt; lia. }
                congruence. }
              { apply Push1_H_D4. }
Qed.

Lemma pref_Hpow k : pref_of (repeat SigH k) = [].
Proof. destruct k; reflexivity. Qed.

Lemma Hpow0 k y ns : 0 < y ->
  Push (repeat SigH k) (sweep y ns) (sweep (y+2*k) ns).
Proof.
  revert y; induction k as [|k IH]; intros y Hy.
  - cbn. replace (y+0) with y by lia. constructor.
  - cbn [repeat]. replace (y+2*S k) with ((y+2)+2*k) by lia.
    eapply Push_cons.
    + exact (proj2 (proj2 (sweep_rules ns)) y Hy).
    + apply IH; lia.
    + apply pref_Hpow.
Qed.

Lemma Hpow1 k a y ns : 0 < y ->
  Push (repeat SigH k) (CRD a::sweep y ns)
    (CRD (a+2*k)::sweep (y+4*k) ns).
Proof.
  revert a y; induction k as [|k IH]; intros a y Hy.
  - cbn. replace (a+0) with a by lia. replace (y+0) with y by lia.
    constructor.
  - cbn [repeat].
    replace (a+2*S k) with ((a+2)+2*k) by lia.
    replace (y+4*S k) with ((y+4)+4*k) by lia.
    eapply Push_cons with (cs1:=CRD (a+2)::sweep (y+4) ns).
    + apply Push1_H_RD.
      replace (y+4) with (y+2*2) by lia.
      change (Push (repeat SigH 2) (sweep y ns) (sweep (y+2*2) ns)).
      apply Hpow0; exact Hy.
    + apply IH; lia.
    + apply pref_Hpow.
Qed.

Lemma Hpow2 k a b y ns : 0 < y ->
  Push (repeat SigH k) (CRD a::CRD b::sweep y ns)
    (CRD (a+2*k)::CRD (b+4*k)::sweep (y+8*k) ns).
Proof.
  revert a b y; induction k as [|k IH]; intros a b y Hy.
  - cbn. replace (a+0) with a by lia. replace (b+0) with b by lia.
    replace (y+0) with y by lia. constructor.
  - cbn [repeat].
    replace (a+2*S k) with ((a+2)+2*k) by lia.
    replace (b+4*S k) with ((b+4)+4*k) by lia.
    replace (y+8*S k) with ((y+8)+8*k) by lia.
    eapply Push_cons with
      (cs1:=CRD (a+2)::CRD (b+4)::sweep (y+8) ns).
    + apply Push1_H_RD.
      replace (b+4) with (b+2*2) by lia.
      replace (y+8) with (y+4*2) by lia.
      change (Push (repeat SigH 2) (CRD b::sweep y ns)
        (CRD (b+2*2)::sweep (y+4*2) ns)).
      apply Hpow1; exact Hy.
    + apply IH; lia.
    + apply pref_Hpow.
Qed.

Lemma Hpow3 k a b c y ns : 0 < y ->
  Push (repeat SigH k) (CRD a::CRD b::CRD c::sweep y ns)
    (CRD (a+2*k)::CRD (b+4*k)::CRD (c+8*k)::sweep (y+16*k) ns).
Proof.
  revert a b c y; induction k as [|k IH]; intros a b c y Hy.
  - cbn. replace (a+0) with a by lia. replace (b+0) with b by lia.
    replace (c+0) with c by lia. replace (y+0) with y by lia. constructor.
  - cbn [repeat].
    replace (a+2*S k) with ((a+2)+2*k) by lia.
    replace (b+4*S k) with ((b+4)+4*k) by lia.
    replace (c+8*S k) with ((c+8)+8*k) by lia.
    replace (y+16*S k) with ((y+16)+16*k) by lia.
    eapply Push_cons with
      (cs1:=CRD (a+2)::CRD (b+4)::CRD (c+8)::sweep (y+16) ns).
    + apply Push1_H_RD.
      replace (b+4) with (b+2*2) by lia.
      replace (c+8) with (c+4*2) by lia.
      replace (y+16) with (y+8*2) by lia.
      change (Push (repeat SigH 2) (CRD b::CRD c::sweep y ns)
        (CRD (b+2*2)::CRD (c+4*2)::sweep (y+8*2) ns)).
      apply Hpow2; exact Hy.
    + apply IH; lia.
    + apply pref_Hpow.
Qed.

Lemma Hpow4 k a b c d y ns : 0 < y ->
  Push (repeat SigH k) (CRD a::CRD b::CRD c::CRD d::sweep y ns)
    (CRD (a+2*k)::CRD (b+4*k)::CRD (c+8*k)::CRD (d+16*k)::
      sweep (y+32*k) ns).
Proof.
  revert a b c d y; induction k as [|k IH]; intros a b c d y Hy.
  - cbn. replace (a+0) with a by lia. replace (b+0) with b by lia.
    replace (c+0) with c by lia. replace (d+0) with d by lia.
    replace (y+0) with y by lia. constructor.
  - cbn [repeat].
    replace (a+2*S k) with ((a+2)+2*k) by lia.
    replace (b+4*S k) with ((b+4)+4*k) by lia.
    replace (c+8*S k) with ((c+8)+8*k) by lia.
    replace (d+16*S k) with ((d+16)+16*k) by lia.
    replace (y+32*S k) with ((y+32)+32*k) by lia.
    eapply Push_cons with (cs1:=CRD (a+2)::CRD (b+4)::CRD (c+8)::
      CRD (d+16)::sweep (y+32) ns).
    + apply Push1_H_RD.
      replace (b+4) with (b+2*2) by lia.
      replace (c+8) with (c+4*2) by lia.
      replace (d+16) with (d+8*2) by lia.
      replace (y+32) with (y+16*2) by lia.
      change (Push (repeat SigH 2) (CRD b::CRD c::CRD d::sweep y ns)
        (CRD (b+2*2)::CRD (c+4*2)::CRD (d+8*2)::
          sweep (y+16*2) ns)).
      apply Hpow3; exact Hy.
    + apply IH; lia.
    + apply pref_Hpow.
Qed.

Lemma sweep_ok y ns : ScanOK y ns -> sweep y ns = rdcols (scan y ns).
Proof.
  revert y; induction ns as [|n ns IH]; intros y H.
  - cbn [ScanOK sweep scan rdcols]. f_equal; lia.
  - cbn [ScanOK] in H. destruct H as [Hn H].
    cbn [sweep scan rdcols].
    replace (n <? 2*y) with true by
      (symmetry; apply Nat.ltb_lt; exact Hn).
    cbn.
    f_equal. apply IH,H.
Qed.

Lemma rdcols_app xs ys : rdcols (xs++ys) = rdcols xs++rdcols ys.
Proof.
  induction xs as [|a xs IH].
  - reflexivity.
  - change (CRD a::rdcols (xs++ys) = CRD a::(rdcols xs++rdcols ys)).
    now rewrite IH.
Qed.

Lemma Cycle_formula ns : ScanOK 135 ns ->
  Cycle (rdcols ns) (rdcols (transform ns)).
Proof.
  intro H. unfold transform. rewrite rdcols_app. cbn [rdcols].
  rewrite <-sweep_ok by exact H.
  eapply Cycle_intro with
    (n0:=sweep 7 ns)
    (n1:=CRD 10::CRD 20::sweep 39 ns)
    (n2:=CRD 5::CRD 9::CRD 18::CRD 36::sweep 71 ns).
  - eapply Push_cons with (cs1:=sweep 1 ns).
    + exact (proj1 (proj2 (sweep_rules ns))).
    + eapply Push_cons with (cs1:=sweep 3 ns).
      * exact (proj2 (proj2 (sweep_rules ns)) 1%nat (ltac:(lia))).
      * eapply Push_cons with (cs1:=sweep 5 ns).
        -- exact (proj2 (proj2 (sweep_rules ns)) 3 (ltac:(lia))).
        -- apply Push_single. exact (proj2 (proj2 (sweep_rules ns)) 5 (ltac:(lia))).
        -- reflexivity.
      * reflexivity.
    + reflexivity.
  - (* Each incoming H doubles through the two fixed columns, so it raises
       the sweep capacity by eight. *)
    exact (Hpow2 4 2 4 7 ns (ltac:(lia))).
  - (* The four fixed columns turn one H into sixteen H signals. *)
    exact (Hpow4 1 3 5 10 20 39 ns (ltac:(lia))).
  - (* Here each H reaches the suffix as thirty-two H signals. *)
    exact (Hpow4 2 5 9 18 36 71 ns (ltac:(lia))).
Qed.

Lemma q_scan_app n m ys :
  scan (q (n+5)) (map q (seq n m) ++ ys) =
  map q (seq (n+5) m) ++ scan (q (n+m+5)) ys.
Proof.
  revert n; induction m as [|m IH]; intro n.
  - cbn [seq map scan]. replace (n+0+5) with (n+5) by lia.
    reflexivity.
  - cbn [seq map]. change
      (q (n+5) :: scan (2*q (n+5)-q n) (map q (seq (S n) m)++ys) =
       q (n+5) :: (map q (seq (S (n+5)) m)++
         scan (q (n+S m+5)) ys)).
    f_equal.
    replace (2*q (n+5)-q n) with (q (n+6)) by
      (rewrite q_rec; reflexivity).
    replace (n+6) with (S n+5) by lia.
    rewrite (IH (S n)).
    replace (S (n+5)) with (S n+5) by lia.
    replace (S n+m+5) with (n+S m+5) by lia.
    reflexivity.
Qed.

Lemma eval_colZ_pos base e j : j < 8 -> ErrGood base e ->
  (0 < eval_colZ base j e)%Z.
Proof.
  intros Hj HE. unfold ErrGood,zabs_le_nat in HE.
  destruct HE as (H0&H1&H2&H3&H4&H5&H6&H7).
  destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try lia;
    unfold eval_colZ,eget; cbn;
    replace (base+0) with base by lia; lia.
Qed.

Lemma eval_col_spec base e j : j < 8 -> ErrGood base e ->
  Z.of_nat (eval_col base j e) = eval_colZ base j e.
Proof.
  intros Hj HE. pose proof (eval_colZ_pos base e j Hj HE) as Hpos.
  unfold eval_col,eval_colZ in *.
  rewrite Z2Nat.id; [reflexivity|].
  lia.
Qed.

Lemma eval_col_pos base e j : j < 8 -> ErrGood base e ->
  0 < eval_col base j e.
Proof.
  intros Hj HE. apply Nat2Z.inj_lt.
  rewrite eval_col_spec by assumption. cbn. apply eval_colZ_pos; assumption.
Qed.

Lemma nat_sub_of_Z a b c :
  (Z.of_nat a - Z.of_nat b = Z.of_nat c)%Z -> a-b = c.
Proof.
  intro H.
  assert (Hba : b <= a) by (apply Nat2Z.inj_le; lia).
  apply Nat2Z.inj. rewrite Nat2Z.inj_sub by exact Hba. exact H.
Qed.

Lemma nat_sub_sub_of_Z a b c d :
  (Z.of_nat a - Z.of_nat b - Z.of_nat c = Z.of_nat d)%Z ->
  a-b-c = d.
Proof.
  intro H.
  assert (Hba : b <= a) by (apply Nat2Z.inj_le; lia).
  assert (Hc : c <= a-b).
  { apply Nat2Z.inj_le. rewrite Nat2Z.inj_sub by exact Hba. lia. }
  apply Nat2Z.inj.
  rewrite Nat2Z.inj_sub by exact Hc.
  rewrite Nat2Z.inj_sub by exact Hba.
  exact H.
Qed.

Lemma tail8_scan base e : ErrGood base e ->
  scan (q (base+5)) (tail8 base e) =
  q (base+5) :: tail8 (base+6) (enext e).
Proof.
  intro HE.
  assert (E0:=eval_col_spec base e 0 (ltac:(lia)) HE).
  assert (E1:=eval_col_spec base e 1 (ltac:(lia)) HE).
  assert (E2:=eval_col_spec base e 2 (ltac:(lia)) HE).
  assert (E3:=eval_col_spec base e 3 (ltac:(lia)) HE).
  assert (E4:=eval_col_spec base e 4 (ltac:(lia)) HE).
  assert (E5:=eval_col_spec base e 5 (ltac:(lia)) HE).
  assert (E6:=eval_col_spec base e 6 (ltac:(lia)) HE).
  assert (E7:=eval_col_spec base e 7 (ltac:(lia)) HE).
  pose proof (ErrGood_next base e HE) as HE'.
  assert (F0:=eval_col_spec (base+6) (enext e) 0 (ltac:(lia)) HE').
  assert (F1:=eval_col_spec (base+6) (enext e) 1 (ltac:(lia)) HE').
  assert (F2:=eval_col_spec (base+6) (enext e) 2 (ltac:(lia)) HE').
  assert (F3:=eval_col_spec (base+6) (enext e) 3 (ltac:(lia)) HE').
  assert (F4:=eval_col_spec (base+6) (enext e) 4 (ltac:(lia)) HE').
  assert (F5:=eval_col_spec (base+6) (enext e) 5 (ltac:(lia)) HE').
  assert (F6:=eval_col_spec (base+6) (enext e) 6 (ltac:(lia)) HE').
  assert (F7:=eval_col_spec (base+6) (enext e) 7 (ltac:(lia)) HE').
  unfold eval_colZ,eget,enext in E0,E1,E2,E3,E4,E5,E6,E7,
    F0,F1,F2,F3,F4,F5,F6,F7.
  cbn [e0 e1 e2 e3 e4 e5 e6 e7] in E0,E1,E2,E3,E4,E5,E6,E7,
    F0,F1,F2,F3,F4,F5,F6,F7.
  pose proof (q_rec_Z base 0) as R0.
  pose proof (q_rec_Z base 1) as R1.
  pose proof (q_rec_Z base 2) as R2.
  pose proof (q_rec_Z base 3) as R3.
  pose proof (q_rec_Z base 4) as R4.
  pose proof (q_rec_Z base 5) as R5.
  pose proof (q_rec_Z base 6) as R6.
  pose proof (q_rec_Z base 7) as R7.
  fold (enext e) in F0,F1,F2,F3,F4,F5,F6,F7.
  replace (base+0) with base in E0 by lia.
  replace (base+6+0) with (base+6) in F0,R0 by lia.
  replace (base+5+0) with (base+5) in R0 by lia.
  replace (base+0) with base in R0 by lia.
  replace (base+6+1) with (base+7) in F1,R1 by lia.
  replace (base+5+1) with (base+6) in R1 by lia.
  replace (base+6+2) with (base+8) in F2,R2 by lia.
  replace (base+5+2) with (base+7) in R2 by lia.
  replace (base+6+3) with (base+9) in F3,R3 by lia.
  replace (base+5+3) with (base+8) in R3 by lia.
  replace (base+6+4) with (base+10) in F4,R4 by lia.
  replace (base+5+4) with (base+9) in R4 by lia.
  replace (base+6+5) with (base+11) in F5,R5 by lia.
  replace (base+5+5) with (base+10) in R5 by lia.
  replace (base+6+6) with (base+12) in F6,R6 by lia.
  replace (base+5+6) with (base+11) in R6 by lia.
  replace (base+6+7) with (base+13) in F7,R7 by lia.
  replace (base+5+7) with (base+12) in R7 by lia.
  assert (A0 : 2*q (base+5)-eval_col base 0 e =
      eval_col (base+6) 0 (enext e)).
  { apply nat_sub_of_Z. rewrite Nat2Z.inj_mul. lia. }
  assert (A1 : 2*eval_col (base+6) 0 (enext e)-eval_col base 1 e =
      eval_col (base+6) 1 (enext e)).
  { apply nat_sub_of_Z. rewrite Nat2Z.inj_mul. lia. }
  assert (A2 : 2*eval_col (base+6) 1 (enext e)-eval_col base 2 e =
      eval_col (base+6) 2 (enext e)).
  { apply nat_sub_of_Z. rewrite Nat2Z.inj_mul. lia. }
  assert (A3 : 2*eval_col (base+6) 2 (enext e)-eval_col base 3 e =
      eval_col (base+6) 3 (enext e)).
  { apply nat_sub_of_Z. rewrite Nat2Z.inj_mul. lia. }
  assert (A4 : 2*eval_col (base+6) 3 (enext e)-eval_col base 4 e =
      eval_col (base+6) 4 (enext e)).
  { apply nat_sub_of_Z. rewrite Nat2Z.inj_mul. lia. }
  assert (A5 : 2*eval_col (base+6) 4 (enext e)-eval_col base 5 e =
      eval_col (base+6) 5 (enext e)).
  { apply nat_sub_of_Z. rewrite Nat2Z.inj_mul. lia. }
  assert (A6 : 2*eval_col (base+6) 5 (enext e)-eval_col base 6 e =
      eval_col (base+6) 6 (enext e)).
  { apply nat_sub_of_Z. rewrite Nat2Z.inj_mul. lia. }
  assert (A7 : 2*eval_col (base+6) 6 (enext e)-eval_col base 7 e-1 =
      eval_col (base+6) 7 (enext e)).
  { apply nat_sub_sub_of_Z. rewrite Nat2Z.inj_mul. lia. }
  unfold tail8. cbn [scan].
  rewrite A0,A1,A2,A3,A4,A5,A6,A7. reflexivity.
Qed.

Lemma transform_orbit k : transform (orbit k) = orbit (S k).
Proof.
  unfold transform,orbit.
  change ([4;9;17;34;68;135;266] ++
    scan 523 (map q (seq 0 (6*k)) ++ tail8 (6*k) (erriter k)) =
    [4;9] ++ map q (seq 0 (6*S k)) ++
      tail8 (6*S k) (erriter (S k))).
  rewrite <-q_5.
  rewrite q_scan_app with (n:=0%nat) (m:=6*k).
  rewrite tail8_scan by apply erriter_good.
  cbn [erriter].
  replace (6*S k) with (5+6*k+1) by lia.
  rewrite seq_app. cbn [seq map]. rewrite seq_app. cbn [seq map].
  rewrite !map_app. cbn [map].
  rewrite ?q_0, ?q_1, ?q_2, ?q_3, ?q_4.
  replace (0+5) with 5 by lia.
  replace (5+6*k) with (6*k+5) by lia.
  repeat rewrite app_assoc.
  replace (0+(6*k+5)) with (6*k+5) by lia.
  replace (6*k+5+1) with (6*k+6) by lia.
  cbn [app].
  f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. f_equal.
  rewrite <-app_assoc. reflexivity.
Qed.

Lemma q_map_positive xs : Forall (fun n => 0 < n) (map q xs).
Proof. induction xs; cbn; constructor; auto using q_pos. Qed.

Lemma tail8_positive base e : ErrGood base e ->
  Forall (fun n => 0 < n) (tail8 base e).
Proof.
  intro HE. unfold tail8.
  constructor; [apply eval_col_pos; [lia|exact HE]|].
  constructor; [apply eval_col_pos; [lia|exact HE]|].
  constructor; [apply eval_col_pos; [lia|exact HE]|].
  constructor; [apply eval_col_pos; [lia|exact HE]|].
  constructor; [apply eval_col_pos; [lia|exact HE]|].
  constructor; [apply eval_col_pos; [lia|exact HE]|].
  constructor; [apply eval_col_pos; [lia|exact HE]|].
  constructor; [apply eval_col_pos; [lia|exact HE]|constructor].
Qed.

Lemma orbit_positive k : Forall (fun n => 0 < n) (orbit k).
Proof.
  unfold orbit. apply Forall_app. split.
  - repeat constructor; lia.
  - apply Forall_app. split.
    + apply q_map_positive.
    + apply tail8_positive,erriter_good.
Qed.

Lemma ScanOK_pos y ns : ScanOK y ns -> 0 < y.
Proof. destruct ns; cbn [ScanOK]; lia. Qed.

Lemma scan_positive_ok y ns :
  Forall (fun n => 0 < n) (scan y ns) -> ScanOK y ns.
Proof.
  revert y; induction ns as [|n ns IH]; intros y HP.
  - cbn [scan ScanOK] in *. inversion HP; lia.
  - cbn [scan] in HP. inversion HP as [|? ? Hy HP']; subst.
    cbn [ScanOK].
    pose proof (IH (2*y-n) HP') as HOK.
    split; [pose proof (ScanOK_pos _ _ HOK); lia|exact HOK].
Qed.

Lemma orbit_scan_ok k : ScanOK 135 (orbit k).
Proof.
  apply scan_positive_ok.
  pose proof (orbit_positive (S k)) as HP.
  rewrite <-transform_orbit in HP.
  unfold transform in HP. apply Forall_app in HP. exact (proj2 HP).
Qed.

Lemma orbit_cycle k : Cycle (rdcols (orbit k)) (rdcols (orbit (S k))).
Proof. rewrite <-transform_orbit. apply Cycle_formula,orbit_scan_ok. Qed.

Lemma orbit_progress k : Config (rdcols (orbit k)) -->+
  Config (rdcols (orbit (S k))).
Proof. apply Cycle_BigStep,orbit_cycle. Qed.

Lemma macro_nonhalt : ~halts tm (Config (rdcols init_ns)).
Proof.
  rewrite <-orbit_0.
  eapply progress_nonhalt_cond with
    (C:=fun k : nat => Config (rdcols (orbit k)))
    (P:=fun _ : nat => True).
  - intros k _. exists (S k). split; [apply orbit_progress|trivial].
  - trivial.
Qed.

Theorem nonhalt : ~halts tm c0.
Proof. eapply multistep_nonhalt; [exact init|exact macro_nonhalt]. Qed.

Print Assumptions nonhalt.

End TM11.
