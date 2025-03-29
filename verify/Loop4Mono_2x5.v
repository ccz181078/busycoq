From BusyCoq Require Import Individual25.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Open Scope list.

Fixpoint sum n (ls:list nat) :=
match ls with
| [] => n
| h::t => S h+sum n t
end.

Fixpoint sum' n ls :=
match ls with
| [] => [n]
| h::t => (sum n ls)::(sum' n t)
end.

Lemma sum'_length n ls:
  length (sum' n ls) = S (length ls).
Proof.
  induction ls; cbn.
  1: reflexivity.
  rewrite IHls.
  reflexivity.
Qed.

Lemma sum_S n ls:
  sum (S n) ls = S (sum n ls).
Proof.
  induction ls.
  1: reflexivity.
  cbn.
  lia.
Qed.

Lemma sum'_S n ls:
  sum' (S n) ls = map S (sum' n ls).
Proof.
  induction ls.
  1: reflexivity.
  cbn.
  rewrite <-IHls.
  rewrite sum_S.
  f_equal.
  lia.
Qed.

Lemma sum_O ls a:
  sum O (ls++[a]) = S (sum a ls).
Proof.
  induction ls.
  1: cbn; lia.
  cbn.
  rewrite IHls.
  lia.
Qed.

Lemma sum'_O ls a:
  sum' O (ls++[a]) = map S (sum' a ls) ++ [O].
Proof.
  induction ls.
  1: cbn; f_equal; lia.
  cbn.
  rewrite <-IHls.
  rewrite sum_O.
  f_equal.
  lia.
Qed.

Ltac ind' i:=
  induction i as [|h t IHi]; intros;
  es; er;
  try (
  follow IHi;
  es).

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB3RA4RB---2LB_2LA4RB0RA1LA1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint L0 ls :=
match ls with
| [] => 0inf <* <[1;0]
| h::t => L0 t <* <[4;0]^^h <* <[3]
end.

Fixpoint L1 ls l :=
match ls with
| [] => l
| h::t => L1 t l <* <[4;0]^^h <* [4]
end.

Lemma Inc1 ls0 ls1 n r:
  L1 ls1 (L0 (S n::ls0)) <{{B}} r -->*
  L1 ls1 (L0 ls0 <* <[4;0]^^n <* <[4;1]) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc2 ls0 ls1 n r:
  L1 ls1 (L0 ls0 <* <[4;0]^^n <* <[4;1]) <{{B}} r -->*
  L1 (ls1++[n]) (L0 ls0) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc3 ls1 r:
  L1 ls1 (L0 []) <{{B}} r -->*
  L1 ls1 (0inf<*[3]) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc4 ls1 r:
  L1 ls1 (0inf<*[3]) <{{B}} r -->*
  L1 ls1 (0inf<*[1]) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc5 ls1 r:
  L1 ls1 (0inf<*[1]) <{{B}} r -->*
  L1 ls1 (0inf) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc6 ls1 r:
  L1 ls1 (0inf) <{{B}} r -->*
  L0 ls1 {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc7 ls1 r:
  L1 ls1 (L0 [O]) <{{B}} r -->*
  L1 ls1 (0inf<* <[1;1]) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc8 ls1 r:
  L1 ls1 (0inf<* <[1;1]) <{{B}} r -->*
  L1 ls1 (0inf<*[1]) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc12 ls0 ls1 n m:
  L1 ls1 (L0 (S n::ls0)) <{{B}} [2;2]^^(m) *> 0inf -->*
  L1 (ls1++[n]) (L0 ls0) <{{B}} [2;2]^^(2+m) *> 0inf.
Proof.
  follow Inc1.
  es; er.
  follow Inc2.
  es.
Qed.

Lemma Incs12 ls0 ls0' ls1 m:
  L1 ls1 (L0 ((map S ls0)++ls0')) <{{B}} [2;2]^^m *> 0inf -->*
  L1 (ls1++ls0) (L0 (ls0')) <{{B}} [2;2]^^((length ls0)*2+m) *> 0inf.
Proof.
  gen ls0 ls1 m.
  induction ls0; cbn; intros.
  1: rewrite app_nil_r; finish.
  follow Inc12.
  follow IHls0.
  rewrite <-app_assoc; cbn.
  es.
Qed.

Definition S0 ls :=
  L1 [] (L0 (ls++[])) <{{B}} [2;2]^^1 *> 0inf.

Lemma BigStep_S ls:
  S0 (map S ls) -->+
  S0 ((4+(length ls)*2)::ls).
Proof.
  follow Incs12.
  follow Inc3.
  es; er.
  follow Inc4.
  es; er.
  follow Inc5.
  es; er.
  follow Inc6.
  rewrite app_nil_r.
  es.
Qed.

Lemma BigStep_O ls:
  S0 ((map S ls)++[O]) -->+
  S0 ((4+(length ls)*2)::ls).
Proof.
  unfold S0.
  rewrite <-app_assoc.
  follow Incs12.
  follow Inc7.
  es; er.
  follow Inc8.
  es; er.
  follow Inc5.
  es; er.
  follow Inc6.
  rewrite app_nil_r.
  es.
Qed.

Definition config '(n,ls) := S0 (sum' n ls).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (2,[3])%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(n,ls) => ls<>[] /\ sum n ls <= (length ls)*2+4).
  2: cbn; split; [congruence|lia].
  intros [n ls] [Hls Hs].
  destruct n as [|n].
  - pose proof (exists_last Hls) as [ls' [a' Ha']].
    subst ls.
    exists (a',((length ls')*2+5-sum a' ls')::ls').
    rewrite sum_O in Hs.
    rewrite length_app in Hs.
    cbn in Hs.
    split.
    + unfold config.
      rewrite sum'_O.
      follow10 BigStep_O.
      finish.
      f_equal.
      rewrite sum'_length.
      cbn. f_equal. lia.
    + split.
      1: congruence.
      cbn. lia.
  - exists (n,((length ls)*2+5-sum n ls)::ls).
    rewrite sum_S in Hs.
    split.
    + unfold config.
      rewrite sum'_S.
      follow10 BigStep_S.
      finish.
      f_equal.
      rewrite sum'_length.
      cbn. f_equal. lia.
    + split.
      1: congruence.
      cbn. lia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB3LA4RB---2LB_2LA4RB0RA1RA1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint L0 ls l :=
match ls with
| [] => l
| h::t => L0 t l <* <[4;0]^^h <* <[4;1;1]
end.

Fixpoint L1 ls l :=
match ls with
| [] => l
| h::t => L1 t l <* <[4;0]^^h <* [4]
end.

Lemma Inc1 ls0 ls1 l n r:
  L1 ls1 (L0 (n::ls0) l) <{{B}} r -->*
  L1 ls1 (L0 ls0 l <* <[4;0]^^n <* <[4;1]) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc2 ls0 ls1 l n r:
  L1 ls1 (L0 ls0 l <* <[4;0]^^n <* <[4;1]) <{{B}} r -->*
  L1 (ls1++[n]) (L0 ls0 l) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc3 ls1 r:
  L1 ls1 (L0 [] (0inf <* <[1;0])) <{{B}} r -->*
  L1 ls1 (0inf <* <[1;1]) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc4 ls1 r:
  L1 ls1 (0inf <* <[1;1]) <{{B}} r -->*
  L1 ls1 (0inf <* [1]) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc5 ls1 r:
  L1 ls1 (0inf<*[1]) <{{B}} r -->*
  L1 ls1 (0inf) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc6 ls1 r:
  L1 (map S ls1) (0inf) <{{B}} r -->*
  L0 ls1 (0inf <* <[1;0]) {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc7 ls1 r:
  L1 ls1 (L0 [O] (0inf <* <[1;0])) <{{B}} r -->*
  L1 ls1 (0inf<* <[1;0;4;1]) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc8 ls1 r:
  L1 ls1 (0inf<* <[1;0;4;1]) <{{B}} r -->*
  L1 (ls1++[O]) (L0 [] (0inf <* <[1;0])) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc9 ls1 r:
  L1 ((map S ls1) ++ [O]) (0inf) <{{B}} r -->*
  L0 ls1 (0inf <* <[1;1;1]) {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc3' ls1 r:
  L1 ls1 (L0 [] (0inf <* <[1;1;1])) <{{B}} r -->*
  L1 ls1 (0inf <* <[1;1]) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc7' ls1 r:
  L1 ls1 (L0 [O] (0inf <* <[1;1;1])) <{{B}} r -->*
  L1 ls1 (0inf<* <[1;1;1;4;1]) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc8' ls1 r:
  L1 ls1 (0inf<* <[1;1;1;4;1]) <{{B}} r -->*
  L1 (ls1++[O]) (0inf<* <[1;1;1]) <* [4] {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc12 ls0 ls1 l n m:
  L1 ls1 (L0 (n::ls0) l) <{{B}} [2;2]^^(m) *> 0inf -->*
  L1 (ls1++[n]) (L0 ls0 l) <{{B}} [2;2]^^(2+m) *> 0inf.
Proof.
  follow Inc1.
  es; er.
  follow Inc2.
  es.
Qed.

Lemma Incs12 ls0 ls0' ls1 l m:
  L1 ls1 (L0 (ls0++ls0') l) <{{B}} [2;2]^^m *> 0inf -->*
  L1 (ls1++ls0) (L0 (ls0') l) <{{B}} [2;2]^^((length ls0)*2+m) *> 0inf.
Proof.
  gen ls0 ls1 m.
  induction ls0; cbn; intros.
  1: rewrite app_nil_r; finish.
  follow Inc12.
  follow IHls0.
  rewrite <-app_assoc; cbn.
  es.
Qed.

Definition S0 l ls :=
  L1 [] (L0 (ls++[]) l) <{{B}} [2;2]^^1 *> 0inf.

Lemma BigStep_S_1 ls:
  S0 (0inf <* <[1;0]) (map S ls) -->+
  S0 (0inf <* <[1;0]) ((3+(length ls)*2)::ls).
Proof.
  follow Incs12.
  follow Inc3.
  es; er.
  follow Inc4.
  es; er.
  follow Inc5.
  es; er.
  follow Inc6.
  rewrite app_nil_r.
  rewrite length_map.
  es.
Qed.

Lemma BigStep_O_1 ls:
  S0 (0inf <* <[1;0]) ((map S ls)++[O]) -->+
  S0 (0inf <* <[1;1;1]) ((5+(length ls)*2)::ls).
Proof.
  unfold S0.
  rewrite <-app_assoc.
  follow Incs12.
  follow Inc7.
  es; er.
  follow Inc8.
  es; er.
  follow Inc3.
  es; er.
  follow Inc4.
  es; er.
  follow Inc5.
  es; er.
  follow Inc9.
  rewrite app_nil_r.
  rewrite length_map.
  es.
Qed.

Lemma BigStep_S_2 ls:
  S0 (0inf <* <[1;1;1]) (map S ls) -->+
  S0 (0inf <* <[1;0]) ((3+(length ls)*2)::ls).
Proof.
  follow Incs12.
  follow Inc3'.
  es; er.
  follow Inc4.
  es; er.
  follow Inc5.
  es; er.
  follow Inc6.
  rewrite app_nil_r.
  rewrite length_map.
  es.
Qed.

Lemma BigStep_O_2 ls:
  S0 (0inf <* <[1;1;1]) ((map S ls)++[O]) -->+
  S0 (0inf <* <[1;1;1]) ((5+(length ls)*2)::ls).
Proof.
  unfold S0.
  rewrite <-app_assoc.
  follow Incs12.
  follow Inc7'.
  es; er.
  follow Inc8'.
  es; er.
  follow Inc3'.
  es; er.
  follow Inc4.
  es; er.
  follow Inc5.
  es; er.
  follow Inc9.
  rewrite app_nil_r.
  rewrite length_map.
  es.
Qed.

Definition mp(tp:bool) :=
  0inf <* (if tp then <[1;0] else <[1;1;1]).

Definition config '(n,ls,tp) := S0 (mp tp) (sum' n ls).

Lemma BigStep_O ls tp:
  S0 (mp tp) ((map S ls)++[O]) -->+
  S0 (mp false) ((5+(length ls)*2)::ls).
Proof.
  destruct tp; cbn.
  - apply BigStep_O_1.
  - apply BigStep_O_2.
Qed.

Lemma BigStep_S ls tp:
  S0 (mp tp) (map S ls) -->+
  S0 (mp true) ((3+(length ls)*2)::ls).
Proof.
  destruct tp; cbn.
  - apply BigStep_S_1.
  - apply BigStep_S_2.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (1,[3],true)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(n,ls,tp) => ls<>[] /\ sum n ls <= (length ls)*2+5).
  2: cbn; split; [congruence|lia].
  intros [[n ls] tp] [Hls Hs].
  destruct n as [|n].
  - pose proof (exists_last Hls) as [ls' [a' Ha']].
    subst ls.
    exists (a',((length ls')*2+6-sum a' ls')::ls',false).
    rewrite sum_O in Hs.
    rewrite length_app in Hs.
    cbn in Hs.
    split.
    + unfold config.
      rewrite sum'_O.
      follow10 BigStep_O.
      finish.
      f_equal.
      rewrite sum'_length.
      cbn. f_equal. lia.
    + split.
      1: congruence.
      cbn. lia.
  - exists (n,((length ls)*2+4-sum n ls)::ls,true).
    rewrite sum_S in Hs.
    split.
    + unfold config.
      rewrite sum'_S.
      follow10 BigStep_S.
      finish.
      f_equal.
      rewrite sum'_length.
      cbn. f_equal. lia.
    + split.
      1: congruence.
      cbn. lia.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1LB0RB4RA2RB2LA_2RA4RA3LB---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint L0 ls l :=
match ls with
| [] => l
| h::t => L0 t l <* <[4;0]^^h <* <[4;2;2]
end.

Fixpoint L1 ls l :=
match ls with
| [] => l
| h::t => L1 t l <* <[4;0]^^h <* [4]
end.

Lemma Inc1 ls0 ls1 l n r:
  L1 ls1 (L0 (n::ls0) l) <{{A}} r -->*
  L1 ls1 (L0 ls0 l <* <[4;0]^^n <* <[4;2]) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc2 ls0 ls1 l n r:
  L1 ls1 (L0 ls0 l <* <[4;0]^^n <* <[4;2]) <{{A}} r -->*
  L1 (ls1++[n]) (L0 ls0 l) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc3 ls1 r:
  L1 ls1 (L0 [] (0inf <* <[2;0])) <{{A}} r -->*
  L1 ls1 (0inf <* <[2;2]) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc4 ls1 r:
  L1 ls1 (0inf <* <[2;2]) <{{A}} r -->*
  L1 ls1 (0inf <* [2]) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc5 ls1 r:
  L1 ls1 (0inf<*[2]) <{{A}} r -->*
  L1 ls1 (0inf) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc6 ls1 r:
  L1 (map S ls1) (0inf) <{{A}} r -->*
  L0 ls1 (0inf <* <[2;0]) {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc7 ls1 r:
  L1 ls1 (L0 [O] (0inf <* <[2;0])) <{{A}} r -->*
  L1 ls1 (0inf<* <[2;0;4;2]) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc8 ls1 r:
  L1 ls1 (0inf<* <[2;0;4;2]) <{{A}} r -->*
  L1 (ls1++[O]) (L0 [] (0inf <* <[2;0])) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc9 ls1 r:
  L1 ((map S ls1) ++ [O]) (0inf) <{{A}} r -->*
  L0 ls1 (0inf <* <[2;2;2]) {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc3' ls1 r:
  L1 ls1 (L0 [] (0inf <* <[2;2;2])) <{{A}} r -->*
  L1 ls1 (0inf <* <[2;2]) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc7' ls1 r:
  L1 ls1 (L0 [O] (0inf <* <[2;2;2])) <{{A}} r -->*
  L1 ls1 (0inf<* <[2;2;2;4;2]) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc8' ls1 r:
  L1 ls1 (0inf<* <[2;2;2;4;2]) <{{A}} r -->*
  L1 (ls1++[O]) (0inf<* <[2;2;2]) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc12 ls0 ls1 l n m:
  L1 ls1 (L0 (n::ls0) l) <{{A}} [1;1]^^(m) *> 0inf -->*
  L1 (ls1++[n]) (L0 ls0 l) <{{A}} [1;1]^^(2+m) *> 0inf.
Proof.
  follow Inc1.
  es; er.
  follow Inc2.
  es.
Qed.

Lemma Incs12 ls0 ls0' ls1 l m:
  L1 ls1 (L0 (ls0++ls0') l) <{{A}} [1;1]^^m *> 0inf -->*
  L1 (ls1++ls0) (L0 (ls0') l) <{{A}} [1;1]^^((length ls0)*2+m) *> 0inf.
Proof.
  gen ls0 ls1 m.
  induction ls0; cbn; intros.
  1: rewrite app_nil_r; finish.
  follow Inc12.
  follow IHls0.
  rewrite <-app_assoc; cbn.
  es.
Qed.

Definition S0 l ls :=
  L1 [] (L0 (ls++[]) l) <{{A}} [1;1]^^1 *> 0inf.

Lemma BigStep_S_1 ls:
  S0 (0inf <* <[2;0]) (map S ls) -->+
  S0 (0inf <* <[2;0]) ((3+(length ls)*2)::ls).
Proof.
  follow Incs12.
  follow Inc3.
  es; er.
  follow Inc4.
  es; er.
  follow Inc5.
  es; er.
  follow Inc6.
  rewrite app_nil_r.
  rewrite length_map.
  es.
Qed.

Lemma BigStep_O_1 ls:
  S0 (0inf <* <[2;0]) ((map S ls)++[O]) -->+
  S0 (0inf <* <[2;2;2]) ((5+(length ls)*2)::ls).
Proof.
  unfold S0.
  rewrite <-app_assoc.
  follow Incs12.
  follow Inc7.
  es; er.
  follow Inc8.
  es; er.
  follow Inc3.
  es; er.
  follow Inc4.
  es; er.
  follow Inc5.
  es; er.
  follow Inc9.
  rewrite app_nil_r.
  rewrite length_map.
  es.
Qed.

Lemma BigStep_S_2 ls:
  S0 (0inf <* <[2;2;2]) (map S ls) -->+
  S0 (0inf <* <[2;0]) ((3+(length ls)*2)::ls).
Proof.
  follow Incs12.
  follow Inc3'.
  es; er.
  follow Inc4.
  es; er.
  follow Inc5.
  es; er.
  follow Inc6.
  rewrite app_nil_r.
  rewrite length_map.
  es.
Qed.

Lemma BigStep_O_2 ls:
  S0 (0inf <* <[2;2;2]) ((map S ls)++[O]) -->+
  S0 (0inf <* <[2;2;2]) ((5+(length ls)*2)::ls).
Proof.
  unfold S0.
  rewrite <-app_assoc.
  follow Incs12.
  follow Inc7'.
  es; er.
  follow Inc8'.
  es; er.
  follow Inc3'.
  es; er.
  follow Inc4.
  es; er.
  follow Inc5.
  es; er.
  follow Inc9.
  rewrite app_nil_r.
  rewrite length_map.
  es.
Qed.

Definition mp(tp:bool) :=
  0inf <* (if tp then <[2;0] else <[2;2;2]).

Definition config '(n,ls,tp) := S0 (mp tp) (sum' n ls).

Lemma BigStep_O ls tp:
  S0 (mp tp) ((map S ls)++[O]) -->+
  S0 (mp false) ((5+(length ls)*2)::ls).
Proof.
  destruct tp; cbn.
  - apply BigStep_O_1.
  - apply BigStep_O_2.
Qed.

Lemma BigStep_S ls tp:
  S0 (mp tp) (map S ls) -->+
  S0 (mp true) ((3+(length ls)*2)::ls).
Proof.
  destruct tp; cbn.
  - apply BigStep_S_1.
  - apply BigStep_S_2.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (2,[2],true)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(n,ls,tp) => ls<>[] /\ sum n ls <= (length ls)*2+5).
  2: cbn; split; [congruence|lia].
  intros [[n ls] tp] [Hls Hs].
  destruct n as [|n].
  - pose proof (exists_last Hls) as [ls' [a' Ha']].
    subst ls.
    exists (a',((length ls')*2+6-sum a' ls')::ls',false).
    rewrite sum_O in Hs.
    rewrite length_app in Hs.
    cbn in Hs.
    split.
    + unfold config.
      rewrite sum'_O.
      follow10 BigStep_O.
      finish.
      f_equal.
      rewrite sum'_length.
      cbn. f_equal. lia.
    + split.
      1: congruence.
      cbn. lia.
  - exists (n,((length ls)*2+4-sum n ls)::ls,true).
    rewrite sum_S in Hs.
    split.
    + unfold config.
      rewrite sum'_S.
      follow10 BigStep_S.
      finish.
      f_equal.
      rewrite sum'_length.
      cbn. f_equal. lia.
    + split.
      1: congruence.
      cbn. lia.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB0RB4RA2LB2LA_2RA4RA3RB---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint L0 ls :=
match ls with
| [] => 0inf <* <[2;0]
| h::t => L0 t <* <[4;0]^^h <* <[3]
end.

Fixpoint L1 ls l :=
match ls with
| [] => l
| h::t => L1 t l <* <[4;0]^^h <* [4]
end.

Lemma Inc1 ls0 ls1 n r:
  L1 ls1 (L0 (S n::ls0)) <{{A}} r -->*
  L1 ls1 (L0 ls0 <* <[4;0]^^n <* <[4;2]) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc2 ls0 ls1 n r:
  L1 ls1 (L0 ls0 <* <[4;0]^^n <* <[4;2]) <{{A}} r -->*
  L1 (ls1++[n]) (L0 ls0) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc3 ls1 r:
  L1 ls1 (L0 []) <{{A}} r -->*
  L1 ls1 (0inf<*[3]) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc4 ls1 r:
  L1 ls1 (0inf<*[3]) <{{A}} r -->*
  L1 ls1 (0inf<*[2]) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc5 ls1 r:
  L1 ls1 (0inf<*[2]) <{{A}} r -->*
  L1 ls1 (0inf) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc6 ls1 r:
  L1 ls1 (0inf) <{{A}} r -->*
  L0 ls1 {{B}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc7 ls1 r:
  L1 ls1 (L0 [O]) <{{A}} r -->*
  L1 ls1 (0inf<* <[2;2]) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc8 ls1 r:
  L1 ls1 (0inf<* <[2;2]) <{{A}} r -->*
  L1 ls1 (0inf<*[2]) <* [4] {{A}}> r.
Proof.
  gen r.
  ind' ls1.
Qed.

Lemma Inc12 ls0 ls1 n m:
  L1 ls1 (L0 (S n::ls0)) <{{A}} [1;1]^^(m) *> 0inf -->*
  L1 (ls1++[n]) (L0 ls0) <{{A}} [1;1]^^(2+m) *> 0inf.
Proof.
  follow Inc1.
  es; er.
  follow Inc2.
  es.
Qed.

Lemma Incs12 ls0 ls0' ls1 m:
  L1 ls1 (L0 ((map S ls0)++ls0')) <{{A}} [1;1]^^m *> 0inf -->*
  L1 (ls1++ls0) (L0 (ls0')) <{{A}} [1;1]^^((length ls0)*2+m) *> 0inf.
Proof.
  gen ls0 ls1 m.
  induction ls0; cbn; intros.
  1: rewrite app_nil_r; finish.
  follow Inc12.
  follow IHls0.
  rewrite <-app_assoc; cbn.
  es.
Qed.

Definition S0 ls :=
  L1 [] (L0 (ls++[])) <{{A}} [1;1]^^1 *> 0inf.

Lemma BigStep_S ls:
  S0 (map S ls) -->+
  S0 ((4+(length ls)*2)::ls).
Proof.
  follow Incs12.
  follow Inc3.
  es; er.
  follow Inc4.
  es; er.
  follow Inc5.
  es; er.
  follow Inc6.
  rewrite app_nil_r.
  es.
Qed.

Lemma BigStep_O ls:
  S0 ((map S ls)++[O]) -->+
  S0 ((4+(length ls)*2)::ls).
Proof.
  unfold S0.
  rewrite <-app_assoc.
  follow Incs12.
  follow Inc7.
  es; er.
  follow Inc8.
  es; er.
  follow Inc5.
  es; er.
  follow Inc6.
  rewrite app_nil_r.
  es.
Qed.

Definition config '(n,ls) := S0 (sum' n ls).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (3,[2])%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(n,ls) => ls<>[] /\ sum n ls <= (length ls)*2+4).
  2: cbn; split; [congruence|lia].
  intros [n ls] [Hls Hs].
  destruct n as [|n].
  - pose proof (exists_last Hls) as [ls' [a' Ha']].
    subst ls.
    exists (a',((length ls')*2+5-sum a' ls')::ls').
    rewrite sum_O in Hs.
    rewrite length_app in Hs.
    cbn in Hs.
    split.
    + unfold config.
      rewrite sum'_O.
      follow10 BigStep_O.
      finish.
      f_equal.
      rewrite sum'_length.
      cbn. f_equal. lia.
    + split.
      1: congruence.
      cbn. lia.
  - exists (n,((length ls)*2+5-sum n ls)::ls).
    rewrite sum_S in Hs.
    split.
    + unfold config.
      rewrite sum'_S.
      follow10 BigStep_S.
      finish.
      f_equal.
      rewrite sum'_length.
      cbn. f_equal. lia.
    + split.
      1: congruence.
      cbn. lia.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB0LB3LB4RB---_1LA2RB3RA2LB1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [2]*>r) (at level 30).
Notation "l |> r" := (l<*[4] {{B}}> r) (at level 30).

Fixpoint L0 l ls :=
match ls with
| [] => l
| n::ls0 => L0 l ls0 <* [2] <* <[3;1]^^n <* [3]
end.

Fixpoint L1 l ls :=
match ls with
| [] => l
| n::ls0 => L1 l ls0 <* [4] <* <[3;1]^^n <* [3]
end.

Lemma LInc l r n ls0 ls1:
  L0 (L1 l (n::ls1)) ls0 <| r -->*
  L0 (L1 l ls1) (ls0++[n]) |> r.
Proof.
  gen l r n ls1.
  ind' ls0.
Qed.

Lemma LOv0 r ls:
  L0 (0inf <* <[1;2;3]) ls <| r -->*
  L1 (0inf <* <[2;3]) (ls++[O]) {{A}}> r.
Proof.
  gen r.
  ind' ls.
Qed.

Lemma LOv1 r ls:
  L0 (0inf <* <[2;3]) ls <| r -->*
  L1 (0inf <* <[1;2;3]) (ls++[O]) {{A}}> r.
Proof.
  gen r.
  ind' ls.
Qed.

Definition lh(x:bool) := 0inf <* (if x then <[1;2;3] else <[2;3]).

Definition S0 '(l,ls1,ls0,n) :=
  L0 (L1 (lh l) ls1) ls0 <| [3] *> [3;3]^^n *> [1] *> 0inf.

Lemma LInc2 l n1 n2 ls0 ls1 n:
  S0 (l,n1::n2::ls1,ls0,n) -->+
  S0 (l,ls1,ls0++[n1;n2],S n).
Proof.
  unfold S0.
  follow LInc.
  es; er.
  follow LInc.
  rewrite <-app_assoc.
  es; er.
Qed.

Lemma LOv l n0 ls n:
  S0 (l,[],n0::ls,n) -->+
  S0 (negb l,ls++[O],[O;(n+n0)],O).
Proof.
  unfold S0.
  cbn[L1].
  remember (n0::ls) as ls0.
  destruct l.
  - follow LOv0.
    es; er.
    subst ls0.
    epose proof (LInc _ _ n0 [] (ls++[O])) as HLInc.
    follow HLInc.
    es.
  - follow LOv1.
    es; er.
    subst ls0.
    epose proof (LInc _ _ n0 [] (ls++[O])) as HLInc.
    follow HLInc.
    es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (true,[],[O;O],O)).
  1: er.
  eapply progress_nonhalt_cond with (P:=fun '(_,ls1,ls0,_) => Nat.Even (length ls1) /\ Nat.Even (length ls0) /\ []<>ls0).
  2:{
    cbn; repeat split.
    - exists O; trivial.
    - exists 1%nat; trivial.
    - congruence.
  }
  intros [[[l ls1] ls0] n] [[l1 Hls1] [[l0 Hls0] Hls0']].
  destruct ls1 as [|n1 [|n2 ls1]].
  - destruct ls0 as [|n0 ls0].
    1: congruence.
    cbn in Hls0.
    eexists (_,_,_,_).
    repeat split.
    1: apply LOv.
    + exists (l0).
      rewrite List.length_app; cbn; lia.
    + exists 1%nat.
      cbn; trivial.
    + congruence.
  - cbn in Hls1.
    lia.
  - cbn in Hls1.
    eexists (_,_,_,_).
    repeat split.
    1: apply LInc2.
    + exists (l1-1).
      lia.
    + exists (S l0).
      rewrite List.length_app; cbn; lia.
    + destruct ls0; cbn;
      congruence.
Qed.

End TM5.


