From BusyCoq Require Import Individual25.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Open Scope list.

Definition tm := Eval compute in (TM_from_str "1RB0LB2LA4LB3LA_2LA---3RA4RB2RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LS :=
| L0(n1:nat)
| L1(n1:nat)
| L2(n1:nat)
| L3(n1 n2:nat)
| L4(n1 n2:nat)
| L5(n1:nat)
| L6(n1:nat)
| L7(n1 n2:nat)
| L8(n1 n2:nat)
| L9(n1 n2:nat)
| L10(n1 n2:nat)
| L11(n1:nat)
| L12(n1:nat)
| L13(n1:nat)
| L14(n1 n2:nat)
| L15(n1 n2:nat)
.

Definition LC(x:LS) :=
match x with
| L0 n1 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;2;4; 4;2]
| L1 n1 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;2;4; 2;2;4]
| L2 n1 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;2;4; 2;2;2;2]
| L3 n1 n2 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;2;2;2;4;4] <* <[2;2]^^n2 <* <[4;4]
| L4 n1 n2 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;2;2;2;4;4] <* <[2;2]^^n2 <* <[4;2;2]
| L5 n1 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;4;4;2;4]
| L6 n1 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;4;4;2;2;2]
| L7 n1 n2 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;4;2;2;4] <* <[2;2]^^n2 <* <[4;4]
| L8 n1 n2 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;4;2;2;4] <* <[2;2]^^n2 <* <[4;2;2]
| L9 n1 n2 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;2;4] <* <[2;2]^^n2 <* <[4;4]
| L10 n1 n2 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;2;4] <* <[2;2]^^n2 <* <[4;2;2]
| L11 n1 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;2;4; 2;2;4;2]
| L12 n1 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;2;4; 2;2;2;2;4]
| L13 n1 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;2;4; 2;2;2;2;2;2]
| L14 n1 n2 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;2;2;2;4;4;4;4] <* <[2;2]^^n2 <* <[4;4]
| L15 n1 n2 => 0inf <* <[1;3;1] <* [4] <* <[2;2;4]^^n1 <* <[4;2;2;2;4;4;4;4] <* <[2;2]^^n2 <* <[4;2;2]
end.

Definition Lnxt'(x:LS):LS :=
match x with
| L0 n1 => L1 n1
| L1 n1 => L2 n1
| L2 n1 => L3 n1 0
| L3 n1 n2 => L4 n1 n2
| L4 n1 n2 => L3 n1 (S n2)
| L5 n1 => L6 n1
| L6 n1 => L7 n1 0
| L7 n1 n2 => L8 n1 n2
| L8 n1 n2 => L7 n1 (S n2)
| L9 n1 n2 => L10 n1 n2
| L10 n1 n2 => L9 n1 (S n2)
| L11 n1 => L12 n1
| L12 n1 => L13 n1
| L13 n1 => L14 n1 0
| L14 n1 n2 => L15 n1 n2
| L15 n1 n2 => L14 n1 (S n2)
end.

Notation "l <|' r" := (l <{{B}} [4] *> r) (at level 30).
Notation "l <| r" := (l <{{A}} r) (at level 30).
Notation "l |> r" := (l {{B}}> r) (at level 30).

Lemma Lnxt'_spec x r:
  LC x <|' r -->+
  LC (Lnxt' x) |> r.
Proof.
  destruct x; cbn; es.
Qed.

Definition Lnxt(x:LS):LS*(list nat) :=
match x with
| L0 n1 => (L0 n1,[0;1]%nat)
| L1 n1 => (L0 n1,[1;1;0]%nat)
| L2 n1 => (L0 n1,[1;1;1;1]%nat)
| L3 n1 n2 => (L5 (S n1),([1;1]^^n2 ++ [0;0])%nat)
| L4 n1 n2 => (L5 (S n1),([1;1]^^n2 ++ [0;1;1])%nat)
| L5 n1 => (L9 n1 0,[1;0]%nat)
| L6 n1 => (L9 n1 0,[1;1;1]%nat)
| L7 n1 n2 => (L11 n1,([1;1]^^n2 ++ [0;0])%nat)
| L8 n1 n2 => (L11 n1,([1;1]^^n2 ++ [0;1;1])%nat)
| L9 n1 n2 => (L0 n1,([1;1]^^n2 ++ [0;0])%nat)
| L10 n1 n2 => (L0 n1,([1;1]^^n2 ++ [0;1;1])%nat)
| L11 n1 => (L0 n1,[1;1;0;1]%nat)
| L12 n1 => (L0 n1,[1;1;1;1;0]%nat)
| L13 n1 => (L0 n1,[1;1;1;1;1;1]%nat)
| L14 n1 n2 => (L5 (S n1),([0;0] ++ [1;1]^^n2 ++ [0;0])%nat)
| L15 n1 n2 => (L5 (S n1),([0;0] ++ [1;1]^^n2 ++ [0;1;1])%nat)
end.

Definition Rmp(b:nat):sym :=
match b with
| O => 3
| _ => 2
end.

Lemma map_lpow{T T0}(ls:list T)(f:T->T0) n:
  map f (ls^^n) =
  (map f ls)^^n.
Proof.
  induction n; cbn.
  1: trivial.
  rewrite map_app.
  rewrite IHn.
  trivial.
Qed.

Ltac rw_map :=
  cbn;
  repeat (rewrite map_app || rewrite map_lpow);
  cbn;
  repeat rewrite Str_app_assoc.

Lemma Lnxt_spec x r:
  let (y0,y1):=Lnxt x in
  LC x <| r -->+
  LC y0 |> (map Rmp y1) *> r.
Proof.
  destruct x; cbn.
  all: rw_map; es.
Qed.

Inductive Config :=
| cfgR(x:LS)(ls1 ls2:list nat)
| cfgL(x:LS)(ls1 ls2:list nat)
| cfgL'(x:LS)(ls1 ls2:list nat)
.

Definition Lmp(b:nat):sym :=
match b with
| O => 4
| _ => 2
end.

Definition to_config(cfg:Config) :=
match cfg with
| cfgR x ls1 ls2 => LC x <* (map Lmp ls1) |> (map Rmp ls2) *> 0inf
| cfgL x ls1 ls2 => LC x <* (map Lmp ls1) <| (map Rmp ls2) *> 0inf
| cfgL' x ls1 ls2 => LC x <* (map Lmp ls1) <|' (map Rmp ls2) *> 0inf
end.

Lemma BigStep c:
  exists c',
  to_config c -->+
  to_config c'.
Proof.
  destruct c.
  - destruct ls2 as [|[|] ls2].
    + exists (cfgL x ls1 [1]%nat); es.
    + exists (cfgR x (0%nat::ls1) ls2); es.
    + destruct ls2 as [|[|] ls2].
      * exists (cfgL x ls1 [0;1;1]%nat); es.
      * exists (cfgR x (1::0::ls1)%nat ls2); es.
      * exists (cfgL' x ls1 (1::ls2)%nat); es.
  - destruct ls1 as [|[|] ls1].
    + exists (let (y0,y1):=Lnxt x in cfgR y0 [] (y1++ls2)).
      epose proof (Lnxt_spec x _) as E.
      destruct (Lnxt x) as (y0,y1).
      cbn.
      rw_map.
      apply E.
    + exists (cfgL x ls1 (0::ls2)%nat); es.
    + exists (cfgL x ls1 (1::ls2)%nat); es.
  - destruct ls1 as [|[|] ls1].
    + exists (cfgR (Lnxt' x) [] ls2).
      apply Lnxt'_spec.
    + exists (cfgR x (1::1::ls1)%nat ls2); es.
    + exists (cfgL' x ls1 (0::ls2)%nat); es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgR (L0 2) [] [1;1;0;1;1;1;0;1;1]%nat)).
  1: er.
  eapply progress_nonhalt_simple.
  apply BigStep.
Qed.

