From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import DivModCases.

Module TM1.
Definition tm := TM_from_str "1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---1RC".
Definition tm' := TM_from_str "1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC".

Inductive LD := D11 | D10 | D1.

Inductive Config :=
| cfg1(l:list LD)(c' b:nat)
| cfg2(l:list LD)(c' b c:nat)
| cfg3(c' a b:nat)
.

Notation "l <| r" := (l <{{B}} 0>>r) (at level 30).

Section to_config_sec.
Hypothesis s:sym.
Definition w := <[1;s;1;s;1].

Fixpoint LC ls c :=
match ls with
| [] => 0inf <* w^^c <* <[0;0]
| D11::t => LC t c <* <[1;s]
| D10::t => LC t c <* <[1;0]
| D1::t => LC t c <* <[1]
end.

Definition to_config x :=
match x with
| cfg1 l c b => LC l c <* <[0;0] <* <[1;0]^^b {{A}}> 0inf
| cfg2 l c' b c => LC (D1::l) c' <* <[0] <* <[0;1]^^b {{D}}> [0] *> [1]^^c *> 0inf
| cfg3 c' a b => 0inf <* w^^c' <* <[0;0] <| [1]^^(2+a) *> [0] *> [1]^^b *> 0inf
end.

Fixpoint sum ls :=
match ls with
| [] => O
| D11::t => (sum t)+2
| D10::t => (sum t)+2
| D1::t => (sum t)+1
end.

Lemma LC_ws n:
  LC ([D1;D11;D11]^^n) 0 = 0inf <* w^^n.
Proof.
  induction n; cbn.
  1: solve_const0_eq.
  congruence.
Qed.

Lemma LC_D10s n m:
  LC ([D10]^^n) m = 0inf <* w^^m <* <[0;0] <* <[1;0]^^n.
Proof.
  induction n; cbn.
  1: trivial.
  rewrite IHn; trivial.
Qed.

End to_config_sec.

Lemma LL l r c:
  LC 0 l c <| r -[ tm' ]->*
  0inf <* (w 0)^^c <* <[0;0] <| [1]^^(sum l) *> r.
Proof.
  gen r.
  induction l as [|[] t]; cbn; intros.
  all: es; er; follow; es.
Qed.

Lemma LL' l r c:
  LC 1 l c <| r -[ tm ]->*
  0inf <* (w 1)^^c <* <[0;0] <| [1]^^(sum l) *> r.
Proof.
  gen r.
  induction l as [|[] t]; cbn; intros.
  all: es; er; follow; es.
Qed.

Definition f x :=
(match x with
| cfg1 l c b =>
  match b with
  | 0 => Some (cfg3 c ((sum l)+4) 0)
  | S b => Some (cfg1 (D1::D11::D11::l) c b)
  end
| cfg2 l c' b c =>
  match b with
  | 0 => Some (cfg3 c' ((sum l)+c) 0)
  | 1 => Some (cfg3 c' ((sum l)) (1+c))
  | 2 =>
    match c with
    | 0 => None
    | 1 => Some (cfg3 c' ((sum l)+7) 0)
    | S (S c) =>
      match mod2 c with
      | mod2eq0 c => Some (cfg2 (D11::D11::D11::D1::l) c' c 0)
      | mod2eq1 c => Some (cfg1 (D1::D11::D11::D11::D1::l) c' c)
      end
    end
  | S (S (S b)) => Some (cfg2 (D11::D11::D1::l) c' b (1+c))
  end
| cfg3 c a b =>
  match a with
  | 0 =>
    match mod2 b with
    | mod2eq0 b => Some (cfg2 (D11::D11::[D1;D11;D11]^^c) 0 b 0)
    | mod2eq1 b => Some (cfg1 ([D1;D11;D11]^^(1+c)) 0 b)
    end
  | S a =>
    match mod2 a with
    | mod2eq0 a => Some (cfg2 (D11::D11::[D1;D11;D11]^^c) 0 a b)
    | mod2eq1 a =>
      match b with
      | 0 => Some (cfg1 ([D1;D11;D11]^^(1+c)) 0 a)
      | S b =>
        match mod2 b with
        | mod2eq0 b => Some (cfg2 ([D10]^^a) (1+c) (b) 0)
        | mod2eq1 b => Some (cfg1 (D1::[D10]^^a) (1+c) b)
        end
      end
    end
  end
end)%nat.

Definition cfg0 := cfg3 0 0 0.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | mod2eq0 _ => _ | _ => _ end] =>
  destruct a; subst
end.

Ltac solve_v1 s :=
  erewrite <-(halts_iff _ _ _ f (to_config s) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config,w in *;
  repeat des_nat;
  try (split; trivial);
  cbn;
  repeat (rewrite LC_ws || rewrite LC_D10s);
  try solve[esx; er; follow; es].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  pose proof LL'.
  solve_v1 1.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  pose proof LL.
  solve_v1 0.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM1.


Module TM2.
Definition tm := TM_from_str "1LB1LD_0RC1LA_1LA1RC_1LA1RE_1LF0RD_---0LE".
Definition tm' := TM_from_str "1LB1LD_0RC1LA_1LA1RC_0LB1RE_1LF0RD_---0LE".

Definition to_config '(a,b,c) := 0inf <* [1]^^(a) <{{D}} [1;1]^^(b) *> [1;0]^^(c) *> 0inf.
Definition cfg0 := (0,1,0)%nat.

Definition f '(a,b,c) :=
(match a with
| 0 =>
  match c with
  | 0 => Some (1+b*2,1,0)
  | 1 => Some (2+b*2,1,0)
  | S (S c) => Some (2+b*2,1,1+c)
  end
| 1 =>
  match c with
  | 0 => None
  | 1 => Some (3+b*2,1,0)
  | S (S c) => Some (4+b*2,1,c)
  end
| 2 =>
  match c with
  | 0 => Some (2,1,b)
  | S c => Some (0,2+b,c)
  end
| 3 =>
  match c with
  | 0 => Some (4,1,b)
  | S c => Some (1,2+b,c)
  end
| S (S (S (S a))) =>
  match c with
  | 0 => Some (a,2,1+b)
  | S c => Some (2+a,2+b,c)
  end
end)%nat.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 :=
  erewrite <-(halts_iff _ _ _ f to_config (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [[a b] c] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM2.


Module TM3.
Definition tm := TM_from_str "1RB1RA_0RC1RF_1LD---_0LE1LE_1RA1LD_1LD0LF".
Definition tm' := TM_from_str "1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC".

Definition to_config '(a,b,c) := 0inf <{{E}} [1;1]^^(2+a) *> [0]^^(1+b*2) *> [1]^^c *> [0;1] *> 0inf.

Definition f '(a,b,c) :=
(match b with
| O =>
  match c with
  | O => None
  | S O => Some (0,1,9+a*2)
  | S (S c) => Some (0,3+a,c)
  end
| S O =>
  match c with
  | O => Some (0,1,11+a*2)
  | S c => Some (0,4+a,c)
  end
| S (S b) => Some (3+a,b,c)
end)%nat.

Definition cfg0 := (0,1,5)%nat.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 :=
  erewrite <-(halts_iff _ _ _ f to_config (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [[a b] c] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM3.


Module TM4.
Definition tm := TM_from_str "1LB1RE_1LC1LA_0RD1LB_1RB1RD_1LF0RA_---0LE".
Definition tm' := TM_from_str "1LB1LD_0RC1LA_1RA1RC_1LA1RE_1LF0RD_---0LE".

Definition to_config (q:Q) '(a,b,c) := 0inf <* [1]^^(a) <{{ q }} [1;1]^^(b) *> [1;0]^^(c) *> 0inf.
Definition cfg0 := (0,250,5)%nat.

Definition f '(a,b,c) :=
(match a with
| 0 =>
  match c with
  | 0 => Some (1+b*2,1,1)
  | 1 => Some (2+b*2,1,1)
  | S (S c) => Some (4+b*2,0,1+c)
  end
| 1 =>
  match c with
  | 0 => None
  | 1 => Some (3+b*2,1,1)
  | 2 => Some (4+b*2,1,1)
  | S (S (S c)) => Some (6+b*2,0,1+c)
  end
| 2 =>
  match c with
  | 0 =>
    match b with
    | 0 => Some (2,1,1)
    | S b => Some (4,0,1+b)
    end
  | S c => Some (0,2+b,c)
  end
| 3 =>
  match c with
  | 0 =>
    match b with
    | 0 => Some (4,1,1)
    | S b => Some (6,0,1+b)
    end
  | S c => Some (1,2+b,c)
  end
| S (S (S (S a))) =>
  match c with
  | 0 => Some (a,2,1+b)
  | S c => Some (2+a,2+b,c)
  end
end)%nat.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 q :=
  erewrite <-(halts_iff _ _ _ f (to_config q) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; shelve | ];
  intros [[a b] c] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  solve[esx].

Ltac stepn n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; simpl_tape; try reflexivity.

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A.
  Unshelve.
  stepn 2002118%N.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D.
  Unshelve.
  stepn 2095634%N.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM4.


