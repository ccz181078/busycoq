From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Fixpoint RC x :=
match x with
| [] => 0inf
| x0::x1 => [1]^^x0 *> [0] *> RC x1
end.

Definition Config:Type := nat*(list nat).

Definition to_config '(a,x) :=
  0inf <* <[1]^^a <* [0] <{{A}} [1] *> RC x.

Definition f0 a b c d r :=
(match c with
| O =>
match b with
| O =>
match a with
| O => None (*Ov0_0*)
| S O => Some (0,3::1+d::r) (*Ov0_1*)
| S (S a0) => Some (0,a0::0::1::1+d::r) (*Ov0*)
end
| S O => Some (0,4+a+d::r) (*Ov1*)
| S (S b0) => Some (1+a,b0::0::1+d::r) (*Inc1*)
end
| S c0 => Some (1+a,b::c0::d::r) (*Inc2*)
end)%nat.

Definition f '(a,r) :=
match r with
| [] => f0 a 0 0 0 []
| [r0] => f0 a r0 0 0 []
| [r0;r1] => f0 a r0 r1 0 []
| r0::r1::r2::r3 => f0 a r0 r1 r2 r3
end.

Definition cfg0:Config := (0,[2])%nat.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 :=
  erewrite <-(halts_iff _ _ _ f to_config (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [a r] _;
  unfold f,f0,to_config;
  destruct r as [|b [|c [|d r]]];
  repeat des_nat;
  try (split; trivial);
  cbn[RC]; solve[esx].

Module TM39_34.
Definition tm := TM_from_str "1RB1LA_1LC0RE_1LF0LD_1RD1LA_1RC1RE_---0LC".
Definition tm' := TM_from_str "1RB1LA_0RC0RD_1LC1LA_1RE1RD_1LF0LA_---0LE".

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

End TM39_34.

Module TM43_34.
Definition tm := TM_from_str "1RB1LA_1RC0RE_1LD0LF_---1LA_1RF1RE_1LC0LA".
Definition tm' := TM_from_str "1RB1LA_0RC0RD_1LC1LA_1RE1RD_1LF0LA_---0LE".

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

End TM43_34.


