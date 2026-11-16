From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Module Class1.

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

End Class1.


Module Class2.

Fixpoint RC x :=
match x with
| [] => 0inf
| x0::x1 => [1]^^x0 *> [0] *> RC x1
end.

Definition Config:Type := nat*(list nat).

Definition f0 a b c d r :=
(match b with
| 0 => Some (0,a+c::2+d::r) (* Ov0 *)
| 1 => Some (0,3+a+c::d::r) (* Ov1 *)
| 2 =>
  match a with
  | 0 => Some (0,1::3+c::d::r) (* Ov2_0 *)
  | 1 => None (* Ov2_1 *)
  | S (S a0) => Some (0,a0::1::3+c::d::r) (* Ov2 *)
  end
| S (S (S b0)) => Some (1+a,b0::2+c::d::r) (*Inc1*)
end)%nat.

Definition C '(a,x) :=
  0inf <* <[1]^^a <* [0] <{{A}} [] *> RC x.

Definition C' '(a,x) :=
  0inf <* <[1]^^a <* [0] <{{A}} [1;1] *> RC x.

Definition f '(a,r) :=
match r with
| [] => f0 a 0 0 0 []
| [r0] => f0 a r0 0 0 []
| [r0;r1] => f0 a r0 r1 0 []
| r0::r1::r2::r3 => f0 a r0 r1 r2 r3
end.

Definition cfg0:Config := (0,[])%nat.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 to_config :=
  erewrite <-(halts_iff _ _ _ f to_config (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [a r] _;
  unfold f,f0,to_config;
  destruct r as [|b [|c [|d r]]];
  repeat des_nat;
  try (split; trivial);
  cbn[RC]; solve[esx].

Module TM10_8.
Definition tm := TM_from_str "1RB1LA_1LA0RC_1LD1RC_0LF1LE_1LC0LA_---1LE".
Definition tm' := TM_from_str "1RB1LA_1RC0RC_1LD1RC_1LA1LE_1LF0LA_---0LD".

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 C'.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 C.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM10_8.


Module TM18_8.
Definition tm := TM_from_str "1RB1LA_1LA0RC_1LD1RC_0LD1LE_1LF0LA_---1RC".
Definition tm' := TM_from_str "1RB1LA_1RC0RC_1LD1RC_1LA1LE_1LF0LA_---0LD".

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 C'.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 C.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM18_8.

End Class2.

Module Class3.

Fixpoint RC x :=
match x with
| [] => 0inf
| x0::x1 => [1]^^x0 *> [0] *> RC x1
end.

Definition Config:Type := nat*(list nat).

Definition f0 a b c d r :=
(match b with
| 2 => Some (0,4+a+c::d::r) (* Ov2 *)
| 1 => Some (0,3+a+c::d::r) (* Ov1 *)
| 0 =>
  match a with
  | 0 => Some (0,1::1+c::d::r) (* Ov0_0 *)
  | 1 => None (* Ov0_1 *)
  | S (S a0) => Some (0,a0::1::1+c::d::r) (* Ov0 *)
  end
| S (S (S b0)) => Some (1+a,b0::2+c::d::r) (*Inc1*)
end)%nat.

Definition C '(a,x) :=
  0inf <* <[1]^^a <* [0] <{{B}} [1] *> RC x.

Definition f '(a,r) :=
match r with
| [] => f0 a 0 0 0 []
| [r0] => f0 a r0 0 0 []
| [r0;r1] => f0 a r0 r1 0 []
| r0::r1::r2::r3 => f0 a r0 r1 r2 r3
end.

Definition cfg0:Config := (0,[12])%nat.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 to_config :=
  erewrite <-(halts_iff _ _ _ f to_config (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [a r] _;
  unfold f,f0,to_config;
  destruct r as [|b [|c [|d r]]];
  repeat des_nat;
  try (split; trivial);
  cbn[RC]; solve[esx].

Module TM21_13.
Definition tm := TM_from_str "1RB0LB_1RC1LB_0LD0RE_---1LC_1LF1RE_0LF1LA".
Definition tm' := TM_from_str "1LB0LF_1RC1LB_---0RD_1LE1RD_0LE1LA_1LC1LB".

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 C.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 C.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM21_13.

End Class3.


