From BusyCoq Require Import BBinf Individual62.
Require Import Ascii String List PeanoNat NArith.


Lemma Permute_halts_iff tm tm' f q t:
  Perm tm tm' f ->
  halts tm (q,t) <->
  halts tm' (f q,t).
Proof.
  intro H.
  split; intro.
  - eapply perm_halts; eauto.
  - eapply perm_halts'; eauto.
Qed.

Open Scope N.

Definition Q_from_char'(x:ascii):Q :=
match Q_from_char x with
| Some y => y
| _ => A
end.

Fixpoint mp_from_str(x:string)(n:Q):Q :=
match x with
| String x0 (String x1 (String x2 (String x3 (String x4 (String x5 _))))) =>
  match n with
  | A => Q_from_char' x0
  | B => Q_from_char' x1
  | C => Q_from_char' x2
  | D => Q_from_char' x3
  | E => Q_from_char' x4
  | F => Q_from_char' x5
  end
| _ => n
end.

Ltac solve_evstep T :=
  eapply without_counter;
  eapply multistep_c_spec with (n:=N.to_nat T);
  vm_compute;
  simpl_tape;
  reflexivity.

Ltac solve_eqv tm tm' f T1 T2 :=
  rewrite (halts_evstep_iff tm);
  [ | solve_evstep T1 ];
  rewrite (halts_evstep_iff tm');
  [ | solve_evstep T2 ];
  eapply (Permute_halts_iff tm tm' f);
  split;
  [ intros q s; destruct q,s; cbn; congruence
  | intros q s s' d q'; destruct q,s; cbn; intros H; inverts H; reflexivity ].


Module TM1.
Definition tm := TM_from_str "1RB0LC_1LC0RE_1RB1LD_1LA1LD_---0RF_1LA1RF".
Definition tm' := TM_from_str "1RB1LC_1LA0RE_1LD1LC_1RB0LA_---0RF_1LD1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBACEF") 1 1.
Time Qed.
End TM1.


Module TM2.
Definition tm := TM_from_str "1RB---_1LC1LD_0RB0LC_0RE1LB_1RB1RF_0RA1RE".
Definition tm' := TM_from_str "1RB1RE_1LC1LD_0RB0LC_0RA1LB_0RF1RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2.


Module TM3.
Definition tm := TM_from_str "1RB1RA_1RC0RB_0LC0LD_1LA1LE_0RB0LF_---1LD".
Definition tm' := TM_from_str "1RB0RA_0LB0LC_1LD1LE_1RA1RD_0RA0LF_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 8 1.
Time Qed.
End TM3.


Module TM4.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_0LB---_1RA0LD".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEFB") 8 1.
Time Qed.
End TM4.


Module TM5.
Definition tm := TM_from_str "1RB1LE_0RC0LD_1LD1LA_0LA0RF_0LB1LF_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1LE_0LE0RA_1RB1LF_0LB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM5.


Module TM6.
Definition tm := TM_from_str "1LB0LB_1RC0LF_1RD1LA_0RF1RE_0RC---_0LA0RD".
Definition tm' := TM_from_str "1RB0LD_1RC1LE_0RD1RF_0LE0RC_1LA0LA_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCFD") 1 12.
Time Qed.
End TM6.


Module TM7.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA1RF_1RD---".
Definition tm' := TM_from_str "1RB---_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEDBFA") 1 6.
Time Qed.
End TM7.


Module TM8.
Definition tm := TM_from_str "1LB1LE_1LC0RC_0RD0LA_1RB1RE_0RC1RF_0RC---".
Definition tm' := TM_from_str "1RB1RE_1LC0RC_0RA0LD_1LB1LE_0RC1RF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 17.
Time Qed.
End TM8.


Module TM9.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RD1LB_0LA1RE_0RA0RF_0LE---".
Definition tm' := TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA0RB_0RD0RF_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 3 4.
Time Qed.
End TM9.


Module TM10.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC0LF_1RE---".
Definition tm' := TM_from_str "1RB---_1LC0LA_1RF0LD_0LE0RD_0RC0LB_1LE0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FECDBA") 25 44.
Time Qed.
End TM10.


Module TM11.
Definition tm := TM_from_str "1RB1LC_1LA0RF_0LD---_0LE1LE_0LB0RF_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1RB1LD_0LE---_0LF1LF_0LB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM11.


Module TM12.
Definition tm := TM_from_str "1RB1LA_0LA0RC_1RD1LB_1RB0RE_0RB1RF_1RA---".
Definition tm' := TM_from_str "1RB0RE_0LC0RD_1RB1LC_1RA1LB_0RB1RF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDAEF") 1 1.
Time Qed.
End TM12.


Module TM13.
Definition tm := TM_from_str "1RB---_1LC1LB_1RD1RC_0LE0RD_1LB0LF_0LA1LE".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_0LE1LC_1RF---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 1 5.
Time Qed.
End TM13.


Module TM14.
Definition tm := TM_from_str "1RB1RA_0LC0RB_1LF0LD_0LE1LC_1RC---_1LA1LF".
Definition tm' := TM_from_str "1RB---_1LC0LF_1LD1LC_1RE1RD_0LB0RE_0LA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBFAC") 5 1.
Time Qed.
End TM14.


Module TM15.
Definition tm := TM_from_str "1RB0LE_0RC0RB_0LD1LA_1LD0LA_1RB0LF_---0LA".
Definition tm' := TM_from_str "1RB0LF_0RC0RB_0LD1LE_1LD0LE_1RB0LA_---0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM15.


Module TM16.
Definition tm := TM_from_str "1RB1RC_1LC0RE_---0LD_1LA1LD_1RB0RF_0LD0RA".
Definition tm' := TM_from_str "1RB0RF_1LC0RA_---0LD_1LE1LD_1RB1RC_0LD0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM16.


Module TM17.
Definition tm := TM_from_str "1LB1RD_0LC0LC_0LD1LF_1LE0RE_1RA1RE_---1LB".
Definition tm' := TM_from_str "1RB1RA_1LC1RE_0LD0LD_0LE1LF_1LA0RA_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 2 3.
Time Qed.
End TM17.


Module TM18.
Definition tm := TM_from_str "1RB0LC_1LA0RD_1LA0LA_1RE0RD_1RA0RF_0RD---".
Definition tm' := TM_from_str "1RB0RF_1RC0LD_1LB0RE_1LB0LB_1RA0RE_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 105 107.
Time Qed.
End TM18.


Module TM19.
Definition tm := TM_from_str "1RB0LE_1RC1RE_0LC1LD_1LF0RB_0RD1RF_0LA---".
Definition tm' := TM_from_str "1RB1RF_0LB1LC_1LD0RA_0LE---_1RA0LF_0RC1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCFD") 6 16.
Time Qed.
End TM19.


Module TM20.
Definition tm := TM_from_str "1RB0RF_0LC1RA_1RD1LB_0RE---_0LB1RE_1LF0RC".
Definition tm' := TM_from_str "1RB1LD_0RC---_0LD1RC_0LA1RE_1RD0RF_1LF0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDABCF") 1 3.
Time Qed.
End TM20.


Module TM21.
Definition tm := TM_from_str "1LB0LF_0RC0LD_1RB1RA_1LE0RD_1RA1LA_---0LC".
Definition tm' := TM_from_str "1RB1LB_1LC0LE_0RF0LD_1LA0RD_---0LF_1RC1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFDAE") 3 1.
Time Qed.
End TM21.


Module TM22.
Definition tm := TM_from_str "1LB1LE_0RC0LD_1LD1RC_0LA1RB_0LB1LF_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_1LB1LF_0LB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 7 1.
Time Qed.
End TM22.


Module TM23.
Definition tm := TM_from_str "1LB0RA_1RC1LF_1LD1RC_1RA1LE_1LC0LD_0RC---".
Definition tm' := TM_from_str "1RB1LF_1LC0RB_1RE1LD_0RE---_1LA1RE_1LE0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEAFD") 2 5.
Time Qed.
End TM23.


Module TM24.
Definition tm := TM_from_str "1RB0RF_1RC0RA_0LD0RB_0LA1LE_0LA0RD_1LC---".
Definition tm' := TM_from_str "1RB0RE_0LC0RA_0LE1LD_0LE0RC_1RA0RF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 5 2.
Time Qed.
End TM24.


Module TM25.
Definition tm := TM_from_str "1RB0RD_1RC1RA_1LD0RB_0RF0LE_1LA1LD_---0RC".
Definition tm' := TM_from_str "1RB1RE_1LC0RA_0RF0LD_1LE1LC_1RA0RC_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 12 1.
Time Qed.
End TM25.


Module TM26.
Definition tm := TM_from_str "1LB1RE_0RC0LE_1RE1RD_1RB0RB_1LF0LC_---0LA".
Definition tm' := TM_from_str "1RB1RF_1LC0LA_---0LD_1LE1RB_0RA0LB_1RE0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 2 9.
Time Qed.
End TM26.


Module TM27.
Definition tm := TM_from_str "1LB1RA_0LC0LD_1RC0RA_---0LE_1RF1LE_1RB0RC".
Definition tm' := TM_from_str "1RB0RC_0LC0LE_1RC0RD_1LB1RD_---0LF_1RA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 4.
Time Qed.
End TM27.


Module TM28.
Definition tm := TM_from_str "1LB1RC_0LC0LE_0RD0RF_1RA0RB_1LB0LC_1RD---".
Definition tm' := TM_from_str "1RB---_1RC0RD_1LD1RF_0LF0LE_1LD0LF_0RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFBEA") 3275 3220.
Time Qed.
End TM28.


Module TM29.
Definition tm := TM_from_str "1RB0RA_1LC0RA_1RB1LD_0LE---_0LF0RF_0LB0RC".
Definition tm' := TM_from_str "1RB1LC_1LA0RF_0LD---_0LE0RE_0LB0RA_1RB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBACDE") 1 1.
Time Qed.
End TM29.


Module TM30.
Definition tm := TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LA1RC_1RF0RB_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1RF_1RD0LC_1LE1RC_1RB1LE_1RA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM30.


Module TM31.
Definition tm := TM_from_str "1LB0RE_1RC1RB_0LD0RC_1LA0LE_0LF1LD_1RD---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_0LE1LC_1RC---_1LA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 4 5.
Time Qed.
End TM31.


Module TM32.
Definition tm := TM_from_str "1RB1LE_0RC0LD_1LD1LA_0LA0RF_0LB1LD_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1LE_0LE0RA_1RB1LF_0LB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM32.


Module TM33.
Definition tm := TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF0RE_1RA---_0RA0LA".
Definition tm' := TM_from_str "1RB---_1RC1RE_1LD0LD_0RE0LC_1RF0RA_0RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 31 23.
Time Qed.
End TM33.


Module TM34.
Definition tm := TM_from_str "1LB1RA_0RA0LC_0LD0LE_1RC1LD_1RE1RF_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 8 8.
Time Qed.
End TM34.


Module TM35.
Definition tm := TM_from_str "1RB1RE_1RC0LF_1LD---_0RE0LD_0RF1RA_1LD1LF".
Definition tm' := TM_from_str "1RB0LE_1LC---_0RD0LC_0RE1RF_1LC1LE_1RA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 7 6.
Time Qed.
End TM35.


Module TM36.
Definition tm := TM_from_str "1RB0LD_1RC0RB_1RD0RF_0RE1RF_0LF---_1LA0LD".
Definition tm' := TM_from_str "1RB0RA_1RC0RE_0RD1RE_0LE---_1LF0LC_1RA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 230 218.
Time Qed.
End TM36.


Module TM37.
Definition tm := TM_from_str "1LB---_1RC0LE_1RD0RC_1RE0RF_0LD0LF_1LA0RE".
Definition tm' := TM_from_str "1RB0RA_1RC0RD_0LB0LD_1LE0RC_1LF---_1RA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 11 10.
Time Qed.
End TM37.


Module TM38.
Definition tm := TM_from_str "1LB1LE_1RC0LC_0LA0RD_1RB1RE_0LC0LF_1RA---".
Definition tm' := TM_from_str "1RB1RE_1RC0LC_0LD0RA_1LB1LE_0LC0LF_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 19 1.
Time Qed.
End TM38.


Module TM39.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0LF_1LC1RB_1RB---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1RC_0LC0LF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM39.


Module TM40.
Definition tm := TM_from_str "1RB1LE_0RC0LD_1LD1LF_0LA0RA_0LB1LC_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1LA_0LE0RE_1RB1LF_0LB1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM40.


Module TM41.
Definition tm := TM_from_str "1LB0LE_0RC1RE_0LA1RD_1LE0RF_1LA0RB_1RE---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1LD0LB_0RE1RB_0LC1RF_1LB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 6 1.
Time Qed.
End TM41.


Module TM42.
Definition tm := TM_from_str "1RB0RA_1LC0RA_1RF1LD_0LE---_0LF1LF_0LB0RA".
Definition tm' := TM_from_str "1RB1LE_0LC0RD_1LA0RD_1RC0RD_0LF---_0LB1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCAEFB") 1 4.
Time Qed.
End TM42.


Module TM43.
Definition tm := TM_from_str "1LB0RE_1RC1RB_0LD0RC_1LA0LE_1LF1LD_1RC---".
Definition tm' := TM_from_str "1RB---_0LC0RB_1LE0LD_1LA1LC_1LF0RD_1RB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 2 5.
Time Qed.
End TM43.


Module TM44.
Definition tm := TM_from_str "1LB1LC_1RC0LC_0LF0RD_1RE---_1LF0RC_0RD0LA".
Definition tm' := TM_from_str "1RB0LB_0LC0RE_0RE0LD_1LA1LB_1RF---_1LC0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABEFC") 1 4.
Time Qed.
End TM44.


Module TM45.
Definition tm := TM_from_str "1LB0RA_1RC0LF_1LD1RC_1RA1LE_1LC0LD_0RB---".
Definition tm' := TM_from_str "1RB1LF_1LC0RB_1RE0LD_0RC---_1LA1RE_1LE0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEAFD") 1 4.
Time Qed.
End TM45.


Module TM46.
Definition tm := TM_from_str "1LB1RF_0RC---_1RE1LD_0LC0RE_0RA0LA_0RD1RE".
Definition tm' := TM_from_str "1RB1LE_0RC0LC_1LD1RF_0RA---_0LA0RB_0RE1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEBF") 38 24.
Time Qed.
End TM46.


Module TM47.
Definition tm := TM_from_str "1LB1RE_0RB0LC_0RD0LF_1RA---_1RD1LB_0LB0RA".
Definition tm' := TM_from_str "1RB1LD_1RC---_1LD1RA_0RD0LE_0RB0LF_0LD0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBAF") 1 9.
Time Qed.
End TM47.


Module TM48.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_1RF0LD_1LC---".
Definition tm' := TM_from_str "1RB0LD_1LC---_1RE1RA_1RC0RE_1LF1RD_1LC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCDAB") 1 6.
Time Qed.
End TM48.


Module TM49.
Definition tm := TM_from_str "1LB0RD_1LC1LD_0RA1RF_0LF0LE_0RB---_1RC0LB".
Definition tm' := TM_from_str "1RB0LD_0RC1RA_1LD0RE_1LB1LE_0LA0LF_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEFA") 11 1.
Time Qed.
End TM49.


Module TM50.
Definition tm := TM_from_str "1LB---_0LC0RF_0LD1LE_1RE0RA_1RF0RD_1RB0RD".
Definition tm' := TM_from_str "1RB0RE_1RC0RE_0LD0RB_0LE1LA_1RA0RF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEAB") 1 7.
Time Qed.
End TM50.


Module TM51.
Definition tm := TM_from_str "1RB1LC_0LA0RA_0LD1LD_1LE1RF_1RB0LC_0RB---".
Definition tm' := TM_from_str "1RB0LD_0LC0RC_1RB1LD_0LE1LE_1LA1RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM51.


Module TM52.
Definition tm := TM_from_str "1LB1RE_0LC0RE_0RC0LD_0RE0LB_1RF1LB_1RA---".
Definition tm' := TM_from_str "1RB---_1LC1RD_0LE0RD_1RA1LC_0RE0LF_0RD0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEFDA") 1 4.
Time Qed.
End TM52.


Module TM53.
Definition tm := TM_from_str "1RB1LD_0RC0RB_1LC0LA_0RB0LE_0LF1LA_1RD---".
Definition tm' := TM_from_str "1RB---_0RC0LF_0RD0RC_1LD0LE_1RC1LB_0LA1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDBFA") 39 44.
Time Qed.
End TM53.


Module TM54.
Definition tm := TM_from_str "1LB0LB_1RC1LB_1RA0RD_0LC0RE_1LF1RE_---0LA".
Definition tm' := TM_from_str "1RB1LA_1RC0RD_1LA0LA_0LB0RE_1LF1RE_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 4 1.
Time Qed.
End TM54.


Module TM55.
Definition tm := TM_from_str "1RB1LE_0LC1RE_---1LD_0LE1LF_1RA0RF_1RB0LB".
Definition tm' := TM_from_str "1RB0LB_0LC1RE_---1LD_0LE1LA_1RF0RA_1RB1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM55.


Module TM56.
Definition tm := TM_from_str "1LB0LF_1RC0RA_1LA1RD_1RE0RC_1RB---_0RC0LF".
Definition tm' := TM_from_str "1RB---_1RC0RD_1LD1RF_1LB0LE_0RC0LE_1RA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCFAE") 51 52.
Time Qed.
End TM56.


Module TM57.
Definition tm := TM_from_str "1RB0RB_1RC0LF_1LD1RA_0LE0LD_1RE0RB_1RD---".
Definition tm' := TM_from_str "1RB0LE_1LC1RF_0LD0LC_1RD0RA_1RC---_1RA0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 50 38.
Time Qed.
End TM57.


Module TM58.
Definition tm := TM_from_str "1LB1RE_1RC0LD_1LE0LB_0LC0RE_1RB0RF_---1RA".
Definition tm' := TM_from_str "1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFAD") 10 1.
Time Qed.
End TM58.


Module TM59.
Definition tm := TM_from_str "1RB0RC_0LC1RF_0RD0LB_1RE1RA_1RA0RA_1LC---".
Definition tm' := TM_from_str "1RB1RC_1RC0RC_1RD0RE_0LE1RF_0RA0LD_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 6 1.
Time Qed.
End TM59.


Module TM60.
Definition tm := TM_from_str "1RB0RF_1RC0LC_0LD0RA_1RE1LD_0LE1LB_1LA---".
Definition tm' := TM_from_str "1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC0RF_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDABF") 1 21.
Time Qed.
End TM60.


Module TM61.
Definition tm := TM_from_str "1RB1LA_0LA0RC_1RD1LB_0LC0RE_0RB1RF_1LB---".
Definition tm' := TM_from_str "1RB1LC_0LA0RE_0LD0RA_1RC1LD_0RC1RF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCABEF") 9 6.
Time Qed.
End TM61.


Module TM62.
Definition tm := TM_from_str "1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LC_1RD0RA".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LE_0LB0RA_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCEBDA") 27 68.
Time Qed.
End TM62.


Module TM63.
Definition tm := TM_from_str "1RB1LF_1LC0LD_1LD1RC_1RE1LB_0LA0RE_0RE---".
Definition tm' := TM_from_str "1RB1LE_0LC0RB_1RE1LD_0RB---_1LF0LA_1LA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEFABD") 1 7.
Time Qed.
End TM63.


Module TM64.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RE_1RF1RB_1LC---".
Definition tm' := TM_from_str "1RB1RE_1LC---_1LD0LC_1RE0RA_1LC1RF_1RD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECFAB") 2 2.
Time Qed.
End TM64.


Module TM65.
Definition tm := TM_from_str "1RB1RD_1RC---_0RD0LC_1RE0RA_1RF0LA_1LC1LF".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDABC") 2026 2020.
Time Qed.
End TM65.


Module TM66.
Definition tm := TM_from_str "1LB0RB_1RC0LA_1LE1LD_---1RA_0RF1LC_0RA1RF".
Definition tm' := TM_from_str "1RB0LE_1LC1LF_0RD1LB_0RE1RD_1LA0RA_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABFCD") 51 40.
Time Qed.
End TM66.


Module TM67.
Definition tm := TM_from_str "1RB1RA_1RC1LB_1RD1RA_1LE0RF_0RC0LE_1RB---".
Definition tm' := TM_from_str "1RB---_1RC1LB_1RD1RF_1LE0RA_0RC0LE_1RB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM67.


Module TM68.
Definition tm := TM_from_str "1LB0RF_1RC0LD_0LD0RC_0LE---_1LA1LE_1RD1RF".
Definition tm' := TM_from_str "1RB1RA_0LC---_1LD1LC_1LE0RA_1RF0LB_0LB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 4 1.
Time Qed.
End TM68.


Module TM69.
Definition tm := TM_from_str "1RB1LF_1LC0RE_1LE0LD_0LC0RA_0RA0LA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RE_1LE0LD_0LC0RF_0RF0LF_1RB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM69.


Module TM70.
Definition tm := TM_from_str "1RB---_1LC0RB_0LD1LD_1RE1LF_1RB1LF_0RA0LF".
Definition tm' := TM_from_str "1RB1LE_1LC0RB_0LD1LD_1RA1LE_0RF0LE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM70.


Module TM71.
Definition tm := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA0RD_0LC1LF_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_0RE0LD_1LE0RD_1RB0LF_0LC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM71.


Module TM72.
Definition tm := TM_from_str "1RB0LD_0RC1LA_0RD1RA_1LE1RF_1RB0LE_1RC---".
Definition tm' := TM_from_str "1RB0LA_0RC1LE_0RD1RE_1LA1RF_1RB0LD_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM72.


Module TM73.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC1LF_0LC---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM73.


Module TM74.
Definition tm := TM_from_str "1LB0LC_1RC1LE_0RE0RD_1RC1LB_0LA0LF_1LA---".
Definition tm' := TM_from_str "1RB1LC_0RC0RE_0LD0LF_1LA0LB_1RB1LA_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 2886 2971.
Time Qed.
End TM74.


Module TM75.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1RB1LE".
Definition tm' := TM_from_str "1RB1LE_0RC0RB_1LD0LF_1LE---_1LA1RF_1RB1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM75.


Module TM76.
Definition tm := TM_from_str "1LB0LF_1RC1LA_1RD0RC_0LD1LE_0LA0RE_1LA---".
Definition tm' := TM_from_str "1RB1LE_1RC0RB_0LC1LD_0LE0RD_1LA0LF_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 8.
Time Qed.
End TM76.


Module TM77.
Definition tm := TM_from_str "1RB0LC_1RC---_0RD0RF_1LE0RE_0LA1RA_0LB0RA".
Definition tm' := TM_from_str "1RB---_0RC0RF_1LD0RD_0LE1RE_1RA0LB_0LA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 55 77.
Time Qed.
End TM77.


Module TM78.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_0RF---_1RA0LD".
Definition tm' := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 771 1070.
Time Qed.
End TM78.


Module TM79.
Definition tm := TM_from_str "1RB1LE_1LC0RA_1RB0LD_1LB0LB_0LF---_0LB1LA".
Definition tm' := TM_from_str "1RB0LC_1LA0RD_1LB0LB_1RB1LE_0LF---_0LB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBACEF") 1 1.
Time Qed.
End TM79.


Module TM80.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LA_0LC---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM80.


Module TM81.
Definition tm := TM_from_str "1RB---_0RC1RC_1LD0RD_0LE0LF_1RA0LB_1RB1LE".
Definition tm' := TM_from_str "1RB1LE_0RC1RC_1LD0RD_0LE0LA_1RF0LB_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM81.


Module TM82.
Definition tm := TM_from_str "1LB---_0RC1LA_1RD0RD_1LE1RF_0RB0LD_0RD0RE".
Definition tm' := TM_from_str "1RB0RB_1LC1RF_0RD0LB_0RA1LE_1LD---_0RB0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDABCF") 22 1.
Time Qed.
End TM82.


Module TM83.
Definition tm := TM_from_str "1RB0RB_1LC0RA_1RB0LD_1LE0LD_1LB1LF_1RD---".
Definition tm' := TM_from_str "1RB0LC_1LA0RE_1LD0LC_1LB1LF_1RB0RB_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM83.


Module TM84.
Definition tm := TM_from_str "1RB0LD_1RC1RA_1LA0RE_1LF1LC_0RF0LC_1RB---".
Definition tm' := TM_from_str "1RB---_1RC1RD_1LD0RF_1RB0LE_1LA1LC_0RA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM84.


Module TM85.
Definition tm := TM_from_str "1LB0RA_1RB0LC_1LE0RD_1RA0LC_1LD0LF_0LD---".
Definition tm' := TM_from_str "1RB0LD_1LC0RB_1RC0LD_1LE0RA_1LA0LF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 5 1.
Time Qed.
End TM85.


Module TM86.
Definition tm := TM_from_str "1LB0RF_1RC1LA_1RA0RD_1RE1LD_0LF0RC_---0LA".
Definition tm' := TM_from_str "1RB1LA_0LC0RF_---0LD_1LE0RC_1RF1LD_1RD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 1 4.
Time Qed.
End TM86.


Module TM87.
Definition tm := TM_from_str "1RB1LE_1RC0RB_1RD1RF_1LA0LD_1RB0LD_---0RA".
Definition tm' := TM_from_str "1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM87.


Module TM88.
Definition tm := TM_from_str "1LB1LA_1LC0LA_1RD1LB_1RE0RD_1RF0RB_1LE---".
Definition tm' := TM_from_str "1RB0RC_1LA---_1LE0LD_1LC1LD_1RF1LC_1RA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEFAB") 1 5.
Time Qed.
End TM88.


Module TM89.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF0RE_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RB_1LD0LF_1RB1LE_1LC0LD_0LA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM89.


Module TM90.
Definition tm := TM_from_str "1LB0RA_0RC---_1LF0LD_1RE1LC_1RF0RA_1LD0LA".
Definition tm' := TM_from_str "1RB1LD_1RC0RE_1LA0LE_1LC0LA_1LF0RE_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDABC") 4 1.
Time Qed.
End TM90.


Module TM91.
Definition tm := TM_from_str "1LB0RA_1LC1RB_0LD1LE_1RA0LC_1LF1LD_0LC---".
Definition tm' := TM_from_str "1RB0LD_1LC0RB_1LD1RC_0LA1LE_1LF1LA_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 52 69.
Time Qed.
End TM91.


Module TM92.
Definition tm := TM_from_str "1LB0LA_0RC0RD_---0RD_1RE1RF_1LA1LE_0LA1RB".
Definition tm' := TM_from_str "1RB1RF_1LC1LB_1LD0LC_0RE0RA_---0RA_0LC1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM92.


Module TM93.
Definition tm := TM_from_str "1RB---_1LC0RF_0RE0LD_1LE1LF_1RB0LF_0LC0RA".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LE_0LC0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM93.


Module TM94.
Definition tm := TM_from_str "1RB1LF_0RC0RE_1LD1RB_1LB1RF_---1LC_1RD0LA".
Definition tm' := TM_from_str "1RB0LF_1LC1RA_0RE0RD_---1LE_1LB1RC_1RC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCEBDA") 114 122.
Time Qed.
End TM94.


Module TM95.
Definition tm := TM_from_str "1RB---_1LC1LB_0RD0LC_1RE---_0RA1RF_1RB1RF".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RE---_0RF1RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM95.


Module TM96.
Definition tm := TM_from_str "1LB1LD_1RC1LA_1LB1RD_1RE0LB_1RC0RF_---0RB".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1RB1LD_1LC1LE_1RA0LC_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCBEAF") 145 140.
Time Qed.
End TM96.


Module TM97.
Definition tm := TM_from_str "1LB0RF_1LC---_1RD0LF_1RE0RD_1RF0RA_0LE0LA".
Definition tm' := TM_from_str "1RB0RC_0LA0LC_1LD0RB_1LE---_1RF0LB_1RA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 1 4.
Time Qed.
End TM97.


Module TM98.
Definition tm := TM_from_str "1RB---_1RC0RF_0LD1LF_1LA1LE_1RF0LA_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1RC0RA_0LD1LA_1LF1LE_1RA0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM98.


Module TM99.
Definition tm := TM_from_str "1RB---_0RC0LB_1RD0RF_1RE0LF_1LB1LE_1RA1RC".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDABCE") 2262 2020.
Time Qed.
End TM99.


Module TM100.
Definition tm := TM_from_str "1LB---_0LC0RB_0RD1LC_1RE0LA_1RB1RF_1RB0RA".
Definition tm' := TM_from_str "1RB0RE_0LC0RB_0RD1LC_1RF0LE_1LB---_1RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 6.
Time Qed.
End TM100.


Module TM101.
Definition tm := TM_from_str "1RB0RC_1RC---_1RD1RF_1LE0LD_0LA1LE_1RE0RA".
Definition tm' := TM_from_str "1RB0RC_0LC1LB_1RF0RD_1RE1RA_1LB0LE_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFDEBA") 87 42.
Time Qed.
End TM101.


Module TM102.
Definition tm := TM_from_str "1LB---_1RC0LB_0RD1LB_0LF1RE_0RF1RA_1LB0RC".
Definition tm' := TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA0RB_0RD1RF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCED") 3 4.
Time Qed.
End TM102.


Module TM103.
Definition tm := TM_from_str "1RB1RE_0LC1RD_1LD0LD_1RA1LC_1RF0RA_---1LA".
Definition tm' := TM_from_str "1RB1LD_1RC1RE_0LD1RA_1LA0LA_1RF0RB_---1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 4 1.
Time Qed.
End TM103.


Module TM104.
Definition tm := TM_from_str "1LB1RE_1RC0LB_0RE1LD_1LF0LC_1RA1LD_---0RA".
Definition tm' := TM_from_str "1RB1LE_1LC1RA_1RD0LC_0RA1LE_1LF0LD_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 3 10.
Time Qed.
End TM104.


Module TM105.
Definition tm := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RD---".
Definition tm' := TM_from_str "1RB1RC_1RC---_1RD0RA_1RE1RD_1LF1LE_0RC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFCAB") 12348 13012.
Time Qed.
End TM105.


Module TM106.
Definition tm := TM_from_str "1LB1RB_1RA0LC_1LD1LB_0RE0RF_1LC1RD_---1LE".
Definition tm' := TM_from_str "1RB0LC_1LA1RA_1LD1LA_0RE0RF_1LC1RD_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BACDEF") 92 79.
Time Qed.
End TM106.


Module TM107.
Definition tm := TM_from_str "1RB0LA_1LC1LE_1RD1LC_1LA1RE_1RF0RD_1RC---".
Definition tm' := TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LA1LE_1RF0RB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 10 9.
Time Qed.
End TM107.


Module TM108.
Definition tm := TM_from_str "1LB1LF_0RC0LB_1RE1RD_1RA1RD_0RA---_1RD1LA".
Definition tm' := TM_from_str "1RB1LC_1RC1RB_1LD1LA_0RE0LD_1RF1RB_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBFA") 3 1.
Time Qed.
End TM108.


Module TM109.
Definition tm := TM_from_str "1RB0RE_0LC1LD_1LA1LB_1LF1RA_1RD0RC_---0LB".
Definition tm' := TM_from_str "1RB0RE_1LC1RF_---0LD_0LE1LB_1LF1LD_1RD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEBAC") 116 159.
Time Qed.
End TM109.


Module TM110.
Definition tm := TM_from_str "1RB0LF_1LC0LD_1RD1LB_1LE1RD_---1RF_1LA0RA".
Definition tm' := TM_from_str "1RB1LF_1LC1RB_---1RD_1LE0RE_1RF0LD_1LA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 43 53.
Time Qed.
End TM110.


Module TM111.
Definition tm := TM_from_str "1RB---_0LC1RF_0RD0LC_1RE0RA_1LC1LF_1RD0LE".
Definition tm' := TM_from_str "1RB0LC_1RC0RE_1LD1LA_0RB0LD_1RF---_0LD1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDBCA") 9 19.
Time Qed.
End TM111.


Module TM112.
Definition tm := TM_from_str "1RB---_1LC1RE_1LD0LC_1RE0LE_1RF1LD_1RB0RA".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1LD0LC_1RE0LE_1RA1LD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM112.


Module TM113.
Definition tm := TM_from_str "1LB---_0LC1RD_1LD1LE_0RE0RA_0LA0RF_1RB1RD".
Definition tm' := TM_from_str "1RB1RF_0LC1RF_1LF1LD_0LE0RA_1LB---_0RD0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFDA") 731 787.
Time Qed.
End TM113.


Module TM114.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RB_1LD1LF_1RB1LE_1LC0LD_1LA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM114.


Module TM115.
Definition tm := TM_from_str "1RB1LB_1LC1RF_0RE0LD_0LC0RE_1RA---_1RE1LC".
Definition tm' := TM_from_str "1RB---_1RC1LC_1LD1RF_0RA0LE_0LD0RA_1RA1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 2 9.
Time Qed.
End TM115.


Module TM116.
Definition tm := TM_from_str "1RB0LE_1LC0RD_1LA1LB_1RB1RA_0LB1LF_0RB---".
Definition tm' := TM_from_str "1RB1RD_1LC0RA_1LD1LB_1RB0LE_0LB1LF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM116.


Module TM117.
Definition tm := TM_from_str "1RB1RC_1LC0LE_1RE0RD_1RF0LC_1LB0RC_---0RA".
Definition tm' := TM_from_str "1RB0RD_1LC0RA_1LA0LB_1RE0LA_---0RF_1RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCADBE") 5 1.
Time Qed.
End TM117.


Module TM118.
Definition tm := TM_from_str "1RB0RF_1LC0RA_1RA0LD_0LE1LC_0RC0LC_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM118.


Module TM119.
Definition tm := TM_from_str "1LB1LD_0RC1LA_1RA0LB_0LA0RE_0LC0RF_---1RD".
Definition tm' := TM_from_str "1RB0LC_1LC1LD_0RA1LB_0LB0RE_0LA0RF_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 5 1.
Time Qed.
End TM119.


Module TM120.
Definition tm := TM_from_str "1LB0RF_0RC0LA_1RE1RD_0RE---_1LF1RC_1LF1RA".
Definition tm' := TM_from_str "1RB1RF_1LC1RA_1LC1RD_1LE0RC_0RA0LD_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 6 6.
Time Qed.
End TM120.


Module TM121.
Definition tm := TM_from_str "1RB1RA_1LC0RA_1RB1LD_1LE1LF_0LB0LD_---0LE".
Definition tm' := TM_from_str "1RB1LC_1LA0RE_1LD1LF_0LB0LC_1RB1RE_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM121.


Module TM122.
Definition tm := TM_from_str "1LB0RF_0LC0LB_1LD0LA_0RE0LC_1RC1RF_1RE---".
Definition tm' := TM_from_str "1RB1RD_1LC0LE_0RA0LB_1RA---_1LF0RD_0LB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCAD") 2 3.
Time Qed.
End TM122.


Module TM123.
Definition tm := TM_from_str "1RB0LA_0RC1LF_0RD0LE_1LD0LE_1RB1LF_---1LA".
Definition tm' := TM_from_str "1RB1LE_0RC1LE_0RD0LA_1LD0LA_---1LF_1RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM123.


Module TM124.
Definition tm := TM_from_str "1RB---_1LC1LF_1RD0LB_1RA1RE_0RC0RE_1LB1LB".
Definition tm' := TM_from_str "1RB1RF_1RC---_1LD1LE_1RA0LC_1LC1LC_0RD0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAFE") 8 2.
Time Qed.
End TM124.


Module TM125.
Definition tm := TM_from_str "1RB0LC_1LA0RE_1LD0LF_1RE---_1RF0RB_1RB1RF".
Definition tm' := TM_from_str "1RB1RA_1LC0RF_1RB0LD_1LE0LA_1RF---_1RA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM125.


Module TM126.
Definition tm := TM_from_str "1LB0RB_0RC0LD_1RA1LC_1LE---_1RE0LF_0LA1RD".
Definition tm' := TM_from_str "1RB1LA_1LC0RC_0RA0LD_1LE---_1RE0LF_0LB1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 126 127.
Time Qed.
End TM126.


Module TM127.
Definition tm := TM_from_str "1RB1LF_1RC0RB_0LD0LA_0RA1LE_1RD1LC_1LD---".
Definition tm' := TM_from_str "1RB1LE_0RC1LA_1RD1LF_1RE0RD_0LB0LC_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBAF") 14 5.
Time Qed.
End TM127.


Module TM128.
Definition tm := TM_from_str "1LB0LF_0LC0LF_1LD---_1RE0LA_0RB0RE_1RD1LA".
Definition tm' := TM_from_str "1RB0LE_0RC0RB_0LD0LF_1LA---_1LC0LF_1RA1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDABF") 1530 1689.
Time Qed.
End TM128.


Module TM129.
Definition tm := TM_from_str "1RB0LD_1LC1RE_---0LD_1LA1LB_1RF0RE_1RD0RA".
Definition tm' := TM_from_str "1RB0RC_1LC1LD_1RD0LB_1LF1RE_1RA0RE_---0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFBEA") 3 3.
Time Qed.
End TM129.


Module TM130.
Definition tm := TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA0RB_0RD1RF_1RD---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1RD0LC_0RE1LC_0LB1RF_0RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBFA") 3 1.
Time Qed.
End TM130.


Module TM131.
Definition tm := TM_from_str "1RB0RF_1LC0RA_1LF0LD_1LE---_0LB1LB_1RB0LB".
Definition tm' := TM_from_str "1RB0LB_1LC0RF_1LA0LD_1LE---_0LB1LB_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM131.


Module TM132.
Definition tm := TM_from_str "1LB0RA_0LC1RA_0RD1LE_1RA0LB_0LD0LF_1RA---".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LD1RB_0RA1LE_0LA0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 4 3.
Time Qed.
End TM132.


Module TM133.
Definition tm := TM_from_str "1LB1LF_1LC0RD_0RB0LB_1LA1RE_1RB0LA_1LE---".
Definition tm' := TM_from_str "1RB0LE_1LC0RD_0RB0LB_1LE1RA_1LB1LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 8 5.
Time Qed.
End TM133.


Module TM134.
Definition tm := TM_from_str "1RB---_1LC0RB_0LD1RB_0RF1LE_0LF0LA_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LD1RB_0RA1LE_0LA0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM134.


Module TM135.
Definition tm := TM_from_str "1LB1RD_1LC0LC_1RD0LB_1RF1RE_1LE0RA_0LE---".
Definition tm' := TM_from_str "1RB1RC_0LC---_1LC0RD_1LE1RA_1LF0LF_1RA0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFACB") 1 4.
Time Qed.
End TM135.


Module TM136.
Definition tm := TM_from_str "1LB1LE_0RC0LF_1RD1RC_0LE1RB_1LA0LA_---1RB".
Definition tm' := TM_from_str "1RB1RA_0LC1RE_1LD0LD_1LE1LC_0RA0LF_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM136.


Module TM137.
Definition tm := TM_from_str "1RB1RF_1LC1RE_1LD0LC_1RB1LD_1RA0RB_0LE---".
Definition tm' := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB1RF_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM137.


Module TM138.
Definition tm := TM_from_str "1LB1RD_1LC1LB_1RA0RF_1RC1RE_0RA0RA_---0LB".
Definition tm' := TM_from_str "1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0RB_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 6 8.
Time Qed.
End TM138.


Module TM139.
Definition tm := TM_from_str "1LB---_1RC1RD_0LD1RB_0RB0LE_0RA0LF_---1LD".
Definition tm' := TM_from_str "1RB1RC_0LC1RA_0RA0LD_0RE0LF_1LA---_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 5.
Time Qed.
End TM139.


Module TM140.
Definition tm := TM_from_str "1RB0LE_1RC---_0RD0RC_1LD0LA_1RB0LF_---0LA".
Definition tm' := TM_from_str "1RB0LF_1RC---_0RD0RC_1LD0LE_1RB0LA_---0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM140.


Module TM141.
Definition tm := TM_from_str "1RB---_1RC0RC_1LD1RF_0LE0LB_0RA0LF_1RA0LE".
Definition tm' := TM_from_str "1RB0LF_1RC---_1RD0RD_1LE1RA_0LF0LC_0RB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 1 20.
Time Qed.
End TM141.


Module TM142.
Definition tm := TM_from_str "1RB0LC_1LA0RE_1LD0RE_1LA0LF_1RB0RE_0LA---".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1RB0LD_1LE0RA_1LC0LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM142.


Module TM143.
Definition tm := TM_from_str "1RB1LE_1LC0RA_0LF0LD_1LE1LE_1RB1LC_---0LE".
Definition tm' := TM_from_str "1RB1LC_1LC0RE_0LF0LD_1LA1LA_1RB1LA_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM143.


Module TM144.
Definition tm := TM_from_str "1LB0RF_1RC---_1LD0RC_0LE1LD_1RF1LA_0RA0LC".
Definition tm' := TM_from_str "1RB---_1LC0RB_0LD1LC_1RE1LF_0RF0LB_1LA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 3 8.
Time Qed.
End TM144.


Module TM145.
Definition tm := TM_from_str "1RB---_1RC1LC_1LC1RD_1RA1LE_0RA0LF_0LE0RF".
Definition tm' := TM_from_str "1RB1LB_1LB1RC_1RF1LD_0RF0LE_0LD0RE_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 11 2.
Time Qed.
End TM145.


Module TM146.
Definition tm := TM_from_str "1RB0LC_1RC0RF_0LD1LA_1LF1LE_1RA1LE_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RA_0LD1LF_1LA1LE_1RF1LE_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM146.


Module TM147.
Definition tm := TM_from_str "1RB1LF_1RC0RD_1LD0LE_1RB0LC_1LA0RB_0LD---".
Definition tm' := TM_from_str "1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM147.


Module TM148.
Definition tm := TM_from_str "1LB1LF_0RC1LC_1RE1RD_0RC0LA_0LB1RC_---0RD".
Definition tm' := TM_from_str "1RB1RD_0LC1RA_0RA1LA_0RA0LE_1LC1LF_---0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECADBF") 1 14.
Time Qed.
End TM148.


Module TM149.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB1LF_1LC0RE_1RB---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA0RD_0LC1LF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM149.


Module TM150.
Definition tm := TM_from_str "1LB0RB_0LC1RF_1RD1LE_0RA---_0LF0LD_0RA0LB".
Definition tm' := TM_from_str "1RB1LE_0RC---_1LD0RD_0LA1RF_0LF0LB_0RC0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 21 31.
Time Qed.
End TM150.


Module TM151.
Definition tm := TM_from_str "1LB0RD_1RC0LF_1LD1LC_1RE0LC_1RA1RE_---0LA".
Definition tm' := TM_from_str "1RB0LF_1LC1LB_1RD0LB_1RE1RD_1LA0RC_---0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 16 22.
Time Qed.
End TM151.


Module TM152.
Definition tm := TM_from_str "1RB0LF_1RC---_1RD1RE_0LE1RC_0RC0LA_---1LE".
Definition tm' := TM_from_str "1RB1RC_0LC1RA_0RA0LD_1RE0LF_1RA---_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM152.


Module TM153.
Definition tm := TM_from_str "1LB0RF_0RC0LA_1LF1LD_0LE---_0RC0LC_1RA0RE".
Definition tm' := TM_from_str "1RB0RF_1LC0RA_0RD0LB_1LA1LE_0LF---_0RD0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 368 437.
Time Qed.
End TM153.


Module TM154.
Definition tm := TM_from_str "1RB0RF_0RC0LC_1RD1RA_1LE0LE_0RA0LD_1RC---".
Definition tm' := TM_from_str "1RB---_1RC1RE_1LD0LD_0RE0LC_1RF0RA_0RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 61 79.
Time Qed.
End TM154.


Module TM155.
Definition tm := TM_from_str "1LB0LA_1LC0LF_0LD1RE_0RE---_1RF1LA_1LE0RC".
Definition tm' := TM_from_str "1RB1LC_1LA0RE_1LD0LC_1LE0LB_0LF1RA_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 12 13.
Time Qed.
End TM155.


Module TM156.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RE1RD_1RC1RA_0LA1RF_0RA---".
Definition tm' := TM_from_str "1RB1RD_0RC1RA_0LD1RF_1LE0RB_1RB0LE_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBACF") 23 15.
Time Qed.
End TM156.


Module TM157.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_1RF---_1RA1RF".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 5 6.
Time Qed.
End TM157.


Module TM158.
Definition tm := TM_from_str "1LB1RD_1RC---_1LC1LA_0RF0RE_1LF0RD_0LA0LC".
Definition tm' := TM_from_str "1RB---_1LB1LC_1LA1RD_0RF0RE_1LF0RD_0LC0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 10 1.
Time Qed.
End TM158.


Module TM159.
Definition tm := TM_from_str "1LB1RA_0RA0LC_1LD1RB_1RA0LE_0LB1LF_1RB---".
Definition tm' := TM_from_str "1RB0LE_1LC1RB_0RB0LD_1LA1RC_0LC1LF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 3 1.
Time Qed.
End TM159.


Module TM160.
Definition tm := TM_from_str "1RB1LA_1RC1RE_1RD0LA_1LC1RD_0RF0RD_---1LA".
Definition tm' := TM_from_str "1RB0LC_1LA1RB_1RD1LC_1RA1RE_0RF0RB_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 19 31.
Time Qed.
End TM160.


Module TM161.
Definition tm := TM_from_str "1LB1LE_1RC0RD_1RD0LC_1LA0RB_1LF---_1LC1RD".
Definition tm' := TM_from_str "1RB0LA_1LC0RF_1LF1LD_1LE---_1LA1RB_1RA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 5 1.
Time Qed.
End TM161.


Module TM162.
Definition tm := TM_from_str "1RB0RF_1RC0RA_1LD0RB_0LE0LC_1LA0LD_---0RE".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_0LD0LB_1LE0LC_1RA0RF_---0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 445 444.
Time Qed.
End TM162.


Module TM163.
Definition tm := TM_from_str "1LB---_1LC0LD_1RD1LF_0RF0RE_1RD1LC_0LB0LA".
Definition tm' := TM_from_str "1RB1LC_0RC0RE_0LD0LF_1LA0LB_1RB1LA_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDABEC") 2920 2971.
Time Qed.
End TM163.


Module TM164.
Definition tm := TM_from_str "1LB0RA_0RC0RA_1LE0LD_1RB1LC_1LF---_1LD0LD".
Definition tm' := TM_from_str "1RB1LC_0RC0RF_1LD0LA_1LE---_1LA0LA_1LB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 4 1.
Time Qed.
End TM164.


Module TM165.
Definition tm := TM_from_str "1LB---_0RC0LE_0LE0RD_1RE1RA_1LF0RB_1RC0LB".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 4 1.
Time Qed.
End TM165.


Module TM166.
Definition tm := TM_from_str "1RB1LA_1LC0RE_1RF1RD_---1LE_1RB0LB_1LA1RC".
Definition tm' := TM_from_str "1RB0LB_1LC0RA_1RE1RD_---1LA_1LF1RC_1RB1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM166.


Module TM167.
Definition tm := TM_from_str "1LB1RA_1RC1LE_1LD0RC_1RA1LA_0LF0LB_0RB---".
Definition tm' := TM_from_str "1RB1LB_1LC1RB_1RF1LD_0LE0LC_0RC---_1LA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFADE") 18 21.
Time Qed.
End TM167.


Module TM168.
Definition tm := TM_from_str "1LB0RA_1LC0RA_0LD1LD_1LE---_1RF1RB_0LB0RF".
Definition tm' := TM_from_str "1RB1RC_0LC0RB_1LE0RD_1LC0RD_0LF1LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEFAB") 1 4.
Time Qed.
End TM168.


Module TM169.
Definition tm := TM_from_str "1RB0LF_1LC---_0RD0LC_0RE1RE_1RA0RF_1RD1LF".
Definition tm' := TM_from_str "1RB1LA_0RC1RC_1RD0RA_1RE0LA_1LF---_0RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 7 1.
Time Qed.
End TM169.


Module TM170.
Definition tm := TM_from_str "1RB1RF_0RC1RD_1RD---_1LE0RA_0RC1LF_1RA0LE".
Definition tm' := TM_from_str "1RB---_1LC0RE_0RA1LD_1RE0LC_1RF1RD_0RA1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 107 228.
Time Qed.
End TM170.


Module TM171.
Definition tm := TM_from_str "1LB---_0LC0RD_1RB1LC_1RE1LB_0LD0RF_0RB1RA".
Definition tm' := TM_from_str "1RB1LC_0LA0RE_0LD0RA_1RC1LD_0RC1RF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 1 3.
Time Qed.
End TM171.


Module TM172.
Definition tm := TM_from_str "1RB---_0RC0LD_1LD1LA_0LE0RA_1RB1LF_0LB1LA".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD1LF_0LA0RF_0LB1LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM172.


Module TM173.
Definition tm := TM_from_str "1LB0RD_0LC1LA_1RD0LE_1RB1RE_0RA1RF_0LC---".
Definition tm' := TM_from_str "1RB1RD_0LC1LE_1RA0LD_0RE1RF_1LB0RA_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 5.
Time Qed.
End TM173.


Module TM174.
Definition tm := TM_from_str "1RB1LC_0LA0RB_0LD1LD_1LE1LF_1RB1RE_---1RA".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1RB1LD_0LE1LE_1LA1LF_---1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM174.


Module TM175.
Definition tm := TM_from_str "1LB1RC_1RA1LD_0LB0LF_1LB0LE_1LC---_0RF0RB".
Definition tm' := TM_from_str "1RB1LC_1LA1RD_1LA0LF_0LA0LE_0RE0RA_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BADCFE") 1 18.
Time Qed.
End TM175.


Module TM176.
Definition tm := TM_from_str "1RB1LA_1LC1RE_0RD0LC_1LE1RF_1RA0RB_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1RE_0RD0LC_1LE1RA_1RF0RB_1RB1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM176.


Module TM177.
Definition tm := TM_from_str "1RB1LD_1RC0RE_1LA0LE_1LC0LA_0LF0RE_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RF_1LD0LF_1RB1LE_1LC0LD_0LA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM177.


Module TM178.
Definition tm := TM_from_str "1RB1LE_0RC---_1LD1RF_1RA0RB_0LA1RF_0RD0LA".
Definition tm' := TM_from_str "1RB0RC_1RC1LE_0RD---_1LA1RF_0LB1RF_0RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 4 8.
Time Qed.
End TM178.


Module TM179.
Definition tm := TM_from_str "1RB1LE_1RC0RE_0RD0RB_1LE0RF_0LA0LE_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RE_0RD0RB_1LE0RA_0LF0LE_1RB1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM179.


Module TM180.
Definition tm := TM_from_str "1RB1RD_1LC0LE_0RD0LC_1RA0RD_1LB0RF_1RE---".
Definition tm' := TM_from_str "1RB---_1LC0RA_1LD0LB_0RE0LD_1RF0RE_1RC1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEBA") 4 8.
Time Qed.
End TM180.


Module TM181.
Definition tm := TM_from_str "1LB0LE_1LC0RE_1RD1RC_0LA0RD_1LF1LA_1RD---".
Definition tm' := TM_from_str "1RB---_0LC0RB_1LE0LD_1LA1LC_1LF0RD_1RB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEFBDA") 988 969.
Time Qed.
End TM181.


Module TM182.
Definition tm := TM_from_str "1RB1RA_1RC0LA_1LD1LC_0RE0LD_1RF---_0RB0LA".
Definition tm' := TM_from_str "1RB0LF_1LC1LB_0RD0LC_1RE---_0RA0LF_1RA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 9 7.
Time Qed.
End TM182.


Module TM183.
Definition tm := TM_from_str "1LB1RE_0LC1LF_0RD0LA_1RA0RE_1RF---_0RC0RC".
Definition tm' := TM_from_str "1RB0RF_1LC1RF_0LE1LD_0RE0RE_0RA0LB_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEAFD") 7 12.
Time Qed.
End TM183.


Module TM184.
Definition tm := TM_from_str "1RB1RA_0LC0RB_1RB1LD_0LE1RD_1LA1LF_---1LE".
Definition tm' := TM_from_str "1RB1LC_0LA0RB_0LD1RC_1LE1LF_1RB1RE_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM184.


Module TM185.
Definition tm := TM_from_str "1RB0LB_1LC0RA_1RE1RD_---1LA_0LF1RC_1LA1LF".
Definition tm' := TM_from_str "1RB1RF_0LC1RA_1LD1LC_1RE0LE_1LA0RD_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 1 7.
Time Qed.
End TM185.


Module TM186.
Definition tm := TM_from_str "1RB0LA_0RC0RA_1LD1RE_0LC---_1LA1RF_1RB0RB".
Definition tm' := TM_from_str "1RB0RB_0RC0RF_1LD1RE_0LC---_1LF1RA_1RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM186.


Module TM187.
Definition tm := TM_from_str "1LB1RB_1RC0RE_0LF0RD_1RA0RF_---0RF_1LC1LB".
Definition tm' := TM_from_str "1RB0RF_0LC0RD_1LB1LA_1RE0RC_1LA1RA_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABDFC") 1 3.
Time Qed.
End TM187.


Module TM188.
Definition tm := TM_from_str "1RB0RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1LB---".
Definition tm' := TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB0RF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM188.


Module TM189.
Definition tm := TM_from_str "1RB0RE_0RC0RA_0LD0LF_1LE0LB_1RB1LC_1LD---".
Definition tm' := TM_from_str "1RB1LC_0RC0RE_0LD0LF_1LA0LB_1RB0RA_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM189.


Module TM190.
Definition tm := TM_from_str "1RB1RC_0LC1RA_0RA1LD_1RB0RE_0LF0LE_---1LC".
Definition tm' := TM_from_str "1RB0RE_0LC1RD_0RD1LA_1RB1RC_0LF0LE_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM190.


Module TM191.
Definition tm := TM_from_str "1LB0RB_0LC0RF_1RD1LE_0RA0LF_0LD1LF_0LC---".
Definition tm' := TM_from_str "1RB1LE_0RC0LF_1LD0RD_0LA0RF_0LB1LF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 23 33.
Time Qed.
End TM191.


Module TM192.
Definition tm := TM_from_str "1RB0LA_0RC0LE_0LD1RE_1LA0RB_0RD1RF_1RD---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1RD0LC_0RE0LF_0LB1RF_0RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBFA") 3 1.
Time Qed.
End TM192.


Module TM193.
Definition tm := TM_from_str "1LB0LB_1LC0RE_1LD0RF_1RB1LA_---1RF_1LC1RC".
Definition tm' := TM_from_str "1RB1LE_1LC0RF_1LA0RD_1LC1RC_1LB0LB_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCAFD") 25 70.
Time Qed.
End TM193.


Module TM194.
Definition tm := TM_from_str "1LB1LE_1RC0LA_---0RD_1RE1RF_0LB1LD_1RA0RF".
Definition tm' := TM_from_str "1RB1RF_0LC1LA_1RE0LD_1LC1LB_---0RA_1RD0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEABF") 1 4.
Time Qed.
End TM194.


Module TM195.
Definition tm := TM_from_str "1RB1LF_1RC1RF_0RD0RB_1LE0RE_0LA---_1RB0LF".
Definition tm' := TM_from_str "1RB0LA_1RC1RA_0RD0RB_1LE0RE_0LF---_1RB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM195.


Module TM196.
Definition tm := TM_from_str "1LB---_0LC0RB_0RD1LC_1RE0LA_1LC1RF_1RB0RA".
Definition tm' := TM_from_str "1RB0RE_0LC0RB_0RD1LC_1RF0LE_1LB---_1LC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 6.
Time Qed.
End TM196.


Module TM197.
Definition tm := TM_from_str "1RB0LA_0LC---_1LE0RD_1RC0RA_1LF1LC_0LA0LB".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_1LD1LB_0LE0LF_1RF0LE_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBACD") 4 1.
Time Qed.
End TM197.


Module TM198.
Definition tm := TM_from_str "1RB---_0LC0LB_1LE0RD_1LE0RA_1RF0LD_1RC0RF".
Definition tm' := TM_from_str "1RB0LD_1RC0RB_1LA0RD_1LA0RE_1RF---_0LC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCDAB") 4 10.
Time Qed.
End TM198.


Module TM199.
Definition tm := TM_from_str "1LB0LE_1LC1LB_1RD1RC_0LA0RD_0LF1LA_1RA---".
Definition tm' := TM_from_str "1RB---_1LC0LF_1LD1LC_1RE1RD_0LB0RE_0LA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 762 747.
Time Qed.
End TM199.


Module TM200.
Definition tm := TM_from_str "1RB1LF_1RC1LA_1RD0RC_0LE0LB_---0LF_1RB1LE".
Definition tm' := TM_from_str "1RB0RA_0LC0LE_---0LD_1RE1LC_1RA1LF_1RE1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEABCD") 1 4.
Time Qed.
End TM200.


Module TM201.
Definition tm := TM_from_str "1LB0LF_0RC1LE_0LE1RD_1RA0RC_1RD1LA_0LE---".
Definition tm' := TM_from_str "1RB1LC_1RC0RE_1LD0LF_0RE1LA_0LA1RB_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBAF") 3 1.
Time Qed.
End TM201.


Module TM202.
Definition tm := TM_from_str "1LB1LE_0LC1RD_1RA1LA_1RB1RE_1LF0RB_---0LD".
Definition tm' := TM_from_str "1RB1RE_0LC1RA_1RD1LD_1LB1LE_1LF0RB_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 20 17.
Time Qed.
End TM202.


Module TM203.
Definition tm := TM_from_str "1LB1RD_1LC1RB_0RA0LC_0LB0RE_1RA0RF_---1RE".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1LD1RC_0RB0LD_0LC0RA_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 8 16.
Time Qed.
End TM203.


Module TM204.
Definition tm := TM_from_str "1LB1RD_1RC0RC_1LE0LA_0RB---_1RF0LC_1RD1RE".
Definition tm' := TM_from_str "1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDBEA") 4 1.
Time Qed.
End TM204.


Module TM205.
Definition tm := TM_from_str "1LB0LD_1RC1LA_1LD0RD_1RE1LB_1RC0RF_---1RA".
Definition tm' := TM_from_str "1RB0RF_1LC0RC_1RA1LD_1RB1LE_1LD0LC_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDBCAF") 25 28.
Time Qed.
End TM205.


Module TM206.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RE_1RF1RB_1RC---".
Definition tm' := TM_from_str "1RB---_1LC0LB_1RE0RD_1RA1RE_1LB1RF_1RC0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEBFDA") 1 4.
Time Qed.
End TM206.


Module TM207.
Definition tm := TM_from_str "1LB0RB_1RC1RE_1LD0LC_1RA1LC_---0RF_1RB0RA".
Definition tm' := TM_from_str "1RB0RE_1RC1RF_1LD0LC_1RE1LC_1LB0RB_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 8 23.
Time Qed.
End TM207.


Module TM208.
Definition tm := TM_from_str "1LB0LF_1RC1LF_1RD0RC_0LD1LE_0LA0RE_1LA---".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_0LC1LD_0LE0RD_1LA0LF_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 8.
Time Qed.
End TM208.


Module TM209.
Definition tm := TM_from_str "1LB1RE_0RC0LB_0LA1RD_0RE---_1RA0RF_1RE0RC".
Definition tm' := TM_from_str "1RB0RE_1RC0RA_1LD1RB_0RE0LD_0LC1RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 962 904.
Time Qed.
End TM209.


Module TM210.
Definition tm := TM_from_str "1LB1LC_1RC0LA_1RD0RB_1RE1RE_1RF---_1RA1RD".
Definition tm' := TM_from_str "1RB1RB_1RC---_1RD1RA_1LE1LF_1RF0LD_1RA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 6 14.
Time Qed.
End TM210.


Module TM211.
Definition tm := TM_from_str "1RB1LF_1RC0RB_0LD1LE_0LA1LC_1RB1LE_0LA---".
Definition tm' := TM_from_str "1RB1LA_1RC0RB_0LD1LA_0LE1LC_1RB1LF_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM211.


Module TM212.
Definition tm := TM_from_str "1LB1LA_0RC---_1RD1RC_1RE1LA_1LF1RB_0RB0LF".
Definition tm' := TM_from_str "1RB1LF_1LC1RD_0RD0LC_0RE---_1RA1RE_1LD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 1 4.
Time Qed.
End TM212.


Module TM213.
Definition tm := TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA1LB_1RD0RB_---0RD".
Definition tm' := TM_from_str "1RB0RD_0RC1LD_1LD1RA_0LE0RF_1RB0LB_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBAF") 32 22.
Time Qed.
End TM213.


Module TM214.
Definition tm := TM_from_str "1RB1RC_0LC0LE_0RA0LD_1RE0LF_1RA1RE_---1LC".
Definition tm' := TM_from_str "1RB0LF_1RC1RB_1RD1RE_0LE0LB_0RC0LA_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM214.


Module TM215.
Definition tm := TM_from_str "1RB0LC_1LA0RD_1LA0LA_1RE0RD_1RA1RF_1LB---".
Definition tm' := TM_from_str "1RB1RF_1RC0LD_1LB0RE_1LB0LB_1RA0RE_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 113 115.
Time Qed.
End TM215.


Module TM216.
Definition tm := TM_from_str "1LB1LA_1RC1RB_0LD0RC_1LA0LE_1LF1LD_1RC---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_1RB---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 2 5.
Time Qed.
End TM216.


Module TM217.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LF_1LE---_1LA1RA_1RB1LE".
Definition tm' := TM_from_str "1RB1LE_0RC0RB_1LD0LA_1LE---_1LF1RF_1RB1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM217.


Module TM218.
Definition tm := TM_from_str "1RB1RF_1RC1RB_1LD0RA_1RB1LE_---0LF_0LC1LF".
Definition tm' := TM_from_str "1RB1LD_1RC1RB_1LA0RF_---0LE_0LC1LE_1RB1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM218.


Module TM219.
Definition tm := TM_from_str "1RB---_0RC1RE_1RD0LD_1LC1LB_1RF0RE_0LF0RA".
Definition tm' := TM_from_str "1RB0RA_0LB0RC_1RD---_0RE1RA_1RF0LF_1LE1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 1 4.
Time Qed.
End TM219.


Module TM220.
Definition tm := TM_from_str "1LB1RE_0LC0RD_0RD0LB_1RA1LB_1RF1LB_1RD---".
Definition tm' := TM_from_str "1RB1LC_1LC1RE_0LD0RA_0RA0LC_1RF1LC_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 1 4.
Time Qed.
End TM220.


Module TM221.
Definition tm := TM_from_str "1RB0LE_1LC0RE_0RF0LD_1LA1RC_0LC1LF_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_0RA0LD_1LE1RC_1RB0LF_0LC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM221.


Module TM222.
Definition tm := TM_from_str "1LB0LC_0RC0RB_1LE1LD_1RB---_0LF1LC_1LA0LF".
Definition tm' := TM_from_str "1RB---_0RC0RB_1LD1LA_0LE1LC_1LF0LE_1LB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 33.
Time Qed.
End TM222.


Module TM223.
Definition tm := TM_from_str "1LB1RE_1LC0LB_1RD0LA_1RF0RA_0LE0RC_1LE---".
Definition tm' := TM_from_str "1RB0RE_1LC---_0LC0RD_1RA0LE_1LF1RC_1LD0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDACB") 1 5.
Time Qed.
End TM223.


Module TM224.
Definition tm := TM_from_str "1RB0RE_1LC1LD_0RA0LC_1RA0LB_1RF---_0LC1RD".
Definition tm' := TM_from_str "1RB0LC_1RC0RE_1LD1LA_0RB0LD_1RF---_0LD1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 5 19.
Time Qed.
End TM224.


Module TM225.
Definition tm := TM_from_str "1RB1RF_1LC1LB_1RD0LC_1LE---_1RB0RA_0RE1RA".
Definition tm' := TM_from_str "1RB0RE_1LC1LB_1RD0LC_1LA---_1RB1RF_0RA1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM225.


Module TM226.
Definition tm := TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB1RF_1RC---".
Definition tm' := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 449 430.
Time Qed.
End TM226.


Module TM227.
Definition tm := TM_from_str "1LB1LF_0RC0LD_1RD1RC_0LE1RB_---0LF_0LA1LA".
Definition tm' := TM_from_str "1RB1RA_0LC1RF_---0LD_0LE1LE_1LF1LD_0RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 1 5.
Time Qed.
End TM227.


Module TM228.
Definition tm := TM_from_str "1LB0LA_1LC0LD_0RD0RC_1LF1LE_1RC---_0LA1LD".
Definition tm' := TM_from_str "1RB---_0RC0RB_1LD1LA_0LE1LC_1LF0LE_1LB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCAD") 2 20.
Time Qed.
End TM228.


Module TM229.
Definition tm := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1LB_0RD0LC_1RE0RF_1RB0LF_1RA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM229.


Module TM230.
Definition tm := TM_from_str "1RB0LD_0RC---_1LD0RF_0LE0RC_1RC1LF_0LA1LB".
Definition tm' := TM_from_str "1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCAD") 1 6.
Time Qed.
End TM230.


Module TM231.
Definition tm := TM_from_str "1LB---_1LC1LD_1LD1RC_1LE1LB_1RF0LA_0LD0RF".
Definition tm' := TM_from_str "1RB0LF_0LC0RB_1LA1LD_1LE1LC_1LC1RE_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDECAB") 1 3.
Time Qed.
End TM231.


Module TM232.
Definition tm := TM_from_str "1LB0LF_1RC1RE_0LE1RD_0RB1LE_0RD0LA_---1LC".
Definition tm' := TM_from_str "1RB1RC_0LC1RE_0RE0LD_1LA0LF_0RA1LC_---1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 1 4.
Time Qed.
End TM232.


Module TM233.
Definition tm := TM_from_str "1LB0LE_0RC0LB_0LD1RC_1LF0RE_1RB---_1RD1LA".
Definition tm' := TM_from_str "1RB1LC_1LA0RF_1LD0LF_0RE0LD_0LB1RE_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBFA") 8 1.
Time Qed.
End TM233.


Module TM234.
Definition tm := TM_from_str "1RB1RA_0RC0LE_1LC1LD_0RA1LB_---0LF_1RB1LF".
Definition tm' := TM_from_str "1RB1LA_0RC0LF_1LC1LD_0RE1LB_1RB1RE_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM234.


Module TM235.
Definition tm := TM_from_str "1RB0LC_1LA1RD_1LA1RB_1RB0RE_1RF0RC_---0RA".
Definition tm' := TM_from_str "1RB0RE_1LC1RA_1RB0LD_1LC1RB_1RF0RD_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDAEF") 1 1.
Time Qed.
End TM235.


Module TM236.
Definition tm := TM_from_str "1RB0RB_1RC0RD_0LD1RE_0RF0LC_1LD---_1RA1RB".
Definition tm' := TM_from_str "1RB1RC_1RC0RC_1RD0RE_0LE1RF_0RA0LD_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 2 17.
Time Qed.
End TM236.


Module TM237.
Definition tm := TM_from_str "1LB---_1LC1RB_1LD1LF_1LE0LE_1RB1LD_1LA0RF".
Definition tm' := TM_from_str "1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFAD") 63 82.
Time Qed.
End TM237.


Module TM238.
Definition tm := TM_from_str "1LB0RA_0LC1RE_1RD0LA_1RB1RC_0RF---_0RD0RF".
Definition tm' := TM_from_str "1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RF---_0RA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 4.
Time Qed.
End TM238.


Module TM239.
Definition tm := TM_from_str "1RB0LF_0RC0RB_0LD1LA_1LD0LE_1RB0LA_---1RC".
Definition tm' := TM_from_str "1RB0LE_0RC0RB_0LD1LE_1LD0LA_1RB0LF_---1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM239.


Module TM240.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RD1LB_0LA1RE_0RA1RF_0LB---".
Definition tm' := TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA0RB_0RD1RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 3 4.
Time Qed.
End TM240.


Module TM241.
Definition tm := TM_from_str "1LB0RC_0LC0LB_0RD0RE_1RA---_1LA1RF_1RC0RE".
Definition tm' := TM_from_str "1RB0RF_0RC0RF_1RD---_1LE0RB_0LB0LE_1LD1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 1701 1530.
Time Qed.
End TM241.


Module TM242.
Definition tm := TM_from_str "1LB---_0LC0RE_1LD0RF_1RB0LF_1RC0LE_0RB0RA".
Definition tm' := TM_from_str "1RB0LA_1LC0RD_1RE0LD_0RE0RF_0LB0RA_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEBCAD") 1 4.
Time Qed.
End TM242.


Module TM243.
Definition tm := TM_from_str "1RB1LD_1RC1RA_0LC1LB_0LF0LE_0RA1RE_---0LD".
Definition tm' := TM_from_str "1RB1RC_0LB1LA_1RA1LD_0LF0LE_0RC1RE_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 3 4.
Time Qed.
End TM243.


Module TM244.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1RF---_1LC1LF".
Definition tm' := TM_from_str "1RB---_1LC1LB_1LD1RC_1RF1LE_1LA0LD_1RC0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFCEAB") 2 4.
Time Qed.
End TM244.


Module TM245.
Definition tm := TM_from_str "1RB0LC_1LA0RA_1RD1LE_1RA1RF_1LA0RD_1RE---".
Definition tm' := TM_from_str "1RB1RF_1RC0LD_1LB0RB_1RA1LE_1LB0RA_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 12 4.
Time Qed.
End TM245.


Module TM246.
Definition tm := TM_from_str "1RB1LE_1LC0RC_1RD1LA_1RB0RF_1LA0LC_---1RE".
Definition tm' := TM_from_str "1RB0RF_1LC0RC_1RA1LD_1RB1LE_1LD0LC_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM246.


Module TM247.
Definition tm := TM_from_str "1LB1LF_1RC0LE_1RE0RD_1RC---_0LA0RE_1RB1LF".
Definition tm' := TM_from_str "1RB0RF_0LC0RB_1LE1LD_1RE1LD_1RA0LB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEAFBD") 1 8.
Time Qed.
End TM247.


Module TM248.
Definition tm := TM_from_str "1RB0LC_1RC0RA_0LD0RB_1LA0LE_1LC0LF_1RD---".
Definition tm' := TM_from_str "1RB0RE_0LC0RA_1LE0LD_1LB0LF_1RA0LB_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 98 70.
Time Qed.
End TM248.


Module TM249.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RD0LD_1RA0RE_1RD1RF_1RE---".
Definition tm' := TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBAF") 7 11.
Time Qed.
End TM249.


Module TM250.
Definition tm := TM_from_str "1LB0LF_1LC0LB_1LD0LE_1LE---_1RA0RF_1RE1RF".
Definition tm' := TM_from_str "1RB0RF_1LC0LF_1LD0LC_1LE0LA_1LA---_1RA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 149 115.
Time Qed.
End TM250.


Module TM251.
Definition tm := TM_from_str "1LB1RD_1LC0LB_0LD0LD_1RE1LC_1RA0RF_1RA---".
Definition tm' := TM_from_str "1RB---_1LC1RE_1LD0LC_0LE0LE_1RF1LD_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 10 5.
Time Qed.
End TM251.


Module TM252.
Definition tm := TM_from_str "1LB1LF_1LC0RC_0RD0LA_1RB1RE_0LE1RF_0RC---".
Definition tm' := TM_from_str "1RB1RE_1LC0RC_0RA0LD_1LB1LF_0LE1RF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 17.
Time Qed.
End TM252.


Module TM253.
Definition tm := TM_from_str "1RB1RF_1LC0LB_0LD1LC_1RE0RA_1RA---_0RA0RD".
Definition tm' := TM_from_str "1RB0RC_1RC---_1RD1RF_1LE0LD_0LA1LE_0RC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 39 79.
Time Qed.
End TM253.


Module TM254.
Definition tm := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LE_0LC0RB_0LD1LB".
Definition tm' := TM_from_str "1RB1LE_0RC0LF_1LD0RF_0LA---_0LB1LD_0LA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 22 32.
Time Qed.
End TM254.


Module TM255.
Definition tm := TM_from_str "1LB1RE_1LC1RD_0RB0LC_0RA0LB_1RA0LF_---1LE".
Definition tm' := TM_from_str "1RB0LF_1LC1RA_1LE1RD_0RB0LC_0RC0LE_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEDAF") 3 2.
Time Qed.
End TM255.


Module TM256.
Definition tm := TM_from_str "1LB1RC_1RA1RD_1RB0LC_---0RE_1LF0RA_1LF0LC".
Definition tm' := TM_from_str "1RB1RC_1LA1RF_---0RD_1LE0RB_1LE0LF_1RA0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BAFCDE") 32 34.
Time Qed.
End TM256.


Module TM257.
Definition tm := TM_from_str "1RB1RD_1RC0RB_0LD1LA_0LE1LC_1RB1LF_0LE---".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_0LD1LE_0LA1LC_1RB1RD_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM257.


Module TM258.
Definition tm := TM_from_str "1RB1RA_1RC0RD_0LD1RC_---0LE_0RA1LF_1RA1LD".
Definition tm' := TM_from_str "1RB0RC_0LC1RB_---0LD_0RE1LF_1RA1RE_1RE1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 5.
Time Qed.
End TM258.


Module TM259.
Definition tm := TM_from_str "1LB1LE_1RC---_0LD0RC_0LE1LF_1LA0RF_1RE0LB".
Definition tm' := TM_from_str "1RB0LD_1LC0RA_1LD1LB_1RE---_0LF0RE_0LB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 7 1.
Time Qed.
End TM259.


Module TM260.
Definition tm := TM_from_str "1RB0RA_0RC---_1LD0RF_0LE0LD_1RB1LD_1RC1RA".
Definition tm' := TM_from_str "1RB1LD_0RC---_1LD0RE_0LA0LD_1RC1RF_1RB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM260.


Module TM261.
Definition tm := TM_from_str "1RB0LD_1RC1RD_1LD1RD_1RF1LE_0LD0LE_0RA---".
Definition tm' := TM_from_str "1RB1RC_1LC1RC_1RE1LD_0LC0LD_0RF---_1RA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 42 32.
Time Qed.
End TM261.


Module TM262.
Definition tm := TM_from_str "1LB1RA_1LC1LE_1RD1LC_1RA0RA_1LF0LC_---0LB".
Definition tm' := TM_from_str "1RB1LA_1RC0RC_1LD1RC_1LA1LE_1LF0LA_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 1369 1475.
Time Qed.
End TM262.


Module TM263.
Definition tm := TM_from_str "1LB0LA_0RC1LC_1LF0RD_1RE1RB_0LB1RB_0LA---".
Definition tm' := TM_from_str "1RB1RC_0LC1RC_0RD1LD_1LE0RA_0LF---_1LC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 4 1.
Time Qed.
End TM263.


Module TM264.
Definition tm := TM_from_str "1LB1LE_1LC---_1LD1RC_0LE1LA_1RF0LD_1LC0RF".
Definition tm' := TM_from_str "1RB0LD_1LC0RB_1LD1RC_0LA1LE_1LF1LA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCDAB") 10 19.
Time Qed.
End TM264.


Module TM265.
Definition tm := TM_from_str "1LB1RC_1RC1LA_0RD0LA_0LA0RE_---0RF_0LC0RC".
Definition tm' := TM_from_str "1RB1LD_0RC0LD_0LD0RE_1LA1RB_---0RF_0LB0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 4 1.
Time Qed.
End TM265.


Module TM266.
Definition tm := TM_from_str "1LB1LA_1RC1LF_0RE0LD_---1RC_0RF1RD_1RA0LA".
Definition tm' := TM_from_str "1RB1LD_0RC0LF_0RD1RF_1RE0LE_1LA1LE_---1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABFCD") 4 1.
Time Qed.
End TM266.


Module TM267.
Definition tm := TM_from_str "1RB1RE_1LC0RA_1RB1LD_0LE---_0LF1LF_0LB0RA".
Definition tm' := TM_from_str "1RB1LC_1LA0RF_0LD---_0LE1LE_0LB0RF_1RB1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBACDE") 1 1.
Time Qed.
End TM267.


Module TM268.
Definition tm := TM_from_str "1RB1LC_1LA0RE_1LD1LF_0LB0LC_1RB1LE_---0RD".
Definition tm' := TM_from_str "1RB1LA_1LC0RA_1RB1LD_1LE1LF_0LB0LD_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM268.


Module TM269.
Definition tm := TM_from_str "1LB0RF_1RC0LB_0LE0RD_1RA---_1RD1LB_0RC0LB".
Definition tm' := TM_from_str "1RB0LA_0LC0RD_1RD1LA_1RE---_1LA0RF_0RB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABDCF") 1 3.
Time Qed.
End TM269.


Module TM270.
Definition tm := TM_from_str "1LB1RA_1RC0LF_---0LD_1LA0RE_1RD0RB_1LB1LF".
Definition tm' := TM_from_str "1RB0RD_1LC0RA_1LD1RC_1RF0LE_1LD1LE_---0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFBAE") 5 1.
Time Qed.
End TM270.


Module TM271.
Definition tm := TM_from_str "1LB1RC_0RA1LD_1RA1LE_1RB0LD_1LF0LE_---0RA".
Definition tm' := TM_from_str "1RB1LE_1LC1RA_0RB1LD_1RC0LD_1LF0LE_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 6 5.
Time Qed.
End TM271.


Module TM272.
Definition tm := TM_from_str "1LB0RA_0RC0LE_---0LD_1RA1LE_1LD1RF_0RB0RE".
Definition tm' := TM_from_str "1RB1LD_1LC0RB_0RE0LD_1LA1RF_---0LA_0RC0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEADF") 4 1.
Time Qed.
End TM272.


Module TM273.
Definition tm := TM_from_str "1RB---_1RC1LB_1LD1RF_0LF0LE_0RC0LD_1RA0RC".
Definition tm' := TM_from_str "1RB1LA_1LC1RE_0LE0LD_0RB0LC_1RF0RB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 36 51.
Time Qed.
End TM273.


Module TM274.
Definition tm := TM_from_str "1RB1RA_1LC0LB_1LF0RD_---0RE_1RC1RA_0RC1LB".
Definition tm' := TM_from_str "1RB1RF_1LC0RE_0RB1LD_1LB0LD_---0RA_1RD1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDBEAC") 5 1.
Time Qed.
End TM274.


Module TM275.
Definition tm := TM_from_str "1LB1RD_1RC0LB_0LE0RD_1RA1LF_---0RA_0LC0LF".
Definition tm' := TM_from_str "1RB0LA_0LC0RE_---0RD_1LA1RE_1RD1LF_0LB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 1 4.
Time Qed.
End TM275.


Module TM276.
Definition tm := TM_from_str "1RB---_1LC0RC_0RE0LD_1LC1LB_0LD1RF_1RB0RA".
Definition tm' := TM_from_str "1RB0RF_1LC0RC_0RE0LD_1LC1LB_0LD1RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM276.


Module TM277.
Definition tm := TM_from_str "1RB0RA_1LC0RA_1RB1LD_0LE---_0LF1LF_0LB1RF".
Definition tm' := TM_from_str "1RB1LC_1LA0RF_0LD---_0LE1LE_0LB1RE_1RB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBACDE") 1 1.
Time Qed.
End TM277.


Module TM278.
Definition tm := TM_from_str "1LB1LF_1RC1LB_0RD0RC_1RE---_0LA0LF_0LE0RB".
Definition tm' := TM_from_str "1RB1LA_0RC0RB_1RD---_0LE0LF_1LA1LF_0LD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 66 22.
Time Qed.
End TM278.


Module TM279.
Definition tm := TM_from_str "1RB0LC_1LC1RC_0RA1LD_0LC1LE_0LA0LF_1RC---".
Definition tm' := TM_from_str "1RB---_0RC1LE_1RD0LB_1LB1RB_0LB1LF_0LC0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEFA") 64 46.
Time Qed.
End TM279.


Module TM280.
Definition tm := TM_from_str "1RB0RA_1LC0RA_1RB0LD_1LE1LB_1LC0LF_0LC---".
Definition tm' := TM_from_str "1RB0LC_1LA0RE_1LD1LB_1LA0LF_1RB0RE_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM280.


Module TM281.
Definition tm := TM_from_str "1RB0LD_0RC0LD_1RD0RE_1LB1LF_0RA0RF_1RE---".
Definition tm' := TM_from_str "1RB0RD_1LC1LF_0RA0LB_0RE0RF_1RC0LB_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECABDF") 1 13.
Time Qed.
End TM281.


Module TM282.
Definition tm := TM_from_str "1RB1LC_0LC1RE_---0LD_0RE1LA_1RF1RB_1LB0RE".
Definition tm' := TM_from_str "1RB1RC_1LC0RA_0LD1RA_---0LE_0RA1LF_1RC1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEAB") 5 1.
Time Qed.
End TM282.


Module TM283.
Definition tm := TM_from_str "1LB0RA_1RB1RC_1LD0LA_1RA1LE_1LF0LD_1LC---".
Definition tm' := TM_from_str "1RB1LE_1LC0RB_1RC1RD_1LA0LB_1LF0LA_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 1 6.
Time Qed.
End TM283.


Module TM284.
Definition tm := TM_from_str "1RB0LB_1LC1LF_---1RD_0LF1RE_1RD1RF_0RE0LA".
Definition tm' := TM_from_str "1RB1RC_0LC1RA_0RA0LD_1RE0LE_1LF1LC_---1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBAC") 1 4.
Time Qed.
End TM284.


Module TM285.
Definition tm := TM_from_str "1RB0LC_1LA0RD_1LA1LB_0RE1RF_---1RA_1RC0RB".
Definition tm' := TM_from_str "1RB0RD_1LC1LD_1RD0LB_1LC0RE_0RF1RA_---1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEFA") 2 2.
Time Qed.
End TM285.


Module TM286.
Definition tm := TM_from_str "1RB1RF_1LC1RE_1LD0LC_1RB1LD_1RA0RB_0RD---".
Definition tm' := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB1RF_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM286.


Module TM287.
Definition tm := TM_from_str "1RB0LC_1RC0RA_0LD1LA_0RB1LE_1RA0LF_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RF_0LD1LF_0RB1LE_1RF0LA_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM287.


Module TM288.
Definition tm := TM_from_str "1RB0RC_1LC0RA_---1RD_1RB0LE_1LD1LF_1LE0RD".
Definition tm' := TM_from_str "1RB0LD_1LC0RF_---1RA_1LA1LE_1LD0RA_1RB0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM288.


Module TM289.
Definition tm := TM_from_str "1LB0LE_1LC1LB_1RD1RC_0LA0RD_0LF1LA_1RB---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_0LE1LC_1RF---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 36 57.
Time Qed.
End TM289.


Module TM290.
Definition tm := TM_from_str "1RB0RA_0LC0LE_0RE1LD_1RC1LB_1RA1LF_1LC---".
Definition tm' := TM_from_str "1RB1LE_0RC1LA_1RD1LF_1RE0RD_0LB0LC_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBACF") 15 5.
Time Qed.
End TM290.


Module TM291.
Definition tm := TM_from_str "1LB0LE_1RC0RE_1RD0RB_0LA0RC_1LD1LF_0LD---".
Definition tm' := TM_from_str "1RB0RE_1RC0RA_0LD0RB_1LA0LE_1LC1LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 19 1.
Time Qed.
End TM291.


Module TM292.
Definition tm := TM_from_str "1LB0LD_1LC0LA_1RD1LC_0LF0RE_1RD1RE_---1LB".
Definition tm' := TM_from_str "1RB1RA_0LC0RA_---1LD_1LE0LF_1RB1LE_1LD0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEBAC") 1 3.
Time Qed.
End TM292.


Module TM293.
Definition tm := TM_from_str "1RB1RF_1RC---_1RD1RC_1LE1LD_0RF0LE_1RC0RA".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 2 6.
Time Qed.
End TM293.


Module TM294.
Definition tm := TM_from_str "1RB1RA_1LB1LC_1RD0LF_1RF1LE_---0RA_0LE0LC".
Definition tm' := TM_from_str "1RB1LC_0LC0LF_---0RD_1RE1RD_1LE1LF_1RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFACB") 1 4.
Time Qed.
End TM294.


Module TM295.
Definition tm := TM_from_str "1LB0LB_1RC1LE_1RE1RD_0RE---_0LA0RF_1RA0RC".
Definition tm' := TM_from_str "1RB0RE_1LC0LC_1RE1LD_0LB0RA_1RD1RF_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEFDA") 12 1.
Time Qed.
End TM295.


Module TM296.
Definition tm := TM_from_str "1LB1RC_1RC1LA_0LB0RD_0RE0LB_0LB0RF_---0RC".
Definition tm' := TM_from_str "1RB1LC_0LA0RD_1LA1RB_0RE0LA_0LA0RF_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 2 11.
Time Qed.
End TM296.


Module TM297.
Definition tm := TM_from_str "1RB0RE_1RC---_1LD1RA_1RE1RD_0LF1RA_0LA1LF".
Definition tm' := TM_from_str "1RB1RA_0LC1RD_0LD1LC_1RE0RB_1RF---_1LA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 23 7.
Time Qed.
End TM297.


Module TM298.
Definition tm := TM_from_str "1RB---_1LC0RB_0LF1LD_1RC0LE_0RA0LE_1RA1LE".
Definition tm' := TM_from_str "1RB1LF_1RC---_1LD0RC_0LA1LE_1RD0LF_0RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 5 4.
Time Qed.
End TM298.


Module TM299.
Definition tm := TM_from_str "1RB---_1LC0RA_0RD0LC_1RE0RE_1RF1LE_1RB1RD".
Definition tm' := TM_from_str "1RB1RD_1LC0RF_0RD0LC_1RE0RE_1RA1LE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM299.


Module TM300.
Definition tm := TM_from_str "1RB1RF_1RC0RB_1LD0RA_1LE0LD_1RB0LC_0RB---".
Definition tm' := TM_from_str "1RB0LC_1RC0RB_1LD0RE_1LA0LD_1RB1RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM300.


Module TM301.
Definition tm := TM_from_str "1LB0RF_1LC---_1RD0LF_1RE0RD_0RA0RA_0LE0LA".
Definition tm' := TM_from_str "1RB0LF_1RC0RB_0RD0RD_1LE0RF_1LA---_0LC0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 7 16.
Time Qed.
End TM301.


Module TM302.
Definition tm := TM_from_str "1RB1LD_1RC0LE_1LA1RB_0LA0LB_0RE1RF_0RA---".
Definition tm' := TM_from_str "1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 67 30.
Time Qed.
End TM302.


Module TM303.
Definition tm := TM_from_str "1LB0RE_1RC1RB_0LD0RC_1LA0LE_1LF1LD_1LD---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_1LC---_1LA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 1442 2289.
Time Qed.
End TM303.


Module TM304.
Definition tm := TM_from_str "1LB0RE_1LC1LF_0LD1LB_1RE0LA_0RA0RD_1RD---".
Definition tm' := TM_from_str "1RB---_1RC0LD_0RD0RB_1LE0RC_1LF1LA_0LB1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 1 15.
Time Qed.
End TM304.


Module TM305.
Definition tm := TM_from_str "1LB1RF_1RC0LC_0RD1LC_1LA0RE_0LA1RA_---0RE".
Definition tm' := TM_from_str "1RB0LB_0RC1LB_1LD0RE_1LA1RF_0LD1RD_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 35 4.
Time Qed.
End TM305.


Module TM306.
Definition tm := TM_from_str "1RB0LF_1LC1LE_0RD1LB_1RB1RD_---1RF_1LA0RA".
Definition tm' := TM_from_str "1RB1RA_1LC1LD_0RA1LB_---1RE_1LF0RF_1RB0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM306.


Module TM307.
Definition tm := TM_from_str "1LB0LF_1LC---_1RD0LE_1RF1RC_0RA0RC_1LA1LE".
Definition tm' := TM_from_str "1RB1RE_1LC1LF_1LD0LB_1LE---_1RA0LF_0RC0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEAFB") 17257 15353.
Time Qed.
End TM307.


Module TM308.
Definition tm := TM_from_str "1LB---_0RC1LD_1RF1RA_1RE0LB_1RC1RD_1LD0RE".
Definition tm' := TM_from_str "1RB1RD_1RC1RF_1LD0RA_1RA0LE_0RB1LD_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEBDAC") 212 89.
Time Qed.
End TM308.


Module TM309.
Definition tm := TM_from_str "1RB1RF_0LC0RE_1LD1LB_1RB0LB_0RF---_0RA1RE".
Definition tm' := TM_from_str "1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM309.


Module TM310.
Definition tm := TM_from_str "1LB1LE_1RC0LE_1LA0RD_0RE1RF_0LF---_0RB1LC".
Definition tm' := TM_from_str "1RB0LD_1LC0RF_1LA1LD_0LE---_0RA1LB_0RD1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABFDE") 109 163.
Time Qed.
End TM310.


Module TM311.
Definition tm := TM_from_str "1RB0RF_0RC0RA_1LD1LE_0LE0LD_1RB0LC_1RE---".
Definition tm' := TM_from_str "1RB0LC_0RC0RE_1LD1LA_0LA0LD_1RB0RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM311.


Module TM312.
Definition tm := TM_from_str "1LB1LA_1RC0LA_---0LD_1LF0RE_1RD0RB_1LB1RF".
Definition tm' := TM_from_str "1RB0RD_1LC0RA_1LD1RC_1RF0LE_1LD1LE_---0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDFBAC") 5 1.
Time Qed.
End TM312.


Module TM313.
Definition tm := TM_from_str "1RB0LC_1RC0RF_1LD0RA_1RE0LD_1LE0RA_0RC---".
Definition tm' := TM_from_str "1RB0RF_1LC0RE_1RD0LC_1LD0RE_1RA0LB_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 86 190.
Time Qed.
End TM313.


Module TM314.
Definition tm := TM_from_str "1LB0RA_0LC1LF_0RD1LE_1RA---_0LF0LD_1RA0LB".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LD1LA_0RE1LF_1RB---_0LA0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 735 707.
Time Qed.
End TM314.


Module TM315.
Definition tm := TM_from_str "1RB0LF_1RC0RC_1RD1RE_0LE0LB_0RC0LA_---1LE".
Definition tm' := TM_from_str "1RB1RC_0LC0LE_0RA0LD_1RE0LF_1RA0RA_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM315.


Module TM316.
Definition tm := TM_from_str "1LB1RE_1RC0LA_1LD0RD_1RB0RB_0RF---_0RB1RA".
Definition tm' := TM_from_str "1RB0LD_1LC0RC_1RA0RA_1LA1RE_0RF---_0RA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 5.
Time Qed.
End TM316.


Module TM317.
Definition tm := TM_from_str "1LB0RF_0LC0LF_1LD0LC_1RE0LB_0LA0RD_0RE---".
Definition tm' := TM_from_str "1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEFABD") 1 6.
Time Qed.
End TM317.


Module TM318.
Definition tm := TM_from_str "1RB1LC_0LC0RA_0LF0RD_1RE---_0LA0LB_1LA0LB".
Definition tm' := TM_from_str "1RB---_0LC0LF_1RF1LD_0LE0RA_1LC0LF_0LD0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFDABE") 4 1.
Time Qed.
End TM318.


Module TM319.
Definition tm := TM_from_str "1LB0RC_1RC0LF_0LD1RC_1RB1RE_1RA1LE_---0LE".
Definition tm' := TM_from_str "1RB1RD_1RC0LF_0LA1RC_1RE1LD_1LB0RC_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 3 2.
Time Qed.
End TM319.


Module TM320.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_1LE---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM320.


Module TM321.
Definition tm := TM_from_str "1RB---_1LC0RE_1RF0LD_1RE1LB_1RC1RA_1LC0RC".
Definition tm' := TM_from_str "1RB1RF_1RC0LD_1LB0RB_1RA1LE_1LB0RA_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEBDAC") 12 4.
Time Qed.
End TM321.


Module TM322.
Definition tm := TM_from_str "1RB1LF_1LC1LB_0RD0LC_1RE---_0RA1RA_1RB1RF".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RE---_0RF1RF_1RB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM322.


Module TM323.
Definition tm := TM_from_str "1LB0RC_1RC0LA_1RA1RD_1LE0RC_1RF0LD_---1RE".
Definition tm' := TM_from_str "1RB0LC_1RC1RD_1LA0RB_1LE0RB_1RF0LD_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 6 5.
Time Qed.
End TM323.


Module TM324.
Definition tm := TM_from_str "1LB---_1RC1LC_1LF0RD_1RE1RC_0LF0RE_1LD0LA".
Definition tm' := TM_from_str "1RB1RF_0LC0RB_1LA0LD_1LE---_1RF1LF_1LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 1 4.
Time Qed.
End TM324.


Module TM325.
Definition tm := TM_from_str "1RB1LA_1RC1RB_1RD0LA_1LE1RF_0RF0LE_0RB---".
Definition tm' := TM_from_str "1RB0LF_1LC1RD_0RD0LC_0RE---_1RA1RE_1RE1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEABCD") 1 6.
Time Qed.
End TM325.


Module TM326.
Definition tm := TM_from_str "1RB0RD_1LC1RE_1LF0LD_0RE1LC_1LC1RA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1RE_1LA0LD_0RE1LC_1LC1RF_1RB0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM326.


Module TM327.
Definition tm := TM_from_str "1RB1LC_1LA0RD_0LD0LF_1LE0RA_1RD1LF_0LA---".
Definition tm' := TM_from_str "1RB1LC_1LA0RD_0LD---_1RE1LF_1LD0RB_0LB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBAC") 17 19.
Time Qed.
End TM327.


Module TM328.
Definition tm := TM_from_str "1RB0RE_0LC1LE_0LF1LD_1RE0LF_1RA0LB_1RA---".
Definition tm' := TM_from_str "1RB---_1RC0RF_0LD1LF_0LA1LE_1RF0LA_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 81 49.
Time Qed.
End TM328.


Module TM329.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC1LF_1RA---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM329.


Module TM330.
Definition tm := TM_from_str "1LB0LC_1RC0RD_1LA0RB_1RE0LA_0LD1RF_0RC---".
Definition tm' := TM_from_str "1RB0LC_0LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 1 4.
Time Qed.
End TM330.


Module TM331.
Definition tm := TM_from_str "1RB1RC_0LC---_1LE0RD_1RC0RA_1LF1LC_0LA0LB".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_1LD1LB_0LE0LF_1RF1RB_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBACD") 4 1.
Time Qed.
End TM331.


Module TM332.
Definition tm := TM_from_str "1LB0LF_0RC1RF_0RF1RD_0LD0RE_1RF---_1LA0RB".
Definition tm' := TM_from_str "1RB---_1LC0RD_1LD0LB_0RE1RB_0RB1RF_0LF0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 6 1.
Time Qed.
End TM332.


Module TM333.
Definition tm := TM_from_str "1LB1RE_0LC0RE_1RC0LD_0RF0LB_1RF1LB_1RA---".
Definition tm' := TM_from_str "1RB---_1LC1RD_0LE0RD_1RA1LC_1RE0LF_0RA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEFDA") 1 4.
Time Qed.
End TM333.


Module TM334.
Definition tm := TM_from_str "1LB1LF_1LC---_1RD1RC_1RF1RE_0LF0RE_0LD1LA".
Definition tm' := TM_from_str "1RB1RA_1RC1RD_0LB1LE_0LC0RD_1LF1LC_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABDC") 6 2.
Time Qed.
End TM334.


Module TM335.
Definition tm := TM_from_str "1RB0RA_1LC0RA_1RF1LD_0LE---_0LF1LC_0LB0RA".
Definition tm' := TM_from_str "1RB1LE_0LC0RD_1LA0RD_1RC0RD_0LF---_0LB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCAEFB") 1 4.
Time Qed.
End TM335.


Module TM336.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RD1LB_0LA1RE_0RA1RF_1LB---".
Definition tm' := TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA0RB_0RD1RF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 3 4.
Time Qed.
End TM336.


Module TM337.
Definition tm := TM_from_str "1LB0LC_1RC0RD_1LA0RB_1RB0LE_1LF---_0LD0LC".
Definition tm' := TM_from_str "1RB0LE_1RC0RA_1LD0RB_1LB0LC_1LF---_0LA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 5.
Time Qed.
End TM337.


Module TM338.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RC_1LC1LF_0RA---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM338.


Module TM339.
Definition tm := TM_from_str "1RB0RA_1LC1LF_1RD0LB_---0RE_1RF1RA_0LC1LE".
Definition tm' := TM_from_str "1RB1RF_0LC1LA_1RE0LD_1LC1LB_---0RA_1RD0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDCEAB") 1 9.
Time Qed.
End TM339.


Module TM340.
Definition tm := TM_from_str "1RB0LC_1LA0RD_1LA0LB_1RE1RA_0LD0RF_0RB---".
Definition tm' := TM_from_str "1RB1RC_0LA0RF_1RD0LE_1LC0RA_1LC0LD_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 358 364.
Time Qed.
End TM340.


Module TM341.
Definition tm := TM_from_str "1LB---_1RC1LB_1RA1RD_0LE1RF_1RB0LE_1LE0RC".
Definition tm' := TM_from_str "1RB0LA_1RC1LB_1RD1RE_1LB---_0LA1RF_1LA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 7 1.
Time Qed.
End TM341.


Module TM342.
Definition tm := TM_from_str "1RB1LA_1RC1RE_1RD0LC_1LA---_1RF0RB_1LC1RE".
Definition tm' := TM_from_str "1RB0RF_1LC1RA_1RD0LC_1LE---_1RF1LE_1RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCDAB") 13 56.
Time Qed.
End TM342.


Module TM343.
Definition tm := TM_from_str "1LB0RA_0LC1LD_0RD1LE_1RA0LB_0LD1LF_1LD---".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LD1LA_0RA1LE_0LA1LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 731 705.
Time Qed.
End TM343.


Module TM344.
Definition tm := TM_from_str "1RB0RF_1RC0RA_0LD0RB_0LA1LE_0RE0LA_1LC---".
Definition tm' := TM_from_str "1RB0RE_0LC0RA_0LE1LD_0RD0LE_1RA0RF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 6.
Time Qed.
End TM344.


Module TM345.
Definition tm := TM_from_str "1RB1LC_1LA1RD_1LA1LD_1RE0LA_1LE0RF_---0RA".
Definition tm' := TM_from_str "1RB0LD_1LB0RC_---0RD_1RE1LF_1LD1RA_1LD1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 1 5.
Time Qed.
End TM345.


Module TM346.
Definition tm := TM_from_str "1LB---_1RC0RE_1LD0RD_1RB1LE_1RF0LA_1RA0RF".
Definition tm' := TM_from_str "1RB0RA_1LC---_1RE0RD_1RA0LB_1LF0RF_1RC1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEFDA") 1 5.
Time Qed.
End TM346.


Module TM347.
Definition tm := TM_from_str "1LB0RB_0LC0RF_1RD1LE_0RA0LB_0LD0LF_0RE---".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0RD_0LA0RF_0LB0LF_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 19 39.
Time Qed.
End TM347.


Module TM348.
Definition tm := TM_from_str "1RB0LC_0LA0LC_1RD0LE_1RE0RC_0LF1LC_---1LB".
Definition tm' := TM_from_str "1RB0LC_1RC0RA_0LD1LA_---1LE_0LF0LA_1RE0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEABCD") 4 1.
Time Qed.
End TM348.


Module TM349.
Definition tm := TM_from_str "1LB1LF_0LC0RE_1LD0LA_1RE0LB_1RB0RD_0LB---".
Definition tm' := TM_from_str "1RB0LC_1RC0RA_0LD0RB_1LA0LE_1LC1LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDABF") 59 88.
Time Qed.
End TM349.


Module TM350.
Definition tm := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_1LB---".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 762 750.
Time Qed.
End TM350.


Module TM351.
Definition tm := TM_from_str "1RB0LF_1RC1RF_1LD1RE_0RC0LD_0RF---_1RB1LA".
Definition tm' := TM_from_str "1RB1LF_1RC1RA_1LD1RE_0RC0LD_0RA---_1RB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM351.


Module TM352.
Definition tm := TM_from_str "1LB1RE_1RC1LB_1LE0RD_1RC0LC_1RA1RF_---1LD".
Definition tm' := TM_from_str "1RB0LB_1LC0RA_1RE1RD_---1LA_1LF1RC_1RB1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBACD") 65 52.
Time Qed.
End TM352.


Module TM353.
Definition tm := TM_from_str "1LB0RF_1RC0LA_1LD0RB_1LE1LC_1RA---_1RC1RF".
Definition tm' := TM_from_str "1RB---_1LC0RF_1RD0LB_1LE0RC_1LA1LD_1RD1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 118 133.
Time Qed.
End TM353.


Module TM354.
Definition tm := TM_from_str "1RB---_1LC0LB_0LD1LB_1LE1LA_1RF0RE_1RB0RE".
Definition tm' := TM_from_str "1RB0RE_1LC0LB_0LD1LB_1LE1LF_1RA0RE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM354.


Module TM355.
Definition tm := TM_from_str "1RB1LA_1LC0RF_---0LD_1LE0RC_1RF1LD_1RD0RA".
Definition tm' := TM_from_str "1RB1LC_1RC0RE_1LA0RD_---0LC_1RF1LE_1LD0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDCAB") 2 5.
Time Qed.
End TM355.


Module TM356.
Definition tm := TM_from_str "1LB0RC_1RC0LE_0LF1RD_1RA0RB_1LD1LA_1LA---".
Definition tm' := TM_from_str "1RB0RC_1LC0RE_1RE0LD_1LA1LB_0LF1RA_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEADF") 7 8.
Time Qed.
End TM356.


Module TM357.
Definition tm := TM_from_str "1LB0LC_1RC0RE_1RA0LD_0LA0RB_---1RF_1LC1RB".
Definition tm' := TM_from_str "1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABFDE") 5 1.
Time Qed.
End TM357.


Module TM358.
Definition tm := TM_from_str "1LB0LA_1RC0LD_0RF0RD_1LA1RE_0LE0RB_0LD---".
Definition tm' := TM_from_str "1RB0LD_0RC0RD_0LD---_1LE1RF_1LA0LE_0LF0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABDFC") 91 171.
Time Qed.
End TM358.


Module TM359.
Definition tm := TM_from_str "1RB1RF_1RC1RD_1LB---_0RA1LE_1RF0LD_1RA0LF".
Definition tm' := TM_from_str "1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LD---_0RC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 24 50.
Time Qed.
End TM359.


Module TM360.
Definition tm := TM_from_str "1LB0RD_0LC---_1RD0LF_1RE1RF_0LF1LA_0RA1RB".
Definition tm' := TM_from_str "1RB1RC_0LC1LF_0RF1RD_0LE---_1RA0LC_1LD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 1 7.
Time Qed.
End TM360.


Module TM361.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD0LF_0RE---".
Definition tm' := TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC0LF_1RA1LC_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 6 3.
Time Qed.
End TM361.


Module TM362.
Definition tm := TM_from_str "1LB0LE_0RC0LB_1RD0RC_1RA1RC_1LA0RF_1RE---".
Definition tm' := TM_from_str "1RB---_1LC0RA_1LD0LB_0RE0LD_1RF0RE_1RC1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 92 88.
Time Qed.
End TM362.


Module TM363.
Definition tm := TM_from_str "1LB0RE_1RC0LD_1LA1RA_0LF1LE_0LC0RA_---0LC".
Definition tm' := TM_from_str "1RB0LE_1LC1RC_1LA0RD_0LB0RC_0LF1LD_---0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 5.
Time Qed.
End TM363.


Module TM364.
Definition tm := TM_from_str "1RB0LA_0LC---_1RF0RD_1RE1LD_0RC1RC_1LA1LF".
Definition tm' := TM_from_str "1RB1LA_0RC1RC_1RD0RA_1LE1LD_1RF0LE_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCABD") 4 1.
Time Qed.
End TM364.


Module TM365.
Definition tm := TM_from_str "1LB0RA_0LC1RA_0RD1LE_1RA0LB_0LD1LF_0LD---".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LD1RB_0RA1LE_0LA1LF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 4 3.
Time Qed.
End TM365.


Module TM366.
Definition tm := TM_from_str "1LB---_0LC0RB_1LD0LF_1LE1LD_1RB1RE_1LA1LC".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_1LB---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFAD") 497 308.
Time Qed.
End TM366.


Module TM367.
Definition tm := TM_from_str "1LB1RA_1RC1LD_0RD0RC_1LE0LB_1LF---_1LA1RB".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 15 21.
Time Qed.
End TM367.


Module TM368.
Definition tm := TM_from_str "1RB0LA_0RC0LA_1LB1RD_1RC1LE_0LF0LE_---0RC".
Definition tm' := TM_from_str "1RB1LE_1LC1RA_0RB0LD_1RC0LD_0LF0LE_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCBAEF") 4 5.
Time Qed.
End TM368.


Module TM369.
Definition tm := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LE---".
Definition tm' := TM_from_str "1RB1RC_0LA---_1RD0RA_1RE0LA_1LF1LE_0RC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFCAB") 6 2.
Time Qed.
End TM369.


Module TM370.
Definition tm := TM_from_str "1LB---_1RC0LC_0LE0RD_1LE0RD_0RF0LA_1LA1RD".
Definition tm' := TM_from_str "1RB0LB_0LC0RE_0RF0LD_1LA---_1LC0RE_1LD1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 1 4.
Time Qed.
End TM370.


Module TM371.
Definition tm := TM_from_str "1RB1LB_1RC0RB_0LC0LD_0LF1LE_1RA1LC_1RE---".
Definition tm' := TM_from_str "1RB0RA_0LB0LC_0LD1LE_1RE---_1RF1LB_1RA1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCED") 10 1.
Time Qed.
End TM371.


Module TM372.
Definition tm := TM_from_str "1RB0LC_1LA0RE_1LD1LC_1LA0LF_1RB0RE_0LA---".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1RB0LD_1LE1LD_1LC0LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM372.


Module TM373.
Definition tm := TM_from_str "1LB---_1LC1LF_0LD1RB_1RE0LE_1RC0LB_1LA0RF".
Definition tm' := TM_from_str "1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDCABE") 6 12.
Time Qed.
End TM373.


Module TM374.
Definition tm := TM_from_str "1LB1RE_1RC0LC_0LF0RD_1RE---_1LF0RC_0RD0LA".
Definition tm' := TM_from_str "1RB0LB_0LC0RE_0RE0LD_1LA1RF_1RF---_1LC0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABEFC") 1 4.
Time Qed.
End TM374.


Module TM375.
Definition tm := TM_from_str "1RB---_1LC1RD_1LA0LB_1LC0RE_1RD0RF_0RB0RE".
Definition tm' := TM_from_str "1RB0RF_1LC0RA_1LE0LD_1LC1RB_1RD---_0RD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDCBAF") 2 2.
Time Qed.
End TM375.


Module TM376.
Definition tm := TM_from_str "1RB---_0RC0LD_1LD1LA_0LE0RE_1RB1LF_0LB1LA".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD1LF_0LA0RA_0LB1LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM376.


Module TM377.
Definition tm := TM_from_str "1LB1LA_1RC1RB_0LD0RC_1LA0LE_0LF1LD_1RD---".
Definition tm' := TM_from_str "1RB---_1LC0LF_1LD1LC_1RE1RD_0LB0RE_0LA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBFA") 4 1.
Time Qed.
End TM377.


Module TM378.
Definition tm := TM_from_str "1RB1RD_0LC0RB_1RB1LD_0LE1RA_1LA1LF_---1LE".
Definition tm' := TM_from_str "1RB1LC_0LA0RB_0LD1RE_1LE1LF_1RB1RC_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM378.


Module TM379.
Definition tm := TM_from_str "1RB0RE_0LC1RE_---0LD_0RE1LF_1RA0LD_1RB1LC".
Definition tm' := TM_from_str "1RB0LE_1RC0RA_0LD1RA_---0LE_0RA1LF_1RC1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 5 1.
Time Qed.
End TM379.


Module TM380.
Definition tm := TM_from_str "1LB0RA_1RC1RC_1LD1RC_1RA1LE_1LF0LD_1LC---".
Definition tm' := TM_from_str "1RB1LE_1LC0RB_1RD1RD_1LA1RD_1LF0LA_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 2 3.
Time Qed.
End TM380.


Module TM381.
Definition tm := TM_from_str "1RB1LE_0LC0RB_1RB1LD_0LE---_1LF1RF_1LA0RF".
Definition tm' := TM_from_str "1RB1LC_0LA0RB_0LD---_1LE1RE_1LF0RE_1RB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBACDE") 1 1.
Time Qed.
End TM381.


Module TM382.
Definition tm := TM_from_str "1RB0LD_1LC0LB_1RD0RC_1LA0RE_1RA1RF_0LA---".
Definition tm' := TM_from_str "1RB0RA_1LC0RE_1RD0LB_1LA0LD_1RC1RF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 5 1.
Time Qed.
End TM382.


Module TM383.
Definition tm := TM_from_str "1LB0LC_1RC0LA_1LB0RD_1RE1RB_0LD0RF_0RC---".
Definition tm' := TM_from_str "1RB1RC_0LA0RF_1RD0LE_1LC0RA_1LC0LD_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDABF") 365 364.
Time Qed.
End TM383.


Module TM384.
Definition tm := TM_from_str "1RB0LE_0RC0RA_1RD0RC_1LE1LD_1LA0LF_1LD---".
Definition tm' := TM_from_str "1RB0RA_1LC1LB_1LE0LD_1LB---_1RF0LC_0RA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 227 241.
Time Qed.
End TM384.


Module TM385.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD1RA_0RA0LA_0RB1RF_1RB---".
Definition tm' := TM_from_str "1RB---_0LC0RE_1RE1RD_1LB1RF_0RD0LD_0RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 7.
Time Qed.
End TM385.


Module TM386.
Definition tm := TM_from_str "1LB1RF_1LC0LB_0LD0LF_1RE---_1RA1LE_1RD0RA".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_0LA0LF_1RA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 18 17.
Time Qed.
End TM386.


Module TM387.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_1RF0LD_0LE---".
Definition tm' := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 123 94.
Time Qed.
End TM387.


Module TM388.
Definition tm := TM_from_str "1RB0RC_1LC1RE_1LA0LD_0RB0LD_1RF0RB_1RA---".
Definition tm' := TM_from_str "1RB---_1RC0RD_1LD1RF_1LB0LE_0RC0LE_1RA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 52 52.
Time Qed.
End TM388.


Module TM389.
Definition tm := TM_from_str "1LB0LA_0RC1LA_1RD0LB_1RE0RD_1LC0RF_0LC---".
Definition tm' := TM_from_str "1RB0LD_1RC0RB_1LA0RF_0RA1LE_1LD0LE_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDABCF") 5 1.
Time Qed.
End TM389.


Module TM390.
Definition tm := TM_from_str "1RB1LE_1LC1LB_0RD0LC_1RE---_0RF1LA_1RA1RF".
Definition tm' := TM_from_str "1RB---_0RC1LD_1RD1RC_1RE1LB_1LF1LE_0RA0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 77 39.
Time Qed.
End TM390.


Module TM391.
Definition tm := TM_from_str "1RB0RA_1LC0RA_1LD0LB_1RB1LE_0LA0LF_0LE---".
Definition tm' := TM_from_str "1RB1LE_1LC0RD_1LA0LB_1RB0RD_0LD0LF_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM391.


Module TM392.
Definition tm := TM_from_str "1LB1LF_0LC0RE_1LD0LA_1RE0RA_1RB0RD_0LB---".
Definition tm' := TM_from_str "1RB0RE_1RC0RA_0LD0RB_1LA0LE_1LC1LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDABF") 59 88.
Time Qed.
End TM392.


Module TM393.
Definition tm := TM_from_str "1LB1RF_1RC0RD_1RA0LD_0RA1LE_1RD0LE_0RB---".
Definition tm' := TM_from_str "1RB0LD_1LC1RF_1RA0RD_0RB1LE_1RD0LE_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 3 3.
Time Qed.
End TM393.


Module TM394.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LD_0RB1RF_1RB---".
Definition tm' := TM_from_str "1RB---_0LC0RD_1RD0LD_0RE0LD_1LB1RF_0RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 5.
Time Qed.
End TM394.


Module TM395.
Definition tm := TM_from_str "1RB1RF_0RC---_1RD0LA_1LE1LD_0RF0LE_1RC0RA".
Definition tm' := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 768 1070.
Time Qed.
End TM395.


Module TM396.
Definition tm := TM_from_str "1RB0LD_1LC1LB_0RD0LC_1RE1RD_0RF1RA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1LB_0RD0LC_1RE1RD_0RA1RF_1RB0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM396.


Module TM397.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RD0LD_1RA0RE_1RD1RF_1RC---".
Definition tm' := TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBAF") 7 11.
Time Qed.
End TM397.


Module TM398.
Definition tm := TM_from_str "1RB1LA_1RC1RB_1RD1RF_1LE0RB_0RD0LE_1LA---".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_0RB0LC_1RA1RD_1LF---_1RD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDABCE") 1 8.
Time Qed.
End TM398.


Module TM399.
Definition tm := TM_from_str "1LB0RC_1RB0LA_1RD1LD_1LE0RD_0LB1LF_1LA---".
Definition tm' := TM_from_str "1RB1LB_1LC0RB_0LF1LD_1LE---_1LF0RA_1RF0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 5 1.
Time Qed.
End TM399.


Module TM400.
Definition tm := TM_from_str "1RB0LD_0LC0RA_1RB1LD_0LE1LF_1LA1RF_0RB---".
Definition tm' := TM_from_str "1RB1LC_0LA0RE_0LD1LF_1LE1RF_1RB0LC_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM400.


Module TM401.
Definition tm := TM_from_str "1LB0RE_1LC0LC_0LD1LA_1RE---_1RA0RF_1RB1RA".
Definition tm' := TM_from_str "1RB---_1RC0RF_1LD0RB_1LE0LE_0LA1LC_1RD1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 31 4.
Time Qed.
End TM401.


Module TM402.
Definition tm := TM_from_str "1RB0RF_1LC1RE_1LD0LC_1RB1LD_1RA0RB_0RB---".
Definition tm' := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM402.


Module TM403.
Definition tm := TM_from_str "1RB0LF_1LC0RD_1RB1LC_1LE1RD_---0LA_0RA1LF".
Definition tm' := TM_from_str "1RB1LA_1LA0RC_1LD1RC_---0LE_1RB0LF_0RE1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM403.


Module TM404.
Definition tm := TM_from_str "1RB1LF_0RC1LF_0RD0LE_1LD0LA_1RB0LE_---1LE".
Definition tm' := TM_from_str "1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM404.


Module TM405.
Definition tm := TM_from_str "1LB0LD_1LC0LA_1RD1LC_1LF0RE_1RD1RE_---0RB".
Definition tm' := TM_from_str "1RB1RA_1LC0RA_---0RD_1LF0LE_1LD0LB_1RB1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDFBAC") 1 5.
Time Qed.
End TM405.


Module TM406.
Definition tm := TM_from_str "1LB0RD_1RC0LD_1RA0RC_1LB0RE_1RF---_0LA0LF".
Definition tm' := TM_from_str "1RB0LD_1RC0RB_1LA0RD_1LA0RE_1RF---_0LC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 10.
Time Qed.
End TM406.


Module TM407.
Definition tm := TM_from_str "1RB0LB_0LC0RF_---1LD_1LE0LA_1RB1LE_1RB1RF".
Definition tm' := TM_from_str "1RB1LA_0LC0RE_---1LD_1LA0LF_1RB1RE_1RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM407.


Module TM408.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC0LF_0LA---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RE_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM408.


Module TM409.
Definition tm := TM_from_str "1LB1LE_1RC0LA_1LA0LD_1LC0RE_1RD1LF_0RD---".
Definition tm' := TM_from_str "1RB1LF_1LC0RA_1LD0LB_1LE1LA_1RC0LD_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECBAF") 5 1.
Time Qed.
End TM409.


Module TM410.
Definition tm := TM_from_str "1LB1RA_0RA0LC_1LD1RB_1RC0LE_0LB1LF_1RA---".
Definition tm' := TM_from_str "1RB---_1LC1RB_0RB0LD_1LE1RC_1RD0LF_0LC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 3 1.
Time Qed.
End TM410.


Module TM411.
Definition tm := TM_from_str "1RB1RE_0RC1RB_1LD0RD_1LA0RE_---0LF_1RB0LB".
Definition tm' := TM_from_str "1RB0LB_0RC1RB_1LD0RD_1LE0RF_1RB1RF_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM411.


Module TM412.
Definition tm := TM_from_str "1RB---_0RC0RE_0RD0RA_1LD1LE_1RB1LF_0LE0LF".
Definition tm' := TM_from_str "1RB1LE_0RC0RA_0RD0RF_1LD1LA_0LA0LE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM412.


Module TM413.
Definition tm := TM_from_str "1RB0RA_1RC1RC_0LD1LE_0RA0LC_1LF0RA_1LC---".
Definition tm' := TM_from_str "1RB1RB_0LC1LE_0RD0LB_1RA0RD_1LF0RD_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 6.
Time Qed.
End TM413.


Module TM414.
Definition tm := TM_from_str "1RB---_0RC0RC_0RD0LE_1RE0RA_1LF1RA_0LC1LB".
Definition tm' := TM_from_str "1RB0RF_1LC1RF_0LE1LD_0RE0RE_0RA0LB_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 24 30.
Time Qed.
End TM414.


Module TM415.
Definition tm := TM_from_str "1LB0LA_1LC1LA_0RD0RE_0LA1RC_1RA0RF_---1RD".
Definition tm' := TM_from_str "1RB0RF_1LC0LB_1LD1LB_0RE0RA_0LB1RD_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 1 20.
Time Qed.
End TM415.


Module TM416.
Definition tm := TM_from_str "1RB0LD_1RC1RE_1RD1LD_1LA1LC_0RA0RF_---0RE".
Definition tm' := TM_from_str "1RB1LB_1LC1LA_1RD0LB_1RA1RE_0RC0RF_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 6 13.
Time Qed.
End TM416.


Module TM417.
Definition tm := TM_from_str "1RB1LA_1RC1RB_1RD1LA_1LE0RF_0RD0LE_1RA---".
Definition tm' := TM_from_str "1RB1RA_1RC1LF_1LD0RE_0RC0LD_1RF---_1RA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 13 14.
Time Qed.
End TM417.


Module TM418.
Definition tm := TM_from_str "1LB0RF_0RC1LD_1RE0LD_0LB1LF_1RA---_0LC0RD".
Definition tm' := TM_from_str "1RB0LE_1RC---_1LD0RF_0RA1LE_0LD1LF_0LA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEBF") 6 1.
Time Qed.
End TM418.


Module TM419.
Definition tm := TM_from_str "1RB0LE_1LC0RA_1LD0LC_0RE0LA_0RD1LF_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM419.


Module TM420.
Definition tm := TM_from_str "1RB1LC_0LA0RE_0LD0RA_1RC1LD_0RC1RF_1RD---".
Definition tm' := TM_from_str "1RB1LA_0LA0RC_1RD1LB_0LC0RE_0RB1RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBAEF") 6 9.
Time Qed.
End TM420.


Module TM421.
Definition tm := TM_from_str "1RB0LD_1LC0RC_1RD1LA_1RB1RE_0LC1RF_---1RA".
Definition tm' := TM_from_str "1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM421.


Module TM422.
Definition tm := TM_from_str "1RB0RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0LA---".
Definition tm' := TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB0RF_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM422.


Module TM423.
Definition tm := TM_from_str "1RB1LA_0LA0RC_1RD1LB_0LC0RE_0RB1RF_1LA---".
Definition tm' := TM_from_str "1RB1LC_0LA0RE_0LD0RA_1RC1LD_0RC1RF_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCABEF") 9 6.
Time Qed.
End TM423.


Module TM424.
Definition tm := TM_from_str "1RB1RF_1LC1LF_0RD0LC_1RE---_0RF1RF_1RA0LB".
Definition tm' := TM_from_str "1RB0LC_1RC1RA_1LD1LA_0RE0LD_1RF---_0RA1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 1 9.
Time Qed.
End TM424.


Module TM425.
Definition tm := TM_from_str "1LB0RB_1RC0LE_0RF1RD_1RA---_0LB0LA_1RD1LD".
Definition tm' := TM_from_str "1RB1LB_1RC---_1LD0RD_1RF0LE_0LD0LC_0RA1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFBEA") 1 23.
Time Qed.
End TM425.


Module TM426.
Definition tm := TM_from_str "1LB1RD_1RC1RF_0LD0RC_1LE0LA_0LA1LA_---1RB".
Definition tm' := TM_from_str "1RB1RF_0LC0RB_1LE0LD_1LA1RC_0LD1LD_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 4.
Time Qed.
End TM426.


Module TM427.
Definition tm := TM_from_str "1RB---_0RC1RD_0LD1RF_1LE0RB_1RB0LE_0RD1RA".
Definition tm' := TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM427.


Module TM428.
Definition tm := TM_from_str "1RB0LC_1RC0RF_0LD0RC_1LA1LE_1RA0LF_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RA_0LD0RC_1LF1LE_1RF0LA_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM428.


Module TM429.
Definition tm := TM_from_str "1RB1RF_1LC1RA_1RD1LC_1LA0RE_1RD0LD_---1LE".
Definition tm' := TM_from_str "1RB0LB_1LC0RA_1RE1RD_---1LA_1LF1RC_1RB1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEFBAD") 6 1.
Time Qed.
End TM429.


Module TM430.
Definition tm := TM_from_str "1LB1LF_0RC0LB_1RA0RD_1RE---_0LB1RF_1RC0LA".
Definition tm' := TM_from_str "1RB0LC_1RC0RE_1LD1LA_0RB0LD_1RF---_0LD1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEFA") 12 19.
Time Qed.
End TM430.


Module TM431.
Definition tm := TM_from_str "1RB0RB_1LC1RA_1RB1LD_0LB1LE_0LF1LC_---0RD".
Definition tm' := TM_from_str "1RB1LC_1LA1RD_0LB1LE_1RB0RB_0LF1LA_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBACEF") 1 1.
Time Qed.
End TM431.


Module TM432.
Definition tm := TM_from_str "1RB0RD_1LC0RE_1LA0RD_0RA0LB_1RC1RF_0RB---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0RD_0RC0LE_1LB0RA_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEBDAF") 3 3.
Time Qed.
End TM432.


Module TM433.
Definition tm := TM_from_str "1LB---_1LC1LA_1LD0LB_1RE1LC_1RF0RE_1RC0RC".
Definition tm' := TM_from_str "1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB1LF_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEBCDA") 2 3.
Time Qed.
End TM433.


Module TM434.
Definition tm := TM_from_str "1LB---_1RC0LD_1RD0RB_0LE1LB_0RC1LF_0RF0LA".
Definition tm' := TM_from_str "1RB0RF_0LC1LF_0RA1LD_0RD0LE_1LF---_1RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 1 6.
Time Qed.
End TM434.


Module TM435.
Definition tm := TM_from_str "1RB0LC_1RC0RF_0LD1LA_0LA1LE_1RA1LE_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RA_0LD1LF_0LF1LE_1RF1LE_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM435.


Module TM436.
Definition tm := TM_from_str "1LB0RF_1RC0LE_1RD0LC_1RA0RE_0LB1LC_0RA---".
Definition tm' := TM_from_str "1RB0LA_1RC0RE_1LD0RF_1RA0LE_0LD1LA_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 5 1.
Time Qed.
End TM436.


Module TM437.
Definition tm := TM_from_str "1LB0RE_1RC0LB_1LA0RD_1RA1LF_1RD0LA_---0RC".
Definition tm' := TM_from_str "1RB0LA_1LC0RE_1LA0RD_1RE0LC_1RC1LF_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 5.
Time Qed.
End TM437.


Module TM438.
Definition tm := TM_from_str "1RB1LD_1RC1RE_0LD1RA_1LA0LA_1RF0RB_---0RB".
Definition tm' := TM_from_str "1RB1RE_0LC1RD_1LD0LD_1RA1LC_1RF0RA_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 4.
Time Qed.
End TM438.


Module TM439.
Definition tm := TM_from_str "1LB0RD_1LC1LC_1RA1LA_---1RE_0LF1RA_0LC1LF".
Definition tm' := TM_from_str "1RB1LB_1LC0RD_1LA1LA_---1RE_0LF1RB_0LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 2 3.
Time Qed.
End TM439.


Module TM440.
Definition tm := TM_from_str "1RB0RD_1LC0RA_1LA0LC_0RE0LB_1LB0RF_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1LD0LC_1RB0RE_0RF0LB_1LB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM440.


Module TM441.
Definition tm := TM_from_str "1LB1LE_1RC0LA_0LB0RD_1RE1RC_1LA0LF_---0RD".
Definition tm' := TM_from_str "1RB0LC_0LA0RD_1LA1LE_1RE1RB_1LC0LF_---0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 4.
Time Qed.
End TM441.


Module TM442.
Definition tm := TM_from_str "1LB1LC_0RC1LE_0LE0RD_1RA0RF_0LA1RB_---1RC".
Definition tm' := TM_from_str "1RB0RF_1LC1LE_0RE1LD_0LB1RC_0LD0RA_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEADF") 4 1.
Time Qed.
End TM442.


Module TM443.
Definition tm := TM_from_str "1RB0LE_1LC1RF_0LD0LC_1RD0RA_0RA---_1RA0RA".
Definition tm' := TM_from_str "1RB0RB_1RC0LF_1LD1RA_0LE0LD_1RE0RB_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 36 46.
Time Qed.
End TM443.


Module TM444.
Definition tm := TM_from_str "1LB---_1RC0RF_1RE1LD_0LA0LB_0LC0RE_1LA0RF".
Definition tm' := TM_from_str "1RB0RE_1RC1LD_0LB0RC_0LF0LA_1LF0RE_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABDCE") 2 3.
Time Qed.
End TM444.


Module TM445.
Definition tm := TM_from_str "1RB1RE_1LC0RE_1RA0LD_0LB1LF_0RF---_0LB1RC".
Definition tm' := TM_from_str "1RB0LD_1RC1RF_1LA0RF_0LC1LE_0LC1RA_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADFE") 107 158.
Time Qed.
End TM445.


Module TM446.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RC_1LC0LF_0RD---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM446.


Module TM447.
Definition tm := TM_from_str "1LB0RD_0LC0RD_1RA1LD_0LF1LE_0RA---_1RE0LB".
Definition tm' := TM_from_str "1RB0LD_0RC---_1LD0RF_0LE0RF_1RC1LF_0LA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 13 1.
Time Qed.
End TM447.


Module TM448.
Definition tm := TM_from_str "1RB0LC_1RC0RF_1LA1LD_0LA1LE_0LE0RA_1RE---".
Definition tm' := TM_from_str "1RB---_0LB0RC_1RD0LE_1RE0RA_1LC1LF_0LC1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 1 4.
Time Qed.
End TM448.


Module TM449.
Definition tm := TM_from_str "1RB1RE_1LC0LA_1RA0LD_0LB0LD_1RF---_0LF0RC".
Definition tm' := TM_from_str "1RB0LD_1RC1RE_1LA0LB_0LC0LD_1RF---_0LF0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 11 15.
Time Qed.
End TM449.


Module TM450.
Definition tm := TM_from_str "1RB1LA_1LC0RC_1LD1RC_1LF1LE_1RB0LA_---0LC".
Definition tm' := TM_from_str "1RB0LE_1LC0RC_1LD1RC_1LF1LA_1RB1LE_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM450.


Module TM451.
Definition tm := TM_from_str "1RB1LA_1LC0RF_---0RD_1LA0LE_1LD0LB_1RB1RF".
Definition tm' := TM_from_str "1RB1RA_1LC0RA_---0RD_1LF0LE_1LD0LB_1RB1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM451.


Module TM452.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LF_0RB1RD_0RA---".
Definition tm' := TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 32 22.
Time Qed.
End TM452.


Module TM453.
Definition tm := TM_from_str "1LB0LA_0LC0LC_1RD0LF_1RE---_1LA0RF_0RB0RC".
Definition tm' := TM_from_str "1RB---_1LC0RF_1LD0LC_0LE0LE_1RA0LF_0RD0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 7 10.
Time Qed.
End TM453.


Module TM454.
Definition tm := TM_from_str "1RB1LC_1LA1RD_0LB1LE_1RB0RB_0LF1LA_---1LA".
Definition tm' := TM_from_str "1RB0RB_1LC1RA_1RB1LD_0LB1LE_0LF1LC_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDAEF") 1 1.
Time Qed.
End TM454.


Module TM455.
Definition tm := TM_from_str "1RB1RA_0LC0RA_---1LD_1LE0LF_1RB1LE_1RB0LB".
Definition tm' := TM_from_str "1RB1LA_0LC0RE_---1LD_1LA0LF_1RB1RE_1RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM455.


Module TM456.
Definition tm := TM_from_str "1LB0LB_0RC0LA_1RD0LB_0RE1RB_1RA1RF_1RD---".
Definition tm' := TM_from_str "1RB---_0RC1RE_1RD1RA_1LE0LE_0RF0LD_1RB0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 5 1.
Time Qed.
End TM456.


Module TM457.
Definition tm := TM_from_str "1RB0LA_1LC1LD_1LA1LC_1RE0RB_---0RF_1RB1RD".
Definition tm' := TM_from_str "1RB1RE_1LC1LE_1LD1LC_1RB0LD_1RF0RB_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM457.


Module TM458.
Definition tm := TM_from_str "1LB1RE_1RC0RF_1RF1LD_0LC1RE_0RB0LC_0RA---".
Definition tm' := TM_from_str "1RB0RC_1RC1LE_0RD---_1LA1RF_0LB1RF_0RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABEFC") 2 11.
Time Qed.
End TM458.


Module TM459.
Definition tm := TM_from_str "1RB0RF_1LC0RC_0RE0LD_1LC1LB_0LB1RA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RC_0RE0LD_1LC1LB_0LB1RF_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM459.


Module TM460.
Definition tm := TM_from_str "1RB---_1LC0RF_0RA0LD_1LE1LA_1RB0LF_0LC0RA".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RF0LD_1LA1LF_0LC0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM460.


Module TM461.
Definition tm := TM_from_str "1RB0LB_1RC1LF_0LD0RD_0RE1LC_1RA---_0LA0RA".
Definition tm' := TM_from_str "1RB1LF_0LC0RC_0RD1LB_1RE---_1RA0LA_0LE0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 5 2.
Time Qed.
End TM461.


Module TM462.
Definition tm := TM_from_str "1LB---_0LC0RF_1LD0LA_1LE1RE_0RB0RC_1RD1RE".
Definition tm' := TM_from_str "1RB1RC_1LC1RC_0RF0RD_1LB0LE_1LF---_0LD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDBCA") 1 5.
Time Qed.
End TM462.


Module TM463.
Definition tm := TM_from_str "1LB1RA_1LC0LC_0LD1LD_1RE0RB_0RF---_1LC0RA".
Definition tm' := TM_from_str "1RB0RE_0RC---_1LD0RF_0LA1LA_1LD0LD_1LE1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEDABC") 1 5.
Time Qed.
End TM463.


Module TM464.
Definition tm := TM_from_str "1RB---_0RC0RF_1LD1RA_0LD1LE_1RF0LE_1RB1RE".
Definition tm' := TM_from_str "1RB1RE_0RC0RA_1LD1RF_0LD1LE_1RA0LE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM464.


Module TM465.
Definition tm := TM_from_str "1RB0LB_1LA0RC_1LD1RE_1LB1LF_1RB0LD_1LE---".
Definition tm' := TM_from_str "1RB0LE_1LC0RD_1RB0LB_1LE1RA_1LB1LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM465.


Module TM466.
Definition tm := TM_from_str "1LB1RA_0LC0LE_0RD---_1LE0RA_0LF1LF_1RC0RB".
Definition tm' := TM_from_str "1RB0RE_0RC---_1LD0RF_0LA1LA_0LB0LD_1LE1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEBCDA") 1 5.
Time Qed.
End TM466.


Module TM467.
Definition tm := TM_from_str "1RB---_1LC1LB_0RD0LC_1RE---_0RA1LF_1RB1RF".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RE---_0RF1LA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM467.


Module TM468.
Definition tm := TM_from_str "1LB1LE_0LC0RC_1RD1LF_0RA0LB_1RD---_0LD1LA".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1LA_0LE0RE_1RB1LF_0LB1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBAF") 628 454.
Time Qed.
End TM468.


Module TM469.
Definition tm := TM_from_str "1RB0LD_0RC0LA_1LD0RD_0LE0LF_1RB1LC_0RA---".
Definition tm' := TM_from_str "1RB1LC_0RC0LF_1LD0RD_0LA0LE_0RF---_1RB0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM469.


Module TM470.
Definition tm := TM_from_str "1RB0RD_1LC0RA_1RE0LD_0LC1LB_1RB0RF_---0RE".
Definition tm' := TM_from_str "1RB0RE_1LC0RF_1RA0LD_0LC1LB_---0RA_1RB0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM470.


Module TM471.
Definition tm := TM_from_str "1RB0LC_1LA0RA_1RD0LF_1RE---_1RF1RB_1LA0RD".
Definition tm' := TM_from_str "1RB---_1RC1RF_1LD0RA_1RF0LE_1RA0LC_1LD0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFEABC") 910 1198.
Time Qed.
End TM471.


Module TM472.
Definition tm := TM_from_str "1RB0RA_1LC0RE_1LD0LB_1RC0LF_1RA0RD_1LE---".
Definition tm' := TM_from_str "1RB0LC_1LA0LF_1LD---_1RE0RA_1RF0RE_1LB0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBADC") 8 4.
Time Qed.
End TM472.


Module TM473.
Definition tm := TM_from_str "1RB0RD_1LC0LD_1RB0RA_1LE0RF_0LB0RB_1RA---".
Definition tm' := TM_from_str "1RB0RC_1LA0LD_1RB0RD_1LE0RF_0LB0RB_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBADEF") 1 1.
Time Qed.
End TM473.


Module TM474.
Definition tm := TM_from_str "1LB0RD_1LC1LE_1RD0RA_0LC1RA_0LF---_1LA1RB".
Definition tm' := TM_from_str "1RB0RC_0LA1RC_1LD0RB_1LA1LE_0LF---_1LC1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 1 4.
Time Qed.
End TM474.


Module TM475.
Definition tm := TM_from_str "1RB0RE_0LC0RB_1RA1LD_1LC0LD_---1RF_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_0LC0RB_1RE1LD_1LC0LD_1RB0RF_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM475.


Module TM476.
Definition tm := TM_from_str "1RB0LD_1LC1RD_1LA0LC_1LB0LE_1RB0RF_1RE---".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1LD0LC_1RB0LE_1LB0LA_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 1.
Time Qed.
End TM476.


Module TM477.
Definition tm := TM_from_str "1RB0RD_1LC0RF_1RA1LB_1RE1LD_0LF0RA_---0LB".
Definition tm' := TM_from_str "1RB1LA_0LC0RF_---0LD_1LE0RC_1RF1LD_1RD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 1 9.
Time Qed.
End TM477.


Module TM478.
Definition tm := TM_from_str "1RB0RA_1LC0RA_0RD0LB_1RF1LE_0LC---_1LB1RD".
Definition tm' := TM_from_str "1RB1LF_1LC1RA_1LE0RD_1RC0RD_0RA0LC_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEAFB") 1 5.
Time Qed.
End TM478.


Module TM479.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB1LF_1LC1RB_1RA---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1RC_0LC1LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM479.


Module TM480.
Definition tm := TM_from_str "1RB1LE_0RC0LD_1LD1RB_0LA0RF_0LB1LD_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1RB_0LE0RA_1RB1LF_0LB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM480.


Module TM481.
Definition tm := TM_from_str "1RB1RE_0RC1RB_1LD0LA_1RA0LE_1LF0RA_---1LC".
Definition tm' := TM_from_str "1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 2380 2835.
Time Qed.
End TM481.


Module TM482.
Definition tm := TM_from_str "1LB0LA_0RC0LC_1LE1RD_1RC1RF_---1LF_1LA0RD".
Definition tm' := TM_from_str "1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBACD") 123 158.
Time Qed.
End TM482.


Module TM483.
Definition tm := TM_from_str "1RB0RF_0RC0RE_1LD1RD_1LE1RA_1RB0LE_---0RE".
Definition tm' := TM_from_str "1RB0LA_0RC0RA_1LD1RD_1LA1RE_1RB0RF_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM483.


Module TM484.
Definition tm := TM_from_str "1LB0LE_1LC1LB_1RD1RC_0LA0RD_0LF1LA_0RB---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_0LE1LC_0RF---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 766 763.
Time Qed.
End TM484.


Module TM485.
Definition tm := TM_from_str "1LB1RF_1LC0LB_1RD1LC_1RA1RE_1LC0RD_1RD---".
Definition tm' := TM_from_str "1RB1LA_1RC1RE_1LD1RF_1LA0LD_1LA0RB_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 10 10.
Time Qed.
End TM485.


Module TM486.
Definition tm := TM_from_str "1LB0LE_0RC0LB_1RE1RD_1LE1RF_1LA0RB_1LE---".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA0LD_1LB1RF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEBF") 8 1.
Time Qed.
End TM486.


Module TM487.
Definition tm := TM_from_str "1RB0LD_0LC1RE_1RD0RB_1LA1RD_1RF0RC_---1LB".
Definition tm' := TM_from_str "1RB0RD_1LC1RB_1RD0LB_0LA1RE_1RF0RA_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 5 1.
Time Qed.
End TM487.


Module TM488.
Definition tm := TM_from_str "1LB0LF_1LC---_1RD0RC_0LE1LD_1RF1LA_1RC0LA".
Definition tm' := TM_from_str "1RB0LE_1RC0RB_0LD1LC_1RA1LE_1LF0LA_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 4 9.
Time Qed.
End TM488.


Module TM489.
Definition tm := TM_from_str "1RB---_1LC0RA_0RE0LD_0LB1LE_0LB1RF_1RC0RF".
Definition tm' := TM_from_str "1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDBECA") 1 3.
Time Qed.
End TM489.


Module TM490.
Definition tm := TM_from_str "1RB---_1LC1RE_1LD0LC_1RB1LF_0RD0RA_0LE0LB".
Definition tm' := TM_from_str "1RB1LE_1LC1RD_1LA0LC_0RA0RF_0LD0LB_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM490.


Module TM491.
Definition tm := TM_from_str "1LB---_1RC1LB_1RD1RC_1RE1RA_1LF0RB_0RE0LF".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_0RB0LC_1RE1LD_1RA1RE_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 1 8.
Time Qed.
End TM491.


Module TM492.
Definition tm := TM_from_str "1LB1RE_0LC0RF_1LD1LB_1RA0LF_0RA1LB_---0RA".
Definition tm' := TM_from_str "1RB0LD_1LC1RF_0LE0RD_---0RB_1LA1LC_0RB1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEAFD") 1 5.
Time Qed.
End TM492.


Module TM493.
Definition tm := TM_from_str "1LB0RD_0RC1LE_1RA1LC_0LA1RB_0LB0LF_0LC---".
Definition tm' := TM_from_str "1RB1LA_1LC0RE_0RA1LD_0LC0LF_0LB1RC_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM493.


Module TM494.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_1LF---_1RA1RF".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 6 5.
Time Qed.
End TM494.


Module TM495.
Definition tm := TM_from_str "1RB0LC_1RC0RF_0LD1LA_1LF1LE_1RA0LF_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RA_0LD1LF_1LA1LE_1RF0LA_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM495.


Module TM496.
Definition tm := TM_from_str "1RB1RF_0RC0RA_1RD0LE_0LC1RA_1LC1RE_---0LB".
Definition tm' := TM_from_str "1RB0LC_0LA1RD_1LA1RC_1RE1RF_0RA0RD_---0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 37 31.
Time Qed.
End TM496.


Module TM497.
Definition tm := TM_from_str "1RB---_1LC0RD_1RE0LD_0RE0LD_0LB0RF_1RB1RA".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM497.


Module TM498.
Definition tm := TM_from_str "1LB0RB_0RC0LD_1RA1LC_1LE---_0LF0LF_0LA0RD".
Definition tm' := TM_from_str "1RB1LA_1LC0RC_0RA0LD_1LE---_0LF0LF_0LB0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 106 103.
Time Qed.
End TM498.


Module TM499.
Definition tm := TM_from_str "1LB0LA_1LC0RD_0RB1LA_---0RE_1RB1RF_1RA1RF".
Definition tm' := TM_from_str "1RB1RF_1LC0RE_0RB1LD_1LB0LD_---0RA_1RD1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 6 1.
Time Qed.
End TM499.


Module TM500.
Definition tm := TM_from_str "1LB0LE_1RC0RE_1LA1RD_1RB0RC_1RF0LE_0LD---".
Definition tm' := TM_from_str "1RB0RD_1LC1RF_1LA0LD_1RE0LD_0LF---_1RA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABFDE") 27 30.
Time Qed.
End TM500.


Module TM501.
Definition tm := TM_from_str "1LB0LF_1LC0LE_1RD0LA_1RB1RE_---0RD_0RD1LC".
Definition tm' := TM_from_str "1RB0LD_1RC1RF_1LA0LF_1LC0LE_0RB1LA_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCABFE") 14 6.
Time Qed.
End TM501.


Module TM502.
Definition tm := TM_from_str "1RB1RC_0LC0LE_0RA0LD_1RE1LF_1RA1LC_---1RB".
Definition tm' := TM_from_str "1RB1LF_1RC1LE_1RD1RE_0LE0LB_0RC0LA_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM502.


Module TM503.
Definition tm := TM_from_str "1RB---_1LC0LD_1LE0RD_0LA1LB_1RF1RE_0LB0RF".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_0LE1LC_1RC---_1LA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECFDAB") 1 5.
Time Qed.
End TM503.


Module TM504.
Definition tm := TM_from_str "1RB0LD_1RC1RE_1LA1RC_1RB1LD_1RF0RC_---0LD".
Definition tm' := TM_from_str "1RB1LA_1RC1RE_1LD1RC_1RB0LA_1RF0RC_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM504.


Module TM505.
Definition tm := TM_from_str "1RB1LE_1RC1LA_1RD0RC_0LD0LA_0RB1LF_0LE---".
Definition tm' := TM_from_str "1RB0RA_0LB0LC_1RD1LE_1RA1LC_0RD1LF_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 1 4.
Time Qed.
End TM505.


Module TM506.
Definition tm := TM_from_str "1LB0RA_1RC1LD_0LB0RC_0LE1LE_0LF1RA_1RB---".
Definition tm' := TM_from_str "1RB---_1RC1LD_0LB0RC_0LE1LE_0LA1RF_1LB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 4 1.
Time Qed.
End TM506.


Module TM507.
Definition tm := TM_from_str "1LB0RF_0RC0LE_1RD1LC_1RA0LD_1RD0LD_0RB---".
Definition tm' := TM_from_str "1RB0LA_1LC0RE_0RF0LD_1RA0LA_0RC---_1RA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFADE") 7 1.
Time Qed.
End TM507.


Module TM508.
Definition tm := TM_from_str "1LB0RE_0LC0RC_1LD0LA_1RC0RF_1RF---_1RC0RA".
Definition tm' := TM_from_str "1RB0RC_1LA0LD_1RB0RD_1LE0RF_0LB0RB_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBAFC") 1 5.
Time Qed.
End TM508.


Module TM509.
Definition tm := TM_from_str "1LB1LD_0RC0RE_0LD1RB_1LA0LD_1RB0RF_---1RC".
Definition tm' := TM_from_str "1RB0RF_0RC0RA_0LD1RB_1LE0LD_1LB1LD_---1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 3 1.
Time Qed.
End TM509.


Module TM510.
Definition tm := TM_from_str "1LB1RE_1RC1LD_1RA0RB_0LB0LC_1RF1RD_---1RC".
Definition tm' := TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_1RF1RD_---1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 61 51.
Time Qed.
End TM510.


Module TM511.
Definition tm := TM_from_str "1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_1RD---".
Definition tm' := TM_from_str "1RB---_0LC0RD_1RD1LB_0RE0LA_1LB1RF_0RB1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBFA") 20 34.
Time Qed.
End TM511.


Module TM512.
Definition tm := TM_from_str "1LB0LD_1RC0RB_1LD1RC_1LE1LA_1LF---_1RB1LF".
Definition tm' := TM_from_str "1RB1LA_1RC0RB_1LD1RC_1LF1LE_1LB0LD_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 3 2.
Time Qed.
End TM512.


Module TM513.
Definition tm := TM_from_str "1RB1LE_0RC0RB_1LD0LF_1LE---_1LF0LA_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA0LF_1RB1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM513.


Module TM514.
Definition tm := TM_from_str "1RB0RE_1RC---_1RD1RE_1RE0RD_0LF1RA_0LA1LF".
Definition tm' := TM_from_str "1RB0RA_0LC1RD_0LD1LC_1RE0RB_1RF---_1RA1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 1 32.
Time Qed.
End TM514.


Module TM515.
Definition tm := TM_from_str "1LB0LE_1RC1LA_1RD0RC_1RA0RA_1LA1LF_0LE---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1RD0RD_1LA0LE_1LD1LF_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 10 8.
Time Qed.
End TM515.


Module TM516.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1RE_1LD0LC_1RB0RF_1RD0RB_1RA1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM516.


Module TM517.
Definition tm := TM_from_str "1LB0LF_0LC0LA_0RD1LB_1RE0RB_1RB1RD_---1LC".
Definition tm' := TM_from_str "1RB0RC_1RC1RA_0LD0LE_0RA1LC_1LC0LF_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDABF") 26 1.
Time Qed.
End TM517.


Module TM518.
Definition tm := TM_from_str "1LB1RE_1RC0LF_1RF1LD_---0RA_1RA1LB_0LD0LB".
Definition tm' := TM_from_str "1RB1LC_0LC0LE_---0RD_1LE1RF_1RA0LB_1RD1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEACFB") 1 4.
Time Qed.
End TM518.


Module TM519.
Definition tm := TM_from_str "1RB1RA_0LC0RB_1RB1LD_0LE1LE_1LA1LF_---1LE".
Definition tm' := TM_from_str "1RB1LC_0LA0RB_0LD1LD_1LE1LF_1RB1RE_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM519.


Module TM520.
Definition tm := TM_from_str "1RB1LF_0LC1RD_---1LA_0RE1RE_1RF0LB_1RB0LB".
Definition tm' := TM_from_str "1RB0LB_0LC1RE_---1LD_1RB1LA_0RF1RF_1RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM520.


Module TM521.
Definition tm := TM_from_str "1LB1LF_1LC0RC_0RD0LA_1RB1RE_0RC1RE_0RC---".
Definition tm' := TM_from_str "1RB1RE_1LC0RC_0RA0LD_1LB1LF_0RC1RE_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 17.
Time Qed.
End TM521.


Module TM522.
Definition tm := TM_from_str "1RB0LC_0RC---_0LD0LF_1RE1LE_1RC1RA_0RA1LD".
Definition tm' := TM_from_str "1RB1LB_1RC1RD_0LA0LE_1RF0LC_0RD1LA_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFCABE") 1 9.
Time Qed.
End TM522.


Module TM523.
Definition tm := TM_from_str "1LB---_1RC0RA_1RD0LD_0LE0RB_1RF1LE_0LF1LC".
Definition tm' := TM_from_str "1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC0RF_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FECDAB") 1 17.
Time Qed.
End TM523.


Module TM524.
Definition tm := TM_from_str "1RB0LA_1RC1RE_1LD0RE_0LF1RE_1RB0RC_---1LA".
Definition tm' := TM_from_str "1RB0RC_1RC1RA_1LD0RA_0LE1RA_---1LF_1RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM524.


Module TM525.
Definition tm := TM_from_str "1LB0RD_0LC0LE_1RD0LB_1RA1LB_0LF1RD_---0RB".
Definition tm' := TM_from_str "1RB0LD_1RC1LD_1LD0RB_0LA0LE_0LF1RB_---0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 4 6.
Time Qed.
End TM525.


Module TM526.
Definition tm := TM_from_str "1RB1RA_1LC0RA_1LD1LC_1RE0LB_1LC0RF_---0RD".
Definition tm' := TM_from_str "1RB0LE_1LC0RD_1LA1LC_---0RA_1LC0RF_1RE1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FECABD") 2 2.
Time Qed.
End TM526.


Module TM527.
Definition tm := TM_from_str "1LB1RB_0RC0RE_0LE0RD_1RA1RB_1LA0LF_1LC---".
Definition tm' := TM_from_str "1RB1RC_1LC1RC_0RF0RD_1LB0LE_1LF---_0LD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFADE") 4 1.
Time Qed.
End TM527.


Module TM528.
Definition tm := TM_from_str "1RB0RA_0LC1RA_1LD1LC_1RB1LE_0LF0LE_1LB---".
Definition tm' := TM_from_str "1RB1LE_0LC1RD_1LA1LC_1RB0RD_0LF0LE_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM528.


Module TM529.
Definition tm := TM_from_str "1RB0RE_0LC0RD_1RB1LC_1RA1LB_0RB1RF_1LC---".
Definition tm' := TM_from_str "1RB1LA_0LA0RC_1RD1LB_1RB0RE_0RB1RF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBACEF") 1 1.
Time Qed.
End TM529.


Module TM530.
Definition tm := TM_from_str "1RB1LE_1LC0RA_1RF1LD_0LE---_0LF1LF_0LB0RA".
Definition tm' := TM_from_str "1RB1LE_0LC0RD_1LA0RD_1RC1LF_0LF---_0LB1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCAEFB") 1 4.
Time Qed.
End TM530.


Module TM531.
Definition tm := TM_from_str "1RB0LD_1RC1RA_1RD0RE_1LE1LA_1RF1LE_---0RB".
Definition tm' := TM_from_str "1RB1RF_1RC0RD_1LD1LF_1RE1LD_---0RA_1RA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 22882 23056.
Time Qed.
End TM531.


Module TM532.
Definition tm := TM_from_str "1LB1RF_0RC0LA_0RE1LD_1LC---_1RA0RA_0RA0RB".
Definition tm' := TM_from_str "1RB0RB_1LC1RF_0RD0LB_0RA1LE_1LD---_0RB0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 19 1.
Time Qed.
End TM532.


Module TM533.
Definition tm := TM_from_str "1LB1LC_0RC0LA_1RA0LD_1RE0RF_1RF---_1RB0RE".
Definition tm' := TM_from_str "1RB---_1RC0RA_0RD0LE_1RE0LF_1LC1LD_1RA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDFAB") 13 11.
Time Qed.
End TM533.


Module TM534.
Definition tm := TM_from_str "1LB1RC_0RC1LD_1RA0RB_0LE---_1LF1LE_0RA1LF".
Definition tm' := TM_from_str "1RB0RC_1LC1RA_0RA1LD_0LE---_1LF1LE_0RB1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 5 1.
Time Qed.
End TM534.


Module TM535.
Definition tm := TM_from_str "1LB1LF_1RC0RF_1RE0RD_1LE1RF_0LA---_1RB0LC".
Definition tm' := TM_from_str "1RB0RE_1RC0RF_0LD---_1LA1LE_1RA0LB_1LC1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABFCE") 5 7.
Time Qed.
End TM535.


Module TM536.
Definition tm := TM_from_str "1RB0LD_1RC1RA_0LA1RE_1LC0RD_0RF---_0RB0RF".
Definition tm' := TM_from_str "1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RF---_0RA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 5 3.
Time Qed.
End TM536.


Module TM537.
Definition tm := TM_from_str "1RB0RB_1LC1RD_1RE0LD_1LC1LE_0LF0RA_---1RB".
Definition tm' := TM_from_str "1RB0LE_0LC0RF_---1RD_1LA1RE_1LA1LB_1RD0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDAEBC") 1 3.
Time Qed.
End TM537.


Module TM538.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RD1LB_0LA1RE_0RA1RF_1RD---".
Definition tm' := TM_from_str "1RB---_0LC1RF_1LE0RD_0RB1LE_1RD0LE_0RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEDBFA") 1 6.
Time Qed.
End TM538.


Module TM539.
Definition tm := TM_from_str "1LB---_1LC0RE_0RD1LF_1RB0LE_0LC1LD_1RD1LA".
Definition tm' := TM_from_str "1RB1LE_1RC0LF_1LD0RF_0RB1LA_1LC---_0LD1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDBFA") 73 49.
Time Qed.
End TM539.


Module TM540.
Definition tm := TM_from_str "1RB0LF_1RC0LB_1LD---_0RE1LE_1RF1LA_1RA0RD".
Definition tm' := TM_from_str "1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 4 10.
Time Qed.
End TM540.


Module TM541.
Definition tm := TM_from_str "1RB---_1LC0RB_0LE1LD_1RB0LC_0RA1LF_0LD0LA".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LD1LA_0RE1LF_1RB---_0LA0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM541.


Module TM542.
Definition tm := TM_from_str "1RB---_1LC0RF_0RA0LD_1LE1LA_1RB0LF_0LC0RE".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RF0LD_1LA1LF_0LC0RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM542.


Module TM543.
Definition tm := TM_from_str "1RB---_1RC0RA_0LD1LF_0RB1LE_1RF1LE_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1RC0RF_0LD1LA_0RB1LE_1RA1LE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM543.


Module TM544.
Definition tm := TM_from_str "1RB0RC_0LA0RE_1RD---_1LE0LF_1RF0LD_0LF1RA".
Definition tm' := TM_from_str "1RB---_1LC0LD_1RD0LB_0LD1RE_1RF0RA_0LE0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 4 1.
Time Qed.
End TM544.


Module TM545.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA0RF_1LB---".
Definition tm' := TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD0RF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 707 735.
Time Qed.
End TM545.


Module TM546.
Definition tm := TM_from_str "1RB1LC_0RC0LE_1LD0RB_1RE---_1LF0RE_0LA1LF".
Definition tm' := TM_from_str "1RB---_1LC0RB_0LD1LC_1RE1LF_0RF0LB_1LA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 5 21.
Time Qed.
End TM546.


Module TM547.
Definition tm := TM_from_str "1LB1RB_1RC0LE_0RA1RD_0LB1RC_---1LF_0RD1LB".
Definition tm' := TM_from_str "1RB0LE_0RC1RD_1LA1RA_0LA1RB_---1LF_0RD1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 8 1.
Time Qed.
End TM547.


Module TM548.
Definition tm := TM_from_str "1RB---_1LC1LB_0RD0LC_1RE---_0RA1RF_1RB1RE".
Definition tm' := TM_from_str "1RB1RE_1LC1LB_0RD0LC_1RE---_0RF1RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM548.


Module TM549.
Definition tm := TM_from_str "1LB0RC_1LC0LA_0RD1RA_0RA1RE_0LE0RF_1RA---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1LD0LB_0RE1RB_0RB1RF_0LF0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 37 60.
Time Qed.
End TM549.


Module TM550.
Definition tm := TM_from_str "1LB1LC_1RC0RF_1LD0LA_1RE0LC_1RB1RE_0RE---".
Definition tm' := TM_from_str "1RB0RE_1LC0LF_1RD0LB_1RA1RD_0RD---_1LA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 127 120.
Time Qed.
End TM550.


Module TM551.
Definition tm := TM_from_str "1RB0RF_0LC1LF_---1LD_0LE0LF_1RD0LF_1RA0LB".
Definition tm' := TM_from_str "1RB0LC_1RC0RA_0LD1LA_---1LE_0LF0LA_1RE0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 37 30.
Time Qed.
End TM551.


Module TM552.
Definition tm := TM_from_str "1LB0RB_0LC1RD_1RA1LE_0RA0LB_0LD1LF_0LC---".
Definition tm' := TM_from_str "1RB1LE_1LC0RC_0LA1RD_0RB0LC_0LD1LF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 35 47.
Time Qed.
End TM552.


Module TM553.
Definition tm := TM_from_str "1RB---_1RC1LE_1RD1LD_1RE0RD_0LE0LF_0LA1LB".
Definition tm' := TM_from_str "1RB0RA_0LB0LC_0LD1LE_1RE---_1RF1LB_1RA1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 1 5.
Time Qed.
End TM553.


Module TM554.
Definition tm := TM_from_str "1LB1RF_1RC0LD_0LE1RD_1LE0LB_---0RA_1RA1LB".
Definition tm' := TM_from_str "1RB0LE_0LC1RE_---0RD_1LA1RF_1LC0LA_1RD1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 1 4.
Time Qed.
End TM554.


Module TM555.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RE_1RF1RA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0LB_1RE0RD_1RA1RE_1LB1RF_1RC0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFDA") 327 128.
Time Qed.
End TM555.


Module TM556.
Definition tm := TM_from_str "1LB0LE_1LC0RE_1RD1RC_0LA0RD_0LF1LA_1RA---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_0LE1LC_1RC---_1LA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 986 963.
Time Qed.
End TM556.


Module TM557.
Definition tm := TM_from_str "1LB---_1RC0LE_1RD0RC_1LB0RE_1RC1LF_0RF0LA".
Definition tm' := TM_from_str "1RB0RA_1LC0RD_1RA0LD_1RA1LE_0RE0LF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCABDE") 165 87.
Time Qed.
End TM557.


Module TM558.
Definition tm := TM_from_str "1RB1RA_1RC0LE_1LD0RE_0RC0LD_1LF1LE_0RA---".
Definition tm' := TM_from_str "1RB0LD_1LC0RD_0RB0LC_1LE1LD_0RF---_1RA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 9 8.
Time Qed.
End TM558.


Module TM559.
Definition tm := TM_from_str "1RB1LE_0RC0LD_1LD0RD_0LA1LB_0LB0LF_1RC---".
Definition tm' := TM_from_str "1RB---_1LC0RC_0LE1LD_0RB0LC_1RD1LF_0LD0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDBCFA") 1 10.
Time Qed.
End TM559.


Module TM560.
Definition tm := TM_from_str "1RB1LE_1LC0RB_1RD1LA_0RE1RD_0LF0LC_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RB_1RE1LD_1RB1LF_0RF1RE_0LA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM560.


Module TM561.
Definition tm := TM_from_str "1LB1RE_0RC0LB_1LE1RD_0RC---_1RF0RA_1RA1LF".
Definition tm' := TM_from_str "1RB1LA_1LC1RE_0RD0LC_1LE1RF_1RA0RB_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDFEA") 8 7.
Time Qed.
End TM561.


Module TM562.
Definition tm := TM_from_str "1LB1LC_1LC---_1LD0LA_1LE0RA_1RF1RE_0LC0RF".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_1LC---_1LA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECFAB") 1 4.
Time Qed.
End TM562.


Module TM563.
Definition tm := TM_from_str "1LB1LE_1LC0RC_0RD0LA_1RB1RE_0RC1LF_---1RD".
Definition tm' := TM_from_str "1RB1RE_1LC0RC_0RA0LD_1LB1LE_0RC1LF_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 19.
Time Qed.
End TM563.


Module TM564.
Definition tm := TM_from_str "1LB1RF_0RC0LE_1RA0LD_0LB0RC_1LC---_0LD1LC".
Definition tm' := TM_from_str "1RB0LF_1LC1RE_0RA0LD_1LA---_0LF1LA_0LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAFDE") 6 1.
Time Qed.
End TM564.


Module TM565.
Definition tm := TM_from_str "1RB0LA_1LC0RD_0RB1LA_---1RE_1RF1LF_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1LC0RE_0RB1LD_1RB0LD_---1RF_1RA1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM565.


Module TM566.
Definition tm := TM_from_str "1LB0LA_1LC0RC_0RD0LA_1RB1RE_0LE1RF_0RC---".
Definition tm' := TM_from_str "1RB1RE_1LC0RC_0RA0LD_1LB0LD_0LE1RF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 17.
Time Qed.
End TM566.


Module TM567.
Definition tm := TM_from_str "1RB0RD_0LC0RF_1RD0LB_1RE0LA_1RA1RC_1LB---".
Definition tm' := TM_from_str "1RB0LE_1RC0LD_1RD1RA_1RE0RB_0LA0RF_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 5 1.
Time Qed.
End TM567.


Module TM568.
Definition tm := TM_from_str "1LB0RB_1RC0LA_1LE1LD_---1RA_1RF1LC_1LD1RF".
Definition tm' := TM_from_str "1RB0LF_1LC1LE_1RD1LB_1LE1RD_---1RF_1LA0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABECD") 48 37.
Time Qed.
End TM568.


Module TM569.
Definition tm := TM_from_str "1RB---_1RC0RC_0LD1RC_1RA0LE_0RA1LF_1RB1LD".
Definition tm' := TM_from_str "1RB1LD_1RC0RC_0LD1RC_1RF0LE_0RF1LA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM569.


Module TM570.
Definition tm := TM_from_str "1RB1RC_1LC1RB_1LD0RA_0LE0LB_1LF1LB_1RC---".
Definition tm' := TM_from_str "1RB---_1LC0RF_0LE0LD_1LB1RD_1LA1LD_1RD1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDBCEA") 4 1.
Time Qed.
End TM570.


Module TM571.
Definition tm := TM_from_str "1LB1LA_0RC---_1RD1RC_1RE0LA_1LF0RC_0RB0LF".
Definition tm' := TM_from_str "1RB0LF_1LC0RE_0RD0LC_0RE---_1RA1RE_1LD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 1 4.
Time Qed.
End TM571.


Module TM572.
Definition tm := TM_from_str "1RB0LC_1RC0RA_0LD1LA_0LA1LE_1RA1LF_0RD---".
Definition tm' := TM_from_str "1RB0RE_0LC1LE_0LE1LD_1RE1LF_1RA0LB_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 49 81.
Time Qed.
End TM572.


Module TM573.
Definition tm := TM_from_str "1RB0LF_0LC1RE_1LC1LD_1RB0LA_0RC0RE_---0LD".
Definition tm' := TM_from_str "1RB0LE_0LC1RD_1LC1LA_0RC0RD_1RB0LF_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM573.


Module TM574.
Definition tm := TM_from_str "1RB0RF_0RC0RE_1LB0LD_1LE---_1RF0LC_0RA0RF".
Definition tm' := TM_from_str "1RB0LE_0RC0RB_1RD0RB_0RE0RA_1LD0LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 54 47.
Time Qed.
End TM574.


Module TM575.
Definition tm := TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RD_0LB1RF_---0RA".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RC_0LA1RE_---0RF_1RA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 98 26.
Time Qed.
End TM575.


Module TM576.
Definition tm := TM_from_str "1LB0LB_0LC0LA_1RD1RC_0RE1LD_1RF0RC_0LB---".
Definition tm' := TM_from_str "1RB0RE_0LC---_0LE0LD_1LC0LC_1RF1RE_0RA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEFAB") 1 4.
Time Qed.
End TM576.


Module TM577.
Definition tm := TM_from_str "1LB0RA_0RC1LE_---0LD_1RA1LF_1RC0RE_1LD1RE".
Definition tm' := TM_from_str "1RB1LF_1LC0RB_0RE1LD_1RE0RD_---0LA_1LA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEADF") 4 1.
Time Qed.
End TM577.


Module TM578.
Definition tm := TM_from_str "1LB---_1RC0LE_0RD1RC_1LA0RB_1LB1LF_0LE1LD".
Definition tm' := TM_from_str "1RB0LE_0RC1RB_1LD0RA_1LA---_1LA1LF_0LE1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 9 22.
Time Qed.
End TM578.


Module TM579.
Definition tm := TM_from_str "1RB0LD_1RC0RF_1LA1LE_1LC1LB_---0LB_1RC1RA".
Definition tm' := TM_from_str "1RB0RE_1LC1LF_1RA0LD_1LB1LA_1RB1RC_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDFE") 58 67.
Time Qed.
End TM579.


Module TM580.
Definition tm := TM_from_str "1LB---_1LC1RD_0RB0LC_0RE1RE_0RA1LF_1RB0LE".
Definition tm' := TM_from_str "1RB0LE_1LC1RD_0RB0LC_0RE1RE_0RF1LA_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 4.
Time Qed.
End TM580.


Module TM581.
Definition tm := TM_from_str "1RB0LC_0LA1RD_1LA1LC_1RE1RF_0RA0RD_---0RE".
Definition tm' := TM_from_str "1RB1RF_0RC0RA_1RD0LE_0LC1RA_1LC1LE_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 29 35.
Time Qed.
End TM581.


Module TM582.
Definition tm := TM_from_str "1RB1RF_1LC0RE_1RF0LD_1RE0LB_1RA---_1LC0RC".
Definition tm' := TM_from_str "1RB---_1RC1RF_1LD0RA_1RF0LE_1RA0LC_1LD0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 910 1198.
Time Qed.
End TM582.


Module TM583.
Definition tm := TM_from_str "1RB0RC_0LC1RC_1RA0LD_0RC1LE_1RB1LF_---0LD".
Definition tm' := TM_from_str "1RB1LF_0LC1RC_1RE0LD_0RC1LA_1RB0RC_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM583.


Module TM584.
Definition tm := TM_from_str "1RB1RD_1LC0RF_1RD0LB_1RA0RE_1RA---_1LF1RB".
Definition tm' := TM_from_str "1RB0LD_1RC0RF_1RD1RB_1LA0RE_1LE1RD_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 156 124.
Time Qed.
End TM584.


Module TM585.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_1RC---_1RA1RF".
Definition tm' := TM_from_str "1RB1RC_1RC---_1RD0RA_1RE1RD_1LF1LE_0RC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCABD") 4 1.
Time Qed.
End TM585.


Module TM586.
Definition tm := TM_from_str "1RB0RE_1LC1LB_---0LD_1RE0LD_0RF1RF_1RB1RA".
Definition tm' := TM_from_str "1RB1RF_1LC1LB_---0LD_1RE0LD_0RA1RA_1RB0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM586.


Module TM587.
Definition tm := TM_from_str "1LB1LE_1RC0LD_1RD0RB_0LA0RD_1RB1LF_0RA---".
Definition tm' := TM_from_str "1RB0RE_0LC0RB_1LE1LD_1RE1LF_1RA0LB_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEABDF") 1 8.
Time Qed.
End TM587.


Module TM588.
Definition tm := TM_from_str "1LB1RC_1RA1LB_1LD1RE_0RB0LD_1RF0RA_1RA---".
Definition tm' := TM_from_str "1RB0RC_1RC---_1LD1RE_1RC1LD_1LF1RA_0RD0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 9 4.
Time Qed.
End TM588.


Module TM589.
Definition tm := TM_from_str "1RB1RC_1LC0RF_1RA0LD_1LE1LB_1RA---_0RE0LB".
Definition tm' := TM_from_str "1RB---_1RC1RD_1LD0RF_1RB0LE_1LA1LC_0RA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 10 33.
Time Qed.
End TM589.


Module TM590.
Definition tm := TM_from_str "1LB0LD_0RC1LF_0LE0RD_1RB1LC_0LB---_0LA0LD".
Definition tm' := TM_from_str "1RB1LC_0RC1LE_0LD0RA_0LB---_0LF0LA_1LB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 4 1.
Time Qed.
End TM590.


Module TM591.
Definition tm := TM_from_str "1RB1RE_1LC0RD_1RB1LA_0RC1RA_0RF0LE_0LA---".
Definition tm' := TM_from_str "1RB1LC_1LA0RD_1RB1RE_0RA1RC_0RF0LE_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBADEF") 1 1.
Time Qed.
End TM591.


Module TM592.
Definition tm := TM_from_str "1RB0LB_0LC0RE_1LA1LD_0LB0LF_1RA1RD_1RC---".
Definition tm' := TM_from_str "1RB---_1LC1LF_1RD0LD_0LB0RE_1RC1RF_0LD0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBFEA") 4 3.
Time Qed.
End TM592.


Module TM593.
Definition tm := TM_from_str "1RB1LF_1LC0RA_1RE0LD_0LC0RE_1RA---_0LA0LE".
Definition tm' := TM_from_str "1RB0LE_1RC---_1RD1LF_1LA0RC_0LA0RB_0LC0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEBF") 7 11.
Time Qed.
End TM593.


Module TM594.
Definition tm := TM_from_str "1LB1LF_0RC0LA_1RA1RD_0RE---_1RA1RF_1RE0RB".
Definition tm' := TM_from_str "1RB0RD_1RC1RA_1LD1LA_0RE0LC_1RC1RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 35 11.
Time Qed.
End TM594.


Module TM595.
Definition tm := TM_from_str "1RB1LD_1RC0LE_1RD0RF_1LE0LB_1RB1LB_1RA---".
Definition tm' := TM_from_str "1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM595.


Module TM596.
Definition tm := TM_from_str "1LB0RE_0RC0LA_1RE0LD_0LB---_0RF1RD_1RA1LD".
Definition tm' := TM_from_str "1RB0LF_0RC1RF_1RD1LF_1LE0RB_0RA0LD_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 6 1.
Time Qed.
End TM596.


Module TM597.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LF_0RB1RD_1RB---".
Definition tm' := TM_from_str "1RB---_0LC0RD_1RD1LB_0RE0LA_1LB1RF_0RB1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 3.
Time Qed.
End TM597.


Module TM598.
Definition tm := TM_from_str "1RB1RA_1RC0RA_1LD0LA_1LE0LD_1LF0LB_1LB---".
Definition tm' := TM_from_str "1RB0RF_1LC0LF_1LD0LC_1LE0LA_1LA---_1RA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 557 523.
Time Qed.
End TM598.


Module TM599.
Definition tm := TM_from_str "1LB1LD_1RC---_0LD0RC_1LE0LA_1LF0RA_1RC1RF".
Definition tm' := TM_from_str "1RB---_0LC0RB_1LE0LD_1LA1LC_1LF0RD_1RB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 4.
Time Qed.
End TM599.


Module TM600.
Definition tm := TM_from_str "1RB0LF_1LC0RE_0LB1LD_1RB0LA_0RB1LA_---0LD".
Definition tm' := TM_from_str "1RB0LE_1LC0RD_0LB1LA_0RB1LE_1RB0LF_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM600.


Module TM601.
Definition tm := TM_from_str "1RB1RF_1RC0LD_1LB0RA_0RC0LE_1LD0LC_1RD---".
Definition tm' := TM_from_str "1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDCBFA") 10 4.
Time Qed.
End TM601.


Module TM602.
Definition tm := TM_from_str "1LB0RC_0RA0LA_1LD1RE_1LA1LF_1RA0LD_1LE---".
Definition tm' := TM_from_str "1RB0LE_1LC0RD_0RB0LB_1LE1RA_1LB1LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 25 42.
Time Qed.
End TM602.


Module TM603.
Definition tm := TM_from_str "1LB---_0LC1LD_0LD0RA_1RE1LB_1RC1RF_0RE0RF".
Definition tm' := TM_from_str "1RB1LD_1RC1RE_0LA0RF_0LC1LA_0RB0RE_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDCABE") 28 34.
Time Qed.
End TM603.


Module TM604.
Definition tm := TM_from_str "1LB0RB_0RC0LB_0LE0RD_1RA1RE_1LF---_1RC0LB".
Definition tm' := TM_from_str "1RB1RE_1LC0RC_0RD0LC_0LE0RA_1LF---_1RD0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 4 1.
Time Qed.
End TM604.


Module TM605.
Definition tm := TM_from_str "1RB1LE_0LC0RF_1RD0LB_1RE0RB_1RA0RC_1LB---".
Definition tm' := TM_from_str "1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 5 1.
Time Qed.
End TM605.


Module TM606.
Definition tm := TM_from_str "1LB---_1RC0LE_1LF0RD_1LE1RB_1LC1LA_0RC0LC".
Definition tm' := TM_from_str "1RB0LE_1LC0RD_0RB0LB_1LE1RA_1LB1LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABDEC") 23 42.
Time Qed.
End TM606.


Module TM607.
Definition tm := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_0LB---".
Definition tm' := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 16 38.
Time Qed.
End TM607.


Module TM608.
Definition tm := TM_from_str "1RB0LC_1RC0RF_1LD0RA_1RE0LD_1LC0RA_0RC---".
Definition tm' := TM_from_str "1RB0RF_1LC0RE_1RD0LC_1LB0RE_1RA0LB_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 86 190.
Time Qed.
End TM608.


Module TM609.
Definition tm := TM_from_str "1RB0RA_1LC1RB_1LE1LD_1LA0LC_1LF---_1RA1LF".
Definition tm' := TM_from_str "1RB1LA_1RC0RB_1LD1RC_1LF1LE_1LB0LD_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 61 25.
Time Qed.
End TM609.


Module TM610.
Definition tm := TM_from_str "1LB0RC_0LC1LE_1RB1RD_1RA0RC_1LF1LA_---0LA".
Definition tm' := TM_from_str "1RB1RC_0LA1LE_1RD0RA_1LB0RA_1LF1LD_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBACEF") 32 42.
Time Qed.
End TM610.


Module TM611.
Definition tm := TM_from_str "1RB1RF_0LC---_1RD1RC_1LE1LD_0RF0LE_1RC0RA".
Definition tm' := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 3 1.
Time Qed.
End TM611.


Module TM612.
Definition tm := TM_from_str "1RB---_1RC0RB_0LD1RE_0RA0LC_1LE1LF_0LA1LC".
Definition tm' := TM_from_str "1RB0RA_0LC1RE_0RD0LB_1RA---_1LE1LF_0LD1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 6.
Time Qed.
End TM612.


Module TM613.
Definition tm := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_0RA---".
Definition tm' := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 476 774.
Time Qed.
End TM613.


Module TM614.
Definition tm := TM_from_str "1LB0RA_0RC0RA_1LE0LD_1RB1LC_1LF---_1LD1RD".
Definition tm' := TM_from_str "1RB1LC_0RC0RF_1LD0LA_1LE---_1LA1RA_1LB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 4 1.
Time Qed.
End TM614.


Module TM615.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_0LF---_1RA1RF".
Definition tm' := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEFB") 6 1.
Time Qed.
End TM615.


Module TM616.
Definition tm := TM_from_str "1RB0LA_1RC---_1LD0RD_0LA0RE_1RB0RF_0LC0RC".
Definition tm' := TM_from_str "1RB0RE_1RC---_1LD0RD_0LF0RA_0LC0RC_1RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM616.


Module TM617.
Definition tm := TM_from_str "1LB0RC_0LC1LF_1LD0RE_1RC1LB_1RA1LB_0LD---".
Definition tm' := TM_from_str "1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECBADF") 2235 3242.
Time Qed.
End TM617.


Module TM618.
Definition tm := TM_from_str "1LB1LD_1RC1LA_0LD1RC_---1RE_1LF0RF_1RA0LE".
Definition tm' := TM_from_str "1RB1LF_0LC1RB_---1RD_1LE0RE_1RF0LD_1LA1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 61 69.
Time Qed.
End TM618.


Module TM619.
Definition tm := TM_from_str "1RB0LC_1LA1RD_1LB0LB_0LF1LE_1RB0LD_---0RE".
Definition tm' := TM_from_str "1RB0LE_1LC1RE_1RB0LD_1LB0LB_0LF1LA_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM619.


Module TM620.
Definition tm := TM_from_str "1LB0RF_1RC1LB_1LE1RD_1RB0RC_1RA0LE_0LA---".
Definition tm' := TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LA0RF_1RA0RB_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 23 20.
Time Qed.
End TM620.


Module TM621.
Definition tm := TM_from_str "1RB---_1LC0LB_0LD0RC_1RE1LA_1RF1LB_1LE1LC".
Definition tm' := TM_from_str "1RB1LF_1RC1LD_1LB1LE_1LE0LD_0LA0RE_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 6 1.
Time Qed.
End TM621.


Module TM622.
Definition tm := TM_from_str "1LB1LC_0LC1LF_1RD0LA_1RA1RE_1RF---_1RC0RC".
Definition tm' := TM_from_str "1RB0LC_1RC1RF_1LD1LA_0LA1LE_1RA0RA_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 314 284.
Time Qed.
End TM622.


Module TM623.
Definition tm := TM_from_str "1RB1RA_1RC1LF_1LD1RE_0RE0LD_0RF---_1RA1LF".
Definition tm' := TM_from_str "1RB1LE_1LC1RD_0RD0LC_0RE---_1RF1LE_1RA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 7 6.
Time Qed.
End TM623.


Module TM624.
Definition tm := TM_from_str "1LB0LA_1LC1RF_1RD0RA_0LC0RE_0RF1RC_---1RD".
Definition tm' := TM_from_str "1RB0RC_0LA0RE_1LD0LC_1LA1RF_0RF1RA_---1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 1 4.
Time Qed.
End TM624.


Module TM625.
Definition tm := TM_from_str "1LB1RE_1LC1LF_1LD0RA_0RC0LC_1RC0LB_1LE---".
Definition tm' := TM_from_str "1RB0LE_1LC0RD_0RB0LB_1LE1RA_1LB1LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCAF") 22 42.
Time Qed.
End TM625.


Module TM626.
Definition tm := TM_from_str "1RB0LE_0LC0RA_1RE0LD_1RE1LF_1RA0LB_---1LC".
Definition tm' := TM_from_str "1RB1LF_1RC0LD_1RD0LB_0LE0RC_1RB0LA_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM626.


Module TM627.
Definition tm := TM_from_str "1LB0LE_0RC0LC_1LA0RD_1RC1RD_0LF0RC_1LC---".
Definition tm' := TM_from_str "1RB1RA_1LC0RA_1LF0LD_0LE0RB_1LB---_0RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFBADE") 4 1.
Time Qed.
End TM627.


Module TM628.
Definition tm := TM_from_str "1LB---_0RC1LD_1RF1RA_1RE0LB_1RC1RD_0LD0RE".
Definition tm' := TM_from_str "1RB0LE_1RC1RA_1RD1RF_0LA0RB_0RC1LA_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FECABD") 7 4.
Time Qed.
End TM628.


Module TM629.
Definition tm := TM_from_str "1LB0LB_0RC0LA_1RF0RD_1RE---_1RA1RC_0RE1RF".
Definition tm' := TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF0RE_1RA---_0RA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 26 33.
Time Qed.
End TM629.


Module TM630.
Definition tm := TM_from_str "1LB0RA_0LC1RA_0RD1LE_1RA0LB_0LD1LF_1RD---".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LD1RB_0RA1LE_0LA1LF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 4 3.
Time Qed.
End TM630.


Module TM631.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB1RD_0RA1LB".
Definition tm' := TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC1LD_0RD1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 30 22.
Time Qed.
End TM631.


Module TM632.
Definition tm := TM_from_str "1RB---_1RC1LB_1LD1RF_0LF0LE_1RD0LD_1RA0RC".
Definition tm' := TM_from_str "1RB1LA_1LC1RE_0LE0LD_1RC0LC_1RF0RB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 38 53.
Time Qed.
End TM632.


Module TM633.
Definition tm := TM_from_str "1RB1RE_1RC1LC_1LD1LB_1RA0LC_0RD0RF_---0RE".
Definition tm' := TM_from_str "1RB1LB_1LC1LA_1RD0LB_1RA1RE_0RC0RF_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 2 8.
Time Qed.
End TM633.


Module TM634.
Definition tm := TM_from_str "1LB0RF_1LC0LA_1RD0LB_0RE0RC_0RA1LE_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0LF_1RD0LB_0RE0RC_0RF1LE_1LB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 5 1.
Time Qed.
End TM634.


Module TM635.
Definition tm := TM_from_str "1RB---_1LC1LB_0RD0LC_1LC1RE_0RA1RF_1RB1RE".
Definition tm' := TM_from_str "1RB1RE_1LC1LB_0RD0LC_1LC1RE_0RF1RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM635.


Module TM636.
Definition tm := TM_from_str "1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RD1LE".
Definition tm' := TM_from_str "1RB---_1LC0LE_1RD0LB_1RB1RA_0LF0RC_0RA1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM636.


Module TM637.
Definition tm := TM_from_str "1RB0LC_1RC0RD_1LA0LD_0LE0RF_1RA1LC_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RE_1LD0LE_1RB0LC_0LF0RA_1RD1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM637.


Module TM638.
Definition tm := TM_from_str "1RB0RF_0RC1RA_1LD0LE_1LC---_1RB1LE_0RB0LF".
Definition tm' := TM_from_str "1RB1LA_0RC1RE_1LD0LA_1LC---_1RB0RF_0RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM638.


Module TM639.
Definition tm := TM_from_str "1RB1RA_1LC1LF_1RE0LD_0RE0LC_0RA---_1RB1LB".
Definition tm' := TM_from_str "1RB1LB_1LC1LA_1RE0LD_0RE0LC_0RF---_1RB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM639.


Module TM640.
Definition tm := TM_from_str "1RB1RD_0LC0LE_0RD1LB_1RA0RD_1RB0LF_---1LC".
Definition tm' := TM_from_str "1RB0LF_0LC0LA_0RD1LB_1RE0RD_1RB1RD_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM640.


Module TM641.
Definition tm := TM_from_str "1LB0LE_1LC1LB_1RD1RC_0LA0RD_0LF1LA_0RA---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_0LE1LC_0RC---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 1 6.
Time Qed.
End TM641.


Module TM642.
Definition tm := TM_from_str "1LB0LA_0RC0RD_0LD1RB_1LA1RE_1RE1RF_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0RD_0LD1RB_1LE1RF_1LB0LE_1RF1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 3 1.
Time Qed.
End TM642.


Module TM643.
Definition tm := TM_from_str "1RB0RD_0LC1RE_1LD1RC_0LE0LC_0RA0RF_1RA---".
Definition tm' := TM_from_str "1RB---_1RC0RE_0LD1RF_1LE1RD_0LF0LD_0RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 764 798.
Time Qed.
End TM643.


Module TM644.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB1LF_1LC0RE_1RA---".
Definition tm' := TM_from_str "1RB---_1LC0RF_0RE0LD_1LE0RD_1RB0LF_0LC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEFDA") 6 1.
Time Qed.
End TM644.


Module TM645.
Definition tm := TM_from_str "1RB---_1RC1RE_1LD0LD_0RE0LC_1RF0RA_0RB1RF".
Definition tm' := TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF0RE_1RA---_0RA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 23 33.
Time Qed.
End TM645.


Module TM646.
Definition tm := TM_from_str "1RB1RE_1LC0RA_---0LD_1LE0LF_1RA0RC_1RE1RB".
Definition tm' := TM_from_str "1RB0RD_1RC1RA_1LD0RB_---0LE_1LA0LF_1RA1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 20 32.
Time Qed.
End TM646.


Module TM647.
Definition tm := TM_from_str "1LB1RE_1RC0LB_0RE0LD_1LF0LC_1RA1LD_---0RD".
Definition tm' := TM_from_str "1RB1LE_1LC1RA_1RD0LC_0RA0LE_1LF0LD_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 6 1.
Time Qed.
End TM647.


Module TM648.
Definition tm := TM_from_str "1RB1LB_1RC1LB_1LD1RE_1LA0LD_1RF0RC_1RB---".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1RB1LB_1RA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM648.


Module TM649.
Definition tm := TM_from_str "1RB---_1RC1RF_1LD1RA_1LE0LD_1RB1LE_1LE0RB".
Definition tm' := TM_from_str "1RB1LA_1RC1RE_1LD1RF_1LA0LD_1LA0RB_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM649.


Module TM650.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RE_1RF1RB_0LE---".
Definition tm' := TM_from_str "1RB1RC_0LA---_1LD1RF_1LE0LD_1RC0RA_1RE0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDFAB") 1 3.
Time Qed.
End TM650.


Module TM651.
Definition tm := TM_from_str "1RB1LC_1LA0RD_1RB1RE_0RA1RC_0RF0LE_0LA---".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_1RB1LA_0RC1RA_0RF0LE_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBADEF") 1 1.
Time Qed.
End TM651.


Module TM652.
Definition tm := TM_from_str "1LB0RA_0LC1RE_0LD1LC_1LE1LA_1RB0RF_---1RD".
Definition tm' := TM_from_str "1RB0RE_0LC1RA_0LD1LC_1LA1LF_---1RD_1LB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 24 27.
Time Qed.
End TM652.


Module TM653.
Definition tm := TM_from_str "1RB0RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0RB---".
Definition tm' := TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB0RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM653.


Module TM654.
Definition tm := TM_from_str "1LB0RC_0RA0RB_1RD0RE_0RE1RC_1LF---_0LF0LB".
Definition tm' := TM_from_str "1RB0RC_0RC1RA_1LD---_0LD0LE_0RF0RE_1LE0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEABCD") 4 1.
Time Qed.
End TM654.


Module TM655.
Definition tm := TM_from_str "1LB1LA_1RC1RB_0LD0RC_1LA0LE_1LF1LD_0RE---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_0RD---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 6 7.
Time Qed.
End TM655.


Module TM656.
Definition tm := TM_from_str "1LB0LC_0RC0LA_1LE0RD_1RE1RF_1RC0LB_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCEDA") 13 4.
Time Qed.
End TM656.


Module TM657.
Definition tm := TM_from_str "1LB0LF_1RC0LB_0RA0LD_---0RE_1RA1RE_1LD1LF".
Definition tm' := TM_from_str "1RB1RA_1LC0LE_1RD0LC_0RB0LF_1LF1LE_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDFAE") 5 1.
Time Qed.
End TM657.


Module TM658.
Definition tm := TM_from_str "1LB0RA_1RC0LD_1LA0RD_0LE0RA_0RC1LF_0LC---".
Definition tm' := TM_from_str "1RB0LD_1LC0RD_1LA0RC_0LE0RC_0RB1LF_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 5.
Time Qed.
End TM658.


Module TM659.
Definition tm := TM_from_str "1LB1RE_1LC1RD_0RB0LC_0LD0RA_1RA0LF_---1LE".
Definition tm' := TM_from_str "1RB0LF_1LC1RA_1LE1RD_0LD0RB_0RC0LE_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEDAF") 3 2.
Time Qed.
End TM659.


Module TM660.
Definition tm := TM_from_str "1LB1RE_1RC1LA_0LB1RD_1LC0RD_0RF0RE_---0LB".
Definition tm' := TM_from_str "1RB1LC_0LA1RD_1LA1RE_1LB0RD_0RF0RE_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 5 6.
Time Qed.
End TM660.


Module TM661.
Definition tm := TM_from_str "1RB1RD_1LC0RA_---1LA_1LE0LB_1RB1LF_0LE0LD".
Definition tm' := TM_from_str "1RB1LF_1LC0RD_---1LD_1RB1RE_1LA0LB_0LA0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 1.
Time Qed.
End TM661.


Module TM662.
Definition tm := TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA1RB_0RB1RD_0RA---".
Definition tm' := TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RF_0RD1RB_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 34 22.
Time Qed.
End TM662.


Module TM663.
Definition tm := TM_from_str "1LB1RE_0LC0LB_1RC1LD_1RC0RA_1RF---_1RA0LC".
Definition tm' := TM_from_str "1RB0LD_1LC1RF_0LD0LC_1RD1LE_1RD0RB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 17 18.
Time Qed.
End TM663.


Module TM664.
Definition tm := TM_from_str "1RB0LC_0LC0RF_1LA0LD_1LE0RE_0RB0LC_1RD---".
Definition tm' := TM_from_str "1RB---_1LC0RC_0RF0LD_1LE0LB_1RF0LD_0LD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDBCA") 7 1.
Time Qed.
End TM664.


Module TM665.
Definition tm := TM_from_str "1RB0RC_1LC0LC_1RD1LB_1LC0RE_---1RF_1RD0RA".
Definition tm' := TM_from_str "1RB1LC_1LA0RD_1LA0LA_---1RE_1RB0RF_1RC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCABDE") 2 2.
Time Qed.
End TM665.


Module TM666.
Definition tm := TM_from_str "1LB1RC_1RC0LF_0LE1LD_1RA0LE_0LB0RD_1LD---".
Definition tm' := TM_from_str "1RB0LF_1LC1RE_1RE0LD_1LA---_0LF1LA_0LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEAFD") 510 635.
Time Qed.
End TM666.


Module TM667.
Definition tm := TM_from_str "1RB0LE_0RC0RB_0LD1LA_1LD0LA_1RB0LF_---1RC".
Definition tm' := TM_from_str "1RB0LF_0RC0RB_0LD1LE_1LD0LE_1RB0LA_---1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM667.


Module TM668.
Definition tm := TM_from_str "1RB0LF_1RC1RA_1LD0RF_---0LE_1RB1LE_0RD1LF".
Definition tm' := TM_from_str "1RB1LA_1RC1RE_1LD0RF_---0LA_1RB0LF_0RD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM668.


Module TM669.
Definition tm := TM_from_str "1LB0RF_1RC1LD_0RD0RC_1LE0LB_1LF---_1LA1RB".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 8 4.
Time Qed.
End TM669.


Module TM670.
Definition tm := TM_from_str "1LB1RD_0LC0RF_1RD1LE_0RA0LB_0LD1LB_1RD---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1RB_0LE0RA_1RB1LF_0LB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBFA") 20 30.
Time Qed.
End TM670.


Module TM671.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC1LF_0LD---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM671.


Module TM672.
Definition tm := TM_from_str "1RB1LC_1LA0RE_1RA0LD_0RA0LF_0RE1RD_1LD---".
Definition tm' := TM_from_str "1RB0LD_1RC1LA_1LB0RE_0RB0LF_0RE1RD_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 5 4.
Time Qed.
End TM672.


Module TM673.
Definition tm := TM_from_str "1RB0LA_1RC---_0LD1RD_1RB0RE_0RF1RC_1LF0LA".
Definition tm' := TM_from_str "1RB0RD_1RC---_0LA1RA_0RE1RC_1LE0LF_1RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM673.


Module TM674.
Definition tm := TM_from_str "1LB0RB_0LC0RF_1RD1LE_0RA0LF_0LD1LB_0LC---".
Definition tm' := TM_from_str "1RB1LE_0RC0LF_1LD0RD_0LA0RF_0LB1LD_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 22 32.
Time Qed.
End TM674.


Module TM675.
Definition tm := TM_from_str "1LB1LC_1RA1LA_0LA0RD_0LA0RE_0LB0RF_---1RD".
Definition tm' := TM_from_str "1RB1LB_1LA1LC_0LB0RD_0LB0RE_0LA0RF_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BACDEF") 7 1.
Time Qed.
End TM675.


Module TM676.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1RF_0LC0RE_---1LD_0RD0RA".
Definition tm' := TM_from_str "1RB0RA_1LC1RE_1RA1LD_0LB0RF_0RD0RC_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDFE") 6 3.
Time Qed.
End TM676.


Module TM677.
Definition tm := TM_from_str "1LB0RD_1LC1LF_1RA0LF_0RF1RE_0RC1LA_0LE---".
Definition tm' := TM_from_str "1RB0LD_1LC0RF_1LA1LD_0LE---_0RA1LB_0RD1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAFED") 2 5.
Time Qed.
End TM677.


Module TM678.
Definition tm := TM_from_str "1RB---_1LC1RD_0RA1LD_1RE0LF_1RA0RB_0RC0LD".
Definition tm' := TM_from_str "1RB0LF_1RC0RD_1RD---_1LE1RA_0RC1LA_0RE0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 1 19.
Time Qed.
End TM678.


Module TM679.
Definition tm := TM_from_str "1RB---_1LC0LF_1RF0LD_1LE0RB_0LB1LA_0RD0RF".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEACDB") 3 6.
Time Qed.
End TM679.


Module TM680.
Definition tm := TM_from_str "1LB1RE_0RC0RD_1LA1RB_---1LC_1RA0LF_1RB1LE".
Definition tm' := TM_from_str "1RB0LF_1LC1RA_0RE0RD_---1LE_1LB1RC_1RC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEDAF") 116 122.
Time Qed.
End TM680.


Module TM681.
Definition tm := TM_from_str "1RB0LE_1RC0RF_1LD0RA_1RC0LE_1LD0LC_0RC---".
Definition tm' := TM_from_str "1RB0RF_1LC0RE_1RB0LD_1LC0LB_1RA0LD_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 82 142.
Time Qed.
End TM681.


Module TM682.
Definition tm := TM_from_str "1RB1LC_1LC0RC_1LD0RB_1LE---_0LF1RE_1RA0LA".
Definition tm' := TM_from_str "1RB0LB_1RC1LD_1LD0RD_1LE0RC_1LF---_0LA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 51 44.
Time Qed.
End TM682.


Module TM683.
Definition tm := TM_from_str "1RB1LC_0LA1RD_0RB1LF_0RE0LC_1RC---_0LD0LE".
Definition tm' := TM_from_str "1RB---_0RC1LE_0LD1RF_1RC1LB_0LF0LA_0RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCBFAE") 877 823.
Time Qed.
End TM683.


Module TM684.
Definition tm := TM_from_str "1LB1RD_1RC0LF_1RA1LC_1RE0RA_1RB---_0LD0LF".
Definition tm' := TM_from_str "1RB1LA_1LC1RE_1RA0LD_0LE0LD_1RF0RB_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEFD") 9 7.
Time Qed.
End TM684.


Module TM685.
Definition tm := TM_from_str "1LB0LE_1LC1RA_1LD0LC_1RB0LA_1RB0RF_1RE---".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1LD0LC_1RB0LE_1LB0LA_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 8 11.
Time Qed.
End TM685.


Module TM686.
Definition tm := TM_from_str "1RB---_1RC0RF_1LD0LF_1LE0LD_1RB0LB_1RB1RA".
Definition tm' := TM_from_str "1RB1RF_1RC0RA_1LD0LA_1LE0LD_1RB0LB_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM686.


Module TM687.
Definition tm := TM_from_str "1RB---_1LC0RA_1RD0LC_0RE1RB_0LB1RF_0RB0LB".
Definition tm' := TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDABCE") 1 3.
Time Qed.
End TM687.


Module TM688.
Definition tm := TM_from_str "1RB1RF_1RC0RA_1LD0RA_1LE0LE_1RB0LD_1RB---".
Definition tm' := TM_from_str "1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM688.


Module TM689.
Definition tm := TM_from_str "1LB---_1RC0LC_0RD1RA_1LE1RF_0LB0RC_0RE0LB".
Definition tm' := TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA0RB_0RD0LA_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 815 618.
Time Qed.
End TM689.


Module TM690.
Definition tm := TM_from_str "1LB1LF_0LC1RD_1LD---_1RE0LA_0RB1LF_0LD0RB".
Definition tm' := TM_from_str "1RB0LE_0RC1LF_0LD1RA_1LA---_1LC1LF_0LA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDABF") 150 141.
Time Qed.
End TM690.


Module TM691.
Definition tm := TM_from_str "1RB1LE_0RC0LD_1LD1RB_0LA0RF_0LB1LF_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1RB_0LE0RA_1RB1LF_0LB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM691.


Module TM692.
Definition tm := TM_from_str "1LB1LB_0LC1LE_1LD1LF_1RE0RE_0LA0RD_1LB---".
Definition tm' := TM_from_str "1RB0RB_0LC0RA_1LD1LD_0LE1LB_1LA1LF_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 1 3.
Time Qed.
End TM692.


Module TM693.
Definition tm := TM_from_str "1RB0RF_1RC0LB_0RD---_0RE0RA_1LE0LF_0LB1LF".
Definition tm' := TM_from_str "1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 298111 332265.
Time Qed.
End TM693.


Module TM694.
Definition tm := TM_from_str "1RB0LB_0LC0RF_---1LD_1LE0LA_1RB0RC_1RB1RF".
Definition tm' := TM_from_str "1RB1RA_0LC0RA_---1LD_1LE0LF_1RB0RC_1RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM694.


Module TM695.
Definition tm := TM_from_str "1LB---_0RC0LA_0LB1RD_0RE0RD_1RC0LF_1LF1LA".
Definition tm' := TM_from_str "1RB0LF_0LC1RE_0RB0LD_1LC---_0RA0RE_1LF1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCBEAF") 1 4.
Time Qed.
End TM695.


Module TM696.
Definition tm := TM_from_str "1RB0LA_0RC1LE_1RD1RF_0LB1RB_1LD1RA_0RB---".
Definition tm' := TM_from_str "1RB1RF_0LC1RC_0RA1LD_1LB1RE_1RC0LE_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECABDF") 1 14.
Time Qed.
End TM696.


Module TM697.
Definition tm := TM_from_str "1RB0RA_1LC0RE_1RA0LD_1LC0LD_1RF---_1RC1LA".
Definition tm' := TM_from_str "1RB0LD_1RC0RB_1LA0RE_1LA0LD_1RF---_1RA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 104 170.
Time Qed.
End TM697.


Module TM698.
Definition tm := TM_from_str "1RB1LE_0RC0RB_0LD0LF_1RE---_1LA0LF_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_0LD0LA_1RE---_1LF0LA_1RB1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM698.


Module TM699.
Definition tm := TM_from_str "1LB1RE_1LC1RD_0RB0LC_1LB0RA_1RA0LF_---1LE".
Definition tm' := TM_from_str "1RB0LF_1LC1RA_1LE1RD_1LC0RB_0RC0LE_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEDAF") 3 2.
Time Qed.
End TM699.


Module TM700.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LA_0LA---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM700.


Module TM701.
Definition tm := TM_from_str "1RB0RA_0LC0LE_---0LD_1RE1LC_1RA1LF_1LD0RE".
Definition tm' := TM_from_str "1RB1LE_1RC1LF_1RD0RC_0LE0LB_---0LA_1LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM701.


Module TM702.
Definition tm := TM_from_str "1LB0LC_0LC1LF_0RD0RE_1RA1LE_1RC0RD_0LA---".
Definition tm' := TM_from_str "1RB0RC_0RC0RA_1RD1LA_1LE0LB_0LB1LF_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCAF") 7 1.
Time Qed.
End TM702.


Module TM703.
Definition tm := TM_from_str "1RB0RA_1LC0LB_1RE0LD_1LE0LF_1LA0RC_0RC---".
Definition tm' := TM_from_str "1RB0LE_1LC0RA_1RD0RC_1LA0LD_1LB0LF_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEBF") 1 5.
Time Qed.
End TM703.


Module TM704.
Definition tm := TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1RB_0RF1RD_0LC0RD".
Definition tm' := TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA---_0RF1RB_0LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 34 22.
Time Qed.
End TM704.


Module TM705.
Definition tm := TM_from_str "1RB0RA_1LC0RA_1RB1LD_0LE---_0LF1LC_0LB0RC".
Definition tm' := TM_from_str "1RB1LC_1LA0RF_0LD---_0LE1LA_0LB0RA_1RB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBACDE") 1 1.
Time Qed.
End TM705.


Module TM706.
Definition tm := TM_from_str "1RB0LA_0RC1RF_0LD1RE_1LA0RB_0RD---_1RB1RD".
Definition tm' := TM_from_str "1RB1RD_0RC1RA_0LD1RF_1LE0RB_1RB0LE_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM706.


Module TM707.
Definition tm := TM_from_str "1LB1RE_1RC0LC_1LD0LD_0LB1RA_1RA0RF_0RA---".
Definition tm' := TM_from_str "1RB0RF_1LC1RA_1RD0LD_1LE0LE_0LC1RB_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 4 1.
Time Qed.
End TM707.


Module TM708.
Definition tm := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_1RC---".
Definition tm' := TM_from_str "1RB1RE_1RC---_1LD1LC_0RE0LD_1RF0RA_1RC1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCDAB") 2 2.
Time Qed.
End TM708.


Module TM709.
Definition tm := TM_from_str "1RB1LC_0LC1RE_---0LD_0RE1LA_1RF1RB_1RB0RC".
Definition tm' := TM_from_str "1RB0RC_0LC1RE_---0LD_0RE1LF_1RA1RB_1RB1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM709.


Module TM710.
Definition tm := TM_from_str "1LB0RB_1RC0LE_0RA1RD_0RE---_1RF0LB_0LF1LE".
Definition tm' := TM_from_str "1RB0LE_0RC1RD_1LA0RA_0RE---_1RF0LA_0LF1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 57 67.
Time Qed.
End TM710.


Module TM711.
Definition tm := TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB1RF_1RA---".
Definition tm' := TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM711.


Module TM712.
Definition tm := TM_from_str "1LB1LA_1RC1RB_0LD0RC_1LA0LE_0LF1LD_0RA---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_0LE1LC_0RF---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 1 6.
Time Qed.
End TM712.


Module TM713.
Definition tm := TM_from_str "1LB0RA_0LC0RE_0RD1LE_1RA0LB_0LD1LF_1RA---".
Definition tm' := TM_from_str "1RB---_1LC0RB_0LE0RD_0LF1LA_0RF1LD_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEFDA") 4 5.
Time Qed.
End TM713.


Module TM714.
Definition tm := TM_from_str "1RB1LD_1RC---_1LD1RA_0LE0RA_1RE0LF_0RB0LD".
Definition tm' := TM_from_str "1RB---_1LC1RD_0LE0RD_1RA1LC_1RE0LF_0RA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 11.
Time Qed.
End TM714.


Module TM715.
Definition tm := TM_from_str "1LB1LA_1RC1RF_1LE0RD_1LE---_0RB0LE_1RA1RB".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_0RA0LC_1LC---_1RF1RA_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABDCE") 1 4.
Time Qed.
End TM715.


Module TM716.
Definition tm := TM_from_str "1RB0LC_0LA---_0LD1RE_0LE1LD_1RF0RE_1RC0RA".
Definition tm' := TM_from_str "1RB0RA_1RC0RE_0LD1RA_0LA1LD_1RF0LC_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCDAB") 6 1.
Time Qed.
End TM716.


Module TM717.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_0LD---_1RA0LD".
Definition tm' := TM_from_str "1RB1RC_0LA---_1RD0RA_1RE0LA_1LF1LE_0RC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCABD") 4 1.
Time Qed.
End TM717.


Module TM718.
Definition tm := TM_from_str "1RB0RF_1LC0RE_1LC0LD_1RE0LB_1RF---_1RC1RA".
Definition tm' := TM_from_str "1RB1RE_1LB0LC_1RD0LF_1RA---_1RF0RA_1LB0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 2 2.
Time Qed.
End TM718.


Module TM719.
Definition tm := TM_from_str "1LB0RA_0LC1LD_1LD1RE_1RA1LC_1RF0RC_---0LB".
Definition tm' := TM_from_str "1RB1LD_1LC0RB_0LD1LA_1LA1RE_1RF0RD_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 11 9.
Time Qed.
End TM719.


Module TM720.
Definition tm := TM_from_str "1LB1RC_1LC1LB_1LD0RC_1RE0LD_1RF0LD_1RA---".
Definition tm' := TM_from_str "1RB0LA_1RC0LA_1RD---_1LE1RF_1LF1LE_1LA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 20 1.
Time Qed.
End TM720.


Module TM721.
Definition tm := TM_from_str "1LB1RC_0RA0LE_0RD0LA_1LC1RD_0LC0LF_1RC---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LB1RC_1LE1RB_0RD0LF_0LB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 3 1.
Time Qed.
End TM721.


Module TM722.
Definition tm := TM_from_str "1LB1LF_0RC1LE_1RD1RC_0LE1RB_---0LA_0LB0RA".
Definition tm' := TM_from_str "1RB1RA_0LC1RE_---0LD_1LE1LF_0RA1LC_0LE0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM722.


Module TM723.
Definition tm := TM_from_str "1RB---_0RC0LB_0LD0RF_1LE0RB_1RC0LB_1RD1RA".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEBCA") 3 1.
Time Qed.
End TM723.


Module TM724.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_1RA---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM724.


Module TM725.
Definition tm := TM_from_str "1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_1RD---".
Definition tm' := TM_from_str "1RB---_1LC1LE_1RF0LD_0LE1LA_1LB0RC_1RE1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFEBDA") 5 2.
Time Qed.
End TM725.


Module TM726.
Definition tm := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LE_0LC1LD_0LD1LB".
Definition tm' := TM_from_str "1RB1LE_0RC0LF_1LD0RF_0LA---_0LB1LD_0LA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 22 34.
Time Qed.
End TM726.


Module TM727.
Definition tm := TM_from_str "1RB1RF_0RC1LC_0LD1LE_1LB1LD_1RF---_1RD0RA".
Definition tm' := TM_from_str "1RB0RF_1LC1LB_0RD1LD_0LB1LE_1RA---_1RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDBEA") 3 1.
Time Qed.
End TM727.


Module TM728.
Definition tm := TM_from_str "1LB0LC_1RA0LF_0RE0RD_1RE---_0RB1RC_0LA1LF".
Definition tm' := TM_from_str "1RB---_0RC1RF_1RD0LE_1LC0LF_0LD1LE_0RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCFABE") 5 1.
Time Qed.
End TM728.


Module TM729.
Definition tm := TM_from_str "1LB0RF_1LC---_0LD1RC_1RE0LE_1RF1LA_1LA0RA".
Definition tm' := TM_from_str "1RB0LB_1RC1LD_1LD0RD_1LE0RC_1LF---_0LA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 47 44.
Time Qed.
End TM729.


Module TM730.
Definition tm := TM_from_str "1LB0RA_0RC0LC_1LD1RA_1RA1LE_1RB0LF_1LC---".
Definition tm' := TM_from_str "1RB1LE_1LC0RB_0RD0LD_1LA1RB_1RC0LF_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 3 1.
Time Qed.
End TM730.


Module TM731.
Definition tm := TM_from_str "1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD0RA".
Definition tm' := TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 4 1.
Time Qed.
End TM731.


Module TM732.
Definition tm := TM_from_str "1RB---_1LC0RF_0LE1LD_1LC0LB_1LA0LC_1RB1RF".
Definition tm' := TM_from_str "1RB1RA_1LC0RA_0LE1LD_1LC0LB_1LF0LC_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM732.


Module TM733.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LF_0RB1RF_0RA---".
Definition tm' := TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD1RF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 33 23.
Time Qed.
End TM733.


Module TM734.
Definition tm := TM_from_str "1RB0LF_0LC0RB_1LA1LD_1LE1LC_1RC1RE_1RB---".
Definition tm' := TM_from_str "1RB---_0LC0RB_1LF1LD_1LE1LC_1RC1RE_1RB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM734.


Module TM735.
Definition tm := TM_from_str "1LB1LE_0RC0LD_1LA0RD_1RC1RB_0LA1LF_1RB---".
Definition tm' := TM_from_str "1RB1RE_1LC0RA_1LE1LD_0LC1LF_0RB0LA_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEBADF") 4 1.
Time Qed.
End TM735.


Module TM736.
Definition tm := TM_from_str "1LB1RE_1RC0RA_1LA1RD_1RB0RC_---1LF_0RC0LF".
Definition tm' := TM_from_str "1RB0RC_1LC1RF_1LA1RD_---1LE_0RB0LE_1RA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABFDE") 27 30.
Time Qed.
End TM736.


Module TM737.
Definition tm := TM_from_str "1LB---_1LC1RB_1RD1LE_1RB0RD_1LA1LF_0RB0LC".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LF1LE_0RC0LA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCABDE") 14 17.
Time Qed.
End TM737.


Module TM738.
Definition tm := TM_from_str "1LB1RC_0LC0LE_0RD0LA_1LC1RD_0LC0LF_1RC---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LB1RC_1LE1RB_0LB0LF_0LB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 11 4.
Time Qed.
End TM738.


Module TM739.
Definition tm := TM_from_str "1RB0RA_1LC1RE_1RF1LD_0LE---_0LF1LF_0LB0RA".
Definition tm' := TM_from_str "1RB1LF_0LC0RE_1LA1RD_0LB1LB_1RC0RE_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECAFDB") 1 6.
Time Qed.
End TM739.


Module TM740.
Definition tm := TM_from_str "1LB0LC_1LC---_1RD1LE_1LC1RD_1RF1LA_0LB0RF".
Definition tm' := TM_from_str "1RB1LC_1LA1RB_1RD1LF_0LE0RD_1LA---_1LE0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEABCD") 4 9.
Time Qed.
End TM740.


Module TM741.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RA0LD_1RA1LE_0RE0LB_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1RE0LD_1RE1LF_1RB0RA_0RF0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM741.


Module TM742.
Definition tm := TM_from_str "1LB1RF_0LC1RE_0RD1LE_1RB0RB_0LA0RA_0RD---".
Definition tm' := TM_from_str "1RB0RB_0LC1RD_0RA1LD_0LE0RE_1LB1RF_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 14 12.
Time Qed.
End TM742.


Module TM743.
Definition tm := TM_from_str "1RB0RB_1LC1RA_1LA1RD_1LE0LC_1LF0LD_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1RF_1LF1RD_1LE0LC_1LA0LD_1RB0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM743.


Module TM744.
Definition tm := TM_from_str "1LB0LD_0RC1RB_1LD0RD_0LE1RF_1RA1LA_0LA---".
Definition tm' := TM_from_str "1RB1LB_1LC0LE_0RD1RC_1LE0RE_0LA1RF_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 5 1.
Time Qed.
End TM744.


Module TM745.
Definition tm := TM_from_str "1RB0RC_1LC0RA_1RB0LD_1LE0RC_1LC0LF_0LC---".
Definition tm' := TM_from_str "1RB0LC_1LA0RE_1LD0RA_1LA0LF_1RB0RA_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM745.


Module TM746.
Definition tm := TM_from_str "1RB---_0RC1RF_1RD0LD_1LE0RB_1RF0LF_1LC0RA".
Definition tm' := TM_from_str "1RB0LB_1LC0RE_1RD0LD_1LA0RF_0RA1RD_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEABCD") 6 27.
Time Qed.
End TM746.


Module TM747.
Definition tm := TM_from_str "1LB1LF_1RC0RE_1LD0RB_0LA1LC_0LC0RA_0LC---".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 11 25.
Time Qed.
End TM747.


Module TM748.
Definition tm := TM_from_str "1LB1LE_1RC0LA_0LF0RD_1RE1RC_1LA0LC_---0LA".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_---0LD_1LA1LF_1RF1RB_1LD0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABEFC") 1 4.
Time Qed.
End TM748.


Module TM749.
Definition tm := TM_from_str "1RB1LD_1RC0RB_0LA1RE_1LA0LD_1RF0RD_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RB_0LD1RF_1RB1LE_1LD0LE_1RA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM749.


Module TM750.
Definition tm := TM_from_str "1RB0LE_1RC1LF_1LD1RB_---0LA_0RA1RE_0LD0LF".
Definition tm' := TM_from_str "1RB1LF_1LC1RA_---0LD_1RA0LE_0RD1RE_0LC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 6 3.
Time Qed.
End TM750.


Module TM751.
Definition tm := TM_from_str "1RB0RE_0LC0RA_1LD1LC_1RB0LA_0RB1RF_0LD---".
Definition tm' := TM_from_str "1RB0LD_0LC0RD_1LA1LC_1RB0RE_0RB1RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM751.


Module TM752.
Definition tm := TM_from_str "1RB1RF_0LC0RE_0RF1RD_1LE0LB_1RA0LD_1RB---".
Definition tm' := TM_from_str "1RB---_0LC0RE_0RA1RD_1LE0LB_1RF0LD_1RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM752.


Module TM753.
Definition tm := TM_from_str "1LB0RA_1RC1LF_0LF1RD_1RE---_1RA1RC_0RE0LE".
Definition tm' := TM_from_str "1RB1RE_1LC0RB_1RE1LD_0RA0LA_0LD1RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEFAD") 2 5.
Time Qed.
End TM753.


Module TM754.
Definition tm := TM_from_str "1LB1LA_1RC1LE_1RD1RB_0LA0RB_0RE0RF_---0LA".
Definition tm' := TM_from_str "1RB1RD_0LC0RD_1LD1LC_1RA1LE_0RE0RF_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 1 15.
Time Qed.
End TM754.


Module TM755.
Definition tm := TM_from_str "1LB1LD_1RC1RB_1LD1RA_---0LE_0RB0LF_0LD0RB".
Definition tm' := TM_from_str "1RB1RA_1LC1RE_---0LD_0RA0LF_1LA1LC_0LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 4.
Time Qed.
End TM755.


Module TM756.
Definition tm := TM_from_str "1LB1RD_1LC1LB_1RA0RF_1RC1RE_0RA0LD_---0LB".
Definition tm' := TM_from_str "1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 4 8.
Time Qed.
End TM756.


Module TM757.
Definition tm := TM_from_str "1RB1LB_1RC1LE_1RD1RF_0LE1RD_0RC0LA_---0RC".
Definition tm' := TM_from_str "1RB1RF_0LC1RB_0RA0LD_1RE1LE_1RA1LC_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM757.


Module TM758.
Definition tm := TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA1RB_0RB1RF_0RA---".
Definition tm' := TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RF_0RD1RF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 35 23.
Time Qed.
End TM758.


Module TM759.
Definition tm := TM_from_str "1LB1RC_0LC1LE_0RD0RF_1RA0RB_0RE0LA_1RD---".
Definition tm' := TM_from_str "1RB0RC_1LC1RE_0LE1LD_0RD0LB_0RA0RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEADF") 3209 3114.
Time Qed.
End TM759.


Module TM760.
Definition tm := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LB_0LC1RD_0LD1LE".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0RF_0LA---_0LB1LF_0LA1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 23 31.
Time Qed.
End TM760.


Module TM761.
Definition tm := TM_from_str "1RB0RF_0RC0RA_1RD0LE_0LC1RA_1LC1RE_---1RB".
Definition tm' := TM_from_str "1RB0LC_0LA1RD_1LA1RC_1RE0RF_0RA0RD_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 35 29.
Time Qed.
End TM761.


Module TM762.
Definition tm := TM_from_str "1LB0RC_1LC0LF_0LD1RC_1RB1RE_1RA1LE_---0LE".
Definition tm' := TM_from_str "1RB1RD_1LC0LF_0LA1RC_1RE1LD_1LB0RC_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 104 94.
Time Qed.
End TM762.


Module TM763.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_1RF0LD_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0LB_1RF1RD_1RA0LE_1RC0RF_1LB1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCEDA") 1 6.
Time Qed.
End TM763.


Module TM764.
Definition tm := TM_from_str "1RB0RD_1LC---_1RD1LC_1LF1RE_1RC1RA_1RB0LF".
Definition tm' := TM_from_str "1RB0LA_1LC---_1RD1LC_1LA1RE_1RC1RF_1RB0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM764.


Module TM765.
Definition tm := TM_from_str "1RB---_1RC0RF_1RD1RC_1LE1LD_0RB0LE_1RA1RB".
Definition tm' := TM_from_str "1RB1RC_1RC---_1RD0RA_1RE1RD_1LF1LE_0RC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 12344 13012.
Time Qed.
End TM765.


Module TM766.
Definition tm := TM_from_str "1RB1LC_1RC1RA_1LD0LA_0RE0LD_1RF---_0RB1RB".
Definition tm' := TM_from_str "1RB---_0RC1RC_1RD1RF_1LE0LF_0RA0LE_1RC1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEAB") 10 8.
Time Qed.
End TM766.


Module TM767.
Definition tm := TM_from_str "1RB0RC_1RC0LE_1LD1RE_1LB0LD_1RF0RC_1RA---".
Definition tm' := TM_from_str "1RB---_1RC0RD_1RD0LF_1LE1RF_1LC0LE_1RA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 11 15.
Time Qed.
End TM767.


Module TM768.
Definition tm := TM_from_str "1LB1LE_0LC1RE_0RD0LA_1LE0RF_1RB1LD_---0RC".
Definition tm' := TM_from_str "1RB1LE_0LC1RA_0RE0LD_1LB1LA_1LA0RF_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 4.
Time Qed.
End TM768.


Module TM769.
Definition tm := TM_from_str "1RB1RE_1LC1RF_1LA0LD_1LE1LE_0RA0LC_1RA---".
Definition tm' := TM_from_str "1RB---_1RC1RF_1LD1RA_1LB0LE_1LF1LF_0RB0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 4 5.
Time Qed.
End TM769.


Module TM770.
Definition tm := TM_from_str "1LB---_1LC1LF_1RD1LE_1RB0RD_1LA0LC_1RE0RE".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LF0LA_1RD0RD_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCABDE") 13 32.
Time Qed.
End TM770.


Module TM771.
Definition tm := TM_from_str "1RB0LB_1LC0RE_---1LD_1LE0LA_1RB1RF_0LB0LC".
Definition tm' := TM_from_str "1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM771.


Module TM772.
Definition tm := TM_from_str "1RB---_1LC1RE_1LD0LC_1RB1LD_1RF0RB_1RD0RA".
Definition tm' := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM772.


Module TM773.
Definition tm := TM_from_str "1RB0RE_0LC1RD_0LD1LC_1RA0RD_1RF0LB_0LE---".
Definition tm' := TM_from_str "1RB0RA_1RC0RE_0LD1RA_0LA1LD_1RF0LC_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 1 38.
Time Qed.
End TM773.


Module TM774.
Definition tm := TM_from_str "1LB0LC_1LC0RD_1RD1LA_1RF1RE_---1RB_1LD0RA".
Definition tm' := TM_from_str "1RB1LF_1RC1RD_1LB0RF_---1RE_1LA0RB_1LE0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEABDC") 4 4.
Time Qed.
End TM774.


Module TM775.
Definition tm := TM_from_str "1RB0LE_1LC0RE_0RF0LD_1LA1RB_0LC0RF_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_0RA0LD_1LE1RB_1RB0LF_0LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM775.


Module TM776.
Definition tm := TM_from_str "1LB1LE_1RC0LC_0LA0RD_1RB0RD_0LC0LF_1RA---".
Definition tm' := TM_from_str "1RB0RA_1RC0LC_0LD0RA_1LB1LE_0LC0LF_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 19 1.
Time Qed.
End TM776.


Module TM777.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RA_0RF1LB_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0LB_1RE0RD_0RA1LB_1LB1RF_1RC0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFDA") 1 4.
Time Qed.
End TM777.


Module TM778.
Definition tm := TM_from_str "1LB0LE_1LC1RF_0RD1RE_---1RE_1LA0RB_1RB0RC".
Definition tm' := TM_from_str "1RB0RC_1LC1RA_0RE1RD_1LF0RB_---1RD_1LB0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCEDA") 4 3.
Time Qed.
End TM778.


Module TM779.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LD0LC_1RA0RF_1LF---_1RB1RB".
Definition tm' := TM_from_str "1RB1RB_1LC1RD_1LD0LC_1RE0RA_1RB1RF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM779.


Module TM780.
Definition tm := TM_from_str "1LB1RA_0LC1LF_1RD---_1LE0LE_1RA1LD_1LA0RF".
Definition tm' := TM_from_str "1RB1LF_1LC1RB_0LE1LD_1LB0RD_1RF---_1LA0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEFAD") 71 90.
Time Qed.
End TM780.


Module TM781.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RD1LB_0LA1RE_0RA1RF_1RA---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1RD0LC_0RE1LC_0LB1RF_0RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 3 2.
Time Qed.
End TM781.


Module TM782.
Definition tm := TM_from_str "1RB0LC_1RC0RF_0LD1LA_1LA1LE_1RA0LF_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RA_0LD1LF_1LF1LE_1RF0LA_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM782.


Module TM783.
Definition tm := TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0RF_0LE1RF".
Definition tm' := TM_from_str "1RB1RC_0LC0RD_1RE1LD_0LB1RD_0RF---_0RA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEFABD") 21 42.
Time Qed.
End TM783.


Module TM784.
Definition tm := TM_from_str "1LB1RE_0RC---_1LF0LD_1RE1LC_1RF0RE_1LD0LA".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDABC") 4 1.
Time Qed.
End TM784.


Module TM785.
Definition tm := TM_from_str "1RB---_1RC0RC_0LD1RC_1RA0LE_0RF1LF_1RB1LD".
Definition tm' := TM_from_str "1RB1LD_1RC0RC_0LD1RC_1RF0LE_0RA1LA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM785.


Module TM786.
Definition tm := TM_from_str "1RB0RE_1RC0RA_0RD0LC_1LE1RF_1LC---_1RB1RA".
Definition tm' := TM_from_str "1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_1RB0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM786.


Module TM787.
Definition tm := TM_from_str "1LB0RD_1LC1LB_1RA1RE_---1RA_1RC0LF_1RF1LE".
Definition tm' := TM_from_str "1RB0LF_1RC1RA_1LD0RE_1LB1LD_---1RC_1RF1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEAF") 24 26.
Time Qed.
End TM787.


Module TM788.
Definition tm := TM_from_str "1RB1RE_1LC0RD_0RB0LC_1RA1RD_0LF---_1RD1LF".
Definition tm' := TM_from_str "1RB1LA_1RC1RB_1RD1RF_1LE0RB_0RD0LE_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBFA") 8 1.
Time Qed.
End TM788.


Module TM789.
Definition tm := TM_from_str "1LB---_1RC1LF_0RE0LD_0LB0RD_1LD0RD_0LC1LA".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0RD_0LA0RD_0LB1LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABDCE") 6 1.
Time Qed.
End TM789.


Module TM790.
Definition tm := TM_from_str "1LB1RC_0RA0LB_0RD0LA_1LA1RE_1RD0LF_---1LE".
Definition tm' := TM_from_str "1RB0LF_1LC1RA_1LE1RD_0RB0LC_0RC0LE_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEDBAF") 2 4.
Time Qed.
End TM790.


Module TM791.
Definition tm := TM_from_str "1LB0RE_1RC0LA_1RD0RC_1LB0RA_1RF---_0LD0LF".
Definition tm' := TM_from_str "1RB0LD_1RC0RB_1LA0RD_1LA0RE_1RF---_0LC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 10.
Time Qed.
End TM791.


Module TM792.
Definition tm := TM_from_str "1LB0RE_1RC0LA_0LB1RD_1RE0RF_1LF---_1LC1RF".
Definition tm' := TM_from_str "1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 4.
Time Qed.
End TM792.


Module TM793.
Definition tm := TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB1RF_0LC---".
Definition tm' := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 465 442.
Time Qed.
End TM793.


Module TM794.
Definition tm := TM_from_str "1LB0RB_0LC1LD_1RD1LE_0RA0LF_0LD1LA_0LC---".
Definition tm' := TM_from_str "1RB1LE_0RC0LF_1LD0RD_0LA1LB_0LB1LC_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 230 86.
Time Qed.
End TM794.


Module TM795.
Definition tm := TM_from_str "1LB1RE_0RC0RD_1LA1RB_---1LC_1RA0LF_1LB1LE".
Definition tm' := TM_from_str "1RB0LF_1LC1RA_0RE0RD_---1LE_1LB1RC_1LC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEDAF") 120 126.
Time Qed.
End TM795.


Module TM796.
Definition tm := TM_from_str "1LB0LD_0RC0LD_1RB1RD_0LE0RF_0LB1RF_1RA---".
Definition tm' := TM_from_str "1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFDEA") 13 1.
Time Qed.
End TM796.


Module TM797.
Definition tm := TM_from_str "1LB0RF_1RC0LA_0LE0RD_0RC1RB_0LF1LB_1LE---".
Definition tm' := TM_from_str "1RB0LF_0LC0RD_0LE1LA_0RB1RA_1LC---_1LA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABDCE") 1 3.
Time Qed.
End TM797.


Module TM798.
Definition tm := TM_from_str "1RB1LE_1LC1RE_1RF1LD_0LE---_0LF1LF_0LB0RA".
Definition tm' := TM_from_str "1RB1LF_0LC0RE_1LA1RD_0LB1LB_1RC1LD_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECAFDB") 1 6.
Time Qed.
End TM798.


Module TM799.
Definition tm := TM_from_str "1LB1RC_0RA0LF_1RD1LB_1RE---_1RA1LB_0LB0RF".
Definition tm' := TM_from_str "1RB1LE_1RC---_1RD1LE_1LE1RA_0RD0LF_0LE0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 34 11.
Time Qed.
End TM799.


Module TM800.
Definition tm := TM_from_str "1LB0RF_1LC1LA_1RD---_1LF0RE_1RA1RE_1RA0LD".
Definition tm' := TM_from_str "1RB---_1LC0RF_1RD0LB_1LE0RC_1LA1LD_1RD1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABFC") 438 499.
Time Qed.
End TM800.


Module TM801.
Definition tm := TM_from_str "1RB0RA_1LC1RE_1RA1LD_0LB0LF_0RD0RC_1LC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RF_0LC0LE_1LA---_0RD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADFE") 5 6.
Time Qed.
End TM801.


Module TM802.
Definition tm := TM_from_str "1LB0RC_1RA1LE_1LD0RB_1RC1LF_0LC0LF_0LB---".
Definition tm' := TM_from_str "1RB1LC_1LA0RD_0LD---_1RE1LF_1LD0RB_0LB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDBAFC") 21 19.
Time Qed.
End TM802.


Module TM803.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LF0LE_1RF1LD_1LC---".
Definition tm' := TM_from_str "1RB1LE_1LC---_1LD1RC_1RF1LE_1LB0LA_1RC0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFCEAB") 2 4.
Time Qed.
End TM803.


Module TM804.
Definition tm := TM_from_str "1LB0LE_1RC1LA_1LB1RD_0LB0LF_1LD---_0RF0RB".
Definition tm' := TM_from_str "1RB1LC_1LA1RD_1LA0LF_0LA0LE_0RE0RA_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDFE") 1 18.
Time Qed.
End TM804.


Module TM805.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RA_1RF1LB_1LC---".
Definition tm' := TM_from_str "1RB1LD_1LC---_1RE0RA_1LC0LD_1LD1RF_1RC0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDCFAB") 1 4.
Time Qed.
End TM805.


Module TM806.
Definition tm := TM_from_str "1LB0RC_0RA0LB_1RD0LE_1RA1RC_1LC0RF_1RE---".
Definition tm' := TM_from_str "1RB1RD_1LC0RD_0RB0LC_1RA0LE_1LD0RF_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 12 9.
Time Qed.
End TM806.


Module TM807.
Definition tm := TM_from_str "1RB1RE_0RC1RB_1LD0RD_1LA0RE_---0LF_1RB1LD".
Definition tm' := TM_from_str "1RB1LD_0RC1RB_1LD0RD_1LE0RF_1RB1RF_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM807.


Module TM808.
Definition tm := TM_from_str "1RB0LA_0RC0RD_1RD1RF_0RE0LD_1LE1RA_1RE---".
Definition tm' := TM_from_str "1RB---_1LB1RC_1RD0LC_0RE0RF_1RF1RA_0RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 1 6.
Time Qed.
End TM808.


Module TM809.
Definition tm := TM_from_str "1RB---_1RC1RA_1LD0RB_1RC0LE_1LF1LD_1RB0RD".
Definition tm' := TM_from_str "1RB0RD_1RC1RF_1LD0RB_1RC0LE_1LA1LD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM809.


Module TM810.
Definition tm := TM_from_str "1LB0LD_1RC0RB_1LD1RC_1LE1LA_1RF---_1RB1LF".
Definition tm' := TM_from_str "1RB0RA_1LC1RB_1LE1LD_1LA0LC_1RF---_1RA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 28 65.
Time Qed.
End TM810.


Module TM811.
Definition tm := TM_from_str "1LB0LA_0RB1RC_0RD0LC_1RE0RF_1LA1RF_1RD---".
Definition tm' := TM_from_str "1RB---_1RC0RA_1LD1RA_1LE0LD_0RE1RF_0RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 1165 1152.
Time Qed.
End TM811.


Module TM812.
Definition tm := TM_from_str "1RB1LF_1LC0RD_0RB0LC_1RE1RD_1RA---_1RD1LA".
Definition tm' := TM_from_str "1RB1LD_1RC1RB_1RD---_1RE1LA_1LF0RB_0RE0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 8 1.
Time Qed.
End TM812.


Module TM813.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_0RE1RC_0LC---_1RA0LD".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_0RF1RA_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEFB") 6 1.
Time Qed.
End TM813.


Module TM814.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RF0LD_0RA1RE_1RA---_0LA1RD".
Definition tm' := TM_from_str "1RB---_1LC0RD_1RD0LC_0RE0LF_0LB1RF_0RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDFAE") 56 70.
Time Qed.
End TM814.


Module TM815.
Definition tm := TM_from_str "1RB---_1RC0RB_1LC1LD_1RC1LE_0LF1LA_1LA0LE".
Definition tm' := TM_from_str "1RB1LC_1LB1LA_0LD1LE_1LE0LC_1RF---_1RB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBACD") 4 5.
Time Qed.
End TM815.


Module TM816.
Definition tm := TM_from_str "1LB---_0LC1RB_1RD0LD_1RE1LF_1LF0RF_1LA0RE".
Definition tm' := TM_from_str "1RB0LB_1RC1LD_1LD0RD_1LE0RC_1LF---_0LA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 14 4.
Time Qed.
End TM816.


Module TM817.
Definition tm := TM_from_str "1LB0RC_1RC0LE_0LF1RD_1RA0RB_1LD0RC_1LA---".
Definition tm' := TM_from_str "1RB0RC_1LC0RE_1RE0LD_1LA0RE_0LF1RA_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEADF") 9 8.
Time Qed.
End TM817.


Module TM818.
Definition tm := TM_from_str "1LB0LA_1RC0LD_1LA0RD_1RE0LC_1RC1RF_0LD---".
Definition tm' := TM_from_str "1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 15 21.
Time Qed.
End TM818.


Module TM819.
Definition tm := TM_from_str "1LB1LC_0LC0RC_1RD1LE_0RA0LB_0LD1LF_0LC---".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD1LA_0LA0RA_0LB1LF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 25 39.
Time Qed.
End TM819.


Module TM820.
Definition tm := TM_from_str "1RB---_0RC0RA_1RD0RE_1LE0LF_1RC0LD_1LD0RA".
Definition tm' := TM_from_str "1RB0LC_1RC0RA_1LA0LD_1LC0RE_1RF---_0RB0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCAD") 53 54.
Time Qed.
End TM820.


Module TM821.
Definition tm := TM_from_str "1RB0RA_1RC1RA_1LD0LE_0RA0LD_1LC0RF_1RE---".
Definition tm' := TM_from_str "1RB---_1LC0RA_1LD0LB_0RE0LD_1RF0RE_1RC1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCDBA") 89 88.
Time Qed.
End TM821.


Module TM822.
Definition tm := TM_from_str "1LB0RE_1RC---_1LC1LD_1LA1RA_0LC0RF_0RA0LA".
Definition tm' := TM_from_str "1RB---_1LB1LC_1LD1RD_1LA0RE_0LB0RF_0RD0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 6 1.
Time Qed.
End TM822.


Module TM823.
Definition tm := TM_from_str "1RB---_1RC0RB_0LD1RB_1RA0LE_0RA0LF_1RD1LD".
Definition tm' := TM_from_str "1RB0RA_0LC1RA_1RE0LD_0RE0LF_1RA---_1RC1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 5.
Time Qed.
End TM823.


Module TM824.
Definition tm := TM_from_str "1LB0RD_0LC0LE_1RD0LB_1RA1LB_0LF1RE_---0RB".
Definition tm' := TM_from_str "1RB0LD_1RC1LD_1LD0RB_0LA0LE_0LF1RE_---0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 1 7.
Time Qed.
End TM824.


Module TM825.
Definition tm := TM_from_str "1RB0RD_0RC0LD_1LD1RA_0LE0RF_1RB0LB_0RB---".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM825.


Module TM826.
Definition tm := TM_from_str "1RB---_1RC1RB_0RD1RE_0LE1RD_1LF0RA_1RA0LF".
Definition tm' := TM_from_str "1RB1RA_0RC1RD_0LD1RC_1LE0RF_1RF0LE_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 11 11.
Time Qed.
End TM826.


Module TM827.
Definition tm := TM_from_str "1LB1RA_0LC1RE_0RD1LF_1RE---_0RA0LB_0LE0LD".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_0RA1LF_0LB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 6 1.
Time Qed.
End TM827.


Module TM828.
Definition tm := TM_from_str "1RB1LA_1RC1RF_1LD0RE_0RB0LD_1RA0LC_---1RE".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_0RA0LC_1RE0LB_1RA1LE_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 13 1.
Time Qed.
End TM828.


Module TM829.
Definition tm := TM_from_str "1RB0RA_1LC0RA_1RB1LD_0LE---_0LF0RF_0LB0RA".
Definition tm' := TM_from_str "1RB1LC_1LA0RF_0LD---_0LE0RE_0LB0RF_1RB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBACDE") 1 1.
Time Qed.
End TM829.


Module TM830.
Definition tm := TM_from_str "1RB1LC_0LC1RE_---0LD_0RE1LA_1RF0LD_1RB0RE".
Definition tm' := TM_from_str "1RB0LE_1RC0RA_0LD1RA_---0LE_0RA1LF_1RC1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEAB") 5 1.
Time Qed.
End TM830.


Module TM831.
Definition tm := TM_from_str "1RB1LC_0LA1RD_0LD0LC_0RE0RF_1RA---_1RF1RE".
Definition tm' := TM_from_str "1RB---_1RC1LD_0LB1RE_0LE0LD_0RA0RF_1RF1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 6 3.
Time Qed.
End TM831.


Module TM832.
Definition tm := TM_from_str "1RB---_1LC0RB_0LE1LD_1RC1RE_1RA1LF_0RA0LF".
Definition tm' := TM_from_str "1RB1LF_1RC---_1LD0RC_0LA1LE_1RD1RA_0RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 5 4.
Time Qed.
End TM832.


Module TM833.
Definition tm := TM_from_str "1RB1LB_1LC1LF_1RD0RA_0LA1RE_1RC0RD_---0LD".
Definition tm' := TM_from_str "1RB0RC_0LC1RE_1RD1LD_1LA1LF_1RA0RB_---0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 3 2.
Time Qed.
End TM833.


Module TM834.
Definition tm := TM_from_str "1LB1LA_1RC0LA_0LB1RD_1RE1RF_0RB0RD_---0RE".
Definition tm' := TM_from_str "1RB1RF_0RC0RA_1RD0LE_0LC1RA_1LC1LE_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDABF") 26 35.
Time Qed.
End TM834.


Module TM835.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA1LE_1RF0RA_1RC0LD_1RC---".
Definition tm' := TM_from_str "1RB0LE_1RC1LA_1LD1RE_1LB0LD_1RF0RC_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEAF") 47 65.
Time Qed.
End TM835.


Module TM836.
Definition tm := TM_from_str "1LB0LF_1RC1LB_1LA1RD_1RE0RC_1RB---_1RA0LF".
Definition tm' := TM_from_str "1RB1LA_1LC1RE_1LA0LD_1RC0LD_1RF0RB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEFD") 21 22.
Time Qed.
End TM836.


Module TM837.
Definition tm := TM_from_str "1LB0RF_1LC1LA_1RD---_0LE0RD_0LA1LF_1RA0LC".
Definition tm' := TM_from_str "1RB0LD_1LC0RA_1LD1LB_1RE---_0LF0RE_0LB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 7 1.
Time Qed.
End TM837.


Module TM838.
Definition tm := TM_from_str "1RB1LA_0LC0LC_0LA1LD_1RE0LC_1RC0RF_1RE---".
Definition tm' := TM_from_str "1RB0RF_0LC1LE_1RD1LC_0LB0LB_1RA0LB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEAF") 2 5.
Time Qed.
End TM838.


Module TM839.
Definition tm := TM_from_str "1RB0RE_1RC1RF_1LD0LC_1RE1LC_0LA0RB_---0RA".
Definition tm' := TM_from_str "1RB1LE_0LC0RD_1RD0RB_1RE1RF_1LA0LE_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 1 5.
Time Qed.
End TM839.


Module TM840.
Definition tm := TM_from_str "1LB1RE_0LC0LF_0RD0LB_1RA0LB_1RD---_0RA0RE".
Definition tm' := TM_from_str "1RB---_1RC0LD_1LD1RA_0LF0LE_0RC0RA_0RB0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFBAE") 1 10.
Time Qed.
End TM840.


Module TM841.
Definition tm := TM_from_str "1RB0LC_1LC0RE_0LD1LD_1LA1LB_0RF1RA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_0LD1LD_1LE1LB_1RB0LC_0RA1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM841.


Module TM842.
Definition tm := TM_from_str "1LB---_1RC1LB_0LB0RD_1RE1LC_1RC0RF_0RC1RA".
Definition tm' := TM_from_str "1RB1LA_0LA0RC_1RD1LB_1RB0RE_0RB1RF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 1 3.
Time Qed.
End TM842.


Module TM843.
Definition tm := TM_from_str "1RB---_1LC1RA_1RD1LC_1LF1RE_1RC0RD_1RB0LF".
Definition tm' := TM_from_str "1RB0LA_1LC1RF_1RD1LC_1LA1RE_1RC0RD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM843.


Module TM844.
Definition tm := TM_from_str "1RB1RA_0LC0RA_---1LD_1RE0LF_1RB1LE_1LD0LB".
Definition tm' := TM_from_str "1RB1LA_0LC0RE_---1LD_1RA0LF_1RB1RE_1LD0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM844.


Module TM845.
Definition tm := TM_from_str "1RB---_1LC0RB_0LD1RB_0RA1LE_0LF0LA_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LD1RB_0RF1LE_0LA0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM845.


Module TM846.
Definition tm := TM_from_str "1RB1LC_1RC---_1LD0RC_1LE0RA_0LF1LA_1RB0LA".
Definition tm' := TM_from_str "1RB0LE_1RC---_1LD0RC_1LF0RE_1RB1LC_0LA1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM846.


Module TM847.
Definition tm := TM_from_str "1LB0RC_1RA0LE_1RD1RB_0LC0RF_1LB0LA_0RA---".
Definition tm' := TM_from_str "1RB1RC_0LA0RF_1RD0LE_1LC0RA_1LC0LD_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCABEF") 365 364.
Time Qed.
End TM847.


Module TM848.
Definition tm := TM_from_str "1LB0RA_0RB1LC_0RD0LD_1RA1RE_0LC1RF_1RD---".
Definition tm' := TM_from_str "1RB1RE_1LC0RB_0RC1LD_0RA0LA_0LD1RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 8 1.
Time Qed.
End TM848.


Module TM849.
Definition tm := TM_from_str "1LB1LE_1RC---_1RD0RB_0LA1LF_1RF1LE_1RC0LD".
Definition tm' := TM_from_str "1RB0RF_0LC1LE_1LF1LD_1RE1LD_1RA0LB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 2 7.
Time Qed.
End TM849.


Module TM850.
Definition tm := TM_from_str "1RB0LC_1RC0RA_0LD0RC_1LA1LE_1RA0LF_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RF_0LD0RC_1LF1LE_1RF0LA_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM850.


Module TM851.
Definition tm := TM_from_str "1LB0RA_1LC1LC_0RD---_1LE1RD_1RA1LF_1LD0LE".
Definition tm' := TM_from_str "1RB1LF_1LC0RB_1LD1LD_0RE---_1LA1RE_1LE0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 2 3.
Time Qed.
End TM851.


Module TM852.
Definition tm := TM_from_str "1LB0LE_0RC0LE_1RD1RC_0RE0RB_1RF1LA_0LE---".
Definition tm' := TM_from_str "1RB1RA_0RC0RF_1RD1LE_0LC---_1LF0LC_0RA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 10 9.
Time Qed.
End TM852.


Module TM853.
Definition tm := TM_from_str "1RB---_1LC0RE_1RD0LC_0LB0RF_1LD1RD_1RB1RA".
Definition tm' := TM_from_str "1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM853.


Module TM854.
Definition tm := TM_from_str "1LB0LC_1RC1LE_1LA1RD_0RC0RA_1LF0RC_---0LD".
Definition tm' := TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_1LF0RB_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 11 1.
Time Qed.
End TM854.


Module TM855.
Definition tm := TM_from_str "1LB1RE_0LC0RC_1RD1LF_0RA---_0RA0LB_0LE1LB".
Definition tm' := TM_from_str "1RB1LE_0RC---_1LD1RF_0LA0RA_0LF1LD_0RC0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 20 30.
Time Qed.
End TM855.


Module TM856.
Definition tm := TM_from_str "1LB1RA_1LC1LE_1RD1LC_1LA0RA_1LF0LC_---0LB".
Definition tm' := TM_from_str "1RB1LA_1LC0RC_1LD1RC_1LA1LE_1LF0LA_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 1381 1491.
Time Qed.
End TM856.


Module TM857.
Definition tm := TM_from_str "1LB0RD_1LC0LA_1RA0LB_0RF1RE_0LC---_0RC0RD".
Definition tm' := TM_from_str "1RB0LC_1LC0RD_1LA0LB_0RF1RE_0LA---_0RA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 6982 6735.
Time Qed.
End TM857.


Module TM858.
Definition tm := TM_from_str "1RB---_1LC0RF_1LD0LD_1LE1LB_1RB0LC_1RE0RA".
Definition tm' := TM_from_str "1RB0LC_1LC0RE_1LD0LD_1LA1LB_1RA0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM858.


Module TM859.
Definition tm := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LE_0LC0RB_0LD1LE".
Definition tm' := TM_from_str "1RB1LE_0RC0LF_1LD0RF_0LA---_0LB1LF_0LA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 23 33.
Time Qed.
End TM859.


Module TM860.
Definition tm := TM_from_str "1RB1LE_1RC---_1RD1LD_1LE1RA_0LF0RA_0RA0LE".
Definition tm' := TM_from_str "1RB---_1RC1LC_1LD1RE_0LF0RE_1RA1LD_0RE0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 15 4.
Time Qed.
End TM860.


Module TM861.
Definition tm := TM_from_str "1RB0LD_1RC1RE_1LA0RB_0LA1LC_1RC1RF_1RB---".
Definition tm' := TM_from_str "1RB---_1RC1RF_1LD0RB_1RB0LE_0LD1LC_1RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM861.


Module TM862.
Definition tm := TM_from_str "1LB0RB_1RA0LC_1RD0LF_1RE---_1RF1RA_1LB0RD".
Definition tm' := TM_from_str "1RB---_1RC1RF_1LD0RA_1RF0LE_1RA0LC_1LD0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 955 1198.
Time Qed.
End TM862.


Module TM863.
Definition tm := TM_from_str "1RB---_0RC0RA_1RD0LF_0RE0LF_1RF0RB_1LD1LA".
Definition tm' := TM_from_str "1RB0RD_1LC1LF_0RA0LB_0RE0RF_1RC0LB_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDECAB") 28 15.
Time Qed.
End TM863.


Module TM864.
Definition tm := TM_from_str "1LB1LF_1RC0LE_0RA1RD_0LB1RC_---1LF_0RD1LB".
Definition tm' := TM_from_str "1RB0LE_0RC1RD_1LA1LF_0LA1RB_---1LF_0RD1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 8 1.
Time Qed.
End TM864.


Module TM865.
Definition tm := TM_from_str "1RB1LF_1LC1RB_---1RD_1LE0RE_1RF0LD_1LA1LC".
Definition tm' := TM_from_str "1RB0LF_1LC1LE_1RD1LB_1LE1RD_---1RF_1LA0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 47 37.
Time Qed.
End TM865.


Module TM866.
Definition tm := TM_from_str "1LB0LE_1LC1LB_1RD1RC_0LA0RD_1LF1LA_0RD---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_0RB---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 1 8.
Time Qed.
End TM866.


Module TM867.
Definition tm := TM_from_str "1LB0RA_1RC0LD_1RC1RA_1RE1LE_1LA0LF_---0LC".
Definition tm' := TM_from_str "1RB1LB_1LC0LF_1LD0RC_1RE0LA_1RE1RC_---0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 1 5.
Time Qed.
End TM867.


Module TM868.
Definition tm := TM_from_str "1LB1LE_1RC0LA_1RE1RD_0RC0RF_0LB0RA_1LE---".
Definition tm' := TM_from_str "1RB1RE_0LC0RD_1RA0LD_1LC1LB_0RA0RF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCAEBF") 1 4.
Time Qed.
End TM868.


Module TM869.
Definition tm := TM_from_str "1RB0RB_0LC1RB_1RE0LD_0RE1LF_1RA---_1RA1LC".
Definition tm' := TM_from_str "1RB1LD_1RC0RC_0LD1RC_1RF0LE_0RF1LA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 5 1.
Time Qed.
End TM869.


Module TM870.
Definition tm := TM_from_str "1RB0LE_1RC0LB_1RD0RE_1LA0RF_0LA1LB_0RD---".
Definition tm' := TM_from_str "1RB0LA_1RC0RE_1LD0RF_1RA0LE_0LD1LA_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 535 559.
Time Qed.
End TM870.


Module TM871.
Definition tm := TM_from_str "1LB0LF_1LC---_0RD1LA_0RE0LC_1LA1RE_1RC1LF".
Definition tm' := TM_from_str "1RB1LA_0RC1LE_0RD0LB_1LE1RD_1LF0LA_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 12 1.
Time Qed.
End TM871.


Module TM872.
Definition tm := TM_from_str "1RB1RA_1RC---_1LD0RF_1RA0LE_0LD1RC_1RA0RE".
Definition tm' := TM_from_str "1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 15 9.
Time Qed.
End TM872.


Module TM873.
Definition tm := TM_from_str "1RB0RF_0RC0RA_1RD0LC_0LE---_0LF1LE_1RF1RB".
Definition tm' := TM_from_str "1RB0LA_0LC---_0LD1LC_1RD1RE_0RA0RF_1RE0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEABCD") 49 35.
Time Qed.
End TM873.


Module TM874.
Definition tm := TM_from_str "1LB0LF_1RC0LE_1LB0RD_1RC0RD_1LA1LC_0LB---".
Definition tm' := TM_from_str "1RB0LC_1LA0RE_1LD1LB_1LA0LF_1RB0RE_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 14 21.
Time Qed.
End TM874.


Module TM875.
Definition tm := TM_from_str "1LB0RE_1RC0LD_1LB0RB_1RE0LA_1RF---_1RA1RC".
Definition tm' := TM_from_str "1RB---_1RC1RF_1LD0RA_1RF0LE_1RA0LC_1LD0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFEAB") 955 1198.
Time Qed.
End TM875.


Module TM876.
Definition tm := TM_from_str "1RB1LE_1RC0RF_1RD0RC_0LE0LA_1LF0LA_---1RB".
Definition tm' := TM_from_str "1RB0RA_0LC0LD_1LF0LD_1RE1LC_1RA0RF_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM876.


Module TM877.
Definition tm := TM_from_str "1RB1RB_1RC1LB_1LD1RE_1LA0LD_1RF0RC_1RB---".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1RB1RB_1RA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM877.


Module TM878.
Definition tm := TM_from_str "1RB---_0RC0LD_1LD1RB_0LE0RE_1RB1LF_0LB1LA".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD1RB_0LA0RA_0LB1LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM878.


Module TM879.
Definition tm := TM_from_str "1LB1LF_0RC1LA_1RA0RD_0LC0RE_---1RC_0LB0LA".
Definition tm' := TM_from_str "1RB0RD_1LC1LF_0RA1LB_0LA0RE_---1RA_0LC0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 5 1.
Time Qed.
End TM879.


Module TM880.
Definition tm := TM_from_str "1RB---_1RC1LE_1LD0RF_1RB1LD_1RF0LD_0LA0RE".
Definition tm' := TM_from_str "1RB1LA_1RC1LD_1LA0RE_1RE0LA_0LF0RD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM880.


Module TM881.
Definition tm := TM_from_str "1LB---_1LC0LB_0RC0RD_1RF1RE_0LB1RC_1LF1LA".
Definition tm' := TM_from_str "1RB1RF_1LB1LC_1LD---_1LE0LD_0RE0RA_0LD1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEAFB") 11 1.
Time Qed.
End TM881.


Module TM882.
Definition tm := TM_from_str "1RB0LF_0LC1LD_0LA0RD_1RE0LC_1LA1RB_1LD---".
Definition tm' := TM_from_str "1RB0LF_1LC1RE_1RE0LD_1LA---_0LF1LA_0LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEFABD") 4 1.
Time Qed.
End TM882.


Module TM883.
Definition tm := TM_from_str "1LB---_0LC0RE_1LD0RF_1RB0LF_1RC0RA_0RB0LF".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEBCAD") 1 4.
Time Qed.
End TM883.


Module TM884.
Definition tm := TM_from_str "1RB0LC_1RC0RA_0LD1LA_0LF1LE_1RA0LF_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RF_0LD1LF_0LA1LE_1RF0LA_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM884.


Module TM885.
Definition tm := TM_from_str "1RB---_1LC1RB_0RB0LD_1LE1RC_1RB0LF_0LC1LA".
Definition tm' := TM_from_str "1RB0LE_1LC1RB_0RB0LD_1LA1RC_0LC1LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM885.


Module TM886.
Definition tm := TM_from_str "1LB1LE_0RC0LD_1LD1RC_0LA1RB_0LB0LF_1RC---".
Definition tm' := TM_from_str "1RB---_1LC1RB_0LE1RD_0RB0LC_1LD1LF_0LD0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDBCFA") 3 1.
Time Qed.
End TM886.


Module TM887.
Definition tm := TM_from_str "1RB1LA_1LC0RC_1LD1RC_1RB1LE_1LF0LA_---1LD".
Definition tm' := TM_from_str "1RB1LD_1LC0RC_1LA1RC_1LF0LE_1RB1LE_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM887.


Module TM888.
Definition tm := TM_from_str "1RB0RA_1LC1RE_1RA1LD_0LB0LF_0RD0RC_0RD---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RF_0LC0LE_0RD---_0RD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADFE") 3 6.
Time Qed.
End TM888.


Module TM889.
Definition tm := TM_from_str "1LB---_0RC1LD_1RD0RC_1LE0RF_0LF0LD_1RC0LA".
Definition tm' := TM_from_str "1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 4 1.
Time Qed.
End TM889.


Module TM890.
Definition tm := TM_from_str "1LB1LA_0RC0RE_1LD0RD_1RC1LE_0LA1RF_---1RD".
Definition tm' := TM_from_str "1RB1LC_1LA0RA_0LD1RF_1LE1LD_0RB0RC_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBACF") 4 1.
Time Qed.
End TM890.


Module TM891.
Definition tm := TM_from_str "1LB1RA_1RC0LA_0LB1RD_1RE0RF_0RB0RD_---1RE".
Definition tm' := TM_from_str "1RB0LC_0LA1RD_1LA1RC_1RE0RF_0RA0RD_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 4.
Time Qed.
End TM891.


Module TM892.
Definition tm := TM_from_str "1LB0RF_1RC0LD_1RA1RC_---0LE_1RA1LE_1RB1RC".
Definition tm' := TM_from_str "1RB1RC_1RC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 3 2.
Time Qed.
End TM892.


Module TM893.
Definition tm := TM_from_str "1LB---_0LC0LB_1RC0RD_1LB1RE_0LB0RF_1RA1RD".
Definition tm' := TM_from_str "1RB1RE_1LC---_0LD0LC_1RD0RE_1LC1RF_0LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 39 45.
Time Qed.
End TM893.


Module TM894.
Definition tm := TM_from_str "1RB0RA_0LB0LC_1LD1LE_1RA1RD_0RA1LF_---0LC".
Definition tm' := TM_from_str "1RB1RA_1RC0RB_0LC0LD_1LA1LE_0RB1LF_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 1 8.
Time Qed.
End TM894.


Module TM895.
Definition tm := TM_from_str "1RB0LC_1RC0RE_1LD1LA_0RB0LD_1RF---_1LD1RA".
Definition tm' := TM_from_str "1RB---_1LC1RF_0RD0LC_1RE0RA_1LC1LF_1RD0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDECAB") 19 5.
Time Qed.
End TM895.


Module TM896.
Definition tm := TM_from_str "1RB1RC_0LA0RF_1RD0LE_1LC0RA_1LC0LE_0RD---".
Definition tm' := TM_from_str "1RB0LC_1LA0RD_1LA0LC_1RE1RA_0LD0RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 364 358.
Time Qed.
End TM896.


Module TM897.
Definition tm := TM_from_str "1RB0RB_1RC1RA_0LD1LE_---1LE_1RB1LF_0LB1LC".
Definition tm' := TM_from_str "1RB1LE_1RC1RF_0LD1LA_---1LA_0LB1LC_1RB0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM897.


Module TM898.
Definition tm := TM_from_str "1LB0LF_0LC0RE_1LD0LA_1RE0LB_1RB0RD_1RC---".
Definition tm' := TM_from_str "1RB0RE_0LC0RA_1LE0LD_1LB0LF_1RA0LB_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 4.
Time Qed.
End TM898.


Module TM899.
Definition tm := TM_from_str "1RB---_1LC0LF_1RE0LD_0LB0RE_1RD0RC_1LD0LA".
Definition tm' := TM_from_str "1RB0RE_0LC0RA_1LE0LD_1LB0LF_1RA0LB_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCEBAD") 93 70.
Time Qed.
End TM899.


Module TM900.
Definition tm := TM_from_str "1RB1LA_1LC1RE_1LD1RC_1RB0LA_1RF0RC_---0LA".
Definition tm' := TM_from_str "1RB0LD_1LC1RE_1LA1RC_1RB1LD_1RF0RC_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM900.


Module TM901.
Definition tm := TM_from_str "1LB0RF_0LC0LA_1RD1RA_1RE0RC_0LA1RD_0RE---".
Definition tm' := TM_from_str "1RB0RF_0LC1RA_1LE0RD_0RB---_0LF0LC_1RA1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEFABD") 1 6.
Time Qed.
End TM901.


Module TM902.
Definition tm := TM_from_str "1RB1RF_1RC---_1LD1LC_1RA1LE_0RF0LE_0RD1RA".
Definition tm' := TM_from_str "1RB---_1LC1LB_1RF1LD_0RE0LD_0RC1RF_1RA1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 7 2.
Time Qed.
End TM902.


Module TM903.
Definition tm := TM_from_str "1RB0LE_1RC0RC_1LD1RC_1LF1LA_1RB1LE_---0LC".
Definition tm' := TM_from_str "1RB1LA_1RC0RC_1LD1RC_1LF1LE_1RB0LA_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM903.


Module TM904.
Definition tm := TM_from_str "1RB0RC_1LC1RB_---0LD_0RA0LE_1RF1LF_1RA1LD".
Definition tm' := TM_from_str "1RB1LE_1RC0RD_1LD1RC_---0LE_0RB0LF_1RA1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 6 2.
Time Qed.
End TM904.


Module TM905.
Definition tm := TM_from_str "1RB---_0LC0RF_1LA0LD_1LE0RC_1LB1LD_1RB1RF".
Definition tm' := TM_from_str "1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM905.


Module TM906.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RF_1LC1LF_0LB---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM906.


Module TM907.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1LD0LD_1RA0RE_1RD0RF_1LE---".
Definition tm' := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 9 9.
Time Qed.
End TM907.


Module TM908.
Definition tm := TM_from_str "1RB0LC_1LA1RB_1RA0LD_1RE1LD_---0RF_1RB0RB".
Definition tm' := TM_from_str "1RB0RB_1LC1RB_1RB0LD_1RC0LE_1RF1LE_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM908.


Module TM909.
Definition tm := TM_from_str "1LB1RA_1LC0LB_0RC1RD_0RE0LD_1RA0RF_1RE---".
Definition tm' := TM_from_str "1RB0RF_1LC1RB_1LD0LC_0RD1RE_0RA0LE_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 8 1.
Time Qed.
End TM909.


Module TM910.
Definition tm := TM_from_str "1RB1LD_1RC0RC_1LD0RB_0LF1LE_1RE0LA_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RC_1LD0RB_0LA1LE_1RE0LF_1RB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM910.


Module TM911.
Definition tm := TM_from_str "1LB1LD_0RC---_0LD0RC_1LE0LA_1LF1LE_1RC1RF".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_0RB---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 1 4.
Time Qed.
End TM911.


Module TM912.
Definition tm := TM_from_str "1LB1RA_1RA0LC_1RB0LD_1RE1LD_1LF0RF_---0RA".
Definition tm' := TM_from_str "1RB0LD_1RC0LA_1LB1RC_1RE1LD_1LF0RF_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBADEF") 3 2.
Time Qed.
End TM912.


Module TM913.
Definition tm := TM_from_str "1RB---_1LC0RF_0RE0LD_1LE1LA_1RB0LF_0LC0RF".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM913.


Module TM914.
Definition tm := TM_from_str "1RB0LC_1LC1RE_---1LD_0RB0LF_1LA0RE_1RB0LF".
Definition tm' := TM_from_str "1RB0LA_1LC1RE_---1LD_0RB0LA_1LF0RE_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM914.


Module TM915.
Definition tm := TM_from_str "1RB1LE_0RC0LD_1LD0LF_0LA0RD_0LB1LC_1RC---".
Definition tm' := TM_from_str "1RB---_1LC0LA_0LD0RC_1RE1LF_0RB0LC_0LE1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 1 6.
Time Qed.
End TM915.


Module TM916.
Definition tm := TM_from_str "1LB0LC_1LC0LF_1RD1LA_0RE0RD_1LE0LC_---0RB".
Definition tm' := TM_from_str "1RB1LD_0RC0RB_1LC0LA_1LE0LA_1LA0LF_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 42 98.
Time Qed.
End TM916.


Module TM917.
Definition tm := TM_from_str "1LB1LE_0RC1LA_0LA0RD_1RC0LF_0LB---_1RF1LD".
Definition tm' := TM_from_str "1RB0LF_0LC0RA_1LE1LD_0LE---_0RB1LC_1RF1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEBADF") 4 1.
Time Qed.
End TM917.


Module TM918.
Definition tm := TM_from_str "1RB0RF_1LC1RE_1LD0LC_0LE0LE_1RA1LD_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1RE_1LD0LC_0LE0LE_1RF1LD_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM918.


Module TM919.
Definition tm := TM_from_str "1RB---_1RC1LB_0LB0RD_1RE1LC_1RC0RF_0RC1RA".
Definition tm' := TM_from_str "1RB1LC_1RC0RE_0LD0RA_1RC1LD_0RC1RF_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDCABE") 2 2.
Time Qed.
End TM919.


Module TM920.
Definition tm := TM_from_str "1RB0LA_0RC0RA_1LD1RE_1LA0RA_---1RF_1RB0RD".
Definition tm' := TM_from_str "1RB0RD_0RC0RE_1LD1RF_1LE0RE_1RB0LE_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM920.


Module TM921.
Definition tm := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_1RB---_1LA0RD".
Definition tm' := TM_from_str "1RB---_0LC0RB_1LE0LD_1LA1LC_1LF0RD_1RB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM921.


Module TM922.
Definition tm := TM_from_str "1RB0LC_1LA0RE_1LD1LA_1RE0RA_1RB1RF_1RE---".
Definition tm' := TM_from_str "1RB1RF_1LC0RA_1RB0LD_1LE1LC_1RA0RC_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM922.


Module TM923.
Definition tm := TM_from_str "1LB---_1RC1RB_1LD1LC_0RE0LD_1RB0RF_1RA1RE".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 757 750.
Time Qed.
End TM923.


Module TM924.
Definition tm := TM_from_str "1LB---_1RC1RD_1LE0RD_0LC0RF_0LA1LA_1LC0RD".
Definition tm' := TM_from_str "1RB1RE_1LC0RE_0LD1LD_1LA---_0LB0RF_1LB0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 4 1.
Time Qed.
End TM924.


Module TM925.
Definition tm := TM_from_str "1LB1RA_0RC0LB_1LA0LD_1RE0RD_1RC0RF_---1RD".
Definition tm' := TM_from_str "1RB0RA_1RC0RF_1LD0LA_1LE1RD_0RC0LE_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECABF") 4 1.
Time Qed.
End TM925.


Module TM926.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_0RE---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC0RF_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM926.


Module TM927.
Definition tm := TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_0RE---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 4 7.
Time Qed.
End TM927.


Module TM928.
Definition tm := TM_from_str "1RB0RE_0LC1LD_1RA1LB_0RA1LB_---1RF_0LC1RA".
Definition tm' := TM_from_str "1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0LA1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 2 9.
Time Qed.
End TM928.


Module TM929.
Definition tm := TM_from_str "1LB0RC_1RC1LE_1RD0LA_0LB0RF_1LA---_0RD0RC".
Definition tm' := TM_from_str "1RB0LE_0LC0RF_1RA1LD_1LE---_1LC0RA_0RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECABDF") 5 1.
Time Qed.
End TM929.


Module TM930.
Definition tm := TM_from_str "1LB---_1LC0RB_0LD1LE_0RE1LF_1RB0LC_0LE1LA".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LD1LA_0RA1LE_0LA1LF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 4 3.
Time Qed.
End TM930.


Module TM931.
Definition tm := TM_from_str "1LB---_0LC0RD_1RB1LC_1RE1LB_1LB0RF_0RB0RA".
Definition tm' := TM_from_str "1RB1LC_1LC0RE_0LD0RA_1RC1LD_0RC0RF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 1 4.
Time Qed.
End TM931.


Module TM932.
Definition tm := TM_from_str "1LB1RF_1RC0LA_0RD0LD_1RA0RE_1RB0RA_0LB---".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_0RD0LD_1RE0RA_1LB1RF_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 5 1.
Time Qed.
End TM932.


Module TM933.
Definition tm := TM_from_str "1LB0RF_1LC0RE_0LD1LE_1RA0RE_0LC0RA_---1RE".
Definition tm' := TM_from_str "1RB0RD_1LC0RF_1LE0RD_0LE0RB_0LA1LD_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEADF") 1 5.
Time Qed.
End TM933.


Module TM934.
Definition tm := TM_from_str "1RB0LD_0RC0RB_1LD0RA_1LE---_0LF1LD_1RB1LE".
Definition tm' := TM_from_str "1RB1LE_0RC0RB_1LD0RF_1LE---_0LA1LD_1RB0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM934.


Module TM935.
Definition tm := TM_from_str "1LB1RE_1RC1LA_1LD0RC_0LA0RD_1RF0RE_---0LD".
Definition tm' := TM_from_str "1RB1LD_1LC0RB_0LD0RC_1LA1RE_1RF0RE_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 6.
Time Qed.
End TM935.


Module TM936.
Definition tm := TM_from_str "1RB---_0RC0LC_1LD0RF_1LE1LA_0LF1LC_1RB0LD".
Definition tm' := TM_from_str "1RB0LD_0RC0LC_1LD0RA_1LE1LF_0LA1LC_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM936.


Module TM937.
Definition tm := TM_from_str "1RB1LE_0RC0LD_1LD1RC_0LA1RB_0LB1LF_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_1RB1LF_0LB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM937.


Module TM938.
Definition tm := TM_from_str "1RB---_0LC1RE_0LD1LC_1RA0LF_1RF1RD_1RB0RE".
Definition tm' := TM_from_str "1RB0RF_0LC1RF_0LD1LC_1RE0LA_1RB---_1RA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM938.


Module TM939.
Definition tm := TM_from_str "1RB0LD_1RC1RF_1RD---_1LA1LE_1LD1LD_0RA0RF".
Definition tm' := TM_from_str "1RB1RF_1RC---_1LD1LE_1RA0LC_1LC1LC_0RD0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 7 6.
Time Qed.
End TM939.


Module TM940.
Definition tm := TM_from_str "1LB1RE_1RC---_1RD1LC_1LF1RE_1RB0RD_0RA0LF".
Definition tm' := TM_from_str "1RB1LA_1LC1RF_0RD0LC_1LE1RF_1RA---_1RE0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABFC") 10 12.
Time Qed.
End TM940.


Module TM941.
Definition tm := TM_from_str "1LB0LE_0RC1RE_1RE1RD_1LE0RF_1LA0RB_1RE---".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA1RB_1LB0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEBF") 6 1.
Time Qed.
End TM941.


Module TM942.
Definition tm := TM_from_str "1RB---_0LB0RC_1RD0LF_1RE1RA_1LC0LD_0LE0LF".
Definition tm' := TM_from_str "1RB0LD_1RC1RE_1LA0LB_0LC0LD_1RF---_0LF0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 4 1.
Time Qed.
End TM942.


Module TM943.
Definition tm := TM_from_str "1RB0LE_1RC0RD_0LD1RA_---0LE_0RA1LF_1RC1LD".
Definition tm' := TM_from_str "1RB1LC_0LC1RE_---0LD_0RE1LA_1RF0LD_1RB0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 1 5.
Time Qed.
End TM943.


Module TM944.
Definition tm := TM_from_str "1LB1RA_1RC0LE_---0RD_1LA1RF_1RD1LE_0RB0RA".
Definition tm' := TM_from_str "1RB1LA_1LC1RE_1LD1RC_1RF0LA_0RD0RC_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFBAE") 11 14.
Time Qed.
End TM944.


Module TM945.
Definition tm := TM_from_str "1RB0RA_1LC1RE_1RA1LD_0LB0LE_0RD0RF_1RA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RE_0LC0LE_0RD0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 3 6.
Time Qed.
End TM945.


Module TM946.
Definition tm := TM_from_str "1RB0RB_1LC0RA_1RB0LD_1LE0LD_1LB0LF_0LD---".
Definition tm' := TM_from_str "1RB0LC_1LA0RE_1LD0LC_1LB0LF_1RB0RB_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM946.


Module TM947.
Definition tm := TM_from_str "1LB1LC_1RA0LF_1RD1RC_1LE0RC_---0LA_0LE1RD".
Definition tm' := TM_from_str "1RB1RA_1LC0RA_---0LD_1LE1LA_1RD0LF_0LC1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 9 6.
Time Qed.
End TM947.


Module TM948.
Definition tm := TM_from_str "1LB0LF_0RC0LC_1LE0RD_1RB1RD_0LF---_0LA0RC".
Definition tm' := TM_from_str "1RB1RA_0RC0LC_1LD0RA_0LE---_0LF0RC_1LB0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 4 1.
Time Qed.
End TM948.


Module TM949.
Definition tm := TM_from_str "1LB1RA_0RA0LC_1LD1RB_0RC0LE_0LB0LF_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LB1RC_1LE1RB_0RD0LF_0LB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 9 4.
Time Qed.
End TM949.


Module TM950.
Definition tm := TM_from_str "1LB1RE_0RC1LF_0LA1RD_0RE0LB_1RB---_0LD0LC".
Definition tm' := TM_from_str "1RB---_0RC1LE_0LD1RF_1LB1RA_0LF0LC_0RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCFAE") 12 10.
Time Qed.
End TM950.


Module TM951.
Definition tm := TM_from_str "1LB1RD_0LC1LB_1LD0RF_1RA1RE_---1LF_1RC0RB".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_1RF1RD_---1LA_0LB1LE_1LE1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEBCDA") 1 6.
Time Qed.
End TM951.


Module TM952.
Definition tm := TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RF_1RB1RD_---0RB".
Definition tm' := TM_from_str "1RB1RD_0RC1LD_1LD1RA_0LE0RF_1RB0LB_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM952.


Module TM953.
Definition tm := TM_from_str "1RB0RA_0LB0LC_1RD1LE_1RA0RF_1LF0LC_---1RD".
Definition tm' := TM_from_str "1RB1LE_1RC0RF_1RD0RC_0LD0LA_1LF0LA_---1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 4 1.
Time Qed.
End TM953.


Module TM954.
Definition tm := TM_from_str "1LB0RE_1RC0RD_1LD1RB_1RA0LE_1LC0RF_0LA---".
Definition tm' := TM_from_str "1RB0LD_1LC0RD_1RE0RA_1LE0RF_1LA1RC_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEADF") 52 53.
Time Qed.
End TM954.


Module TM955.
Definition tm := TM_from_str "1RB0LC_1RC0RE_1LD0LB_1LA0LD_1RA0RF_0RB---".
Definition tm' := TM_from_str "1RB0RF_1RC0LD_1RD0RA_1LE0LC_1LB0LE_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 10 14.
Time Qed.
End TM955.


Module TM956.
Definition tm := TM_from_str "1LB1LF_1RC---_1RE0RD_1RC0LE_0LA1LD_1RD0LB".
Definition tm' := TM_from_str "1RB0RE_0LC1LE_1LF1LD_1RE0LF_1RA0LB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFAEBD") 2 7.
Time Qed.
End TM956.


Module TM957.
Definition tm := TM_from_str "1RB1LC_1RC1RB_1RD1LF_1LE0RB_0RD0LE_---1LA".
Definition tm' := TM_from_str "1RB1LE_1LC0RD_0RB0LC_1RA1RD_---1LF_1RD1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDABCE") 1 8.
Time Qed.
End TM957.


Module TM958.
Definition tm := TM_from_str "1RB---_1RC1LC_1LC1RD_1RA1LE_0LF0RD_0RD0LE".
Definition tm' := TM_from_str "1RB1LE_1RC---_1RD1LD_1LD1RA_0LF0RA_0RA0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 4 15.
Time Qed.
End TM958.


Module TM959.
Definition tm := TM_from_str "1LB0RF_1RC1LA_1RE1LD_0LB0LB_0LC0RE_---1RA".
Definition tm' := TM_from_str "1RB1LC_0LA0RB_0LD0LD_1RA1LE_1LD0RF_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDACBF") 4 4.
Time Qed.
End TM959.


Module TM960.
Definition tm := TM_from_str "1RB---_0LC1RF_1RD1LD_0LE0RB_1LB0RA_0RD0RE".
Definition tm' := TM_from_str "1RB1LB_0LC0RE_1LE0RD_1RE---_0LA1RF_0RB0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM960.


Module TM961.
Definition tm := TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RB0RE_0RB0RF_---0LD".
Definition tm' := TM_from_str "1RB0RE_0RC1RA_1LC0LD_1RB1LD_0RB0RF_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM961.


Module TM962.
Definition tm := TM_from_str "1RB1RA_1LC0RA_1LD1LC_1RE0LB_1RB0RF_---0RD".
Definition tm' := TM_from_str "1RB0RE_1LC0RF_1LD1LC_1RA0LB_---0RD_1RB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM962.


Module TM963.
Definition tm := TM_from_str "1RB0RA_1LC0LB_1RE0LD_1LE0LF_1LA0RC_1LA---".
Definition tm' := TM_from_str "1RB0LE_1LC0RA_1RD0RC_1LA0LD_1LB0LF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEBF") 1 5.
Time Qed.
End TM963.


Module TM964.
Definition tm := TM_from_str "1RB1RA_1LC0RE_---1LD_1RB0LD_0RA1RF_1LA0RC".
Definition tm' := TM_from_str "1RB0LA_1LC0RD_---1LA_0RF1RE_1LF0RC_1RB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM964.


Module TM965.
Definition tm := TM_from_str "1LB0LF_1RC0RE_1RD1LC_1LC0RB_1LA1RE_---0LC".
Definition tm' := TM_from_str "1RB1LA_1LA0RC_1RA0RD_1LE1RD_1LC0LF_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECABDF") 3 2.
Time Qed.
End TM965.


Module TM966.
Definition tm := TM_from_str "1LB1RC_1LC0RE_0LD0RD_1LE0LA_1RB1LF_0RB---".
Definition tm' := TM_from_str "1RB1LF_1LC0RA_0LD0RD_1LA0LE_1LB1RC_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 5.
Time Qed.
End TM966.


Module TM967.
Definition tm := TM_from_str "1LB1RA_1LC1RD_1RA0LE_1LE0RA_1RF0LD_0LD---".
Definition tm' := TM_from_str "1RB0LC_0LC---_1LA0RD_1LE1RD_1LF1RC_1RD0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFCAB") 1 4.
Time Qed.
End TM967.


Module TM968.
Definition tm := TM_from_str "1RB---_1RC0RB_1LD1RF_1RB1LE_0LC0LC_0RE0RA".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RE_0LC0LC_0RD0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM968.


Module TM969.
Definition tm := TM_from_str "1LB1RC_1RC1LA_0LB0RD_0RE0LD_0LB0RF_---0RC".
Definition tm' := TM_from_str "1RB1LC_0LA0RD_1LA1RB_0RE0LD_0LA0RF_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 2 13.
Time Qed.
End TM969.


Module TM970.
Definition tm := TM_from_str "1LB1RE_1RC1LD_1RA0RC_1RB0LA_0RD0RF_1RC---".
Definition tm' := TM_from_str "1RB0LD_1RC1LA_1RD0RC_1LB1RE_0RA0RF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 9 6.
Time Qed.
End TM970.


Module TM971.
Definition tm := TM_from_str "1LB1RE_0LC0RF_1RD1RA_0RA---_0RB1RD_0RA0LA".
Definition tm' := TM_from_str "1RB1RC_0RC---_1LD1RF_0LA0RE_0RC0LC_0RD1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 38 24.
Time Qed.
End TM971.


Module TM972.
Definition tm := TM_from_str "1RB0RF_0LC0RD_1LB1LA_1RE0RC_1RB1RA_---0RC".
Definition tm' := TM_from_str "1RB1RD_0LC0RE_1LB1LD_1RB0RF_1RA0RC_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 1.
Time Qed.
End TM972.


Module TM973.
Definition tm := TM_from_str "1RB0RF_1RC1RC_1RD1RA_1LE0RB_1LC1LA_---0LD".
Definition tm' := TM_from_str "1RB1RD_1LC0RE_1LA1LD_1RE0RF_1RA1RA_---0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 14 8.
Time Qed.
End TM973.


Module TM974.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LF_0RB1RF_1RB---".
Definition tm' := TM_from_str "1RB---_0LC0RD_1RD1LB_0RE0LA_1LB1RF_0RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 3.
Time Qed.
End TM974.


Module TM975.
Definition tm := TM_from_str "1RB0LA_1LC---_1RD1LC_1RA1RE_1RF0RD_1LA1RE".
Definition tm' := TM_from_str "1RB0RF_1LC1RA_1RD0LC_1LE---_1RF1LE_1RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 7 27.
Time Qed.
End TM975.


Module TM976.
Definition tm := TM_from_str "1RB1RF_1LC0RE_1RE0LD_0LC1LB_1RB1RA_0RB---".
Definition tm' := TM_from_str "1RB1RE_1LC0RA_1RA0LD_0LC1LB_1RB1RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM976.


Module TM977.
Definition tm := TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RA0LE_1RF0RB_1RD---".
Definition tm' := TM_from_str "1RB0RE_1RC---_1RD0LA_1RE1LD_1LF1RA_1LC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFCAB") 170 139.
Time Qed.
End TM977.


Module TM978.
Definition tm := TM_from_str "1RB1LE_0RC0LD_1RD0LE_1LB1RF_0RB0LC_1RA---".
Definition tm' := TM_from_str "1RB---_1RC1LF_0RD0LE_1RE0LF_1LC1RA_0RC0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 9 12.
Time Qed.
End TM978.


Module TM979.
Definition tm := TM_from_str "1RB0LA_0RC1LE_0RD1RE_1LA1RF_---1LD_1RB1RD".
Definition tm' := TM_from_str "1RB1RD_0RC1LF_0RD1RF_1LE1RA_1RB0LE_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM979.


Module TM980.
Definition tm := TM_from_str "1LB0RB_1RC0LA_1LE1LD_---1RA_1RF1LC_0LD1RF".
Definition tm' := TM_from_str "1RB1LF_0LC1RB_---1RD_1LE0RE_1RF0LD_1LA1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFCAB") 54 69.
Time Qed.
End TM980.


Module TM981.
Definition tm := TM_from_str "1LB1LF_1RC0LA_0RD1RC_1LE0RB_1LB---_0LA1LD".
Definition tm' := TM_from_str "1RB0LE_0RC1RB_1LD0RA_1LA---_1LA1LF_0LE1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 9 22.
Time Qed.
End TM981.


Module TM982.
Definition tm := TM_from_str "1RB1LA_0LC1RE_1RD1LD_1LA1LF_1RA0RB_---0LB".
Definition tm' := TM_from_str "1RB1LB_1LC1LF_1RD1LC_0LA1RE_1RC0RD_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 4 3.
Time Qed.
End TM982.


Module TM983.
Definition tm := TM_from_str "1LB0LC_1RC0RD_1LA0RB_1RB0LE_1LF---_0LA0LE".
Definition tm' := TM_from_str "1RB0LE_1RC0RA_1LD0RB_1LB0LC_1LF---_0LD0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 5.
Time Qed.
End TM983.


Module TM984.
Definition tm := TM_from_str "1LB1LE_0RC0RF_1RD1RB_1LE---_0LB1LA_0LE1RC".
Definition tm' := TM_from_str "1RB1RE_1LC---_0LE1LD_1LE1LC_0RA0RF_0LC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 22 1.
Time Qed.
End TM984.


Module TM985.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LD_0RB0RF_0LE---".
Definition tm' := TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RB_0RD0RF_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 33 19.
Time Qed.
End TM985.


Module TM986.
Definition tm := TM_from_str "1LB0RB_0RC0LB_0LE0RD_1RA---_1LF1LB_1RC0LF".
Definition tm' := TM_from_str "1RB---_1LC0RC_0RD0LC_0LE0RA_1LF1LC_1RD0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 4 1.
Time Qed.
End TM986.


Module TM987.
Definition tm := TM_from_str "1LB1LE_0LC1RA_1RD0LD_1RB0LA_1LF0RE_1LA---".
Definition tm' := TM_from_str "1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCABEF") 1 6.
Time Qed.
End TM987.


Module TM988.
Definition tm := TM_from_str "1RB1LD_1RC1RB_1LA0LF_1LC1LE_1LA0LA_---0RB".
Definition tm' := TM_from_str "1RB1RA_1LC0LF_1RA1LD_1LB1LE_1LC0LC_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 6 5.
Time Qed.
End TM988.


Module TM989.
Definition tm := TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0LC---".
Definition tm' := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 465 442.
Time Qed.
End TM989.


Module TM990.
Definition tm := TM_from_str "1RB---_1RC1LB_1LD1RF_0RE0LE_1LA0LD_1RA0RC".
Definition tm' := TM_from_str "1RB1LA_1LC1RF_0RD0LD_1LE0LC_1RA---_1RE0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 6 3.
Time Qed.
End TM990.


Module TM991.
Definition tm := TM_from_str "1RB---_1LC1RD_1LD0LC_1RE0LF_1RA0RB_0RB0RA".
Definition tm' := TM_from_str "1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 12510 12287.
Time Qed.
End TM991.


Module TM992.
Definition tm := TM_from_str "1RB---_1LC1RF_0LE0RD_0RB1LC_1RD0LD_0RC1RA".
Definition tm' := TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RB_0RD1RF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDBAE") 49 36.
Time Qed.
End TM992.


Module TM993.
Definition tm := TM_from_str "1LB1LD_1RC1LE_1LA1RC_1LA1RE_0LF0RD_---1LD".
Definition tm' := TM_from_str "1RB1LE_1LC1RB_1LA1LD_1LC1RE_0LF0RD_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 328112 323711.
Time Qed.
End TM993.


Module TM994.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1LC_0RC0RF_0LD---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0RF_1RC1LB_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM994.


Module TM995.
Definition tm := TM_from_str "1RB0RB_1RC0LA_1LD1RA_1RB1LE_0LF1LD_---0LB".
Definition tm' := TM_from_str "1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM995.


Module TM996.
Definition tm := TM_from_str "1LB---_1RC0LE_0RD1RB_1LA0RB_0RD0LF_0LA1LE".
Definition tm' := TM_from_str "1RB0LE_0RC1RA_1LD0RA_1LA---_0RC0LF_0LD1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 9 12.
Time Qed.
End TM996.


Module TM997.
Definition tm := TM_from_str "1RB0RA_1LC1RE_1RA1LD_0LB1RF_0RD0RC_---1LE".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RF_0LC1RE_---1LF_0RD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADFE") 2 7.
Time Qed.
End TM997.


Module TM998.
Definition tm := TM_from_str "1RB---_1LC1LB_1RF1LD_0RE0LD_0RC1RE_1RA1RF".
Definition tm' := TM_from_str "1RB1RA_1RC---_1LD1LC_1RA1LE_0RF0LE_0RD1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 2 7.
Time Qed.
End TM998.


Module TM999.
Definition tm := TM_from_str "1LB1LF_0RC0LA_0LD1RD_0RE---_1RA1RF_1RE0RB".
Definition tm' := TM_from_str "1RB0RD_1RC1RA_1LD1LA_0RE0LC_0LF1RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 35 11.
Time Qed.
End TM999.


Module TM1000.
Definition tm := TM_from_str "1LB---_1RC1LB_0LB0RD_1RE1LC_0LD0RF_0RC1RA".
Definition tm' := TM_from_str "1RB1LC_0LA0RE_0LD0RA_1RC1LD_0RC1RF_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDCABE") 7 6.
Time Qed.
End TM1000.


Module TM1001.
Definition tm := TM_from_str "1RB---_0LC0LB_1RC0RD_1RE0LA_1LB1RF_1RD0RD".
Definition tm' := TM_from_str "1RB0LE_1LC1RF_0LD0LC_1RD0RA_1RC---_1RA0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDABF") 4 1.
Time Qed.
End TM1001.


Module TM1002.
Definition tm := TM_from_str "1LB1RC_0RA0LB_0LC0RD_1LA1RE_1RD0LF_---1LE".
Definition tm' := TM_from_str "1RB0LF_1LC1RA_1LE1RD_0LD0RB_0RC0LE_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEDBAF") 8 2.
Time Qed.
End TM1002.


Module TM1003.
Definition tm := TM_from_str "1LB0RF_1RC0LC_1LE0RD_0RB1RA_1RA0LA_1RD---".
Definition tm' := TM_from_str "1RB0LB_1LC0RE_1RD0LD_1LA0RF_0RA1RD_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 135 217.
Time Qed.
End TM1003.


Module TM1004.
Definition tm := TM_from_str "1LB0RF_1RC0RD_1LD1RB_---1LE_0LA1LE_1RA0LA".
Definition tm' := TM_from_str "1RB0LB_1LC0RA_1RF0RD_---1LE_0LB1LE_1LD1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFDEA") 35 46.
Time Qed.
End TM1004.


Module TM1005.
Definition tm := TM_from_str "1RB0LD_1RC1RD_0LA1LF_0RF1RE_0LA---_1LC0RB".
Definition tm' := TM_from_str "1RB1RD_0LC1LE_1RA0LD_0RE1RF_1LB0RA_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDFE") 6 2.
Time Qed.
End TM1005.


Module TM1006.
Definition tm := TM_from_str "1LB1RD_0LC0LB_1RC0RA_0LB0RE_1RF1RA_1LB---".
Definition tm' := TM_from_str "1RB1RE_1LC---_0LD0LC_1RD0RE_1LC1RF_0LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDFAB") 39 45.
Time Qed.
End TM1006.


Module TM1007.
Definition tm := TM_from_str "1RB---_0LC0RB_1LF1LD_1LE0LE_1LC1RE_1RB0LA".
Definition tm' := TM_from_str "1RB0LF_0LC0RB_1LA1LD_1LE0LE_1LC1RE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1007.


Module TM1008.
Definition tm := TM_from_str "1LB1RD_0LC1LE_1RD1LC_1RA0RE_0RF1LB_---0RE".
Definition tm' := TM_from_str "1RB0RD_1LC1RA_0LF1LD_0RE1LC_---0RD_1RA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFADE") 1 6.
Time Qed.
End TM1008.


Module TM1009.
Definition tm := TM_from_str "1RB0LD_1RC0LE_1LA1RF_---1LE_1RB1LB_1RA0RA".
Definition tm' := TM_from_str "1RB1LB_1RC0LA_1LD1RF_1RB0LE_---1LA_1RD0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 1.
Time Qed.
End TM1009.


Module TM1010.
Definition tm := TM_from_str "1RB1RE_1RC0RC_1RD---_0LD0LE_1RA0LF_0RA1LE".
Definition tm' := TM_from_str "1RB0RB_1RC---_0LC0LD_1RF0LE_0RF1LD_1RA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 1 7.
Time Qed.
End TM1010.


Module TM1011.
Definition tm := TM_from_str "1RB1RD_1LC1LB_0RD0LC_1RE1RA_0RF1LA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1LB_0RD0LC_1RE1RF_0RA1LF_1RB1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1011.


Module TM1012.
Definition tm := TM_from_str "1LB1LA_0RC---_1RD1RC_1RE1LA_1LF1RF_0RB0LF".
Definition tm' := TM_from_str "1RB1LF_1LC1RC_0RD0LC_0RE---_1RA1RE_1LD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 1 4.
Time Qed.
End TM1012.


Module TM1013.
Definition tm := TM_from_str "1LB1RF_0RC0LE_1RA0LD_0LB0RD_1LC---_0LD1LC".
Definition tm' := TM_from_str "1RB0LF_1LC1RE_0RA0LD_1LA---_0LF1LA_0LC0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAFDE") 6 1.
Time Qed.
End TM1013.


Module TM1014.
Definition tm := TM_from_str "1LB1LF_1LC0LA_1LD---_1RE0LF_1RA1RD_0RB0RD".
Definition tm' := TM_from_str "1RB1RE_1LC1LF_1LD0LB_1LE---_1RA0LF_0RC0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 41 32.
Time Qed.
End TM1014.


Module TM1015.
Definition tm := TM_from_str "1RB0LC_1LA1RD_1LB0LB_0LF1LE_1RB0LD_---0RA".
Definition tm' := TM_from_str "1RB0LE_1LC1RE_1RB0LD_1LB0LB_0LF1LA_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM1015.


Module TM1016.
Definition tm := TM_from_str "1LB1RD_1LC1LB_1RA0RF_1RC0RE_1RD1LC_---0LB".
Definition tm' := TM_from_str "1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBAEF") 114 101.
Time Qed.
End TM1016.


Module TM1017.
Definition tm := TM_from_str "1RB0RE_0LC0RA_0LE1LD_0LE0LE_1RA0RF_1LB---".
Definition tm' := TM_from_str "1RB0RF_1RC0RA_0LD0RB_0LA1LE_0LA0LA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 4 5.
Time Qed.
End TM1017.


Module TM1018.
Definition tm := TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_1RC---".
Definition tm' := TM_from_str "1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 1 4.
Time Qed.
End TM1018.


Module TM1019.
Definition tm := TM_from_str "1RB0RF_1RC0RA_0LD0RB_0LA1LE_1RD0LA_1LC---".
Definition tm' := TM_from_str "1RB0RE_0LC0RA_0LE1LD_1RC0LE_1RA0RF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 3 4.
Time Qed.
End TM1019.


Module TM1020.
Definition tm := TM_from_str "1RB0RC_0LA0RE_1RD---_1LE0LF_1RF0LD_1RB1RA".
Definition tm' := TM_from_str "1RB1RC_0LC0RF_1RB0RD_1RE---_1LF0LA_1RA0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM1020.


Module TM1021.
Definition tm := TM_from_str "1LB---_1RC1LB_0LF1RD_1RE0RC_1LF0RA_1RA0LF".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RD0LC_1LE---_1RF1LE_0LC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 19 18.
Time Qed.
End TM1021.


Module TM1022.
Definition tm := TM_from_str "1RB0RB_1LC0RE_0LD1LB_0RA0LE_1RD0LF_0LB---".
Definition tm' := TM_from_str "1RB0LF_0RC0LA_1RD0RD_1LE0RA_0LB1LD_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBAF") 18 27.
Time Qed.
End TM1022.


Module TM1023.
Definition tm := TM_from_str "1LB0RF_1RC1RB_0LD0RC_1LE0LA_1RF1LA_---1LD".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LE0LD_1LA0RF_1RF1LD_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 4.
Time Qed.
End TM1023.


Module TM1024.
Definition tm := TM_from_str "1LB0LB_1RC0LA_1RD0LD_0RF0RE_1RB---_1RA0RF".
Definition tm' := TM_from_str "1RB---_1RC0LF_1RD0LD_0RE0RA_1RF0RE_1LB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 5 1.
Time Qed.
End TM1024.


Module TM1025.
Definition tm := TM_from_str "1LB1LF_0LC0LD_1RD1LB_0RE---_0LB1RF_1LA0RF".
Definition tm' := TM_from_str "1RB1LD_0RC---_0LD1RE_0LA0LB_1LF0RE_1LD1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDABCE") 1 5.
Time Qed.
End TM1025.


Module TM1026.
Definition tm := TM_from_str "1LB1LE_1RC1LD_1RA0RC_1LA0LB_0LF0RD_0RC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_0LF0RD_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 98 123.
Time Qed.
End TM1026.


Module TM1027.
Definition tm := TM_from_str "1RB1LC_1LC1RF_0RE0LD_0LC0RE_1RA---_1RE1LC".
Definition tm' := TM_from_str "1RB---_1RC1LD_1LD1RF_0RA0LE_0LD0RA_1RA1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 2 7.
Time Qed.
End TM1027.


Module TM1028.
Definition tm := TM_from_str "1RB---_1RC1LD_1LD1RF_0RA0LE_0LD0RE_1RA1LD".
Definition tm' := TM_from_str "1RB1LC_1LC1RF_0RE0LD_0LC0RD_1RA---_1RE1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 9 2.
Time Qed.
End TM1028.


Module TM1029.
Definition tm := TM_from_str "1LB0RF_1LC---_1RD0LC_1RF1RE_---0RA_1LD1RC".
Definition tm' := TM_from_str "1RB0LA_1RC1RD_1LB1RA_---0RE_1LF0RC_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABDC") 4 4.
Time Qed.
End TM1029.


Module TM1030.
Definition tm := TM_from_str "1RB1RB_1LC---_1LD1RC_1RF1LE_1LB0LD_0LA0RF".
Definition tm' := TM_from_str "1RB1LF_0LC0RB_1RD1RD_1LE---_1LA1RE_1LD0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEAFB") 1 3.
Time Qed.
End TM1030.


Module TM1031.
Definition tm := TM_from_str "1RB0LD_1RC1RE_1LA0RB_1LE1LE_0LC0LF_0LA---".
Definition tm' := TM_from_str "1RB1RE_1LC0RA_1RA0LD_1LE1LE_0LB0LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 5 4.
Time Qed.
End TM1031.


Module TM1032.
Definition tm := TM_from_str "1RB0LC_1LA0RD_1LB0LA_---1RE_1RF1RB_0LC1LB".
Definition tm' := TM_from_str "1RB1RE_0LC1LE_1LE0LD_1RE0LC_1LD0RF_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECFAB") 1 4.
Time Qed.
End TM1032.


Module TM1033.
Definition tm := TM_from_str "1RB1RE_0LC0RF_1RA1LD_0LB1LC_0RA0RE_1LD---".
Definition tm' := TM_from_str "1RB1LD_1RC1RE_0LA0RF_0LC1LA_0RB0RE_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 30 34.
Time Qed.
End TM1033.


Module TM1034.
Definition tm := TM_from_str "1RB1RA_0LC1RE_1RD1LB_0RA---_1RB0RF_1LF0RC".
Definition tm' := TM_from_str "1RB0RF_0LC1RA_1RD1LB_0RE---_1RB1RE_1LF0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1034.


Module TM1035.
Definition tm := TM_from_str "1LB0RF_1RC1RB_0LD0RC_1LE---_0LA1LA_1RD0LF".
Definition tm' := TM_from_str "1RB0LA_1LC---_0LD1LD_1LE0RA_1RF1RE_0LB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 4 1.
Time Qed.
End TM1035.


Module TM1036.
Definition tm := TM_from_str "1RB1LC_1LC0RE_0LF0LD_1LA1LE_1RB1LA_---0LA".
Definition tm' := TM_from_str "1RB1LE_1LC0RA_0LF0LD_1LE1LA_1RB1LC_---0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1036.


Module TM1037.
Definition tm := TM_from_str "1LB0LF_0RC0LB_1RF1RD_0LD1RE_1LF---_1LA0RB".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA0LD_0LE1RF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEFB") 10 1.
Time Qed.
End TM1037.


Module TM1038.
Definition tm := TM_from_str "1LB0RA_0RC0LC_0LE0LD_1RE---_0RF0LA_1LE1RF".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LB1RC_1LE0RD_0RF0LF_0LB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 4 1.
Time Qed.
End TM1038.


Module TM1039.
Definition tm := TM_from_str "1LB0LD_1LC1LF_1RD---_1RE1LA_0RF0RB_0RA0LC".
Definition tm' := TM_from_str "1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 179 150.
Time Qed.
End TM1039.


Module TM1040.
Definition tm := TM_from_str "1LB0RC_1RC0LE_0RE1RD_1RA1RB_1LA0RF_0RB---".
Definition tm' := TM_from_str "1RB0LC_0RC1RE_1LD0RF_1LA0RB_1RD1RA_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 9 2.
Time Qed.
End TM1040.


Module TM1041.
Definition tm := TM_from_str "1RB1RE_0LC0RC_0RE0RD_1RE---_1LF0RA_0LA0LE".
Definition tm' := TM_from_str "1RB---_1LC0RD_0LD0LB_1RE1RB_0LF0RF_0RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 4 1.
Time Qed.
End TM1041.


Module TM1042.
Definition tm := TM_from_str "1LB0RB_0RC0LE_0LE0RD_1RA---_1LF0LA_1RC0LE".
Definition tm' := TM_from_str "1RB---_1LC0RC_0RF0LD_1LE0LB_1RF0LD_0LD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFADE") 4 1.
Time Qed.
End TM1042.


Module TM1043.
Definition tm := TM_from_str "1RB---_1LC1RA_0LD0RC_1RE0LF_0RB0RB_1LC1LD".
Definition tm' := TM_from_str "1RB0LE_0RC0RC_1LD1RF_0LA0RD_1LD1LA_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 6 1.
Time Qed.
End TM1043.


Module TM1044.
Definition tm := TM_from_str "1RB0LE_1LC0RE_0RF0LD_1LA1LE_0LC0RF_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_0RA0LD_1LE1LF_1RB0LF_0LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1044.


Module TM1045.
Definition tm := TM_from_str "1RB0LC_1RC0RF_0LD1LA_0LF1LE_1RA1LE_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RA_0LD1LF_0LA1LE_1RF1LE_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1045.


Module TM1046.
Definition tm := TM_from_str "1RB1RF_0RC0RB_1LD0RA_0RE0LC_1RC1LF_0LD---".
Definition tm' := TM_from_str "1RB1LD_1LC0RE_0RA0LB_0LC---_1RF1RD_0RB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCAD") 90 174.
Time Qed.
End TM1046.


Module TM1047.
Definition tm := TM_from_str "1LB0LC_1RA---_1RE0RD_1RC1RD_1LF0LD_1LA0LF".
Definition tm' := TM_from_str "1RB1RA_1RC0RA_1LD0LA_1LE0LD_1LF0LB_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBACD") 5 1.
Time Qed.
End TM1047.


Module TM1048.
Definition tm := TM_from_str "1RB0LA_1LC---_1RD1LC_0LA1RE_1RF0RD_1LA0RB".
Definition tm' := TM_from_str "1RB1LA_0LC1RE_1RD0LC_1LA---_1RF0RB_1LC0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 1 4.
Time Qed.
End TM1048.


Module TM1049.
Definition tm := TM_from_str "1RB0LC_1RC0RF_0LD1LA_1RE1LD_1RD0LC_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RA_0LD1LF_1RE1LD_1RD0LC_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1049.


Module TM1050.
Definition tm := TM_from_str "1RB---_1LC0LA_0LD0RC_1RE1LF_0RB0LC_0LE0LA".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0LF_0LA0RD_0LB0LF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 6 1.
Time Qed.
End TM1050.


Module TM1051.
Definition tm := TM_from_str "1LB0LD_1LC1RA_0RD0LE_1LF0RC_1RC---_1LA0LC".
Definition tm' := TM_from_str "1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCAD") 6 1.
Time Qed.
End TM1051.


Module TM1052.
Definition tm := TM_from_str "1LB---_0RC1RB_1LC1RD_1RA0LE_1RB0LF_0RD1LF".
Definition tm' := TM_from_str "1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 6 12.
Time Qed.
End TM1052.


Module TM1053.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_0RA---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM1053.


Module TM1054.
Definition tm := TM_from_str "1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LA---_1RA1RF".
Definition tm' := TM_from_str "1RB1RA_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 479 509.
Time Qed.
End TM1054.


Module TM1055.
Definition tm := TM_from_str "1RB0RA_1LC1RE_1RB1LD_0LE---_0LF1LF_0LB0RA".
Definition tm' := TM_from_str "1RB1LC_1LA1RD_0LD---_0LE1LE_0LB0RF_1RB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBACDE") 1 1.
Time Qed.
End TM1055.


Module TM1056.
Definition tm := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB1RF_1LD---".
Definition tm' := TM_from_str "1RB1RF_1LC1RE_1LD0LC_1RB1LD_1RA0RB_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 1.
Time Qed.
End TM1056.


Module TM1057.
Definition tm := TM_from_str "1LB1RC_1RC0LE_0RA1RD_0LB1RC_---1LF_0RA1LB".
Definition tm' := TM_from_str "1RB0LE_0RC1RD_1LA1RB_0LA1RB_---1LF_0RC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 8 1.
Time Qed.
End TM1057.


Module TM1058.
Definition tm := TM_from_str "1RB0LE_1LC1RD_0LC1LA_0RD0RB_1RB0LF_---0LA".
Definition tm' := TM_from_str "1RB0LF_1LC1RE_0LC1LD_1RB0LA_0RE0RB_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 1.
Time Qed.
End TM1058.


Module TM1059.
Definition tm := TM_from_str "1RB---_1RC0LE_1RD1RF_1LB0LE_1LC1LD_0RB1RA".
Definition tm' := TM_from_str "1RB0LD_1RC1RE_1LA0LD_1LB1LC_0RA1RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 6 14.
Time Qed.
End TM1059.


Module TM1060.
Definition tm := TM_from_str "1RB0RA_1LB1LC_1LD1LD_0LE1LF_1LF0LD_1RA---".
Definition tm' := TM_from_str "1RB---_1RC0RB_1LC1LD_1LE1LE_0LF1LA_1LA0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 4 5.
Time Qed.
End TM1060.


Module TM1061.
Definition tm := TM_from_str "1LB0RA_1RB0RC_1RD0LA_1RE1RF_1LF1RA_---1LC".
Definition tm' := TM_from_str "1RB1RC_1LC1RE_---1LD_1RA0LE_1LF0RE_1RF0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDABC") 1 16.
Time Qed.
End TM1061.


Module TM1062.
Definition tm := TM_from_str "1LB1LE_1RC0LD_1RD1RB_0LE0LF_0LC0LA_---0RB".
Definition tm' := TM_from_str "1RB1RE_0LC0LF_0LA0LD_1LE1LC_1RA0LB_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM1062.


Module TM1063.
Definition tm := TM_from_str "1LB0RC_1RA1LD_0LA0RE_1LA1RF_0RF0LA_---0RC".
Definition tm' := TM_from_str "1RB1LC_1LA0RD_1LB1RF_0LB0RE_0RF0LB_---0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BADCEF") 4 1.
Time Qed.
End TM1063.


Module TM1064.
Definition tm := TM_from_str "1RB1LC_1LA0RE_1LD0LF_0LB0LC_1RB1LE_---1LD".
Definition tm' := TM_from_str "1RB1LA_1LC0RA_1RB1LD_1LE0LF_0LB0LD_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM1064.


Module TM1065.
Definition tm := TM_from_str "1LB1RA_1RA0LC_1RD1LC_1LA1RE_1RF0RA_---0RD".
Definition tm' := TM_from_str "1RB1LA_1LC1RE_1LD1RC_1RC0LA_1RF0RC_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 2 3.
Time Qed.
End TM1065.


Module TM1066.
Definition tm := TM_from_str "1RB1LA_0LC0RE_---1LD_1LA0LF_1RB1RE_1LD0LB".
Definition tm' := TM_from_str "1RB1RA_0LC0RA_---1LD_1LE0LF_1RB1LE_1LD0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1066.


Module TM1067.
Definition tm := TM_from_str "1RB---_1RC1LB_0LB0RD_1RE1LC_0LD0RF_0RC1RA".
Definition tm' := TM_from_str "1RB1LA_0LA0RC_1RD1LB_0LC0RE_0RB1RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 7 7.
Time Qed.
End TM1067.


Module TM1068.
Definition tm := TM_from_str "1RB1RA_1RC1LB_1RD1LA_1LE0RF_0RC0LE_1RB---".
Definition tm' := TM_from_str "1RB---_1RC1LB_1RD1LF_1LE0RA_0RC0LE_1RB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1068.


Module TM1069.
Definition tm := TM_from_str "1LB0RA_0RC1LE_1RA1RD_0LE1RF_0RC0LC_1RC---".
Definition tm' := TM_from_str "1RB1RE_1LC0RB_0RA1LD_0RA0LA_0LD1RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM1069.


Module TM1070.
Definition tm := TM_from_str "1RB1RA_0LC0RB_1LF0LD_0LE1LC_1RF---_1LA0RD".
Definition tm' := TM_from_str "1RB---_1LC0RF_1RD1RC_0LE0RD_1LB0LF_0LA1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 5 1.
Time Qed.
End TM1070.


Module TM1071.
Definition tm := TM_from_str "1LB1RC_0RC0RB_---0LD_1RE1LF_1LA0RE_1LD1RB".
Definition tm' := TM_from_str "1RB1LE_1LC0RB_1LF1RD_---0LA_1LA1RF_0RD0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFDABE") 4 1.
Time Qed.
End TM1071.


Module TM1072.
Definition tm := TM_from_str "1LB0LD_0RC---_1LE1RD_1RC0RF_1LA0LE_1RD1RF".
Definition tm' := TM_from_str "1RB1RA_1RC0RA_1LD1RB_1LE0LD_1LF0LB_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCBDA") 3 1.
Time Qed.
End TM1072.


Module TM1073.
Definition tm := TM_from_str "1RB0RD_0LC0RC_---1LD_1RE1LF_1RA0LF_0LA0RE".
Definition tm' := TM_from_str "1RB0LF_1RC0RE_0LD0RD_---1LE_1RA1LF_0LB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 7 1.
Time Qed.
End TM1073.


Module TM1074.
Definition tm := TM_from_str "1LB0RB_0LC1LF_1RD1LE_0RA0LB_0LD1LA_0RA---".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0RD_0LA1LF_0LB1LC_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 230 86.
Time Qed.
End TM1074.


Module TM1075.
Definition tm := TM_from_str "1LB1RC_1RA0LA_0RD0RC_1RE0LF_0LB---_1LF1LA".
Definition tm' := TM_from_str "1RB0LF_0LC---_1RD0LD_1LC1RE_0RA0RE_1LF1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEABF") 1 4.
Time Qed.
End TM1075.


Module TM1076.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1LB_0RB0RF_0LE---".
Definition tm' := TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RB_0RD0RF_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 31 19.
Time Qed.
End TM1076.


Module TM1077.
Definition tm := TM_from_str "1RB0LC_1RC0RF_1LD0RA_0RE0LD_0LC1LB_0RC---".
Definition tm' := TM_from_str "1RB0RF_1LC0RE_0RD0LC_0LB1LA_1RA0LB_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 84 174.
Time Qed.
End TM1077.


Module TM1078.
Definition tm := TM_from_str "1RB---_0RC0RA_0LD1RF_1LE0RB_1RB0LE_1RD1RF".
Definition tm' := TM_from_str "1RB0LA_0RC0RF_0LD1RE_1LA0RB_1RD1RE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1078.


Module TM1079.
Definition tm := TM_from_str "1LB---_0RC1RD_1LA0RD_0RE1LF_1RB1RA_0LD0LF".
Definition tm' := TM_from_str "1RB1RD_0RC1RE_1LD0RE_1LB---_0RA1LF_0LE0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 5 1.
Time Qed.
End TM1079.


Module TM1080.
Definition tm := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1RB_0LC0RF_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_0RE0LD_1LE1RB_1RB0LF_0LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1080.


Module TM1081.
Definition tm := TM_from_str "1RB1RE_1RC0RA_0LD0LE_1RB1LC_1LD0RF_0RC---".
Definition tm' := TM_from_str "1RB1LC_1RC0RE_0LA0LD_1LA0RF_1RB1RD_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM1081.


Module TM1082.
Definition tm := TM_from_str "1LB1RE_0LC0LB_1RC1LD_0RA0RA_1RF---_1RA0LC".
Definition tm' := TM_from_str "1RB0LD_1LC1RF_0LD0LC_1RD1LE_0RB0RB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 16 19.
Time Qed.
End TM1082.


Module TM1083.
Definition tm := TM_from_str "1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0RB_1LD1LE_1LC1RF_1RB0LE_1RA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1083.


Module TM1084.
Definition tm := TM_from_str "1RB1LA_1RC0LD_0LB0RE_0LA1LB_1RF---_1RD0RE".
Definition tm' := TM_from_str "1RB0RF_0LC1LD_1RD1LC_1RE0LB_0LD0RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBFA") 3 4.
Time Qed.
End TM1084.


Module TM1085.
Definition tm := TM_from_str "1RB0LD_1RC0RC_1LA1RC_0RB0LE_1RA1LF_---1LD".
Definition tm' := TM_from_str "1RB0RB_1LC1RB_1RA0LD_0RA0LE_1RC1LF_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 2 6.
Time Qed.
End TM1085.


Module TM1086.
Definition tm := TM_from_str "1RB1RF_1LC0RE_1LD0LC_1RB0LE_1RA0LB_0LE---".
Definition tm' := TM_from_str "1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM1086.


Module TM1087.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RC_1LC1LF_0LA---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM1087.


Module TM1088.
Definition tm := TM_from_str "1LB1RE_1LC0LB_1RD1LC_1RD1RA_1RF0RD_1LC---".
Definition tm' := TM_from_str "1RB0RD_1LC---_1RD1LC_1RD1RE_1LF1RA_1LC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCDAB") 2 3.
Time Qed.
End TM1088.


Module TM1089.
Definition tm := TM_from_str "1RB---_1RC1RC_1LD1RF_0LE0LD_1RE0RC_1RA0RC".
Definition tm' := TM_from_str "1RB1RB_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 108 137.
Time Qed.
End TM1089.


Module TM1090.
Definition tm := TM_from_str "1RB0RC_1RC---_1RD0RB_0RE0LF_1RF0LA_1LD1LE".
Definition tm' := TM_from_str "1RB---_1RC0RA_0RD0LE_1RE0LF_1LC1LD_1RA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 10 11.
Time Qed.
End TM1090.


Module TM1091.
Definition tm := TM_from_str "1LB1LB_0RC0LC_1RE1RD_0LB1RF_1LA0RE_1RC---".
Definition tm' := TM_from_str "1RB1RE_1LC0RB_1LD1LD_0RA0LA_0LD1RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEBF") 6 1.
Time Qed.
End TM1091.


Module TM1092.
Definition tm := TM_from_str "1RB---_1RC0LE_1LD0RE_0RC0LD_1RF1LE_1RA1RF".
Definition tm' := TM_from_str "1RB0LD_1LC0RD_0RB0LC_1RE1LD_1RF1RE_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 9 8.
Time Qed.
End TM1092.


Module TM1093.
Definition tm := TM_from_str "1RB---_1LC1RF_1RD0LD_0RB1LE_0LC0RD_0RE0RA".
Definition tm' := TM_from_str "1RB0LB_0RC1LD_1LA1RE_0LA0RB_0RD0RF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCABDE") 220 164.
Time Qed.
End TM1093.


Module TM1094.
Definition tm := TM_from_str "1LB1LA_1RC1LF_0LD0RC_1LE1RD_0LA1LA_0RD---".
Definition tm' := TM_from_str "1RB1LF_0LC0RB_1LD1RC_0LE1LE_1LA1LE_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 4 3.
Time Qed.
End TM1094.


Module TM1095.
Definition tm := TM_from_str "1LB0RC_1RA1LD_0LA0RE_1LA1RA_0RF0LA_---0RC".
Definition tm' := TM_from_str "1RB1LC_1LA0RD_1LB1RB_0LB0RE_0RF0LB_---0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BADCEF") 4 1.
Time Qed.
End TM1095.


Module TM1096.
Definition tm := TM_from_str "1LB0RE_0LC1LF_1RD0LC_1RA---_0LA1RF_1LC1LA".
Definition tm' := TM_from_str "1RB0LA_1RC---_1LD0RF_0LA1LE_1LA1LC_0LC1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 6 2.
Time Qed.
End TM1096.


Module TM1097.
Definition tm := TM_from_str "1LB---_0RC0RB_1RE0LD_1RB0LE_1LD0LF_1LB1LA".
Definition tm' := TM_from_str "1RB0LD_0RC0RB_1RD0LA_1LA0LE_1LB1LF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 4 1.
Time Qed.
End TM1097.


Module TM1098.
Definition tm := TM_from_str "1RB1RF_1RC---_1LD1LE_1RA0LC_1LC0RC_0RD0RF".
Definition tm' := TM_from_str "1RB0LD_1RC1RF_1RD---_1LA1LE_1LD0RD_0RA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 4 7.
Time Qed.
End TM1098.


Module TM1099.
Definition tm := TM_from_str "1LB0RC_0LC0LE_0RD0LF_1RE0LB_1LC1RF_0LA---".
Definition tm' := TM_from_str "1RB0LF_1LC1RD_0RA0LD_0LE---_1LF0RC_0LC0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCABD") 86 54.
Time Qed.
End TM1099.


Module TM1100.
Definition tm := TM_from_str "1LB0LE_1RC---_0LD1LD_1RB0RE_0RF0LC_1LA1RF".
Definition tm' := TM_from_str "1RB0RD_1RC---_0LA1LA_0RE0LC_1LF1RE_1LB0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 7 1.
Time Qed.
End TM1100.


Module TM1101.
Definition tm := TM_from_str "1LB0LA_1RC1LE_1RD0RC_0RE0RE_1LA0LF_0RC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_0RD0RD_1LE0LF_1LA0LE_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 5 14.
Time Qed.
End TM1101.


Module TM1102.
Definition tm := TM_from_str "1LB0RA_1RC0LE_0LF0RD_1LA0RA_0LC---_1LA1RD".
Definition tm' := TM_from_str "1RB0LF_0LC0RD_1LE1RD_1LE0RE_1LA0RE_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABDFC") 1 7.
Time Qed.
End TM1102.


Module TM1103.
Definition tm := TM_from_str "1LB---_1LC1RB_1RD1LF_1RE0RD_0LC0RF_1LA0LC".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_0LA0RD_1LE0LA_1LF---_1LA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 13 12.
Time Qed.
End TM1103.


Module TM1104.
Definition tm := TM_from_str "1LB1LC_1RC0LA_1RD0RB_1RE0LF_1RF---_1RA1RD".
Definition tm' := TM_from_str "1RB0LC_1RC---_1RD1RA_1LE1LF_1RF0LD_1RA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 5 15.
Time Qed.
End TM1104.


Module TM1105.
Definition tm := TM_from_str "1RB---_1LC0LE_1RD0LB_1RB1RA_0LF0RC_0RD1LE".
Definition tm' := TM_from_str "1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM1105.


Module TM1106.
Definition tm := TM_from_str "1RB0RF_0RC0LD_1LD1RA_0LE1LC_1RB0LB_0RB---".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA1LC_1RB0RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1106.


Module TM1107.
Definition tm := TM_from_str "1RB0LF_1LC0LE_1RD1LB_0RA1RD_---1RD_1LA0RA".
Definition tm' := TM_from_str "1RB1LD_0RC1RB_1RD0LF_1LA0LE_---1RB_1LC0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 35 43.
Time Qed.
End TM1107.


Module TM1108.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_0LE---".
Definition tm' := TM_from_str "1RB1LC_0LA---_1LD0LC_1RE0RA_1LC1RF_1RD0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECFAB") 74 99.
Time Qed.
End TM1108.


Module TM1109.
Definition tm := TM_from_str "1LB0RF_1RC0LA_1RD1RB_1LE0RB_0RD0LE_1RA---".
Definition tm' := TM_from_str "1RB1RD_1LC0RD_0RB0LC_1RA0LE_1LD0RF_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDABCF") 1 9.
Time Qed.
End TM1109.


Module TM1110.
Definition tm := TM_from_str "1RB1LB_0LC0RA_1LD1LC_0RB0RE_1RB1RF_---1RE".
Definition tm' := TM_from_str "1RB1RF_0LC0RE_1LD1LC_0RB0RA_1RB1LB_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1110.


Module TM1111.
Definition tm := TM_from_str "1RB---_1RC0LE_1RD0RE_1LB1RA_1RB1LF_0LB0LC".
Definition tm' := TM_from_str "1RB1LE_1RC0LA_1RD0RA_1LB1RF_0LB0LC_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1111.


Module TM1112.
Definition tm := TM_from_str "1RB0LE_1RC0RA_1LD0RB_0RA0LC_1LF---_0LA0RA".
Definition tm' := TM_from_str "1RB0RD_1LC0RA_0RD0LB_1RA0LE_1LF---_0LD0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 89 138.
Time Qed.
End TM1112.


Module TM1113.
Definition tm := TM_from_str "1LB1RE_0LC0RF_1RD0LF_0RA---_0RB1RD_0RA1LB".
Definition tm' := TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RE_0RC1LD_0RD1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 30 22.
Time Qed.
End TM1113.


Module TM1114.
Definition tm := TM_from_str "1RB0RD_1LC0RD_0LD0LB_1RE0LF_1RB0RE_0LA---".
Definition tm' := TM_from_str "1RB0RA_1LC0RD_0LD0LB_1RA0LE_0LF---_1RB0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1114.


Module TM1115.
Definition tm := TM_from_str "1LB0LD_1RC1RF_0LA1RB_0RA0LE_---1LA_1LB0RB".
Definition tm' := TM_from_str "1RB1RF_0LC1RA_1LA0LD_0RC0LE_---1LC_1LA0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 5.
Time Qed.
End TM1115.


Module TM1116.
Definition tm := TM_from_str "1RB0LD_1RC1LB_1LA1RE_0RC0LD_1RF0RC_1RB---".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RF_1RB0LE_0RC0LE_1RA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM1116.


Module TM1117.
Definition tm := TM_from_str "1RB0RA_0RC1RE_1LD1LF_0LE1LC_1LA0LD_1RE---".
Definition tm' := TM_from_str "1RB---_1LC0LF_1RD0RC_0RE1RB_1LF1LA_0LB1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 1 5.
Time Qed.
End TM1117.


Module TM1118.
Definition tm := TM_from_str "1RB1LE_0RC0RF_1RD0RE_1LA---_0LA0LD_1RB1RD".
Definition tm' := TM_from_str "1RB1RD_0RC0RA_1RD0RF_1LE---_1RB1LF_0LE0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1118.


Module TM1119.
Definition tm := TM_from_str "1LB0RD_0LC0RA_1RA1LD_0LF1LE_0RA---_1RE0LB".
Definition tm' := TM_from_str "1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADFE") 8 3.
Time Qed.
End TM1119.


Module TM1120.
Definition tm := TM_from_str "1RB1LF_0LC0RB_1RD0RB_1LE---_1LA1RE_1LD0LA".
Definition tm' := TM_from_str "1RB0RF_1LC---_1LD1RC_1RF1LE_1LB0LD_0LA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFABCE") 5 1.
Time Qed.
End TM1120.


Module TM1121.
Definition tm := TM_from_str "1LB0RE_1LC0RD_0LD1LF_1RA0RA_---1RF_0LC0RA".
Definition tm' := TM_from_str "1RB0RB_1LC0RE_1LD0RA_0LA1LF_---1RF_0LD0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 1 5.
Time Qed.
End TM1121.


Module TM1122.
Definition tm := TM_from_str "1RB---_1RC0RA_0LD1LF_1LF1LE_1RF1LE_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1RC0RF_0LD1LA_1LA1LE_1RA1LE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1122.


Module TM1123.
Definition tm := TM_from_str "1LB1RE_1RC0LC_1RE0LD_0LB1RA_1RA0RF_0RA---".
Definition tm' := TM_from_str "1RB0RF_1LC1RA_1RD0LD_1RA0LE_0LC1RB_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 4 1.
Time Qed.
End TM1123.


Module TM1124.
Definition tm := TM_from_str "1RB---_0RC0RF_1LD1RE_0LE0RA_1RB0LF_0RC0RD".
Definition tm' := TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA0RF_0RC0RD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1124.


Module TM1125.
Definition tm := TM_from_str "1RB0LD_0RC0RE_1LD1RF_1LA0LA_1RB0LE_---1RB".
Definition tm' := TM_from_str "1RB0LA_0RC0RA_1LD1RF_1LE0LE_1RB0LD_---1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1125.


Module TM1126.
Definition tm := TM_from_str "1LB---_1LC1RB_0RB0LD_1LE1RC_1RC0LF_0LC1LA".
Definition tm' := TM_from_str "1RB0LE_0RC0LD_1LB1RC_1LA1RB_0LB1LF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCBDAE") 9 4.
Time Qed.
End TM1126.


Module TM1127.
Definition tm := TM_from_str "1LB0RD_1RC0LF_---1RD_0LD0RE_1RA1RB_1LA0LF".
Definition tm' := TM_from_str "1RB1RC_1LC0RF_1RE0LD_1LB0LD_---1RF_0LF0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEFAD") 17 1.
Time Qed.
End TM1127.


Module TM1128.
Definition tm := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LB_0LC0RE_0LD1LE".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0RF_0LA---_0LB1LF_0LA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 23 33.
Time Qed.
End TM1128.


Module TM1129.
Definition tm := TM_from_str "1RB1LC_1LC0RA_1RB1LD_1LC0LE_1LF0LA_---0LB".
Definition tm' := TM_from_str "1RB1LC_1LA0RD_1LA0LE_1RB1LA_1LF0LD_---0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBACEF") 1 1.
Time Qed.
End TM1129.


Module TM1130.
Definition tm := TM_from_str "1LB1LA_1RC1RD_0LA0LB_1RB1LE_1RF0LD_---0RE".
Definition tm' := TM_from_str "1RB1RD_0LC0LA_1LA1LC_1RA1LE_1RF0LD_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 49981 48727.
Time Qed.
End TM1130.


Module TM1131.
Definition tm := TM_from_str "1LB0RB_0LC1RD_1RD1LE_0RA0LB_0LD1LF_0LC---".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0RD_0LA1RB_0LB1LF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 23 31.
Time Qed.
End TM1131.


Module TM1132.
Definition tm := TM_from_str "1LB0RD_1LC1RB_1RA1LE_1RC0RD_1LF0LC_1LA---".
Definition tm' := TM_from_str "1RB1LD_1LC0RF_1LA1RC_1LE0LA_1LB---_1RA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAFDE") 22 6.
Time Qed.
End TM1132.


Module TM1133.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_1LC---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC0RF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM1133.


Module TM1134.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RF_1LC1LD_1RA---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LE_0LC0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM1134.


Module TM1135.
Definition tm := TM_from_str "1LB1LC_0RC0LA_1RA0LD_1RE1RF_1RF---_1RB0RE".
Definition tm' := TM_from_str "1RB1RC_1RC---_1RD0RB_0RE0LF_1RF0LA_1LD1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 4 1.
Time Qed.
End TM1135.


Module TM1136.
Definition tm := TM_from_str "1LB1LF_1RC0LB_0LA0RD_1RE---_1LF0RF_0RC0LF".
Definition tm' := TM_from_str "1RB---_1LC0RC_0RD0LC_0LE0RA_1LF1LC_1RD0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDABC") 1777 1250.
Time Qed.
End TM1136.


Module TM1137.
Definition tm := TM_from_str "1LB1RA_0RA0LC_1LD1RB_1RA0LE_0LB0LF_1RD---".
Definition tm' := TM_from_str "1RB0LE_1LC1RB_0RB0LD_1LA1RC_0LC0LF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 3 1.
Time Qed.
End TM1137.


Module TM1138.
Definition tm := TM_from_str "1RB0LF_0LC1RD_0RD1LD_1RB1RE_0RA0LA_---1LC".
Definition tm' := TM_from_str "1RB1RD_0LC1RA_0RA1LA_0RE0LE_1RB0LF_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM1138.


Module TM1139.
Definition tm := TM_from_str "1RB1LC_0LC1RE_---0LD_0RE1LA_1RF1RB_1LB0RC".
Definition tm' := TM_from_str "1RB1RC_1LC0RD_0LD1RA_---0LE_0RA1LF_1RC1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEAB") 5 1.
Time Qed.
End TM1139.


Module TM1140.
Definition tm := TM_from_str "1RB0RE_1LC1LD_0RA0LC_1RA0LB_1RF---_1LC1RD".
Definition tm' := TM_from_str "1RB---_1LC1RF_0RD0LC_1RE0RA_1LC1LF_1RD0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECFAB") 2 2.
Time Qed.
End TM1140.


Module TM1141.
Definition tm := TM_from_str "1RB0RA_1LC0RA_1RF1LD_0LE---_0LF1LC_0LB1RF".
Definition tm' := TM_from_str "1RB1LE_0LC1RB_1LA0RD_1RC0RD_0LF---_0LB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCAEFB") 1 4.
Time Qed.
End TM1141.


Module TM1142.
Definition tm := TM_from_str "1RB0RD_1LC0RA_1RD0LB_1RE0LD_1RA1RF_0RB---".
Definition tm' := TM_from_str "1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 115 119.
Time Qed.
End TM1142.


Module TM1143.
Definition tm := TM_from_str "1LB1LF_0RC1LB_---1RD_0RE1RF_0LA1RB_1RD0LA".
Definition tm' := TM_from_str "1RB0LD_0RC1RA_0LD1RE_1LE1LA_0RF1LE_---1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 3 1.
Time Qed.
End TM1143.


Module TM1144.
Definition tm := TM_from_str "1LB---_0LC1RE_0RD1LF_1RB---_0RF0RA_0LA0RB".
Definition tm' := TM_from_str "1RB---_0LC1RF_0RA1LD_0LE0RB_1LB---_0RD0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCAFD") 769 823.
Time Qed.
End TM1144.


Module TM1145.
Definition tm := TM_from_str "1LB1RC_1RA0RE_1LD1RF_0RB0LD_---1LA_1RB0RA".
Definition tm' := TM_from_str "1RB0RC_1RC0RD_1LB1RE_---1LC_1LF1RA_0RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBEFDA") 9 6.
Time Qed.
End TM1145.


Module TM1146.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC1LF_1LD---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM1146.


Module TM1147.
Definition tm := TM_from_str "1RB1LC_1LA0RD_1RB1RE_0RA1RC_1RF0LE_1LA---".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_1RB1LA_0RC1RA_1RF0LE_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBADEF") 1 1.
Time Qed.
End TM1147.


Module TM1148.
Definition tm := TM_from_str "1LB1RC_1LC0RE_1LD1LF_1RE0RB_1LC1RB_0LA---".
Definition tm' := TM_from_str "1RB0RF_1LC1RF_1LA1LD_0LE---_1LF1RC_1LC0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCABD") 53 2.
Time Qed.
End TM1148.


Module TM1149.
Definition tm := TM_from_str "1LB0RE_1RC1LB_0LB0RD_1RA1LC_0RC0RF_1LC---".
Definition tm' := TM_from_str "1RB1LA_0LA0RC_1RD1LB_1LA0RE_0RB0RF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 3.
Time Qed.
End TM1149.


Module TM1150.
Definition tm := TM_from_str "1RB1RF_1RC---_1LD1LE_1RA0LC_1RC1LC_0RD0RF".
Definition tm' := TM_from_str "1RB---_1LC1LF_1RD0LB_1RA1RE_0RC0RE_1RB1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCFE") 2 8.
Time Qed.
End TM1150.


Module TM1151.
Definition tm := TM_from_str "1LB---_1RC0RF_1LD0RB_0LE0LC_0LF0LA_1RB1RD".
Definition tm' := TM_from_str "1RB1RD_1RC0RA_1LD0RB_0LE0LC_0LA0LF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 5.
Time Qed.
End TM1151.


Module TM1152.
Definition tm := TM_from_str "1RB0RE_1RC0RB_1LD1LA_1RB1LE_1LF0LD_1LC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LF0LA_1RB0RD_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM1152.


Module TM1153.
Definition tm := TM_from_str "1LB1LF_1LC1RF_1LD0LF_0RE---_1RB0RE_1RE0LA".
Definition tm' := TM_from_str "1RB0RA_1LC1RD_1LF0LD_1RA0LE_1LB1LD_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFAD") 8 1.
Time Qed.
End TM1153.


Module TM1154.
Definition tm := TM_from_str "1RB1RA_1RC0RA_1LD0LF_---1LE_1RB1LF_0LB1LC".
Definition tm' := TM_from_str "1RB1LE_1RC0RF_1LD0LE_---1LA_0LB1LC_1RB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1154.


Module TM1155.
Definition tm := TM_from_str "1RB---_1LC0LD_1LD0LB_1LE0RE_1RF0LA_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_1LC0LD_1LD0LB_1LE0RE_1RA0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1155.


Module TM1156.
Definition tm := TM_from_str "1LB0LD_1RC1RF_0LA1RB_0RA0LE_---1LF_0RB0LD".
Definition tm' := TM_from_str "1RB1RF_0LC1RA_1LA0LD_0RC0LE_---1LF_0RA0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 5.
Time Qed.
End TM1156.


Module TM1157.
Definition tm := TM_from_str "1RB1RF_0LC1RB_0RA0LD_1RE1LE_1RA1LC_---0RB".
Definition tm' := TM_from_str "1RB1LB_1RC1LE_1RD1RF_0LE1RD_0RC0LA_---0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM1157.


Module TM1158.
Definition tm := TM_from_str "1LB1RD_1RC0LE_1LD1RC_0RC0LA_0LD0LF_1RD---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LB1RC_1LE1RB_1RC0LF_0LB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECBFA") 7 4.
Time Qed.
End TM1158.


Module TM1159.
Definition tm := TM_from_str "1RB0RE_1LC1RA_1RB1LD_1LC0LC_0RF1RB_---0RE".
Definition tm' := TM_from_str "1RB1LC_1LA1RD_1LA0LA_1RB0RE_0RF1RB_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBACEF") 1 1.
Time Qed.
End TM1159.


Module TM1160.
Definition tm := TM_from_str "1LB---_0LC0RD_1RB1LC_1RE1LB_1RB0RF_0RB1RA".
Definition tm' := TM_from_str "1RB1LC_1RC0RE_0LD0RA_1RC1LD_0RC1RF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 4 9.
Time Qed.
End TM1160.


Module TM1161.
Definition tm := TM_from_str "1LB0RF_1RC0LF_0LA1RD_0LD0RE_1RA---_0RC0LA".
Definition tm' := TM_from_str "1RB0LD_0LC1RE_1LA0RD_0RB0LC_0LE0RF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEFD") 1 6.
Time Qed.
End TM1161.


Module TM1162.
Definition tm := TM_from_str "1LB1RE_1RC1LD_1RA0RB_0LB0LC_0RF0RD_---0RB".
Definition tm' := TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RF0RD_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 674 805.
Time Qed.
End TM1162.


Module TM1163.
Definition tm := TM_from_str "1LB0LA_0RC1RF_1RE1RD_1RB---_0LA0RB_1LA1RF".
Definition tm' := TM_from_str "1RB1RE_0LC0RD_1LD0LC_0RA1RF_1RD---_1LC1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEBF") 1 4.
Time Qed.
End TM1163.


Module TM1164.
Definition tm := TM_from_str "1RB0RB_0LC0RA_1RB1LD_0LE1LB_1LA1LF_1LD---".
Definition tm' := TM_from_str "1RB1LC_0LA0RE_0LD1LB_1LE1LF_1RB0RB_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM1164.


Module TM1165.
Definition tm := TM_from_str "1LB1RC_1RA0LE_1RD0RE_0LC0RB_0LA0RF_1RD---".
Definition tm' := TM_from_str "1RB---_0LC0RF_1RB0RD_0LE0RA_1LF1RC_1RE0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCBDA") 1 5.
Time Qed.
End TM1165.


Module TM1166.
Definition tm := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA0RF_0LE---".
Definition tm' := TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB0RF_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 103 126.
Time Qed.
End TM1166.


Module TM1167.
Definition tm := TM_from_str "1LB1LC_0LC---_1LD0LA_1LE0RA_1RF1RE_0LC0RF".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_0LC---_1LA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECFAB") 1 4.
Time Qed.
End TM1167.


Module TM1168.
Definition tm := TM_from_str "1RB1LD_0RC1RB_1RD0LF_1LA1LE_---1RF_1LC0RC".
Definition tm' := TM_from_str "1RB0LF_1LC1LE_1RD1LB_0RA1RD_---1RF_1LA0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 43 35.
Time Qed.
End TM1168.


Module TM1169.
Definition tm := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_1RB---".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 760 746.
Time Qed.
End TM1169.


Module TM1170.
Definition tm := TM_from_str "1RB1RE_1LC0RA_1RF1LD_0LE---_0LF1LF_0LB0RA".
Definition tm' := TM_from_str "1RB1LE_0LC0RD_1LA0RD_1RC1RF_0LF---_0LB1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCAEFB") 1 4.
Time Qed.
End TM1170.


Module TM1171.
Definition tm := TM_from_str "1RB1RF_0LC1RC_0RA0LD_1RE1LE_1RA1LC_---0LB".
Definition tm' := TM_from_str "1RB1LB_1RC1LE_1RD1RF_0LE1RE_0RC0LA_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM1171.


Module TM1172.
Definition tm := TM_from_str "1RB1RC_1LA1RF_---0RD_1LE0RB_1LF---_1RA0LF".
Definition tm' := TM_from_str "1RB0LA_1RC1RD_1LB1RA_---0RE_1LF0RC_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 15 1.
Time Qed.
End TM1172.


Module TM1173.
Definition tm := TM_from_str "1LB1LF_0RC0RE_1RD1RB_1LD1LA_0LF1RC_0LB---".
Definition tm' := TM_from_str "1RB1RD_1LB1LC_1LD1LF_0RA0RE_0LF1RA_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 22 1.
Time Qed.
End TM1173.


Module TM1174.
Definition tm := TM_from_str "1LB1RD_0LC0RC_1RD1LE_0RA0LB_0LD1LF_0RB---".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD1RB_0LA0RA_0LB1LF_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 16 32.
Time Qed.
End TM1174.


Module TM1175.
Definition tm := TM_from_str "1LB1LF_1RC1LB_0LE1RD_1RB0RC_1RA1LA_---0LC".
Definition tm' := TM_from_str "1RB1LB_1LC1LF_1RD1LC_0LA1RE_1RC0RD_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 13 11.
Time Qed.
End TM1175.


Module TM1176.
Definition tm := TM_from_str "1RB0LA_0LC0RE_1LA1LD_0RB0LD_1RF---_1LD0RD".
Definition tm' := TM_from_str "1RB---_1LC0RC_0RD0LC_0LE0RA_1LF1LC_1RD0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDECAB") 6 1.
Time Qed.
End TM1176.


Module TM1177.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LD0LC_1RA0RF_1RD---_1RB1RB".
Definition tm' := TM_from_str "1RB1RB_1LC1RD_1LD0LC_1RE0RA_1RB1RF_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1177.


Module TM1178.
Definition tm := TM_from_str "1RB0RB_1LC1RA_0LE1LD_1RB1LF_---1LA_1LD0LC".
Definition tm' := TM_from_str "1RB1LF_1LC1RD_0LE1LA_1RB0RB_---1LD_1LA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM1178.


Module TM1179.
Definition tm := TM_from_str "1LB1RE_1RC0LC_0RA1LD_0LB0RC_0RD0RF_1RA---".
Definition tm' := TM_from_str "1RB0LB_0RC1LD_1LA1RE_0LA0RB_0RD0RF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 600 540.
Time Qed.
End TM1179.


Module TM1180.
Definition tm := TM_from_str "1RB---_0LC0RB_1LE0LD_1LA1LC_1LF1LE_1RB1RF".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_1RB---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1180.


Module TM1181.
Definition tm := TM_from_str "1RB0LF_1LC0LD_1LD1RC_1RE1LB_0LA0RE_0RA---".
Definition tm' := TM_from_str "1RB1LE_0LC0RB_1RE0LD_0RC---_1LF0LA_1LA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEFABD") 1 5.
Time Qed.
End TM1181.


Module TM1182.
Definition tm := TM_from_str "1LB1LE_0RC1LA_1RA0RD_0LE0RF_1RA0LA_---1RC".
Definition tm' := TM_from_str "1RB0LB_1LC1LA_0RD1LB_1RB0RE_0LA0RF_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 5 1.
Time Qed.
End TM1182.


Module TM1183.
Definition tm := TM_from_str "1RB0LC_1LA0RE_1LD0RA_1LA0LF_1RB0RE_0LA---".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1RB0LD_1LE0RC_1LC0LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM1183.


Module TM1184.
Definition tm := TM_from_str "1RB0LA_0RC1LA_1LD1RF_1RE0RB_1RC0LB_0RD---".
Definition tm' := TM_from_str "1RB0LD_1LC1RF_1RA0RD_0RB1LE_1RD0LE_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDBCAF") 5 5.
Time Qed.
End TM1184.


Module TM1185.
Definition tm := TM_from_str "1RB0RF_0LC1LE_0LF1LD_1RE1LD_1RA0LB_1RA---".
Definition tm' := TM_from_str "1RB---_1RC0RA_0LD1LF_0LA1LE_1RF1LE_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 73 43.
Time Qed.
End TM1185.


Module TM1186.
Definition tm := TM_from_str "1RB0RA_0RC0RB_1LD0LE_0LA---_1LE1LF_1RE0LD".
Definition tm' := TM_from_str "1RB0LC_1LB1LA_0LD---_1RE0RD_0RF0RE_1LC0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFCBA") 15 5.
Time Qed.
End TM1186.


Module TM1187.
Definition tm := TM_from_str "1LB---_1RC1LB_1RD0RC_1LE1RD_1LA1LF_1LC0LE".
Definition tm' := TM_from_str "1RB1LA_1RC0RB_1LD1RC_1LF1LE_1LB0LD_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 72 25.
Time Qed.
End TM1187.


Module TM1188.
Definition tm := TM_from_str "1RB1LE_0LC1LA_0RD0LB_1RA0RD_1LF1RD_1LB---".
Definition tm' := TM_from_str "1RB0RA_1RC1LE_0LD1LB_0RA0LC_1LF1RA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 6 1.
Time Qed.
End TM1188.


Module TM1189.
Definition tm := TM_from_str "1LB0LE_0LC0RB_1RD1LF_0RA0LB_1RA---_0LD1LA".
Definition tm' := TM_from_str "1RB---_1LC0LA_0LD0RC_1RE1LF_0RB0LC_0LE1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 290 109.
Time Qed.
End TM1189.


Module TM1190.
Definition tm := TM_from_str "1LB1RD_1LC0LB_0LD0RD_1RE1LC_1RA0RF_1RA---".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1LD0LC_0LE0RE_1RA1LD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 13 4.
Time Qed.
End TM1190.


Module TM1191.
Definition tm := TM_from_str "1RB---_1LC1LB_0RD0LC_1RE0RF_1RB1RE_1RA1RD".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1191.


Module TM1192.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1LB_0RB1RF_1RA---".
Definition tm' := TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RB_0RD1RF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 46 36.
Time Qed.
End TM1192.


Module TM1193.
Definition tm := TM_from_str "1RB0RE_0LC1LE_0LE1LD_1RE1LF_1RA0LB_1RE---".
Definition tm' := TM_from_str "1RB0LC_1RC0RA_0LD1LA_0LA1LE_1RA1LF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 73 43.
Time Qed.
End TM1193.


Module TM1194.
Definition tm := TM_from_str "1LB1RE_1LC0LA_0RD0LB_1RB0RE_1RC1RF_0RC---".
Definition tm' := TM_from_str "1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 10.
Time Qed.
End TM1194.


Module TM1195.
Definition tm := TM_from_str "1RB1LE_0RC1LB_1RD0RF_1LA---_0LA0LE_1RB1RF".
Definition tm' := TM_from_str "1RB1RA_0RC1LB_1RD0RA_1LE---_1RB1LF_0LE0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1195.


Module TM1196.
Definition tm := TM_from_str "1LB1LE_1RC0LC_0LA0RD_1RB0RD_0LC1LF_0LC---".
Definition tm' := TM_from_str "1RB0RA_1RC0LC_0LD0RA_1LB1LE_0LC1LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 17 1.
Time Qed.
End TM1196.


Module TM1197.
Definition tm := TM_from_str "1LB1RA_1RA0LC_---0LD_1RE1LD_1RF0RF_1RA0RA".
Definition tm' := TM_from_str "1RB0RB_1RC0RC_1LD1RC_1RC0LE_---0LF_1RA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 3 2.
Time Qed.
End TM1197.


Module TM1198.
Definition tm := TM_from_str "1LB0RB_1RC0LE_1LD0RD_1RA0LF_1LF---_0LC1LB".
Definition tm' := TM_from_str "1RB0LE_1LC0RC_1RF0LD_1LE---_0LF1LC_1LA0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFADE") 11695 11512.
Time Qed.
End TM1198.


Module TM1199.
Definition tm := TM_from_str "1LB0LF_0RC1RF_1RF1RD_0LD0RE_0LB---_1LA0RB".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA1RB_0LE0RF_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEFB") 8 1.
Time Qed.
End TM1199.


Module TM1200.
Definition tm := TM_from_str "1RB1RF_1RC1RE_1LD---_1RF0LE_0RA1LD_1RA0LF".
Definition tm' := TM_from_str "1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEAFB") 20 44.
Time Qed.
End TM1200.


Module TM1201.
Definition tm := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RC---".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 2340 2020.
Time Qed.
End TM1201.


Module TM1202.
Definition tm := TM_from_str "1LB0RC_0RC1RA_1LF0LD_1RE---_0RB0LF_1LE0LC".
Definition tm' := TM_from_str "1RB---_0RC0LE_0RD1RF_1LE0LA_1LB0LD_1LC0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 4 1.
Time Qed.
End TM1202.


Module TM1203.
Definition tm := TM_from_str "1RB0RB_1RC0LD_1RD1RF_1LE1LB_0LB1LA_1RA---".
Definition tm' := TM_from_str "1RB0LC_1RC1RF_1LD1LA_0LA1LE_1RA0RA_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 11 12.
Time Qed.
End TM1203.


Module TM1204.
Definition tm := TM_from_str "1RB0LE_1LC0RE_0RF0LD_1LA1LF_0LC0RE_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_0RA0LD_1LE1LA_1RB0LF_0LC0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1204.


Module TM1205.
Definition tm := TM_from_str "1LB0LE_1RC0LA_1RD1RB_1LD0RB_1LF1LC_---1LA".
Definition tm' := TM_from_str "1RB1RC_1LB0RC_1RA0LD_1LC0LE_1LF1LA_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCABEF") 1 5.
Time Qed.
End TM1205.


Module TM1206.
Definition tm := TM_from_str "1RB0LE_1RC---_1RD0RF_0RE0RE_1LF0RC_0LA1RA".
Definition tm' := TM_from_str "1RB---_1RC0RE_0RD0RD_1LE0RB_0LF1RF_1RA0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 448 414.
Time Qed.
End TM1206.


Module TM1207.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RC_1LC1LF_0LB---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM1207.


Module TM1208.
Definition tm := TM_from_str "1RB0RC_0LC0LB_1RE1RD_1LB---_0RF1RC_1RA0RE".
Definition tm' := TM_from_str "1RB0RF_1RC0RD_0LD0LC_1RF1RE_1LC---_0RA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 1 15.
Time Qed.
End TM1208.


Module TM1209.
Definition tm := TM_from_str "1RB---_1LC0LD_1RD0LB_1RF1RE_1RF0RA_0LE0RC".
Definition tm' := TM_from_str "1RB1RC_0LC0RF_1RB0RD_1RE---_1LF0LA_1RA0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFACB") 1 4.
Time Qed.
End TM1209.


Module TM1210.
Definition tm := TM_from_str "1LB1RA_1RC1LF_0LD0RC_1RE1LE_1LA---_0RD0LB".
Definition tm' := TM_from_str "1RB1LB_1LC---_1LD1RC_1RF1LE_0RA0LD_0LA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFABE") 13 9.
Time Qed.
End TM1210.


Module TM1211.
Definition tm := TM_from_str "1LB0LC_1RC1RD_1LA1LB_1LE0RB_1RF0LD_---1RE".
Definition tm' := TM_from_str "1RB1RD_1LC1LA_1LA0LB_1LE0RA_1RF0LD_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 69 64.
Time Qed.
End TM1211.


Module TM1212.
Definition tm := TM_from_str "1RB0RA_1LC0RA_1RB1LD_0LE---_0LF1LC_0LB0RA".
Definition tm' := TM_from_str "1RB1LC_1LA0RF_0LD---_0LE1LA_0LB0RF_1RB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBACDE") 1 1.
Time Qed.
End TM1212.


Module TM1213.
Definition tm := TM_from_str "1RB0LC_1RC0RB_1LD0RE_1LA0LD_1RB0RF_1LE---".
Definition tm' := TM_from_str "1RB0RF_1RC0RB_1LD0RA_1LE0LD_1RB0LC_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1213.


Module TM1214.
Definition tm := TM_from_str "1RB1LC_0RC0LF_1LD1LE_0LA0RB_1RB---_0LD0RE".
Definition tm' := TM_from_str "1RB---_0RC0LF_1LD1LA_0LE0RB_1RB1LC_0LD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1214.


Module TM1215.
Definition tm := TM_from_str "1RB1RA_1RC0RC_0LD1RC_---0LE_0RA1LF_1RA1LD".
Definition tm' := TM_from_str "1RB0RB_0LC1RB_---0LD_0RE1LF_1RA1RE_1RE1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 5.
Time Qed.
End TM1215.


Module TM1216.
Definition tm := TM_from_str "1RB0LA_0RC1LD_1LA1RE_---0RC_1RC1LF_1LD0LF".
Definition tm' := TM_from_str "1RB1LF_1LC1RA_1RD0LC_0RB1LE_---0RB_1LE0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEAF") 6 5.
Time Qed.
End TM1216.


Module TM1217.
Definition tm := TM_from_str "1LB0LC_1RB1LA_1RD---_0RD0RE_0LF0LE_1RE0LA".
Definition tm' := TM_from_str "1RB0LC_0LA0LB_1LD0LE_1RD1LC_1RF---_0RF0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 1 4.
Time Qed.
End TM1217.


Module TM1218.
Definition tm := TM_from_str "1LB---_0RC0LE_1RF1RD_1RE0RB_0LB1RA_1RD0RD".
Definition tm' := TM_from_str "1RB1RC_1RC0RC_1RD0RE_0LE1RF_0RA0LD_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEACDB") 4 17.
Time Qed.
End TM1218.


Module TM1219.
Definition tm := TM_from_str "1LB1RD_0LC1LF_1RC0RA_1RB0RE_0LB1RE_---0LD".
Definition tm' := TM_from_str "1RB0RE_0LC1LF_1RC0RD_1LB1RA_0LB1RE_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 4.
Time Qed.
End TM1219.


Module TM1220.
Definition tm := TM_from_str "1LB0RC_1RC1LE_1LF1RD_0LB0RD_1RA0LE_---1RC".
Definition tm' := TM_from_str "1RB1LE_1LC1RD_---1RB_0LA0RD_1RF0LE_1LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABDEC") 2 3.
Time Qed.
End TM1220.


Module TM1221.
Definition tm := TM_from_str "1LB0RD_0LC0LD_0RD1LC_1RE0LA_0RA0RF_1RA---".
Definition tm' := TM_from_str "1RB---_1LC0RD_0LF0LD_1RE0LB_0RB0RA_0RD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFDEA") 179 95.
Time Qed.
End TM1221.


Module TM1222.
Definition tm := TM_from_str "1LB1LE_1RC0RF_1RE0LD_0LC1LC_1LF0RB_---1LA".
Definition tm' := TM_from_str "1RB0LF_1LC0RE_---1LD_1LE1LB_1RA0RC_0LA1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 12 29.
Time Qed.
End TM1222.


Module TM1223.
Definition tm := TM_from_str "1LB---_0LC0RF_1LD0RA_1LE0LA_1RB0LA_0RB0RE".
Definition tm' := TM_from_str "1RB0LD_0LC0RF_1LE0RD_1LB---_1LA0LD_0RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 4.
Time Qed.
End TM1223.


Module TM1224.
Definition tm := TM_from_str "1RB0LB_1LC0RE_1LD0LC_1RB1LB_1RF0RE_---0RA".
Definition tm' := TM_from_str "1RB1LB_1LC0RD_1LA0LC_1RE0RD_---0RF_1RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM1224.


Module TM1225.
Definition tm := TM_from_str "1RB0RF_1LC0RE_1RB0LD_1LC0LD_1RA0LD_0RB---".
Definition tm' := TM_from_str "1RB0LC_1LA0RD_1LA0LC_1RE0LC_1RB0RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM1225.


Module TM1226.
Definition tm := TM_from_str "1LB0LF_0LC0LA_1LD0RD_1RE0LB_1RC1RB_0LD---".
Definition tm' := TM_from_str "1RB1RD_1LC0RC_1RA0LD_0LB0LE_1LD0LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDBCAF") 215 336.
Time Qed.
End TM1226.


Module TM1227.
Definition tm := TM_from_str "1LB---_1LC1RF_1RD1LE_1RB0RD_1LA0LC_0RE0LB".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RE_1LF0LA_0RD0LC_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCABDE") 69 49.
Time Qed.
End TM1227.


Module TM1228.
Definition tm := TM_from_str "1RB1LE_1RC---_1RD1LE_1LD1RA_0LF0RA_0RA0LE".
Definition tm' := TM_from_str "1RB---_1RC1LE_1LC1RD_1RA1LE_0LF0RD_0RD0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 15 6.
Time Qed.
End TM1228.


Module TM1229.
Definition tm := TM_from_str "1RB0RB_1LC0RF_1RD0LC_0RE0RA_0LB1RA_1RA---".
Definition tm' := TM_from_str "1RB0LA_0RC0RE_0LD1RE_1LA0RF_1RD0RD_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDABCF") 1 3.
Time Qed.
End TM1229.


Module TM1230.
Definition tm := TM_from_str "1RB---_1LC0RD_0LE1LD_1RE1RF_0RA1LB_0RB0LE".
Definition tm' := TM_from_str "1RB1RF_0RC1LD_1RD---_1LE0RA_0LB1LA_0RD0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 176 198.
Time Qed.
End TM1230.


Module TM1231.
Definition tm := TM_from_str "1LB---_1RC0LF_0RD0RC_1RE0RC_0RF0RB_1LE0LA".
Definition tm' := TM_from_str "1RB0LE_0RC0RB_1RD0RB_0RE0RA_1LD0LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 8 21.
Time Qed.
End TM1231.


Module TM1232.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RA_1RF1LB_0LB---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 10 18.
Time Qed.
End TM1232.


Module TM1233.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_0LA---_1RA1RF".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 11 6.
Time Qed.
End TM1233.


Module TM1234.
Definition tm := TM_from_str "1RB1RD_1LC0RA_1LD1LB_1RB0LE_0LF0RD_1LC---".
Definition tm' := TM_from_str "1RB0LE_1LC0RD_1LA1LB_1RB1RA_0LF0RA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM1234.


Module TM1235.
Definition tm := TM_from_str "1RB0LD_1LC0LB_1RD0RC_1LA0RE_1RA0RF_0LD---".
Definition tm' := TM_from_str "1RB0RA_1LC0RE_1RD0LB_1LA0LD_1RC0RF_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 5 1.
Time Qed.
End TM1235.


Module TM1236.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD1RF_0RA0LD_0RB1RC_0LD---".
Definition tm' := TM_from_str "1RB1RE_0RC0LB_1LD1RF_0LA0RB_0LB---_0RD1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 92 248.
Time Qed.
End TM1236.


Module TM1237.
Definition tm := TM_from_str "1LB0RC_1LC---_1RD0LE_0RA1RC_0RA0LF_0LB1LE".
Definition tm' := TM_from_str "1RB0LE_0RC1RA_1LD0RA_1LA---_0RC0LF_0LD1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 10 1.
Time Qed.
End TM1237.


Module TM1238.
Definition tm := TM_from_str "1RB0RF_1LC1RE_1LD0LC_1RB1LD_1RA0RB_1RC---".
Definition tm' := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM1238.


Module TM1239.
Definition tm := TM_from_str "1RB1RC_0LC0LC_1RE1LD_0LB1RB_0RF---_0RA0RE".
Definition tm' := TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0LA_0LE1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 37 22.
Time Qed.
End TM1239.


Module TM1240.
Definition tm := TM_from_str "1LB0RE_1RC0LA_0RF0RD_1RE1LA_0LB1LA_---0RC".
Definition tm' := TM_from_str "1RB1LD_0LC1LD_1RE0LD_1LC0RB_0RF0RA_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEABF") 1 4.
Time Qed.
End TM1240.


Module TM1241.
Definition tm := TM_from_str "1LB0LE_0RC---_1RD0RC_1LA1RE_1RC0LF_1LD1LE".
Definition tm' := TM_from_str "1RB0RA_1LC1RD_1LF0LD_1RA0LE_1LB1LD_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 4 1.
Time Qed.
End TM1241.


Module TM1242.
Definition tm := TM_from_str "1LB0LE_1RC0LA_0RD0RB_0RE0RD_1LA0RF_1RD---".
Definition tm' := TM_from_str "1RB0LE_0RC0RA_0RD0RC_1LE0RF_1LA0LD_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 44 47.
Time Qed.
End TM1242.


Module TM1243.
Definition tm := TM_from_str "1LB1LC_1RA1LC_1LA1RD_---0RE_0LA0RF_0RD0LA".
Definition tm' := TM_from_str "1RB1LC_1LA1LC_1LB1RD_---0RE_0LB0RF_0RD0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BACDEF") 6 1.
Time Qed.
End TM1243.


Module TM1244.
Definition tm := TM_from_str "1LB0RA_1LC1LE_1RD0RC_---0LB_1LF1RC_1RA1LE".
Definition tm' := TM_from_str "1RB1LD_1LC0RB_1LE1LD_1LA1RE_1RF0RE_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEFDA") 20 14.
Time Qed.
End TM1244.


Module TM1245.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RC_1LC1LF_0LD---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM1245.


Module TM1246.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RB_0RB1RF_1RB---".
Definition tm' := TM_from_str "1RB---_0LC0RD_1RD0LD_0RE1RB_1LB1RF_0RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 5.
Time Qed.
End TM1246.


Module TM1247.
Definition tm := TM_from_str "1RB0RF_0LC1LE_0LE1LD_1RE1LD_1RA0LB_1RA---".
Definition tm' := TM_from_str "1RB---_1RC0RA_0LD1LF_0LF1LE_1RF1LE_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 73 43.
Time Qed.
End TM1247.


Module TM1248.
Definition tm := TM_from_str "1RB0LF_1RC1LA_0RD---_1LE0RE_0LB0RC_1LD0LE".
Definition tm' := TM_from_str "1RB1LE_0RC---_1LD0RD_0LA0RB_1RA0LF_1LC0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 6 7.
Time Qed.
End TM1248.


Module TM1249.
Definition tm := TM_from_str "1RB1RE_1RC---_1LD0LC_1RE0RA_1LC1RF_1RD0RA".
Definition tm' := TM_from_str "1RB---_1LC0LB_1RE0RD_1RA1RE_1LB1RF_1RC0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 241 128.
Time Qed.
End TM1249.


Module TM1250.
Definition tm := TM_from_str "1LB0RE_0LC1RC_1RD0LA_1RE---_1RF0RB_0RA0RA".
Definition tm' := TM_from_str "1RB---_1RC0RE_0RD0RD_1LE0RB_0LF1RF_1RA0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 19 37.
Time Qed.
End TM1250.


Module TM1251.
Definition tm := TM_from_str "1RB0RF_0LC0RE_0LF1LD_1RB0LA_0RB1RA_1LC---".
Definition tm' := TM_from_str "1RB0LF_0LC0RD_0LE1LA_0RB1RF_1LC---_1RB0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM1251.


Module TM1252.
Definition tm := TM_from_str "1LB0LA_1RC1LA_1LD0RD_1RA1RE_---0RF_1RD0RC".
Definition tm' := TM_from_str "1RB0RE_1RC1RF_1LD0LC_1RE1LC_1LB0RB_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBFA") 4 23.
Time Qed.
End TM1252.


Module TM1253.
Definition tm := TM_from_str "1LB1RE_1LC---_1LD1RE_1RE1LA_0LD0RF_0RE0LD".
Definition tm' := TM_from_str "1RB1LC_0LA0RF_1LD1RB_1LE---_1LA1RB_0RB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 9 28.
Time Qed.
End TM1253.


Module TM1254.
Definition tm := TM_from_str "1RB1LD_1LC1LB_0RE1RD_1RC0LA_1LA1RF_---0RE".
Definition tm' := TM_from_str "1RB0LD_0RC1RA_1LD1RF_1RE1LA_1LB1LE_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBACF") 42 35.
Time Qed.
End TM1254.


Module TM1255.
Definition tm := TM_from_str "1LB1LD_0RC1RE_1LA0RD_0LE0LF_1RB0LA_0RA---".
Definition tm' := TM_from_str "1RB0LD_0RC1RA_1LD0RE_1LB1LE_0LA0LF_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 5 1.
Time Qed.
End TM1255.


Module TM1256.
Definition tm := TM_from_str "1LB1LA_0RC---_1RD1RC_1RE0LA_1LF1RB_0RB0LF".
Definition tm' := TM_from_str "1RB0LF_1LC1RD_0RD0LC_0RE---_1RA1RE_1LD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 1 4.
Time Qed.
End TM1256.


Module TM1257.
Definition tm := TM_from_str "1LB0RC_0LC0LB_1RD0RE_0RA---_1LA1RF_1RA0RE".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_0LD0LC_1RE0RF_0RB---_1LB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 6624 6826.
Time Qed.
End TM1257.


Module TM1258.
Definition tm := TM_from_str "1RB---_1LC1LF_1RD0LB_1RA1RE_0RC0RE_1LB0RB".
Definition tm' := TM_from_str "1RB0LD_1RC1RF_1RD---_1LA1LE_1LD0RD_0RA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 10 7.
Time Qed.
End TM1258.


Module TM1259.
Definition tm := TM_from_str "1LB1LF_1RC1RB_1RD0RC_0LE0LF_0RC0LA_---1LE".
Definition tm' := TM_from_str "1RB0RA_0LC0LF_0RA0LD_1LE1LF_1RA1RE_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM1259.


Module TM1260.
Definition tm := TM_from_str "1RB0LB_1LC0RE_0LC1LD_1RB0RA_1RA1RF_1RE---".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_0LC1LA_1RF1RE_1RD---_1RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM1260.


Module TM1261.
Definition tm := TM_from_str "1RB0RF_0RC0LE_1LD0RA_1LE---_0LF0LD_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_0RC0LE_1LD0RF_1LE---_0LA0LD_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1261.


Module TM1262.
Definition tm := TM_from_str "1RB1LC_1LA1RD_1RB0LC_1RE1LD_1RC0RF_---0RB".
Definition tm' := TM_from_str "1RB0LA_1LC1RD_1RB1LA_1RE1LD_1RA0RF_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBADEF") 1 1.
Time Qed.
End TM1262.


Module TM1263.
Definition tm := TM_from_str "1RB0RD_1LC0RA_0RA0LD_1LE1LF_1RA1LB_0LB---".
Definition tm' := TM_from_str "1RB1LC_1RC0RE_1LD0RB_0RB0LE_1LA1LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 13 18.
Time Qed.
End TM1263.


Module TM1264.
Definition tm := TM_from_str "1RB---_0RC1RA_1RD0RE_1LE0RF_0LF0LE_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1264.


Module TM1265.
Definition tm := TM_from_str "1RB1LA_0LA0RC_1RD1LB_1RB0RE_0RB0RF_1LB---".
Definition tm' := TM_from_str "1RB0RE_0LC0RD_1RB1LC_1RA1LB_0RB0RF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDAEF") 1 1.
Time Qed.
End TM1265.


Module TM1266.
Definition tm := TM_from_str "1RB0LA_0LC0RD_1RD1LA_1RE---_1LA0RF_0RB1RD".
Definition tm' := TM_from_str "1RB---_1LC0RF_1RD0LC_0LE0RA_1RA1LC_0RD1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 34 45.
Time Qed.
End TM1266.


Module TM1267.
Definition tm := TM_from_str "1LB1RE_1RC1LA_1LD0RC_0LA0RD_1RF0RA_---0LD".
Definition tm' := TM_from_str "1RB1LD_1LC0RB_0LD0RC_1LA1RE_1RF0RD_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 6.
Time Qed.
End TM1267.


Module TM1268.
Definition tm := TM_from_str "1LB---_1RC1RF_1LE0RD_0LC0RD_0LA1LA_1LC0RF".
Definition tm' := TM_from_str "1RB1RF_1LC0RE_0LD1LD_1LA---_0LB0RE_1LB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 4 1.
Time Qed.
End TM1268.


Module TM1269.
Definition tm := TM_from_str "1LB0LF_1RC1LA_---1RD_1RE1RB_0RF0RA_1LA1RE".
Definition tm' := TM_from_str "1RB1RE_0RC0RD_1LD1RB_1LE0LC_1RF1LD_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 196288 185934.
Time Qed.
End TM1269.


Module TM1270.
Definition tm := TM_from_str "1LB1LE_1RC1LB_1LA1RD_1RE0RC_1RB1RF_---0LA".
Definition tm' := TM_from_str "1RB1LA_1LC1RE_1LA1LD_1RA1RF_1RD0RB_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 29 28.
Time Qed.
End TM1270.


Module TM1271.
Definition tm := TM_from_str "1RB1RD_1LC1RF_1RF0LD_1RE0LB_0RC---_1RB0RA".
Definition tm' := TM_from_str "1RB0RF_1LC1RA_1RA0LD_1RE0LB_0RC---_1RB1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1271.


Module TM1272.
Definition tm := TM_from_str "1LB0LF_0RC1RE_1RF1RD_1LE0RF_1LA0RB_1LA---".
Definition tm' := TM_from_str "1RB1RE_1LC---_1LD0LB_0RA1RF_1LF0RB_1LC0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEFB") 7 2.
Time Qed.
End TM1272.


Module TM1273.
Definition tm := TM_from_str "1RB---_1RC1RD_1LD0RF_1RB0LE_1LD1LC_0RA0LE".
Definition tm' := TM_from_str "1RB1RC_1LC0RE_1RA0LD_1LC1LB_0RF0LD_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 41 18.
Time Qed.
End TM1273.


Module TM1274.
Definition tm := TM_from_str "1RB---_1LC1RF_1RE1LD_0LB0RC_1RF0RA_0RD0RE".
Definition tm' := TM_from_str "1RB1LD_1RC0RF_0RD0RB_0LE0RA_1LA1RC_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEADBC") 2 7.
Time Qed.
End TM1274.


Module TM1275.
Definition tm := TM_from_str "1LB0RB_0LC1LD_1RD1LE_0RA0LB_0LD0LF_0RA---".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0RD_0LA1LB_0LB0LF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 21 35.
Time Qed.
End TM1275.


Module TM1276.
Definition tm := TM_from_str "1LB1LE_1RC0LC_0LA0RD_1RB0RD_0RE0LF_1RA---".
Definition tm' := TM_from_str "1RB0RA_1RC0LC_0LD0RA_1LB1LE_0RE0LF_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 19 1.
Time Qed.
End TM1276.


Module TM1277.
Definition tm := TM_from_str "1LB1RB_0RC1LD_1RA0LB_0LB1LE_0LC0LF_1RB---".
Definition tm' := TM_from_str "1RB---_0RC1LE_1RD0LB_1LB1RB_0LB1LF_0LC0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 68 46.
Time Qed.
End TM1277.


Module TM1278.
Definition tm := TM_from_str "1LB1LD_1RC0RB_---0LD_1RF1LE_0RC1RB_1LA0RF".
Definition tm' := TM_from_str "1RB1LF_1LC0RB_1LD1LA_1RE0RD_---0LA_0RE1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEAFB") 7 1.
Time Qed.
End TM1278.


Module TM1279.
Definition tm := TM_from_str "1RB1LC_1LA1RD_1LA1LD_1RE0LA_1RB0RF_---0RA".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1RB1LD_1LC1LE_1RA0LC_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM1279.


Module TM1280.
Definition tm := TM_from_str "1RB1RA_0LC0RB_1RB1LD_0LE1RE_1LA1LF_---1LE".
Definition tm' := TM_from_str "1RB1LC_0LA0RB_0LD1RD_1LE1LF_1RB1RE_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM1280.


Module TM1281.
Definition tm := TM_from_str "1RB0LD_1RC1RF_1RD---_1LA1LE_1RD1LD_0RA0RF".
Definition tm' := TM_from_str "1RB---_1LC1LF_1RD0LB_1RA1RE_0RC0RE_1RB1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 6 13.
Time Qed.
End TM1281.


Module TM1282.
Definition tm := TM_from_str "1RB1RD_0LC---_0RD0LC_1RE0RA_1RF0LA_1LC1LF".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDABC") 5 1.
Time Qed.
End TM1282.


Module TM1283.
Definition tm := TM_from_str "1RB---_0RC0RB_1LD0RE_0LD1RA_1LE1LF_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0RF_0LD1RE_1RB---_1LF1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1283.


Module TM1284.
Definition tm := TM_from_str "1RB0LE_1RC0RB_1LD0RA_0LA0LC_0LF---_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_1RC0RB_1LD0RE_0LE0LC_1RB0LF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1284.


Module TM1285.
Definition tm := TM_from_str "1LB0RC_1RA---_1LD1RC_1LE0RA_0LA1LF_1RD0LF".
Definition tm' := TM_from_str "1RB0LA_1LC0RD_0LD1LA_1LF0RE_1LB1RE_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFEBCA") 25 18.
Time Qed.
End TM1285.


Module TM1286.
Definition tm := TM_from_str "1LB0RC_1RC0LE_1LC1RD_1RA1RD_---0LF_1RA1LF".
Definition tm' := TM_from_str "1RB0LE_1LB1RC_1RD1RC_1LA0RB_---0LF_1RD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 3 4.
Time Qed.
End TM1286.


Module TM1287.
Definition tm := TM_from_str "1RB1RC_1LA1RA_1RE1LD_0LE0LC_1RB0RF_0RB---".
Definition tm' := TM_from_str "1RB0RF_1LC1RC_1RB1RD_1RA1LE_0LA0LD_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM1287.


Module TM1288.
Definition tm := TM_from_str "1RB0RC_0LA0RE_0LD0RF_1LE1RA_1RD0LC_1RB---".
Definition tm' := TM_from_str "1RB---_0LC0RF_1RB0RD_0LE0RA_1LF1RC_1RE0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM1288.


Module TM1289.
Definition tm := TM_from_str "1RB---_0RC1LE_0LD1RF_1LB0RA_0LF0LA_1RC0LB".
Definition tm' := TM_from_str "1RB0LE_0LC1RA_1LE0RD_1RE---_0RB1LF_0LA0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 1 4.
Time Qed.
End TM1289.


Module TM1290.
Definition tm := TM_from_str "1LB1RC_1RA0LE_0RD0LA_1LC1RD_0LC1LF_1RD---".
Definition tm' := TM_from_str "1RB---_1LC1RB_0RB0LD_1LE1RC_1RD0LF_0LC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECBFA") 6 7.
Time Qed.
End TM1290.


Module TM1291.
Definition tm := TM_from_str "1LB0LD_1RC---_1LD1RC_1RF1LE_1LC1LA_1RC0RF".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LC1LE_1LF0LA_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCADB") 3 2.
Time Qed.
End TM1291.


Module TM1292.
Definition tm := TM_from_str "1LB1RE_1RC1LD_1RA0RB_0LB0LC_1RF0RB_---0RD".
Definition tm' := TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF0RC_---0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 33 24.
Time Qed.
End TM1292.


Module TM1293.
Definition tm := TM_from_str "1LB1RA_1RC1LF_0LD0RC_1RE1LE_1LA---_1LA0LB".
Definition tm' := TM_from_str "1RB1LB_1LC---_1LD1RC_1RF1LE_1LC0LD_0LA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFABE") 13 11.
Time Qed.
End TM1293.


Module TM1294.
Definition tm := TM_from_str "1LB1LD_1RC0RF_---0LD_1RF1LE_0RC1RF_1LA0RB".
Definition tm' := TM_from_str "1RB1LF_1LC0RD_1LD1LA_1RE0RB_---0LA_0RE1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEAFB") 7 1.
Time Qed.
End TM1294.


Module TM1295.
Definition tm := TM_from_str "1LB1LA_0RC---_1RD1RC_1RE1LA_1LF0RB_0RB0LF".
Definition tm' := TM_from_str "1RB1LF_1LC0RD_0RD0LC_0RE---_1RA1RE_1LD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 1 4.
Time Qed.
End TM1295.


Module TM1296.
Definition tm := TM_from_str "1LB---_1RC1RB_1RE1RD_0LE0RD_0LC1LF_1LA1LE".
Definition tm' := TM_from_str "1RB1RA_1RC1RD_0LB1LE_0LC0RD_1LF1LC_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABDCE") 2 3.
Time Qed.
End TM1296.


Module TM1297.
Definition tm := TM_from_str "1RB0LE_0LC1RC_1RD0RC_1LA0LC_1LF0LA_1LD---".
Definition tm' := TM_from_str "1RB0RA_1LC0LA_1RF0LD_1LE0LC_1LB---_0LA1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 4 1.
Time Qed.
End TM1297.


Module TM1298.
Definition tm := TM_from_str "1RB0LC_1LA0RE_1RD0LA_1RB0RD_1RF---_1RC0RA".
Definition tm' := TM_from_str "1RB0RA_1LC0RE_1RB0LD_1RA0LC_1RF---_1RD0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDAEF") 1 1.
Time Qed.
End TM1298.


Module TM1299.
Definition tm := TM_from_str "1LB1RD_0LC0RC_1RD1LE_0RA0LB_0LD0LF_0RE---".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD1RB_0LA0RA_0LB0LF_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 17 31.
Time Qed.
End TM1299.


Module TM1300.
Definition tm := TM_from_str "1RB0LF_1LC0RD_1LA1LC_---0RE_1LA1RE_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_1LC0RE_1LD1LC_1RB0LA_---0RF_1LD1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM1300.


Module TM1301.
Definition tm := TM_from_str "1LB0RC_1RC0LD_1RA1RD_1LE0RC_1RF0LA_---1RE".
Definition tm' := TM_from_str "1RB0LD_1RC1RD_1LA0RB_1LE0RB_1RF0LC_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 6 5.
Time Qed.
End TM1301.


Module TM1302.
Definition tm := TM_from_str "1RB1LE_0RC0RB_1LD0LA_1LE---_1LF0LA_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LF_1LE---_1LA0LF_1RB1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1302.


Module TM1303.
Definition tm := TM_from_str "1LB1LF_1RC1RB_0LD0RC_0LB1LE_1LA1LD_1RB---".
Definition tm' := TM_from_str "1RB---_1RC1RB_0LD0RC_0LB1LE_1LF1LD_1LB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 6 1.
Time Qed.
End TM1303.


Module TM1304.
Definition tm := TM_from_str "1LB1RF_0RC0LB_1RD1LC_0RE1LE_1RA1RE_0LC---".
Definition tm' := TM_from_str "1RB1RA_1LC1RF_0RD0LC_1RE1LD_0RA1LA_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 3 4.
Time Qed.
End TM1304.


Module TM1305.
Definition tm := TM_from_str "1LB1LE_1LC0RB_0LD1LA_0RE1LF_1RB0LC_0LE---".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 30.
Time Qed.
End TM1305.


Module TM1306.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1LB_0RC0LF_0RC---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM1306.


Module TM1307.
Definition tm := TM_from_str "1RB1LD_1LC1LB_0RE1RD_1RC0LA_1LA0RF_---0LD".
Definition tm' := TM_from_str "1RB0LD_0RC1RA_1LD0RF_1RE1LA_1LB1LE_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBACF") 48 39.
Time Qed.
End TM1307.


Module TM1308.
Definition tm := TM_from_str "1LB0LB_1RC0LC_1RD1LC_1LC0RE_---0RF_1LA1RF".
Definition tm' := TM_from_str "1RB1LA_1LA0RC_---0RD_1LE1RD_1LF0LF_1RA0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 3 2.
Time Qed.
End TM1308.


Module TM1309.
Definition tm := TM_from_str "1RB0RD_0LC1LE_0RD0LB_1RA0RD_1LF0RD_1LB---".
Definition tm' := TM_from_str "1RB0RA_1RC0RA_0LD1LE_0RA0LC_1LF0RA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 6 1.
Time Qed.
End TM1309.


Module TM1310.
Definition tm := TM_from_str "1LB1LA_0RC---_1RD1RC_1RE0LA_1LF1RF_0RB0LF".
Definition tm' := TM_from_str "1RB0LF_1LC1RC_0RD0LC_0RE---_1RA1RE_1LD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 1 4.
Time Qed.
End TM1310.


Module TM1311.
Definition tm := TM_from_str "1RB1RF_1RC0LD_1LB0RE_1RB0LB_1RA1RE_1LD---".
Definition tm' := TM_from_str "1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM1311.


Module TM1312.
Definition tm := TM_from_str "1LB0LE_0RC0LB_1RE1RD_1LE0RF_1LA0RB_1RE---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1LD0LB_0RE0LD_1RB1RF_1LB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 8 1.
Time Qed.
End TM1312.


Module TM1313.
Definition tm := TM_from_str "1RB1RD_1RC1LB_0LA0RC_1LE0LD_1RB0LF_---1LD".
Definition tm' := TM_from_str "1RB0LF_1RC1LB_0LD0RC_1RB1RE_1LA0LE_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 1.
Time Qed.
End TM1313.


Module TM1314.
Definition tm := TM_from_str "1RB1RE_1LC---_1LD1LC_0RE0LD_1RF0RA_1RC0LA".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCDAB") 56 36.
Time Qed.
End TM1314.


Module TM1315.
Definition tm := TM_from_str "1LB1RA_1RA0LC_---0LD_0RE1LF_0RA1RE_1RE1LC".
Definition tm' := TM_from_str "1RB1LE_0RC1RB_1LD1RC_1RC0LE_---0LF_0RB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 11 4.
Time Qed.
End TM1315.


Module TM1316.
Definition tm := TM_from_str "1LB1RD_1LC1LB_1RA1RE_0RC0RA_1RF0LE_1RC---".
Definition tm' := TM_from_str "1RB1RE_1LC1RD_1LA1LC_0RA0RB_1RF0LE_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 55 75.
Time Qed.
End TM1316.


Module TM1317.
Definition tm := TM_from_str "1RB0LB_1RC0RE_1LD0LE_1LA0LD_1RB1RF_1RB---".
Definition tm' := TM_from_str "1RB1RF_1RC0RA_1LD0LA_1LE0LD_1RB0LB_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1317.


Module TM1318.
Definition tm := TM_from_str "1LB---_0LC0RD_1RB1LC_1RE1LB_0LF0RF_0RB1RA".
Definition tm' := TM_from_str "1RB1LE_0LC0RC_0RE1RD_1LE---_0LF0RA_1RE1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 1 6.
Time Qed.
End TM1318.


Module TM1319.
Definition tm := TM_from_str "1RB0LC_1LA1RD_0LB1LD_1LA1LE_1LF0RE_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1RE_1RB0LD_0LB1LE_1LC1LF_1LA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM1319.


Module TM1320.
Definition tm := TM_from_str "1RB1RA_1LC0RA_---1LD_1RB1LE_0LD1LF_0LC1LD".
Definition tm' := TM_from_str "1RB1LE_1LC0RD_---1LA_1RB1RD_0LA1LF_0LC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM1320.


Module TM1321.
Definition tm := TM_from_str "1RB0RE_0LC1LE_1RD1LC_0LB0LB_1RA1RF_---1LD".
Definition tm' := TM_from_str "1RB1LA_0LC0LC_0LA1LD_1RE1RF_1RC0RD_---1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECABDF") 5 2.
Time Qed.
End TM1321.


Module TM1322.
Definition tm := TM_from_str "1LB1LE_1RC0LB_0LD1RD_0LA0RA_0RD1LF_1LA---".
Definition tm' := TM_from_str "1RB0LA_0LC1RC_0LD0RD_1LA1LE_0RC1LF_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 4.
Time Qed.
End TM1322.


Module TM1323.
Definition tm := TM_from_str "1LB0RC_1RA0LE_1RD1RB_1RA0RF_1LB0LA_0RA---".
Definition tm' := TM_from_str "1RB1RD_1RC0RF_1LD0RA_1RC0LE_1LD0LC_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 305 302.
Time Qed.
End TM1323.


Module TM1324.
Definition tm := TM_from_str "1LB1RA_0RB0LC_1RD1LC_1RA1RE_1RF0RA_---0RD".
Definition tm' := TM_from_str "1RB1LA_1RC1RE_1LD1RC_0RD0LA_1RF0RC_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 4 1.
Time Qed.
End TM1324.


Module TM1325.
Definition tm := TM_from_str "1LB0RE_0LC1RF_1RD1LD_0LA0RB_1RB---_0RD0RA".
Definition tm' := TM_from_str "1RB1LB_0LC0RE_1LE0RD_1RE---_0LA1RF_0RB0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEABDF") 823 878.
Time Qed.
End TM1325.


Module TM1326.
Definition tm := TM_from_str "1LB0RB_0RC0LE_0LE0RD_1RA1RE_1LF---_1RC0LB".
Definition tm' := TM_from_str "1RB1RD_1LC0RC_0RF0LD_1LE---_1RF0LC_0LD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFADE") 4 1.
Time Qed.
End TM1326.


Module TM1327.
Definition tm := TM_from_str "1RB1LA_0LA0RC_1RD1LB_1LC0RE_0RB1RF_1RA---".
Definition tm' := TM_from_str "1RB---_1RC1LB_0LB0RD_1RE1LC_1LD0RF_0RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 32 32.
Time Qed.
End TM1327.


Module TM1328.
Definition tm := TM_from_str "1RB---_1RC0RB_0LD1LC_0RA1LE_0RF1LF_0LA0LC".
Definition tm' := TM_from_str "1RB0RA_0LC1LB_0RF1LD_0RE1LE_0LF0LB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 1 8.
Time Qed.
End TM1328.


Module TM1329.
Definition tm := TM_from_str "1RB0LA_0LC1LB_0RD1LA_1RE1RD_1RA0RF_---0RD".
Definition tm' := TM_from_str "1RB1RA_1RC0RF_1RD0LC_0LE1LD_0RA1LC_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 34 20.
Time Qed.
End TM1329.


Module TM1330.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_1RF0LD_1LD---".
Definition tm' := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 32 11.
Time Qed.
End TM1330.


Module TM1331.
Definition tm := TM_from_str "1RB0RC_0LC0RE_---1LD_1LA0LF_1RB1RE_1RB0LB".
Definition tm' := TM_from_str "1RB1RA_0LC0RA_---1LD_1LE0LF_1RB0RC_1RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1331.


Module TM1332.
Definition tm := TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_0RF0LD_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1RE_1LD0LC_1RB1RF_1RD0RB_0RA0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM1332.


Module TM1333.
Definition tm := TM_from_str "1LB0RF_0RC0LE_1RD1LC_1RA0LD_1RD0RA_0RB---".
Definition tm' := TM_from_str "1RB0LA_1LC0RE_0RF0LD_1RA0RB_0RC---_1RA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFADE") 7 1.
Time Qed.
End TM1333.


Module TM1334.
Definition tm := TM_from_str "1RB1LC_0LA0RD_1LA0LC_0LF1RE_1RD0RE_---1RB".
Definition tm' := TM_from_str "1RB0RA_0LC1RA_---1RD_0LE0RB_1RD1LF_1LE0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDFBAC") 1 3.
Time Qed.
End TM1334.


Module TM1335.
Definition tm := TM_from_str "1LB0RA_1RC0LB_1RD0LB_1RE---_1LF1RA_1LA1LF".
Definition tm' := TM_from_str "1RB0LA_1RC0LA_1RD---_1LE1RF_1LF1LE_1LA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 5 1.
Time Qed.
End TM1335.


Module TM1336.
Definition tm := TM_from_str "1RB0RF_1RC1RC_1RD---_1RE1RB_1LF1LA_1RA0LE".
Definition tm' := TM_from_str "1RB1RE_1LC1LD_1RD0LB_1RE0RC_1RF1RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 19 11.
Time Qed.
End TM1336.


Module TM1337.
Definition tm := TM_from_str "1RB---_0RC0RB_1LD0RE_0LE1LA_1LF0LB_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1337.


Module TM1338.
Definition tm := TM_from_str "1RB0RA_1LC0RA_1RB1LD_0LE---_0LF0RF_0LB1RF".
Definition tm' := TM_from_str "1RB1LC_1LA0RF_0LD---_0LE0RE_0LB1RE_1RB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBACDE") 1 1.
Time Qed.
End TM1338.


Module TM1339.
Definition tm := TM_from_str "1LB1LA_0RC0RE_0LD0RD_1RC1LE_0LA1RF_---1RD".
Definition tm' := TM_from_str "1RB1LC_0LA0RA_0LD1RF_1LE1LD_0RB0RC_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBACF") 4 1.
Time Qed.
End TM1339.


Module TM1340.
Definition tm := TM_from_str "1RB1RC_1LC---_1LD1RC_1RF1LE_1LB0LD_1RA0RF".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_1RD1RE_1LE---_1LA1RE_1LD0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEAFB") 10 5.
Time Qed.
End TM1340.


Module TM1341.
Definition tm := TM_from_str "1LB1LA_1RC1LF_1RE1RD_0RB1RC_1RA---_0RD0LF".
Definition tm' := TM_from_str "1RB---_1LC1LB_1RF1LD_0RE0LD_0RC1RF_1RA1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFEAD") 2 5.
Time Qed.
End TM1341.


Module TM1342.
Definition tm := TM_from_str "1LB1RC_1RA1RC_1RA1LD_0LF0LE_0RC1RE_---0LD".
Definition tm' := TM_from_str "1RB1RC_1LA1RC_1RB1LD_0LF0LE_0RC1RE_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BACDEF") 2 7.
Time Qed.
End TM1342.


Module TM1343.
Definition tm := TM_from_str "1RB0LE_1RC1RA_1LD0RA_0RC0LD_1LA0RF_1RE---".
Definition tm' := TM_from_str "1RB1RD_1LC0RD_0RB0LC_1RA0LE_1LD0RF_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 9 9.
Time Qed.
End TM1343.


Module TM1344.
Definition tm := TM_from_str "1LB0RD_1LC0LB_1RA0LD_1RE0LA_1RA1RF_0LD---".
Definition tm' := TM_from_str "1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 5 1.
Time Qed.
End TM1344.


Module TM1345.
Definition tm := TM_from_str "1LB0LD_1RC1RF_0LA1RB_0RA1LE_---1LA_0LA0RB".
Definition tm' := TM_from_str "1RB1RF_0LC1RA_1LA0LD_0RC1LE_---1LC_0LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 5.
Time Qed.
End TM1345.


Module TM1346.
Definition tm := TM_from_str "1RB1RA_0LC0RB_1RB1LD_0LE1LE_1LA1RF_---1LC".
Definition tm' := TM_from_str "1RB1LC_0LA0RB_0LD1LD_1LE1RF_1RB1RE_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM1346.


Module TM1347.
Definition tm := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA0LC".
Definition tm' := TM_from_str "1RB0LD_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 5 9.
Time Qed.
End TM1347.


Module TM1348.
Definition tm := TM_from_str "1LB0LD_1RC1RF_0LA1RB_0RA0LE_---1LA_0RB0RB".
Definition tm' := TM_from_str "1RB1RF_0LC1RA_1LA0LD_0RC0LE_---1LC_0RA0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 5.
Time Qed.
End TM1348.


Module TM1349.
Definition tm := TM_from_str "1RB0RE_1RC0LE_1RD---_0LB1RF_0RD1LD_1RA1LB".
Definition tm' := TM_from_str "1RB---_0LC1RE_1RA0LD_0RB1LB_1RF1LC_1RC0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCABDE") 10 10.
Time Qed.
End TM1349.


Module TM1350.
Definition tm := TM_from_str "1LB---_0LC1LE_1LD1LA_1RE0RF_0LD0RD_0LA0RD".
Definition tm' := TM_from_str "1RB0RC_0LA0RA_0LD0RA_1LE---_0LF1LB_1LA1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 1 5.
Time Qed.
End TM1350.


Module TM1351.
Definition tm := TM_from_str "1RB1RD_0RC0RE_0RD0RA_0LE0LF_1LD0LA_1RA---".
Definition tm' := TM_from_str "1RB---_1RC1RE_0RD0RF_0RE0RB_0LF0LA_1LE0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 49 30.
Time Qed.
End TM1351.


Module TM1352.
Definition tm := TM_from_str "1RB1LE_0RC0RB_1LD0LF_1LE---_1LA0LF_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1RB1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1352.


Module TM1353.
Definition tm := TM_from_str "1RB0LC_1RC0RA_0LD1LA_---1LE_0LF0LA_0LA0RE".
Definition tm' := TM_from_str "1RB0RF_0LC1LF_---1LD_0LE0LF_0LF0RD_1RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 27 36.
Time Qed.
End TM1353.


Module TM1354.
Definition tm := TM_from_str "1RB1LB_1LC1LA_1RD0LB_1RF1RE_0RC0RE_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1LF_1RD0LB_1RA1RE_0RC0RE_1RB1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1354.


Module TM1355.
Definition tm := TM_from_str "1LB1LE_1RC0LD_0LA0RD_1RB0RD_0LD1LF_0LC---".
Definition tm' := TM_from_str "1RB0RA_1RC0LA_0LD0RA_1LB1LE_0LA1LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 17 1.
Time Qed.
End TM1355.


Module TM1356.
Definition tm := TM_from_str "1RB---_1RC0RC_1LD0LE_1RF1LC_1LC0LA_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1356.


Module TM1357.
Definition tm := TM_from_str "1LB0LC_0RA---_1RD1LF_1RE0RD_1LC0RA_1LE1LA".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0RE_1LC1LE_1LF0LA_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 4 1.
Time Qed.
End TM1357.


Module TM1358.
Definition tm := TM_from_str "1LB1RA_0LC1LC_1LD0LA_1RE1RD_---0RF_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_0LC1LC_1LE0LD_1LB1RD_1RF1RE_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 4.
Time Qed.
End TM1358.


Module TM1359.
Definition tm := TM_from_str "1RB1RF_0LC0LE_1RA1LD_0LE1LA_0RF1LC_0RB---".
Definition tm' := TM_from_str "1RB1LD_1RC1RF_0LA0LE_0LE1LB_0RF1LA_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 11 1.
Time Qed.
End TM1359.


Module TM1360.
Definition tm := TM_from_str "1LB1LC_0RC1LA_0LA0RD_0LE0RF_1RD1RA_---1RC".
Definition tm' := TM_from_str "1RB1RC_0LA0RF_1LD1LE_0RE1LC_0LC0RB_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBAF") 5 1.
Time Qed.
End TM1360.


Module TM1361.
Definition tm := TM_from_str "1RB1RE_1RC0RF_1LD1LE_1RB0LC_1RA0RD_1RE---".
Definition tm' := TM_from_str "1RB0LC_1RC0RF_1LA1LD_1RE0RA_1RB1RD_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM1361.


Module TM1362.
Definition tm := TM_from_str "1RB0RC_0LC1RE_---0LD_0RE1LF_1RA0LD_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0LC1RE_---0LD_0RE1LA_1RF0LD_1RB0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1362.


Module TM1363.
Definition tm := TM_from_str "1RB0LC_1RC0RA_0LD1LA_0LA1LE_1RA0LF_0RD---".
Definition tm' := TM_from_str "1RB0RE_0LC1LE_0LE1LD_1RE0LF_1RA0LB_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 55 89.
Time Qed.
End TM1363.


Module TM1364.
Definition tm := TM_from_str "1LB0RF_0LC1RA_1RD1LB_0RE---_1RB1RE_1LF0RC".
Definition tm' := TM_from_str "1RB1RA_0LC1RE_1RD1LB_0RA---_1LB0RF_1LF0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 3.
Time Qed.
End TM1364.


Module TM1365.
Definition tm := TM_from_str "1LB1RB_1RC1RE_0LF0RD_1RA0RF_---1LC_1LC1LB".
Definition tm' := TM_from_str "1RB1RF_0LC0RD_1LB1LA_1RE0RC_1LA1RA_---1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABDFC") 1 3.
Time Qed.
End TM1365.


Module TM1366.
Definition tm := TM_from_str "1RB1LA_1LC1LB_0RD0LC_1RE---_0RF1RF_1RA1RF".
Definition tm' := TM_from_str "1RB---_0RC1RC_1RD1RC_1RE1LD_1LF1LE_0RA0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 65 35.
Time Qed.
End TM1366.


Module TM1367.
Definition tm := TM_from_str "1LB0RA_1RC0LC_1RD1LC_0LB1RE_1RF0RB_0RA---".
Definition tm' := TM_from_str "1RB0RD_0RC---_1LD0RC_1RE0LE_1RF1LE_0LD1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 2 14.
Time Qed.
End TM1367.


Module TM1368.
Definition tm := TM_from_str "1RB0RD_1LC0RF_0RA1LB_---1RE_1LF1RA_1RB0LE".
Definition tm' := TM_from_str "1RB0LF_1LC0RA_0RD1LB_1RB0RE_---1RF_1LA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM1368.


Module TM1369.
Definition tm := TM_from_str "1RB0RF_1LC1RE_1LD0LC_1RB1LD_1RA0RB_1LC---".
Definition tm' := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM1369.


Module TM1370.
Definition tm := TM_from_str "1RB1RE_1LC---_1LE1LD_1LC0RA_1RD0LF_0LD0RE".
Definition tm' := TM_from_str "1RB0LE_1LC0RD_1LA1LB_1RF1RA_0LB0RA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFCBAE") 2 2.
Time Qed.
End TM1370.


Module TM1371.
Definition tm := TM_from_str "1LB0LA_1LC---_1LD1LF_1RE0LD_0LF0RE_1RD0RA".
Definition tm' := TM_from_str "1RB0LA_0LC0RB_1RA0RD_1LE0LD_1LF---_1LA1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 1 4.
Time Qed.
End TM1371.


Module TM1372.
Definition tm := TM_from_str "1LB1LE_1RC0RB_1RF0RD_1LE1RB_1LA0LE_1RD---".
Definition tm' := TM_from_str "1RB0RA_1RC0RD_1RD---_1LE1RA_1LF0LE_1LA1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABDEC") 2728 2758.
Time Qed.
End TM1372.


Module TM1373.
Definition tm := TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RF_1RB1RE".
Definition tm' := TM_from_str "1RB1RE_1RC1LB_1LD1RE_1LB0LD_1RF0RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1373.


Module TM1374.
Definition tm := TM_from_str "1LB1LE_1RC---_0RD1RD_1RE0RA_1LF0LA_0RB0LF".
Definition tm' := TM_from_str "1RB0RF_1LC0LF_0RD0LC_1RE---_0RA1RA_1LD1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 1 4.
Time Qed.
End TM1374.


Module TM1375.
Definition tm := TM_from_str "1RB---_1RC1RD_1LD0RF_1RB0LE_1LD1LC_0RA0LC".
Definition tm' := TM_from_str "1RB0LD_1RC1RA_1LA0RE_1LA1LC_0RF0LC_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM1375.


Module TM1376.
Definition tm := TM_from_str "1LB1RE_0LC1LF_0RD0LA_1RA1RE_1RF---_0RC0RC".
Definition tm' := TM_from_str "1RB---_0RC0RC_0RD0LE_1RE1RA_1LF1RA_0LC1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCDAB") 25 24.
Time Qed.
End TM1376.


Module TM1377.
Definition tm := TM_from_str "1LB1RA_1RC1LE_1RD1LC_1RA0RA_1LF0LC_---0LB".
Definition tm' := TM_from_str "1RB1LA_1RC0RC_1LD1RC_1RA1LE_1LF0LA_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 263 276.
Time Qed.
End TM1377.


Module TM1378.
Definition tm := TM_from_str "1RB0LF_0RC0RB_0LD1LA_1LD0LE_1RB0LA_---0LE".
Definition tm' := TM_from_str "1RB0LE_0RC0RB_0LD1LE_1LD0LA_1RB0LF_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1378.


Module TM1379.
Definition tm := TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA0LD_1LB0RF_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1LD0LB_0RE0LD_1RB1RF_1LB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1379.


Module TM1380.
Definition tm := TM_from_str "1LB0RA_1LC1LA_1LD1LF_1RE---_1LA0RF_0LB1RE".
Definition tm' := TM_from_str "1RB---_1LC0RF_1LD0RC_1LE1LC_1LA1LF_0LD1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 1 5.
Time Qed.
End TM1380.


Module TM1381.
Definition tm := TM_from_str "1RB0RF_1LC1RA_1LE0RD_1LD1RC_1RA0LC_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1RF_1LE0RD_1LD1RC_1RF0LC_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1381.


Module TM1382.
Definition tm := TM_from_str "1LB---_0LC1LF_0RD0LB_1RE0RD_1RB1RB_1LA0RD".
Definition tm' := TM_from_str "1RB1RB_0LC1LE_0RD0LB_1RA0RD_1LF0RD_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 5 7.
Time Qed.
End TM1382.


Module TM1383.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RD1LB_0LF1RE_0RA1RF_1LB---".
Definition tm' := TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA---_0RF1RD_1LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCED") 3 4.
Time Qed.
End TM1383.


Module TM1384.
Definition tm := TM_from_str "1LB0RD_1LC1LE_1RA1RE_1RC1RC_1RD0RF_---0LA".
Definition tm' := TM_from_str "1RB1RB_1RC1RE_1LD0RA_1LB1LE_1RA0RF_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBAEF") 395 358.
Time Qed.
End TM1384.


Module TM1385.
Definition tm := TM_from_str "1RB0LD_0RC0RE_1LD1RF_1LA0LA_1RB0LA_---1RB".
Definition tm' := TM_from_str "1RB0LE_0RC0RA_1LD1RF_1LE0LE_1RB0LD_---1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1385.


Module TM1386.
Definition tm := TM_from_str "1RB1RA_1RC0LF_1LD0RD_0RE0LD_0RF---_1RA1LF".
Definition tm' := TM_from_str "1RB0LE_1LC0RC_0RD0LC_0RE---_1RF1LE_1RA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 7 6.
Time Qed.
End TM1386.


Module TM1387.
Definition tm := TM_from_str "1LB1LA_1RC1LE_1LF0RD_0RE1RF_1RA0LA_---1RC".
Definition tm' := TM_from_str "1RB1LE_1LC0RD_---1RB_0RE1RC_1RF0LF_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABDEC") 2 3.
Time Qed.
End TM1387.


Module TM1388.
Definition tm := TM_from_str "1RB0LF_1RC---_1RD1RE_0LE0LF_0RC0LA_---1LE".
Definition tm' := TM_from_str "1RB1RC_0LC0LF_0RA0LD_1RE0LF_1RA---_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM1388.


Module TM1389.
Definition tm := TM_from_str "1RB1LE_1RC0RF_1LD0RC_0LA1LE_0RB0LE_---0LD".
Definition tm' := TM_from_str "1RB0RE_1LC0RB_0LF1LD_0RA0LD_---0LC_1RA1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 1 8.
Time Qed.
End TM1389.


Module TM1390.
Definition tm := TM_from_str "1LB0LF_0RC1RF_1RF1RD_0LD1RE_1LF---_1LA0RB".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA1RB_0LE1RF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEFB") 8 1.
Time Qed.
End TM1390.


Module TM1391.
Definition tm := TM_from_str "1RB1LD_1LC0RD_0LA0RD_0LF1LE_0RB---_1RE0LC".
Definition tm' := TM_from_str "1RB0LD_0RC---_1LD0RF_0LE0RF_1RC1LF_0LA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDFBA") 8 1.
Time Qed.
End TM1391.


Module TM1392.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC1LF_1RC---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM1392.


Module TM1393.
Definition tm := TM_from_str "1LB1RE_1LC0LF_1LD0LE_1RA0LB_1RD0RA_---0RB".
Definition tm' := TM_from_str "1RB0RC_1RC0LD_1LD1RA_1LF0LE_---0RD_1LB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFBAE") 1 5.
Time Qed.
End TM1393.


Module TM1394.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LD_0RB0RF_0LC---".
Definition tm' := TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RB_0RD0RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 33 21.
Time Qed.
End TM1394.


Module TM1395.
Definition tm := TM_from_str "1RB0RB_1LC0RF_1RD0LC_0RE0RA_0LB1RA_1LD---".
Definition tm' := TM_from_str "1RB0LA_0RC0RE_0LD1RE_1LA0RF_1RD0RD_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDABCF") 1 3.
Time Qed.
End TM1395.


Module TM1396.
Definition tm := TM_from_str "1RB1LA_0LA0RC_1RD1LB_1LC0RE_0RB1RF_1LB---".
Definition tm' := TM_from_str "1RB1LC_1LA0RE_0LD0RA_1RC1LD_0RC1RF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCABEF") 9 6.
Time Qed.
End TM1396.


Module TM1397.
Definition tm := TM_from_str "1LB0RE_0LC0RD_1RB1LC_1RA1LB_0RB1RF_1LB---".
Definition tm' := TM_from_str "1RB1LC_1LC0RE_0LD0RA_1RC1LD_0RC1RF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 1 4.
Time Qed.
End TM1397.


Module TM1398.
Definition tm := TM_from_str "1RB---_1LC0RD_0LD0LC_1RE0LF_0RF1RA_1RB0RC".
Definition tm' := TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1398.


Module TM1399.
Definition tm := TM_from_str "1LB---_1RC0RA_1LF0RD_0RE0LC_0LC0RB_1RE0LD".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FECDBA") 40 25.
Time Qed.
End TM1399.


Module TM1400.
Definition tm := TM_from_str "1RB0LE_1RC0RC_1RD1RA_1LD1LA_---0LF_1LB1LA".
Definition tm' := TM_from_str "1RB1RC_1LB1LC_1RD0LE_1RA0RA_---0LF_1LD1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 31 5.
Time Qed.
End TM1400.


Module TM1401.
Definition tm := TM_from_str "1LB0LE_1LC1LB_1RD1RC_0LA0RD_1LF1LA_0RE---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_0RD---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 762 751.
Time Qed.
End TM1401.


Module TM1402.
Definition tm := TM_from_str "1LB1LC_0LC0RE_1RD1LF_0RA0LB_1RD---_0LD1LB".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1LE_0LE0RA_1RB1LF_0LB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBAF") 24 38.
Time Qed.
End TM1402.


Module TM1403.
Definition tm := TM_from_str "1RB1LB_0RC1RE_0RD0RF_1LA1RC_1RD0LE_---0LA".
Definition tm' := TM_from_str "1RB0LA_1LC1RE_1RD1LD_0RE1RA_0RB0RF_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBAF") 1 7.
Time Qed.
End TM1403.


Module TM1404.
Definition tm := TM_from_str "1LB1LC_0RC0RF_0LF0RD_1RE1RB_0LA1RB_1LE---".
Definition tm' := TM_from_str "1RB1RF_0LC1RF_1LF1LD_0LE0RA_1LB---_0RD0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFDABE") 4 1.
Time Qed.
End TM1404.


Module TM1405.
Definition tm := TM_from_str "1RB1RA_1RC0RD_1LB---_1RA0LE_1LF1RF_0RE1LD".
Definition tm' := TM_from_str "1RB0LE_1RC1RB_1RD0RA_1LC---_1LF1RF_0RE1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 46 61.
Time Qed.
End TM1405.


Module TM1406.
Definition tm := TM_from_str "1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1LC0RF_1LA1LD_0RE0LC_---1LB_1RB0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1406.


Module TM1407.
Definition tm := TM_from_str "1LB0LF_0RC1RF_1RF1RD_0LD0RE_1RF---_1LA0RB".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA1RB_0LE0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEFB") 6 1.
Time Qed.
End TM1407.


Module TM1408.
Definition tm := TM_from_str "1LB---_1LC0RB_1RD0LD_1LF0LE_1RB1RE_0LA1LC".
Definition tm' := TM_from_str "1RB0LB_1LC0LD_0LF1LA_1RE1RD_1LA0RE_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEABDC") 2 3.
Time Qed.
End TM1408.


Module TM1409.
Definition tm := TM_from_str "1LB0RC_1RC1RA_0LD1RB_0RB0LE_0RA0LF_---1LD".
Definition tm' := TM_from_str "1RB1RE_0LC1RA_0RA0LD_0RE0LF_1LA0RB_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 5.
Time Qed.
End TM1409.


Module TM1410.
Definition tm := TM_from_str "1RB1RD_0LC0LE_0RD1LB_1RA0RB_1RB0LF_---1LC".
Definition tm' := TM_from_str "1RB0RC_1RC1RA_0LD0LE_0RA1LC_1RC0LF_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 28 1.
Time Qed.
End TM1410.


Module TM1411.
Definition tm := TM_from_str "1RB1RF_1LC1LE_0LE1LD_1RE0RE_1RA0LB_1RD---".
Definition tm' := TM_from_str "1RB0LC_1RC1RF_1LD1LA_0LA1LE_1RA0RA_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 313 284.
Time Qed.
End TM1411.


Module TM1412.
Definition tm := TM_from_str "1LB1RC_0RA0LF_1RD1LB_1RE---_1RA1LA_0LB0RA".
Definition tm' := TM_from_str "1RB1LE_1RC---_1RD1LD_1LE1RA_0RD0LF_0LE0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 30 9.
Time Qed.
End TM1412.


Module TM1413.
Definition tm := TM_from_str "1LB1LE_0LC0RE_1RD1LF_0RA0LB_1RD---_0LD1LB".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1LA_0LE0RA_1RB1LF_0LB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBAF") 24 38.
Time Qed.
End TM1413.


Module TM1414.
Definition tm := TM_from_str "1LB1LF_0RC1LE_1RD1RC_0LE1RB_---0LA_0LB0LB".
Definition tm' := TM_from_str "1RB1RA_0LC1RE_---0LD_1LE1LF_0RA1LC_0LE0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM1414.


Module TM1415.
Definition tm := TM_from_str "1RB0LE_1RC1RA_0RD---_1RE0RE_1LA0LF_1LD1RC".
Definition tm' := TM_from_str "1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 7804 9684.
Time Qed.
End TM1415.


Module TM1416.
Definition tm := TM_from_str "1RB0LF_1LC1RE_1LD0LC_1LA0RB_1RB0RE_---1RB".
Definition tm' := TM_from_str "1RB0RA_1LC1RA_1LD0LC_1LE0RB_1RB0LF_---1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1416.


Module TM1417.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC1LF_0LB---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM1417.


Module TM1418.
Definition tm := TM_from_str "1RB1LD_1LC0LC_1RA1LB_1RE0RA_1RF0RD_1LC---".
Definition tm' := TM_from_str "1RB0RF_1LC---_1RE1LD_1LC0LC_1RD1LF_1RA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDCFAB") 2 2.
Time Qed.
End TM1418.


Module TM1419.
Definition tm := TM_from_str "1LB---_1LC0LD_1RD0RE_1RF0RC_1RC0LA_0LF0RA".
Definition tm' := TM_from_str "1RB0RE_0LB0RC_1LD---_1LE0LA_1RA0RF_1RE0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEAFB") 1 4.
Time Qed.
End TM1419.


Module TM1420.
Definition tm := TM_from_str "1LB0RE_0LC1RA_1LD1RC_0RB0LD_1RC0RF_1RE---".
Definition tm' := TM_from_str "1RB0RF_1LC1RB_0RD0LC_0LB1RE_1LD0RA_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDBCAF") 1 4.
Time Qed.
End TM1420.


Module TM1421.
Definition tm := TM_from_str "1LB1LC_0RA0LF_1RD1RE_0LA1RC_0RC0LB_---1LE".
Definition tm' := TM_from_str "1RB1RD_0LC1RA_1LE1LA_0RA0LE_0RC0LF_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEABDF") 2 2.
Time Qed.
End TM1421.


Module TM1422.
Definition tm := TM_from_str "1LB1LE_1RC0LC_0LA0RD_1RB1RF_0LC1LF_0LC---".
Definition tm' := TM_from_str "1RB1RF_1RC0LC_0LD0RA_1LB1LE_0LC1LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 17 1.
Time Qed.
End TM1422.


Module TM1423.
Definition tm := TM_from_str "1RB0LF_1RC0RE_1RD1RE_0LE1LB_0RC0LA_---1LE".
Definition tm' := TM_from_str "1RB1RC_0LC1LE_0RA0LD_1RE0LF_1RA0RC_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM1423.


Module TM1424.
Definition tm := TM_from_str "1LB1LE_1RC1RB_1RD0RC_0LD0LA_0RC0LF_---1LA".
Definition tm' := TM_from_str "1RB0RA_0LB0LC_1LD1LE_1RA1RD_0RA0LF_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 1 4.
Time Qed.
End TM1424.


Module TM1425.
Definition tm := TM_from_str "1RB1RF_0LC0RF_1LE0LD_1RC---_0LA1LA_1LC0RB".
Definition tm' := TM_from_str "1RB---_1LC0LA_0LD1LD_1RE1RF_0LB0RF_1LB0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBACF") 4 1.
Time Qed.
End TM1425.


Module TM1426.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB1RF_1LC1LD_0LA---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LE_0LC1RF_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM1426.


Module TM1427.
Definition tm := TM_from_str "1RB1LC_1LA0RF_0LD---_0LE1LE_0LB0RF_1RB1LD".
Definition tm' := TM_from_str "1RB1LE_1LC0RA_1RB1LD_0LE---_0LF1LF_0LB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM1427.


Module TM1428.
Definition tm := TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA0LD_0LE0RF_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1LD0LB_0RE0LD_1RB1RF_0LF0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1428.


Module TM1429.
Definition tm := TM_from_str "1RB0LA_0LC0RA_1LE1RD_0RC1RF_1LA---_1RB0RB".
Definition tm' := TM_from_str "1RB0RB_0LC0RF_1LE1RD_0RC1RA_1LF---_1RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1429.


Module TM1430.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1LF_0RB0RF_0LC---".
Definition tm' := TM_from_str "1RB0LB_0RC1LF_1LD1RE_0LA0RB_0RD0RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 31 21.
Time Qed.
End TM1430.


Module TM1431.
Definition tm := TM_from_str "1RB0RE_0LC1RE_1LD1LB_1RB---_1RA0RF_1LF0LA".
Definition tm' := TM_from_str "1RB---_0LC1RD_1LA1LB_1RE0RF_1RB0RD_1LF0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM1431.


Module TM1432.
Definition tm := TM_from_str "1RB0RE_0RC---_1LD0LA_0LA1LF_1LC0RA_1RA0LC".
Definition tm' := TM_from_str "1RB0LD_1RC0RF_0RD---_1LE0LB_0LB1LA_1LD0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 126 150.
Time Qed.
End TM1432.


Module TM1433.
Definition tm := TM_from_str "1RB1LF_1RC0RC_1RD1RB_0LE1RD_0RC0LA_---1LE".
Definition tm' := TM_from_str "1RB1RE_0LC1RB_0RA0LD_1RE1LF_1RA0RA_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM1433.


Module TM1434.
Definition tm := TM_from_str "1RB1LD_0RC0RE_1LC1RA_1RB0LD_---0RF_0LF1RC".
Definition tm' := TM_from_str "1RB0LA_0RC0RE_1LC1RD_1RB1LA_---0RF_0LF1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM1434.


Module TM1435.
Definition tm := TM_from_str "1LB1RF_1RC0RD_1RD1LC_1LE1RB_0RA0LE_1RC---".
Definition tm' := TM_from_str "1RB1LA_1LC1RE_0RD0LC_1LE1RF_1RA0RB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 11 13.
Time Qed.
End TM1435.


Module TM1436.
Definition tm := TM_from_str "1LB0LF_0RC0LB_1RF1RD_0LD0RE_0LB---_1LA0RB".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA0LD_0LE0RF_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEFB") 8 1.
Time Qed.
End TM1436.


Module TM1437.
Definition tm := TM_from_str "1RB0RA_0LC1RA_1LE0LD_1RC0LF_1LA1LB_0LE---".
Definition tm' := TM_from_str "1RB0LF_1LC0LA_1LE1LD_0LB1RE_1RD0RE_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDBACF") 4 1.
Time Qed.
End TM1437.


Module TM1438.
Definition tm := TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB1RF_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RF_1LD1RB_1LE0LD_1RB0LB_1RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1438.


Module TM1439.
Definition tm := TM_from_str "1RB1LB_1RC0RA_0LD1LE_0RA0LC_1LF0RB_1LC---".
Definition tm' := TM_from_str "1RB0RD_0LC1LE_0RD0LB_1RA1LA_1LF0RA_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 6.
Time Qed.
End TM1439.


Module TM1440.
Definition tm := TM_from_str "1RB1RC_0LC0RE_1RE1LD_1LA0LC_1RB1RF_1RA---".
Definition tm' := TM_from_str "1RB1RF_0LC0RA_1RA1LD_1LE0LC_1RB1RC_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1440.


Module TM1441.
Definition tm := TM_from_str "1LB0RD_1LC1RA_0RB0LC_1LB1RE_1RD0LF_---1LE".
Definition tm' := TM_from_str "1RB0LF_1LC1RA_1LE1RD_1LC0RB_0RC0LE_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEBAF") 3 2.
Time Qed.
End TM1441.


Module TM1442.
Definition tm := TM_from_str "1LB---_1RC0LF_1LD1LC_0RE0LD_1RB0RF_1RA1RE".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 55 36.
Time Qed.
End TM1442.


Module TM1443.
Definition tm := TM_from_str "1LB0LA_1RC0LD_0RD0RB_1LA0RE_1RF---_0RB1LC".
Definition tm' := TM_from_str "1RB---_0RC1LD_1RD0LE_0RE0RC_1LF0RA_1LC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEAB") 3 2.
Time Qed.
End TM1443.


Module TM1444.
Definition tm := TM_from_str "1RB---_1RC1RF_1LD1LE_1RE0LC_1RF0RD_1RA1RA".
Definition tm' := TM_from_str "1RB0LF_1RC0RA_1RD1RD_1RE---_1RF1RC_1LA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 79 95.
Time Qed.
End TM1444.


Module TM1445.
Definition tm := TM_from_str "1RB1LC_0LC1RF_0RD0LD_1RE1RB_1LA0RE_1RD---".
Definition tm' := TM_from_str "1RB1RE_1LC0RB_1RE1LD_0RA0LA_0LD1RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEDABF") 4 1.
Time Qed.
End TM1445.


Module TM1446.
Definition tm := TM_from_str "1RB0LC_1LC1RF_1LE0LD_1LC0RE_1RD0RA_0RD---".
Definition tm' := TM_from_str "1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LC1RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECBAF") 2 2.
Time Qed.
End TM1446.


Module TM1447.
Definition tm := TM_from_str "1RB0RF_1LC0RE_1RB1LD_1LC0LC_---1RA_1RD0RC".
Definition tm' := TM_from_str "1RB1LC_1LA0RD_1LA0LA_---1RE_1RB0RF_1RC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM1447.


Module TM1448.
Definition tm := TM_from_str "1RB---_1LC0RF_0RE0LD_1LE1RC_1RB0LF_0LC1LA".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1RC_0LC1LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1448.


Module TM1449.
Definition tm := TM_from_str "1RB0RA_1LC0RA_0RD0LB_1RF1LE_0LC---_1LA1RD".
Definition tm' := TM_from_str "1RB1LF_1LC1RA_1RD0RC_1LE0RC_0RA0LD_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEAFB") 1 5.
Time Qed.
End TM1449.


Module TM1450.
Definition tm := TM_from_str "1RB0RE_0LC1LD_1RA1LB_0RA1LB_---1RF_0LD1RA".
Definition tm' := TM_from_str "1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0LD1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 3 10.
Time Qed.
End TM1450.


Module TM1451.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_1LB---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM1451.


Module TM1452.
Definition tm := TM_from_str "1LB0RD_1RC0LB_1LA0RD_1RE0LA_1RA0RF_0RA---".
Definition tm' := TM_from_str "1RB0LA_1LC0RD_1LA0RD_1RE0LC_1RC0RF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 5.
Time Qed.
End TM1452.


Module TM1453.
Definition tm := TM_from_str "1RB1RD_1RC0RB_0LD1LA_0LE1LC_1RB1LF_0LA---".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_0LD1LE_0LA1LC_1RB1RD_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1453.


Module TM1454.
Definition tm := TM_from_str "1RB1LE_0LC1RE_---1LD_1RB1LA_0RF1RF_1RA0LB".
Definition tm' := TM_from_str "1RB1LF_0LC1RD_---1LA_0RE1RE_1RF0LB_1RB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM1454.


Module TM1455.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RF_1LC1LD_0LB---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LE_0LC0RF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM1455.


Module TM1456.
Definition tm := TM_from_str "1RB0RF_1RC0LC_0LD0RA_1RE1LD_0LE1LB_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0LC_0LD0RF_1RE1LD_0LE1LB_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1456.


Module TM1457.
Definition tm := TM_from_str "1LB---_1RC1RB_1RD1RD_0LE0RD_0LC1LF_1LA1LE".
Definition tm' := TM_from_str "1RB1RA_1RC1RC_0LD0RC_0LB1LE_1LF1LD_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 3 2.
Time Qed.
End TM1457.


Module TM1458.
Definition tm := TM_from_str "1RB---_1RC0RA_0RD0LE_1RE0LF_1LC1LD_1RA1RB".
Definition tm' := TM_from_str "1RB1RC_1RC---_1RD0RB_0RE0LF_1RF0LA_1LD1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 11 10.
Time Qed.
End TM1458.


Module TM1459.
Definition tm := TM_from_str "1RB---_1LC1LD_0LD0LB_0LE0RD_1RA0LF_0LB1LA".
Definition tm' := TM_from_str "1RB0LF_1RC---_1LD1LE_0LE0LC_0LA0RE_0LC1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 49229 60942.
Time Qed.
End TM1459.


Module TM1460.
Definition tm := TM_from_str "1LB---_1LC0RF_1LD0RE_0LE0RC_1LF0LA_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1LF0RD_1LA0LE_1LB---_0LD0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFDA") 1 5.
Time Qed.
End TM1460.


Module TM1461.
Definition tm := TM_from_str "1RB1RA_1RC1LF_1LD1RD_0RE0LD_0RF---_1RA1LF".
Definition tm' := TM_from_str "1RB1LE_1LC1RC_0RD0LC_0RE---_1RF1LE_1RA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 7 6.
Time Qed.
End TM1461.


Module TM1462.
Definition tm := TM_from_str "1LB0RB_0LC1LF_1RD1LE_0RA0LB_0LD1LB_0RA---".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0RD_0LA1LF_0LB1LD_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 22 34.
Time Qed.
End TM1462.


Module TM1463.
Definition tm := TM_from_str "1LB1RD_1RC---_1LC1LA_0RF0RE_0LC1LF_0LA0RD".
Definition tm' := TM_from_str "1RB---_1LB1LC_1LA1RD_0RF0RE_0LB1LF_0LC0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 6 1.
Time Qed.
End TM1463.


Module TM1464.
Definition tm := TM_from_str "1RB1RB_1RC0LF_0RD0RA_1LE0RC_1LB---_1LC0LE".
Definition tm' := TM_from_str "1RB0LE_0RC0RF_1LD0RB_1LA---_1LB0LD_1RA1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 1 12.
Time Qed.
End TM1464.


Module TM1465.
Definition tm := TM_from_str "1LB1LB_0LC1LC_1LD1RF_1RE1RD_0LA0RE_---1LA".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LD1LD_0LE1LE_1LA1RF_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 1 3.
Time Qed.
End TM1465.


Module TM1466.
Definition tm := TM_from_str "1LB---_0LC1LC_1LD0LA_1RE1RF_1RB0RE_1LA0RF".
Definition tm' := TM_from_str "1RB0RA_0LC1LC_1LE0LD_1LB---_1RA1RF_1LD0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 4.
Time Qed.
End TM1466.


Module TM1467.
Definition tm := TM_from_str "1LB0LA_0RB0RC_1RD1RF_1LD1LE_1LA---_0LA1RB".
Definition tm' := TM_from_str "1RB1RF_1LB1LC_1LD---_1LE0LD_0RE0RA_0LD1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 4 1.
Time Qed.
End TM1467.


Module TM1468.
Definition tm := TM_from_str "1RB1RF_0RC0LD_1RD0RA_1LB0LE_1LD1RA_0RB---".
Definition tm' := TM_from_str "1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCABEF") 1136 1183.
Time Qed.
End TM1468.


Module TM1469.
Definition tm := TM_from_str "1RB---_1LB1RC_1RA1LD_0LE0RC_1RE0LF_0RA0LD".
Definition tm' := TM_from_str "1RB1LD_1RC---_1LC1RA_0LE0RA_1RE0LF_0RB0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 13 1.
Time Qed.
End TM1469.


Module TM1470.
Definition tm := TM_from_str "1LB0RE_1RC0LA_0RF0RD_1RE1LA_0LB1LC_---0RC".
Definition tm' := TM_from_str "1RB1LD_0LC1LE_1RE0LD_1LC0RB_0RF0RA_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEABF") 1 4.
Time Qed.
End TM1470.


Module TM1471.
Definition tm := TM_from_str "1RB0RA_0LC1RB_1LF0LD_1RE1LC_1RA0RF_---1RE".
Definition tm' := TM_from_str "1RB1LE_1RC0RF_1RD0RC_0LE1RD_1LF0LA_---1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM1471.


Module TM1472.
Definition tm := TM_from_str "1LB1RE_1RC0LC_0RA1LD_0LB0RC_0RD0RF_0LE---".
Definition tm' := TM_from_str "1RB0LB_0RC1LD_1LA1RE_0LA0RB_0RD0RF_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 47 31.
Time Qed.
End TM1472.


Module TM1473.
Definition tm := TM_from_str "1RB0RF_1RC0LD_1RD---_1RE1RB_1LF1LA_1RA0LE".
Definition tm' := TM_from_str "1RB1RE_1LC1LD_1RD0LB_1RE0RC_1RF0LA_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 20 10.
Time Qed.
End TM1473.


Module TM1474.
Definition tm := TM_from_str "1RB1RF_1RC0RE_0LD1LC_1RF1LB_---0LB_0RA0RF".
Definition tm' := TM_from_str "1RB0RF_0LC1LB_1RD1LA_0RE0RD_1RA1RD_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCFD") 7 1.
Time Qed.
End TM1474.


Module TM1475.
Definition tm := TM_from_str "1LB---_0LC0RE_1LD0RF_1RB0LF_1RC0RA_0RB0LC".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEBCAD") 1 4.
Time Qed.
End TM1475.


Module TM1476.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RF0RA_1RD1LB_1RC---".
Definition tm' := TM_from_str "1RB---_1RC0RF_1LD1RE_1LB0LD_1RA0RC_1RE1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEFA") 27 12.
Time Qed.
End TM1476.


Module TM1477.
Definition tm := TM_from_str "1RB0RE_0LC1RA_1RE0LD_0RE0LF_1RA---_1RC1LC".
Definition tm' := TM_from_str "1RB1LB_1RC0LF_1RD---_1RE0RC_0LB1RD_0RC0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBFCA") 10 1.
Time Qed.
End TM1477.


Module TM1478.
Definition tm := TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1RB_0RF1RC_0LC0RD".
Definition tm' := TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA---_0RF1RA_0LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 86 230.
Time Qed.
End TM1478.


Module TM1479.
Definition tm := TM_from_str "1LB---_0LC0RD_1RB1LC_1RE1LB_0LF0RF_0RB0RA".
Definition tm' := TM_from_str "1RB1LE_0LC0RC_0RE0RD_1LE---_0LF0RA_1RE1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 1 4.
Time Qed.
End TM1479.


Module TM1480.
Definition tm := TM_from_str "1RB---_1LC1RE_1LD0LC_1RE0LE_1RB0RF_1RE1RA".
Definition tm' := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1480.


Module TM1481.
Definition tm := TM_from_str "1RB0LF_1LB0LC_1RD0LA_0RE0RD_0LB1LC_---1RE".
Definition tm' := TM_from_str "1RB0LE_0RC0RB_0LD1LA_1LD0LA_1RD0LF_---1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDABCF") 1 3.
Time Qed.
End TM1481.


Module TM1482.
Definition tm := TM_from_str "1RB1RF_0LC---_1RD0LC_1RE1LD_0RF1RA_1LC0RE".
Definition tm' := TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA0RC_1RF1RD_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 4 1.
Time Qed.
End TM1482.


Module TM1483.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RD0LC_0RE0RC_0LB1RA_1RB---".
Definition tm' := TM_from_str "1RB0LA_0RC0RA_0LD1RE_1LA0RB_1RD1RF_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDABCF") 1 3.
Time Qed.
End TM1483.


Module TM1484.
Definition tm := TM_from_str "1RB1RA_0LC0RA_---1LD_1LE0LF_1RB0RC_1LD0LB".
Definition tm' := TM_from_str "1RB0RC_0LC0RE_---1LD_1LA0LF_1RB1RE_1LD0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1484.


Module TM1485.
Definition tm := TM_from_str "1LB0RD_1RC0RB_1LE1LA_1LF0LE_1RB1LD_1LC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LF0LA_1LB0RD_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 6 1.
Time Qed.
End TM1485.


Module TM1486.
Definition tm := TM_from_str "1RB1LA_0RC1RE_1LD0LA_1LC---_1RB0RF_0RB0RC".
Definition tm' := TM_from_str "1RB0RF_0RC1RA_1LD0LE_1LC---_1RB1LE_0RB0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1486.


Module TM1487.
Definition tm := TM_from_str "1RB0LE_0LB0RC_1RD---_1LA0RE_0RF0LD_0LD1RB".
Definition tm' := TM_from_str "1RB---_1LC0RD_1RF0LD_0RE0LB_0LB1RF_0LF0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 4 1.
Time Qed.
End TM1487.


Module TM1488.
Definition tm := TM_from_str "1RB1RD_0RC0RA_0LD0RF_1LE---_1RB1LF_0LE0LD".
Definition tm' := TM_from_str "1RB1LE_0RC0RF_0LD0RE_1LA---_0LA0LD_1RB1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1488.


Module TM1489.
Definition tm := TM_from_str "1RB1LD_1LC0RC_0LD1RC_1RF0LE_0RA1LA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RC_0LD1RC_1RA0LE_0RF1LF_1RB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1489.


Module TM1490.
Definition tm := TM_from_str "1LB0LE_1RC0RE_1LA1RD_1RB0RC_0RF0LE_1LA---".
Definition tm' := TM_from_str "1RB0RD_1LC1RF_1LA0LD_0RE0LD_1LC---_1RA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABFDE") 23 24.
Time Qed.
End TM1490.


Module TM1491.
Definition tm := TM_from_str "1RB1RE_1LC1LB_1RD0LC_0RA---_1RB0RF_0RA1RA".
Definition tm' := TM_from_str "1RB0RF_1LC1LB_1RD0LC_0RE---_1RB1RA_0RE1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1491.


Module TM1492.
Definition tm := TM_from_str "1RB0LE_1RC1RB_1RD0RA_1RE1LC_0LA0RF_1LE---".
Definition tm' := TM_from_str "1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 1 5.
Time Qed.
End TM1492.


Module TM1493.
Definition tm := TM_from_str "1RB---_1RC0RF_0LD1LF_1LF1LE_1RF0LA_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1RC0RA_0LD1LA_1LA1LE_1RA0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1493.


Module TM1494.
Definition tm := TM_from_str "1LB1LE_1RC0LD_1RD0RB_0LA0RD_1RB0LF_1RC---".
Definition tm' := TM_from_str "1RB0RE_0LC0RB_1LE1LD_1RE0LF_1RA0LB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEABDF") 1 8.
Time Qed.
End TM1494.


Module TM1495.
Definition tm := TM_from_str "1RB---_0RC0LF_1RD0RE_1LE0RF_0LB0LD_1RC0LA".
Definition tm' := TM_from_str "1RB0LF_1RC0RD_1LD0RA_0LE0LC_0RB0LA_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEBCDA") 1 8.
Time Qed.
End TM1495.


Module TM1496.
Definition tm := TM_from_str "1RB1LC_1LA1RD_0LD---_0LE1LE_0LB0RF_1RB1LD".
Definition tm' := TM_from_str "1RB1LE_1LC1RE_1RB1LD_0LE---_0LF1LF_0LB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM1496.


Module TM1497.
Definition tm := TM_from_str "1RB1LB_1RC0LF_1RD---_1RE0RC_0LB0LA_0RC0LA".
Definition tm' := TM_from_str "1RB---_1RC0RA_0LD0LF_1RA0LE_0RA0LF_1RD1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDABCE") 1 6.
Time Qed.
End TM1497.


Module TM1498.
Definition tm := TM_from_str "1RB0LE_0RC0RE_1LD1RF_0LA0RD_1LD1LA_1RC---".
Definition tm' := TM_from_str "1RB---_1LC1RA_0LD0RC_1RE0LF_0RB0RF_1LC1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 1 6.
Time Qed.
End TM1498.


Module TM1499.
Definition tm := TM_from_str "1RB1RC_1LC0RE_1LD0RA_0LA0LC_0RC0RF_1RC---".
Definition tm' := TM_from_str "1RB---_1LC0RD_0LD0LB_1RE1RB_1LB0RF_0RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 4 1.
Time Qed.
End TM1499.


Module TM1500.
Definition tm := TM_from_str "1LB1LF_0LC1RB_1RA0LD_---1LE_0RF1LC_0RB1RF".
Definition tm' := TM_from_str "1RB0LD_1LC1LF_0LA1RC_---1LE_0RF1LA_0RC1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 6 14.
Time Qed.
End TM1500.


Module TM1501.
Definition tm := TM_from_str "1RB1LD_1LB1RC_1RF1LD_0RF0LE_0LD0RF_1RA---".
Definition tm' := TM_from_str "1RB---_1RC1LE_1LC1RD_1RA1LE_0RA0LF_0LE0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 4 9.
Time Qed.
End TM1501.


Module TM1502.
Definition tm := TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RF1RD_---0RA".
Definition tm' := TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_0RF1RD_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 139 179.
Time Qed.
End TM1502.


Module TM1503.
Definition tm := TM_from_str "1RB1LB_1RC1LE_1RD1RF_0LE1RE_0RC0LA_---0RD".
Definition tm' := TM_from_str "1RB1RF_0LC1RC_0RA0LD_1RE1LE_1RA1LC_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM1503.


Module TM1504.
Definition tm := TM_from_str "1RB0LC_1LA0RF_1LD---_0LE1LC_1LB1LD_1RB0RA".
Definition tm' := TM_from_str "1RB0RC_1LC0RA_1RB0LD_1LE---_0LF1LD_1LB1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM1504.


Module TM1505.
Definition tm := TM_from_str "1LB0RD_1RC0LD_1RA0LC_0RE0RA_0LB1RF_0RB---".
Definition tm' := TM_from_str "1RB0LA_1LC0RD_1RA0LD_0RE0RB_0LC1RF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 5 1.
Time Qed.
End TM1505.


Module TM1506.
Definition tm := TM_from_str "1LB1RA_1LC0LB_0RC1RD_0RE1LB_1RA0RF_1RE---".
Definition tm' := TM_from_str "1RB0RF_1LC1RB_1LD0LC_0RD1RE_0RA1LC_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 5 2.
Time Qed.
End TM1506.


Module TM1507.
Definition tm := TM_from_str "1RB0LF_0RC0LD_1LD1LA_0LE0RA_1RB1LC_0LD---".
Definition tm' := TM_from_str "1RB1LC_0RC0LD_1LD1LE_0LA0RE_1RB0LF_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1507.


Module TM1508.
Definition tm := TM_from_str "1LB0LB_1RC0LF_1RE0LD_0RE0LB_0RA1RD_---1LD".
Definition tm' := TM_from_str "1RB0LF_1RC0LE_0RD1RE_1LA0LA_0RC0LA_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 5 1.
Time Qed.
End TM1508.


Module TM1509.
Definition tm := TM_from_str "1LB1LF_0RC0LB_1RA0RD_1RE---_1LB1RF_1RC0LA".
Definition tm' := TM_from_str "1RB---_1LC1RF_0RD0LC_1RE0RA_1LC1LF_1RD0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDABF") 4 1.
Time Qed.
End TM1509.


Module TM1510.
Definition tm := TM_from_str "1LB0RF_1RC1LE_1RE0RD_1RC1RA_0LB0LA_0RE---".
Definition tm' := TM_from_str "1RB0RF_0LC0LD_1RA1LB_1LC0RE_0RB---_1RA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCAFBE") 4 11.
Time Qed.
End TM1510.


Module TM1511.
Definition tm := TM_from_str "1RB1LA_1RC0RB_1LD1RC_1LF1LE_1LB0LD_1RA---".
Definition tm' := TM_from_str "1RB0RA_1LC1RB_1LE1LD_1LA0LC_1RF---_1RA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 27 65.
Time Qed.
End TM1511.


Module TM1512.
Definition tm := TM_from_str "1RB1RE_0LC1RC_0RA0LD_1RE1LF_1RA0RB_---1LC".
Definition tm' := TM_from_str "1RB1LF_1RC0RD_1RD1RB_0LE1RE_0RC0LA_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM1512.


Module TM1513.
Definition tm := TM_from_str "1RB1LC_1LA0RF_0LD---_0LE1LA_0LB1RE_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1RB1LD_0LE---_0LF1LC_0LB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM1513.


Module TM1514.
Definition tm := TM_from_str "1RB1LF_0LC0RF_---1LD_1RE1LA_1RA0LE_0RC0RD".
Definition tm' := TM_from_str "1RB0LA_1RC1LF_0LD0RF_---1LE_1RA1LB_0RD0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 7 1.
Time Qed.
End TM1514.


Module TM1515.
Definition tm := TM_from_str "1RB0LC_1LA0LD_1LB1LE_0LA1RE_0RF---_1RB0RA".
Definition tm' := TM_from_str "1RB0RC_1LC0LE_1RB0LD_1LB1LF_0LC1RF_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM1515.


Module TM1516.
Definition tm := TM_from_str "1RB1LE_0RC0RF_1RD0RC_1LA0LD_1LD---_1RB1RB".
Definition tm' := TM_from_str "1RB1RB_0RC0RA_1RD0RC_1LE0LD_1RB1LF_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1516.


Module TM1517.
Definition tm := TM_from_str "1RB0RF_0LC1LE_0LF1LD_1RE0LF_1RA0LB_1RA---".
Definition tm' := TM_from_str "1RB0LC_1RC0RF_0LD1LA_0LF1LE_1RA0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 81 49.
Time Qed.
End TM1517.


Module TM1518.
Definition tm := TM_from_str "1RB0LC_1RC0RD_1LA0LD_0LE0RF_1RF1LC_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RE_1LD0LE_1RB0LC_0LF0RA_1RA1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM1518.


Module TM1519.
Definition tm := TM_from_str "1LB---_1RC0RB_1LE0LD_1LA1RB_1RB1LF_1LC0LE".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCEAD") 4 1.
Time Qed.
End TM1519.


Module TM1520.
Definition tm := TM_from_str "1LB0LE_0RC0LB_0LD1RC_1LF0RE_1RB---_0RF1LA".
Definition tm' := TM_from_str "1RB---_0RC0LB_0LD1RC_1LE0RA_0RE1LF_1LB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 6 1.
Time Qed.
End TM1520.


Module TM1521.
Definition tm := TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1RF_0RF0RB_0LC0RD".
Definition tm' := TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA---_0RF0RD_0LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 35 21.
Time Qed.
End TM1521.


Module TM1522.
Definition tm := TM_from_str "1RB---_1LC1LB_0RE0LD_0RB0LD_1RB1RF_0RA1RE".
Definition tm' := TM_from_str "1RB1RE_1LC1LB_0RA0LD_0RB0LD_0RF1RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1522.


Module TM1523.
Definition tm := TM_from_str "1LB0LD_1RC0LA_0RD0RB_0LE0RE_1RA0RF_0LB---".
Definition tm' := TM_from_str "1RB0LE_0RC0RA_0LD0RD_1RE0RF_1LA0LC_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 451 374.
Time Qed.
End TM1523.


Module TM1524.
Definition tm := TM_from_str "1RB1RC_0LC0LC_1RE1LD_0LB0LF_0RF---_0RA0RE".
Definition tm' := TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0LA_0LE0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 39 22.
Time Qed.
End TM1524.


Module TM1525.
Definition tm := TM_from_str "1LB0LC_0LC1LF_1RD0RE_0RA---_1LA0RC_1RC0LA".
Definition tm' := TM_from_str "1RB0LD_1RC0RF_0RD---_1LE0LB_0LB1LA_1LD0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 5 1.
Time Qed.
End TM1525.


Module TM1526.
Definition tm := TM_from_str "1LB---_1LC0LB_0RD0LC_0RB1RE_1RF1LB_0RA1RD".
Definition tm' := TM_from_str "1RB1LD_0RC1RF_1LD---_1LE0LD_0RF0LE_0RD1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 5 7.
Time Qed.
End TM1526.


Module TM1527.
Definition tm := TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_0RF1RA_---0RC".
Definition tm' := TM_from_str "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RF1RB_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 39100 36396.
Time Qed.
End TM1527.


Module TM1528.
Definition tm := TM_from_str "1RB0RE_0LC0LF_1RE0LD_0RE0LF_1RA---_1RC1LC".
Definition tm' := TM_from_str "1RB---_1RC0RA_0LD0LF_1RA0LE_0RA0LF_1RD1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 5 1.
Time Qed.
End TM1528.


Module TM1529.
Definition tm := TM_from_str "1RB1RE_1LC0RA_1RE0LD_1LE---_0LB0LF_0LC1RC".
Definition tm' := TM_from_str "1RB0LE_0LC0LF_1LA0RD_1RC1RB_1LB---_0LA1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCAEBF") 1 4.
Time Qed.
End TM1529.


Module TM1530.
Definition tm := TM_from_str "1RB1LE_0RC0LD_1LD1RE_0LA1LB_1RC0LF_---1RB".
Definition tm' := TM_from_str "1RB0LE_1LC1RA_0LF1LD_0RB0LC_---1RD_1RD1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDBCAE") 1 7.
Time Qed.
End TM1530.


Module TM1531.
Definition tm := TM_from_str "1RB0RF_0RC0LD_1LD1RA_0LE0RF_1RB0LB_0RB---".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1531.


Module TM1532.
Definition tm := TM_from_str "1LB0RC_1RA1LB_0LB0RD_1LE1RD_---0LF_1RC0LB".
Definition tm' := TM_from_str "1RB0LC_0LC0RE_1RD1LC_1LC0RB_1LF1RE_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCBEFA") 1 3.
Time Qed.
End TM1532.


Module TM1533.
Definition tm := TM_from_str "1RB0LF_1RC---_1RD0RD_1LE1RA_---1LA_0RB0LA".
Definition tm' := TM_from_str "1RB---_1RC0RC_1LD1RE_---1LE_1RA0LF_0RA0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 18 1.
Time Qed.
End TM1533.


Module TM1534.
Definition tm := TM_from_str "1LB0LC_0RC---_0RF0LD_0LE1LE_1RB0RC_1LA1RF".
Definition tm' := TM_from_str "1RB0RC_0RC---_0RD0LF_1LE1RD_1LB0LC_0LA1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFAD") 5 1.
Time Qed.
End TM1534.


Module TM1535.
Definition tm := TM_from_str "1LB0LA_0RC0RF_1RE1RD_1RB---_0LA0RB_1LE1LD".
Definition tm' := TM_from_str "1RB1RE_0LC0RD_1LD0LC_0RA0RF_1RD---_1LB1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEBF") 1 4.
Time Qed.
End TM1535.


Module TM1536.
Definition tm := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA---_1LC0RF_1RA0RB".
Definition tm' := TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_1LD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 23 29.
Time Qed.
End TM1536.


Module TM1537.
Definition tm := TM_from_str "1RB1RF_1LC0LB_0LD1LC_1RE0RA_1RA---_1RC0RD".
Definition tm' := TM_from_str "1RB0RC_0LC1LB_1RF0RD_1RE1RA_1LB0LE_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 1 4.
Time Qed.
End TM1537.


Module TM1538.
Definition tm := TM_from_str "1LB1RA_1RC1LF_0LD0RC_1RE0LA_1LA---_1LE0LB".
Definition tm' := TM_from_str "1RB1LF_0LC0RB_1RE0LD_1LA1RD_1LD---_1LE0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 4.
Time Qed.
End TM1538.


Module TM1539.
Definition tm := TM_from_str "1LB1LC_1RA1LE_0LD0RC_1RB1LF_1LC0LE_1RE---".
Definition tm' := TM_from_str "1RB1LF_1RC1LD_1LB1LE_1LE0LD_0LA0RE_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBEADF") 7 1.
Time Qed.
End TM1539.


Module TM1540.
Definition tm := TM_from_str "1LB0RC_1LC0LE_1RD1RA_0LB0RD_1LF---_1RA1LA".
Definition tm' := TM_from_str "1RB1RF_0LC0RB_1LA0LD_1LE---_1RF1LF_1LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCABDE") 20 5.
Time Qed.
End TM1540.


Module TM1541.
Definition tm := TM_from_str "1LB0RE_0LC0RD_1RB1LC_1RA1LB_0RB0RF_0LD---".
Definition tm' := TM_from_str "1RB1LC_1LC0RE_0LD0RA_1RC1LD_0RC0RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 1 4.
Time Qed.
End TM1541.


Module TM1542.
Definition tm := TM_from_str "1RB1RF_1LC1RF_0LE1LD_0RE0RE_0RA0LB_1RD---".
Definition tm' := TM_from_str "1RB---_0RC0RC_0RD0LE_1RE1RA_1LF1RA_0LC1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 30 24.
Time Qed.
End TM1542.


Module TM1543.
Definition tm := TM_from_str "1RB0RD_1LC0RA_1RB1LC_1LE1RD_0LA0LF_---0LC".
Definition tm' := TM_from_str "1RB1LA_1LA0RC_1RB0RD_1LE1RD_0LC0LF_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBADEF") 1 1.
Time Qed.
End TM1543.


Module TM1544.
Definition tm := TM_from_str "1LB0RC_1RA0LD_1RA0RC_1LE1LA_1LB0LF_0LB---".
Definition tm' := TM_from_str "1RB0LC_1LA0RE_1LD1LB_1LA0LF_1RB0RE_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BAECDF") 14 21.
Time Qed.
End TM1544.


Module TM1545.
Definition tm := TM_from_str "1RB1LC_1LA0RF_0LD---_0LE1LE_0LB0RA_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1RB1LD_0LE---_0LF1LF_0LB0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM1545.


Module TM1546.
Definition tm := TM_from_str "1RB0RF_1LC0RE_1RB0LD_1LC0LB_1RA0LB_0RB---".
Definition tm' := TM_from_str "1RB0LC_1RC0RF_1LD0RA_1RC0LE_1LD0LC_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 118 58.
Time Qed.
End TM1546.


Module TM1547.
Definition tm := TM_from_str "1RB0LD_1RC0RC_1RD1RA_1LE0LF_---1LA_1LB1LA".
Definition tm' := TM_from_str "1RB1RD_1LC0LF_---1LD_1RE0LB_1RA0RA_1LE1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 31 5.
Time Qed.
End TM1547.


Module TM1548.
Definition tm := TM_from_str "1RB1RC_1LA1RF_0RB1LD_---0LE_0LC1LA_1RA0LC".
Definition tm' := TM_from_str "1RB0LD_1RC1RD_1LB1RA_0RC1LE_---0LF_0LD1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 8 7.
Time Qed.
End TM1548.


Module TM1549.
Definition tm := TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB1RF_1RE---".
Definition tm' := TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1549.


Module TM1550.
Definition tm := TM_from_str "1LB1RD_1LC1RE_0RA0LC_---0RE_1RF0RB_1RB1RB".
Definition tm' := TM_from_str "1RB0RC_1RC1RC_1LD1RA_0RE0LD_1LC1RF_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDFAB") 7 13.
Time Qed.
End TM1550.


Module TM1551.
Definition tm := TM_from_str "1RB0RE_0LC0RA_1LE0LD_1LB1LF_1RA0LB_0LB---".
Definition tm' := TM_from_str "1RB0LC_1RC0RA_0LD0RB_1LA0LE_1LC1LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 62 88.
Time Qed.
End TM1551.


Module TM1552.
Definition tm := TM_from_str "1LB0LC_1RC0LE_1LE0RD_1RA1RB_1RF1LA_1LC---".
Definition tm' := TM_from_str "1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 10 7.
Time Qed.
End TM1552.


Module TM1553.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_1RA---_1RA0LD".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEFB") 5 2.
Time Qed.
End TM1553.


Module TM1554.
Definition tm := TM_from_str "1RB---_1LC0RE_1RE0LD_1LB0LB_1RA0RF_1RB1RC".
Definition tm' := TM_from_str "1RB1RC_1LC0RE_1RE0LD_1LB0LB_1RF0RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1554.


Module TM1555.
Definition tm := TM_from_str "1LB---_0LC0RE_0LD1LF_1RE0RA_0RF0RE_0LA1RD".
Definition tm' := TM_from_str "1RB0RD_0RC0RB_0LD1RA_1LE---_0LF0RB_0LA1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 1 9.
Time Qed.
End TM1555.


Module TM1556.
Definition tm := TM_from_str "1RB---_1RC0RB_1LC1LD_1LE0RC_0LF1LA_1LA0LE".
Definition tm' := TM_from_str "1RB0RA_1LB1LC_1LD0RB_0LE1LF_1LF0LD_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 5 2.
Time Qed.
End TM1556.


Module TM1557.
Definition tm := TM_from_str "1LB1RF_1RC0LC_0LD0RC_0LE---_1LA1LE_1RD1RF".
Definition tm' := TM_from_str "1RB1RA_0LC---_1LD1LC_1LE1RA_1RF0LF_0LB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 4 1.
Time Qed.
End TM1557.


Module TM1558.
Definition tm := TM_from_str "1LB0RB_1RC1RA_0LD1RB_1LB0LE_0RD0LF_---1LD".
Definition tm' := TM_from_str "1RB1RF_0LC1RA_1LA0LD_0RC0LE_---1LC_1LA0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 1 5.
Time Qed.
End TM1558.


Module TM1559.
Definition tm := TM_from_str "1LB---_1LC0LF_1LD0RF_1RE1RD_0LB0RE_1LA1LB".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_1LC---_1LA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECFABD") 1436 2289.
Time Qed.
End TM1559.


Module TM1560.
Definition tm := TM_from_str "1RB1LE_1RC0RB_1RD1RF_1LA0LE_1RB0LD_---0RA".
Definition tm' := TM_from_str "1RB0LD_1RC0RB_1RD1RF_1LE0LA_1RB1LA_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1560.


Module TM1561.
Definition tm := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LB---".
Definition tm' := TM_from_str "1RB1RE_0LC---_1LD1LC_0RE0LD_1RF0RA_1RC0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEAB") 6 6.
Time Qed.
End TM1561.


Module TM1562.
Definition tm := TM_from_str "1RB0LD_0LC0RB_1RA1LA_0RE1LE_0LF0RA_1LD---".
Definition tm' := TM_from_str "1RB1LB_1RC0LD_0LA0RC_0RE1LE_0LF0RB_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 3 10.
Time Qed.
End TM1562.


Module TM1563.
Definition tm := TM_from_str "1RB0RB_0LC0LF_0RA1LD_1LE0LF_1RA---_1RE1LC".
Definition tm' := TM_from_str "1RB1LE_1RC---_1RD0RD_0LE0LA_0RC1LF_1LB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 1 19.
Time Qed.
End TM1563.


Module TM1564.
Definition tm := TM_from_str "1RB0RE_0LC0RA_1LD1LC_1RB0LD_0RB1RF_0LD---".
Definition tm' := TM_from_str "1RB0LA_0LC0RD_1LA1LC_1RB0RE_0RB1RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM1564.


Module TM1565.
Definition tm := TM_from_str "1RB0LC_1RC1RA_1LD1LF_0RE0LD_1RF---_0RB1LC".
Definition tm' := TM_from_str "1RB---_0RC1LD_1RD1RF_1LE1LB_0RA0LE_1RC0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEAB") 8 14.
Time Qed.
End TM1565.


Module TM1566.
Definition tm := TM_from_str "1RB---_1LC1LB_0RE0LD_0RB0LC_1RB1RF_0RA1RE".
Definition tm' := TM_from_str "1RB1RE_1LC1LB_0RA0LD_0RB0LC_0RF1RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1566.


Module TM1567.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1RE0LA_1LC1LF_---1LE".
Definition tm' := TM_from_str "1RB0LD_1LC1LF_1LD1RC_1RE1LA_1RC0RE_---1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECABF") 2 4.
Time Qed.
End TM1567.


Module TM1568.
Definition tm := TM_from_str "1LB0RF_1RC0LB_0LE0RD_1RA---_1RD1LB_0RC0LA".
Definition tm' := TM_from_str "1RB0LA_0LC0RD_1RD1LA_1RE---_1LA0RF_0RB0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABDCF") 1 3.
Time Qed.
End TM1568.


Module TM1569.
Definition tm := TM_from_str "1LB0RE_0LC0RD_1RB1LC_1RA1LB_0RB1RF_1LC---".
Definition tm' := TM_from_str "1RB1LC_1LC0RE_0LD0RA_1RC1LD_0RC1RF_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 1 4.
Time Qed.
End TM1569.


Module TM1570.
Definition tm := TM_from_str "1RB0LB_0LC0RF_1LA1LD_0RD0LE_1RC---_1RA0RF".
Definition tm' := TM_from_str "1RB---_1LC1LF_1RD0LD_0LB0RE_1RC0RE_0RF0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBFAE") 6 1.
Time Qed.
End TM1570.


Module TM1571.
Definition tm := TM_from_str "1RB0RE_0RC1RB_1LD0RD_1LA0RF_1RB0LC_---0LE".
Definition tm' := TM_from_str "1RB0LC_0RC1RB_1LD0RD_1LE0RF_1RB0RA_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1571.


Module TM1572.
Definition tm := TM_from_str "1LB0RC_1LC0LA_0RD1RA_0RA1RE_1LA0RF_1RA---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1LD0LB_0RE1RB_0RB1RF_1LB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 37 60.
Time Qed.
End TM1572.


Module TM1573.
Definition tm := TM_from_str "1RB0LD_1LC1RE_---0LD_1LA1LB_1RF0RE_0LF0RA".
Definition tm' := TM_from_str "1RB0RA_0LB0RC_1RD0LF_1LE1RA_---0LF_1LC1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 1 4.
Time Qed.
End TM1573.


Module TM1574.
Definition tm := TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB1RF_0RB---".
Definition tm' := TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1574.


Module TM1575.
Definition tm := TM_from_str "1LB0LA_0RC1LC_1LF0RD_1RE1RB_0LB0RD_0LA---".
Definition tm' := TM_from_str "1RB1RC_0LC0RA_0RD1LD_1LE0RA_0LF---_1LC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 4 1.
Time Qed.
End TM1575.


Module TM1576.
Definition tm := TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RF_1RB0RD_---0RB".
Definition tm' := TM_from_str "1RB0RD_0RC1LD_1LD1RA_0LE0RF_1RB0LB_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1576.


Module TM1577.
Definition tm := TM_from_str "1RB0LE_0LC0LF_1LA0RD_1RC0RF_1LB---_0LA1RA".
Definition tm' := TM_from_str "1RB0RF_1LC0RA_1RE0LD_1LE---_0LB0LF_0LC1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEBADF") 4 1.
Time Qed.
End TM1577.


Module TM1578.
Definition tm := TM_from_str "1LB1RD_1RC0LB_0LE0LA_0RE0RF_1RA1LB_1RE---".
Definition tm' := TM_from_str "1RB0LA_0LC0LD_1RD1LA_1LA1RE_0RC0RF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 1 3.
Time Qed.
End TM1578.


Module TM1579.
Definition tm := TM_from_str "1LB0LA_1RC0LD_1RF0RD_1LA1RE_0LE0RB_1LE---".
Definition tm' := TM_from_str "1RB0LE_1RC0RE_1LD---_0LD0RA_1LF1RD_1LA0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABEDC") 95 177.
Time Qed.
End TM1579.


Module TM1580.
Definition tm := TM_from_str "1LB0RB_0LC0RB_1RD1LE_0RA0LB_0LD1LF_1LC---".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0RD_0LA0RD_0LB1LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 22 36.
Time Qed.
End TM1580.


Module TM1581.
Definition tm := TM_from_str "1RB0LA_0RC1RB_1LD1RD_1LA1RE_1RB0RF_---0RA".
Definition tm' := TM_from_str "1RB0RF_0RC1RB_1LD1RD_1LE1RA_1RB0LE_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1581.


Module TM1582.
Definition tm := TM_from_str "1LB1RE_0LC0RE_1RC0LD_0RE0LB_1RF1LB_1RA---".
Definition tm' := TM_from_str "1RB---_1LC1RD_0LE0RD_1RA1LC_1RE0LF_0RD0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEFDA") 1 4.
Time Qed.
End TM1582.


Module TM1583.
Definition tm := TM_from_str "1RB0RB_0LC1RB_1RF0LD_0RE1LE_1RA1LC_1RA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RC_0LD1RC_1RF0LE_0RA1LA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 5 1.
Time Qed.
End TM1583.


Module TM1584.
Definition tm := TM_from_str "1RB0LC_1LC1RD_1LA1LC_---0RE_1RB0RF_0LF1RB".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1LD1LC_1RB0LC_---0RA_0LF1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 1.
Time Qed.
End TM1584.


Module TM1585.
Definition tm := TM_from_str "1LB0LC_1LC0RD_1RD1LA_1RF1RE_---1RB_1RB0RA".
Definition tm' := TM_from_str "1RB1LE_1RC1RF_1RD0RE_1LA0RB_1LD0LA_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDABFC") 5 3.
Time Qed.
End TM1585.


Module TM1586.
Definition tm := TM_from_str "1LB0LD_1RC0LE_0LD0RC_1RE1LA_1RF---_1LD0LC".
Definition tm' := TM_from_str "1RB---_1LC0LF_1RA1LD_1LE0LC_1RF0LA_0LC0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFCAB") 22 21.
Time Qed.
End TM1586.


Module TM1587.
Definition tm := TM_from_str "1RB1LC_1LC0RE_0LF0LD_1LA1LA_1RB1LE_---0LA".
Definition tm' := TM_from_str "1RB1LA_1LC0RA_0LF0LD_1LE1LE_1RB1LC_---0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1587.


Module TM1588.
Definition tm := TM_from_str "1RB---_1RC0LF_1RD0RC_1RE1RA_1LB1LF_0LC0LE".
Definition tm' := TM_from_str "1RB0RA_1RC1RF_1LD1LE_1RA0LE_0LA0LC_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDABCE") 140 107.
Time Qed.
End TM1588.


Module TM1589.
Definition tm := TM_from_str "1RB0LF_1RC---_1LD0RC_1LE1LD_0LA1LF_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_1RC---_1LD0RC_1LE1LD_0LF1LA_1RB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1589.


Module TM1590.
Definition tm := TM_from_str "1RB0LE_0LC0LF_1LA0RD_1RC0RD_1LB---_0LA1RA".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1RE0LD_1LE---_0LB0LF_0LC1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEBADF") 4 1.
Time Qed.
End TM1590.


Module TM1591.
Definition tm := TM_from_str "1LB0LE_1RC0LD_1RD0RB_0LA0RC_1LD0LF_1RA---".
Definition tm' := TM_from_str "1RB0RE_0LC0RA_1LE0LD_1LB0LF_1RA0LB_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEABDF") 118 70.
Time Qed.
End TM1591.


Module TM1592.
Definition tm := TM_from_str "1LB---_1LC0RF_1RD1LF_0RE0RD_1LE0LB_1LA0LB".
Definition tm' := TM_from_str "1RB1LE_0RC0RB_1LC0LD_1LA0RE_1LF0LD_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDABCE") 11 28.
Time Qed.
End TM1592.


Module TM1593.
Definition tm := TM_from_str "1LB0LF_1LC---_1RD0RC_0LE1LD_1RF1LA_1RC0LF".
Definition tm' := TM_from_str "1RB0LA_1RC0RB_0LD1LC_1RA1LE_1LF0LA_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 4 9.
Time Qed.
End TM1593.


Module TM1594.
Definition tm := TM_from_str "1LB1LF_1LC---_1RD1RC_1RE1RE_0LF0RE_0LD1LA".
Definition tm' := TM_from_str "1RB1RA_1RC1RC_0LD0RC_0LB1LE_1LF1LD_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 8 2.
Time Qed.
End TM1594.


Module TM1595.
Definition tm := TM_from_str "1LB1RA_0RC1RD_1LE0RD_1RC0LB_0LF0LA_---0LE".
Definition tm' := TM_from_str "1RB0LE_1LC0RA_0LF0LD_1LE1RD_0RB1RA_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBACF") 4 1.
Time Qed.
End TM1595.


Module TM1596.
Definition tm := TM_from_str "1LB1RC_0RA0LB_1LA0RD_1LA1RE_1RD0LF_---1LE".
Definition tm' := TM_from_str "1RB0LF_1LC1RA_1LE1RD_1LC0RB_0RC0LE_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEDBAF") 4 2.
Time Qed.
End TM1596.


Module TM1597.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC1LF_0LA---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM1597.


Module TM1598.
Definition tm := TM_from_str "1RB---_1RC1RD_1LD0RF_1RB0LE_1LA1LC_0RD0LC".
Definition tm' := TM_from_str "1RB0LD_1RC1RA_1LA0RE_1LF1LC_0RA0LC_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM1598.


Module TM1599.
Definition tm := TM_from_str "1RB---_1LC0RE_1LD1LC_1RB1LF_1RD1RB_0LC1LA".
Definition tm' := TM_from_str "1RB1LE_1LC0RD_1LA1LC_1RA1RB_0LC1LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM1599.


Module TM1600.
Definition tm := TM_from_str "1LB0RE_0RC0LA_1RE0LD_0LB---_0RF1RD_1RA1LC".
Definition tm' := TM_from_str "1RB0LF_0RC1RF_1RD1LA_1LE0RB_0RA0LD_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 6 1.
Time Qed.
End TM1600.


Module TM1601.
Definition tm := TM_from_str "1LB1LD_1LC0LF_0RD0LE_1LF0RC_1RC---_1LA0RB".
Definition tm' := TM_from_str "1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCAD") 6 1.
Time Qed.
End TM1601.


Module TM1602.
Definition tm := TM_from_str "1LB1LA_1LC0LB_0RD0RE_---0RE_1RA1RF_0LB1RC".
Definition tm' := TM_from_str "1RB1RF_1LC1LB_1LD0LC_0RE0RA_---0RA_0LC1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 11 1.
Time Qed.
End TM1602.


Module TM1603.
Definition tm := TM_from_str "1LB0LC_0RA---_1RD1LF_1RE0RD_1LC1RE_1LE1LA".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LC1LE_1LF0LA_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 4 1.
Time Qed.
End TM1603.


Module TM1604.
Definition tm := TM_from_str "1RB1RE_1LC0RC_0RA0LD_1LB0LF_0RC1RE_1RD---".
Definition tm' := TM_from_str "1RB---_1LC0LA_1LD0RD_0RE0LB_1RC1RF_0RD1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDBFA") 13 1.
Time Qed.
End TM1604.


Module TM1605.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RD1LB_0LA1RE_0LE1RF_0RA---".
Definition tm' := TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA0RB_0LE1RF_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 3 4.
Time Qed.
End TM1605.


Module TM1606.
Definition tm := TM_from_str "1LB0LC_1RC0LA_1LB0RD_1RE1RB_1RC0RF_0RC---".
Definition tm' := TM_from_str "1RB1RD_1RC0RF_1LD0RA_1RC0LE_1LD0LC_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDCABF") 305 302.
Time Qed.
End TM1606.


Module TM1607.
Definition tm := TM_from_str "1RB1LE_1RC1LF_1RD0RC_0LE0LB_---0LA_1RB1LA".
Definition tm' := TM_from_str "1RB0RA_0LC0LE_---0LD_1RE1LC_1RA1LF_1RE1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM1607.


Module TM1608.
Definition tm := TM_from_str "1LB0RA_0RC1RE_1LF0LD_1RA1LC_1LD1RE_1LE---".
Definition tm' := TM_from_str "1RB1LE_1LC0RB_0RE1RD_1LA1RD_1LF0LA_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEADF") 4 1.
Time Qed.
End TM1608.


Module TM1609.
Definition tm := TM_from_str "1LB---_0LC0RD_1RB1LC_1RE1LB_1LB0RF_0RB1RA".
Definition tm' := TM_from_str "1RB1LC_1LC0RE_0LD0RA_1RC1LD_0RC1RF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 1 4.
Time Qed.
End TM1609.


Module TM1610.
Definition tm := TM_from_str "1LB0RA_0LC1RA_0RD1LE_1RA---_0LF0LD_1RA0LB".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LD1RB_0RF1LE_0LA0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDFEA") 4 3.
Time Qed.
End TM1610.


Module TM1611.
Definition tm := TM_from_str "1RB0RA_1LC0RD_1LD0LC_1RA0LE_1LC0LF_1RE---".
Definition tm' := TM_from_str "1RB---_1LC0LA_1LD0LC_1RE0LB_1RF0RE_1LC0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCDBA") 2 2.
Time Qed.
End TM1611.


Module TM1612.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RF_1LC1RA_1RA---".
Definition tm' := TM_from_str "1RB---_1LC0RF_0RE0LD_1LE1RB_1RB0LF_0LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEFDA") 6 1.
Time Qed.
End TM1612.


Module TM1613.
Definition tm := TM_from_str "1LB0RE_0LC0LA_0RD0LD_1LE1LF_1RA0RC_0LC---".
Definition tm' := TM_from_str "1RB0RD_1LC0RA_0LD0LB_0RE0LE_1LA1LF_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 350 419.
Time Qed.
End TM1613.


Module TM1614.
Definition tm := TM_from_str "1RB0LA_0RC1RE_1RD0RF_1LE1LA_1RB0LD_1RB---".
Definition tm' := TM_from_str "1RB---_0RC1RE_1RD0RA_1LE1LF_1RB0LD_1RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1614.


Module TM1615.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_1LE---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM1615.


Module TM1616.
Definition tm := TM_from_str "1LB1LF_0RC0RB_1RE0LD_1RB0LE_1LD0LA_1LB---".
Definition tm' := TM_from_str "1RB0LD_0RC0RB_1RD0LA_1LA0LE_1LB1LF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 4 1.
Time Qed.
End TM1616.


Module TM1617.
Definition tm := TM_from_str "1RB1RC_0LC0LD_1RE1LD_0LB1RB_0RF---_0RA0RE".
Definition tm' := TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0LF_0LE1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 40 21.
Time Qed.
End TM1617.


Module TM1618.
Definition tm := TM_from_str "1RB0LE_0RC1RF_0RD---_1RE1LE_1LA1LD_0RA0RF".
Definition tm' := TM_from_str "1RB1LB_1LC1LA_1RD0LB_0RF1RE_0RC0RE_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFABE") 14 13.
Time Qed.
End TM1618.


Module TM1619.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_1RB---_1RA0LD".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEFB") 2029 2020.
Time Qed.
End TM1619.


Module TM1620.
Definition tm := TM_from_str "1RB1RE_1RC0LF_1LD1LC_---0RA_1LB1RA_0LA0LA".
Definition tm' := TM_from_str "1RB0LF_1LC1LB_---0RD_1RA1RE_1LA1RD_0LD0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 51 33.
Time Qed.
End TM1620.


Module TM1621.
Definition tm := TM_from_str "1LB1LA_0RC---_1RD1RC_1RE0LA_1LF0RC_0RE0LF".
Definition tm' := TM_from_str "1RB0LE_1LC0RD_0RB0LC_1RA1RD_1LF1LE_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDABC") 2 7.
Time Qed.
End TM1621.


Module TM1622.
Definition tm := TM_from_str "1RB1LD_1RC---_1LA1RC_1LE0LA_1RF0LB_1RA0RF".
Definition tm' := TM_from_str "1RB0LD_1RC0RB_1RD1LF_1RE---_1LC1RE_1LA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 9 4.
Time Qed.
End TM1622.


Module TM1623.
Definition tm := TM_from_str "1RB1LC_1LA0RE_0LD0RA_1RC1LD_0RC0RF_1LC---".
Definition tm' := TM_from_str "1RB1LA_0LA0RC_1RD1LB_1LC0RE_0RB0RF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBAEF") 6 9.
Time Qed.
End TM1623.


Module TM1624.
Definition tm := TM_from_str "1RB---_1LC1RE_1LD0LC_0LE0RE_1RF1LD_1RB0RA".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1LD0LC_0LE0RE_1RA1LD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1624.


Module TM1625.
Definition tm := TM_from_str "1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0LD_1RD0RF_1LB1LE_0LB0RE_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1625.


Module TM1626.
Definition tm := TM_from_str "1RB1RC_0LC1LE_0RA0LD_1RE0LF_1RA1RD_---1LC".
Definition tm' := TM_from_str "1RB0LF_1RC1RA_1RD1RE_0LE1LB_0RC0LA_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM1626.


Module TM1627.
Definition tm := TM_from_str "1RB---_1RC0RF_0LD1LF_0LF1LE_1RF0LA_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1RC0RA_0LD1LA_0LA1LE_1RA0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1627.


Module TM1628.
Definition tm := TM_from_str "1RB1RC_1LC0RE_1RA0LD_1LC1LB_0RF0LB_1RA---".
Definition tm' := TM_from_str "1RB0LD_1RC1RA_1LA0RE_1LA1LC_0RF0LC_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 10 33.
Time Qed.
End TM1628.


Module TM1629.
Definition tm := TM_from_str "1LB1RC_1RC0LE_0RD0LA_1LC1RD_0LC1LF_1LD---".
Definition tm' := TM_from_str "1RB0LE_0RC0LD_1LB1RC_1LA1RB_0LB1LF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 4 1.
Time Qed.
End TM1629.


Module TM1630.
Definition tm := TM_from_str "1RB1RB_1LC1RD_1LD0LC_1RE0RA_1RB0RF_1LE---".
Definition tm' := TM_from_str "1RB0RE_1LC1RD_1LD0LC_1RA0RF_1LA---_1RB1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1630.


Module TM1631.
Definition tm := TM_from_str "1RB1LF_1RC0RB_1RD0RF_1LE---_1LA1RE_1LD0LA".
Definition tm' := TM_from_str "1RB0RE_1LC---_1LD1RC_1RF1LE_1LB0LD_1RA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFABCE") 20 16.
Time Qed.
End TM1631.


Module TM1632.
Definition tm := TM_from_str "1RB0RE_0LC1RA_1RA1LD_1LC0LD_---1RF_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_0LC1RE_1RE1LD_1LC0LD_1RB0RF_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1632.


Module TM1633.
Definition tm := TM_from_str "1LB1RF_1LC---_0LD0RE_1RE1LD_0RA1LC_0RC0RB".
Definition tm' := TM_from_str "1RB1LA_0RC1LE_1LD1RF_1LE---_0LA0RB_0RE0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 2 6.
Time Qed.
End TM1633.


Module TM1634.
Definition tm := TM_from_str "1LB0LF_1LC1LE_1RD1LA_1RA0RD_1RA0LB_---1RD".
Definition tm' := TM_from_str "1RB1LC_1RC0RB_1LD0LF_1LA1LE_1RC0LD_---1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 12 12.
Time Qed.
End TM1634.


Module TM1635.
Definition tm := TM_from_str "1LB0LF_1RC0RF_1LA1RD_1RE0RC_1RB---_0RC0LF".
Definition tm' := TM_from_str "1RB0RD_1LC1RE_1LA0LD_0RB0LD_1RF0RB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEFD") 25 26.
Time Qed.
End TM1635.


Module TM1636.
Definition tm := TM_from_str "1RB1RE_1LC0RA_1LD0LB_1RA1LD_0RF0RC_0RA---".
Definition tm' := TM_from_str "1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 5028 5810.
Time Qed.
End TM1636.


Module TM1637.
Definition tm := TM_from_str "1RB0RF_0RC0RA_0LD0RE_1LE1RB_1RA1LC_1RD---".
Definition tm' := TM_from_str "1RB1LD_1RC0RF_0RD0RB_0LE0RA_1LA1RC_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 4 7.
Time Qed.
End TM1637.


Module TM1638.
Definition tm := TM_from_str "1LB0LE_0LC0RC_1RD1LF_0RA0LB_0RC---_0LD1LA".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0LF_0LA0RA_0LB1LC_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 530 386.
Time Qed.
End TM1638.


Module TM1639.
Definition tm := TM_from_str "1LB1LD_1LC0LF_1RD0LA_1LC0RE_1RD0RE_0LC---".
Definition tm' := TM_from_str "1RB0LC_1LA0RE_1LD1LB_1LA0LF_1RB0RE_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 302 305.
Time Qed.
End TM1639.


Module TM1640.
Definition tm := TM_from_str "1RB1LE_1RC0RB_1RD1RF_1LA0LD_1RB0LD_---0RE".
Definition tm' := TM_from_str "1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1640.


Module TM1641.
Definition tm := TM_from_str "1LB0LE_1RC1RD_0LA0RC_1LA0RB_1LF---_1RD1LD".
Definition tm' := TM_from_str "1RB1RF_0LC0RB_1LA0LD_1LE---_1RF1LF_1LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABFDE") 6 5.
Time Qed.
End TM1641.


Module TM1642.
Definition tm := TM_from_str "1LB1RD_0LC0RD_0RD0LE_1RA1LB_---0LF_0RD0LB".
Definition tm' := TM_from_str "1RB1LC_1LC1RA_0LD0RA_0RA0LE_---0LF_0RA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 1 4.
Time Qed.
End TM1642.


Module TM1643.
Definition tm := TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA0LD_0RB1RF_0RA---".
Definition tm' := TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RF_0RD1RF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 33 23.
Time Qed.
End TM1643.


Module TM1644.
Definition tm := TM_from_str "1RB---_1LC0RD_1LD0LB_0RE1RB_1RB1RF_1LB0RA".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA1RB_1LB0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1644.


Module TM1645.
Definition tm := TM_from_str "1LB0RC_1LC1LD_1RA1RB_1RE0LB_1LF0RD_---1LE".
Definition tm' := TM_from_str "1RB1RC_1LC0RA_1LA1LD_1RE0LC_1LF0RD_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 83 80.
Time Qed.
End TM1645.


Module TM1646.
Definition tm := TM_from_str "1LB0LC_1RC0LD_1RF1RD_1LE0RC_---1LA_0RA1RF".
Definition tm' := TM_from_str "1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABEFC") 2908 2835.
Time Qed.
End TM1646.


Module TM1647.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA1LE_1RF0RA_0LD0LD_1RC---".
Definition tm' := TM_from_str "1RB---_1RC1LF_1LD1RE_1LB0LD_1RA0RC_0LE0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEFA") 43 61.
Time Qed.
End TM1647.


Module TM1648.
Definition tm := TM_from_str "1LB1RC_1RA1LE_1RD0LB_1RA0RF_1LB1LC_---0RB".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1RB1LD_1LC1LE_1RA0LC_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEADF") 145 140.
Time Qed.
End TM1648.


Module TM1649.
Definition tm := TM_from_str "1LB1RA_1RA0LC_1RD1LC_1RA1RE_1RF0RA_---0RD".
Definition tm' := TM_from_str "1RB1LA_1RC1RE_1LD1RC_1RC0LA_1RF0RC_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 3 2.
Time Qed.
End TM1649.


Module TM1650.
Definition tm := TM_from_str "1LB1LF_1RC0RE_0LE1RD_1RB0RC_1RA1LA_---0LC".
Definition tm' := TM_from_str "1RB0RC_0LC1RE_1RD1LD_1LA1LF_1RA0RB_---0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 12 11.
Time Qed.
End TM1650.


Module TM1651.
Definition tm := TM_from_str "1RB0RA_0LB0LC_1LD1LF_1RE---_1RA1RE_0RA1LB".
Definition tm' := TM_from_str "1RB1RA_1RC0RB_0LC0LD_1LF1LE_0RB1LC_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDFAE") 1 8.
Time Qed.
End TM1651.


Module TM1652.
Definition tm := TM_from_str "1LB1RA_1RC0LA_0LB1RD_1RE1RF_0RB0RD_---0LE".
Definition tm' := TM_from_str "1RB0LC_0LA1RD_1LA1RC_1RE1RF_0RA0RD_---0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 4.
Time Qed.
End TM1652.


Module TM1653.
Definition tm := TM_from_str "1RB1RC_1RC1RF_1LC0LD_1LE0RB_0LA1LD_---0RA".
Definition tm' := TM_from_str "1RB1RF_1LB0LC_1LD0RA_0LE1LC_1RA1RB_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 9 1.
Time Qed.
End TM1653.


Module TM1654.
Definition tm := TM_from_str "1LB1LC_1RA1LE_0LD0RC_1RB0LF_1LC0LE_0LE---".
Definition tm' := TM_from_str "1RB0LF_1RC1LD_1LB1LE_1LE0LD_0LA0RE_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBEADF") 7 1.
Time Qed.
End TM1654.


Module TM1655.
Definition tm := TM_from_str "1RB---_0LC0RE_0RF1RD_1LE0LB_1RF0LD_1RB1RA".
Definition tm' := TM_from_str "1RB1RF_0LC0RE_0RA1RD_1LE0LB_1RA0LD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1655.


Module TM1656.
Definition tm := TM_from_str "1RB1LE_1RC0RF_1LD1LF_---0LA_1LA1RD_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1RC0RA_1LD1LA_---0LE_1RB1LF_1LE1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1656.


Module TM1657.
Definition tm := TM_from_str "1RB0RA_1LC1RA_1LD0LC_1LE0RB_1RB1LF_---0LC".
Definition tm' := TM_from_str "1RB1LF_1LC1RE_1LD0LC_1LA0RB_1RB0RE_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1657.


Module TM1658.
Definition tm := TM_from_str "1RB1RE_1RC0RD_1LB0RA_0RC1LE_0LF---_1LB0LF".
Definition tm' := TM_from_str "1RB0RC_1LA0RF_0RB1LD_0LE---_1LA0LE_1RA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 76 162.
Time Qed.
End TM1658.


Module TM1659.
Definition tm := TM_from_str "1RB0LF_1RC0RA_1LD1LE_1RF1LC_0LD---_1RF1LA".
Definition tm' := TM_from_str "1RB0RE_1LC1LF_1RD1LB_1RD1LE_1RA0LD_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCFD") 10 11.
Time Qed.
End TM1659.


Module TM1660.
Definition tm := TM_from_str "1LB0RD_1LC1RD_1RD0LB_0RA0RE_0RF0LD_---0LD".
Definition tm' := TM_from_str "1RB0LD_0RC0RE_1LD0RB_1LA1RB_0RF0LB_---0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 5 1.
Time Qed.
End TM1660.


Module TM1661.
Definition tm := TM_from_str "1RB---_1LC1LF_1RD0LD_0LB0RE_1RC0RE_0LD0LA".
Definition tm' := TM_from_str "1RB0LB_0LC0RE_1LA1LD_0LB0LF_1RA0RE_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCABED") 3 4.
Time Qed.
End TM1661.


Module TM1662.
Definition tm := TM_from_str "1RB0RF_1LC0RE_1RB0LD_1LC0LD_1RA0LB_0RB---".
Definition tm' := TM_from_str "1RB0LC_1RC0RF_1LD0RA_1RC0LE_1LD0LE_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 118 58.
Time Qed.
End TM1662.


Module TM1663.
Definition tm := TM_from_str "1RB0LE_1RC1RA_1LD1LE_1LF0LC_0RD0RA_1LA---".
Definition tm' := TM_from_str "1RB1RE_1LC1LF_1LD0LB_1LE---_1RA0LF_0RC0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCFD") 3786 3920.
Time Qed.
End TM1663.


Module TM1664.
Definition tm := TM_from_str "1RB---_1LC1RF_1RE0LD_0LB0LD_0LF0RC_1RC0RA".
Definition tm' := TM_from_str "1RB0LF_0LC0RA_1RA0RD_1RE---_1LA1RC_0LE0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 1 4.
Time Qed.
End TM1664.


Module TM1665.
Definition tm := TM_from_str "1LB0LF_1RC0LA_0LE1RD_0RC0RD_1LE1LB_---0LB".
Definition tm' := TM_from_str "1RB0LE_0LC1RD_1LC1LA_0RB0RD_1LA0LF_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABDCF") 1 3.
Time Qed.
End TM1665.


Module TM1666.
Definition tm := TM_from_str "1RB0LF_1RC1LC_1RD1RE_0LB0RD_0RC0LA_---1LE".
Definition tm' := TM_from_str "1RB1RD_0LC0RB_1RA1LA_0RA0LE_1RC0LF_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECABDF") 1 6.
Time Qed.
End TM1666.


Module TM1667.
Definition tm := TM_from_str "1RB0LE_1LC1RF_1RD1LD_0RA0RD_0LB0RC_0LA---".
Definition tm' := TM_from_str "1RB1LB_0RC0RB_1RD0LE_1LA1RF_0LD0RA_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 61 302.
Time Qed.
End TM1667.


Module TM1668.
Definition tm := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_1RC---".
Definition tm' := TM_from_str "1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDBCFA") 1 6.
Time Qed.
End TM1668.


Module TM1669.
Definition tm := TM_from_str "1LB1RE_1RC0LC_0RA1LD_0LB0RC_0RD0RF_0LB---".
Definition tm' := TM_from_str "1RB0LB_0RC1LD_1LA1RE_0LA0RB_0RD0RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 47 33.
Time Qed.
End TM1669.


Module TM1670.
Definition tm := TM_from_str "1LB0LB_0LC0RD_1LD1LB_1RE1LF_1RB0RE_1LA---".
Definition tm' := TM_from_str "1RB0RA_0LC0RD_1LD1LB_1RA1LE_1LF---_1LB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 3.
Time Qed.
End TM1670.


Module TM1671.
Definition tm := TM_from_str "1RB1RF_1LC0RA_1RB1LD_0LE---_1LB1LE_0LC0RB".
Definition tm' := TM_from_str "1RB1LC_1LA0RE_0LD---_1LB1LD_1RB1RF_0LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM1671.


Module TM1672.
Definition tm := TM_from_str "1LB0LE_0RC1RE_1RE1RD_1LE1RF_1LA0RB_1LE---".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA1RB_1LB1RF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEBF") 6 1.
Time Qed.
End TM1672.


Module TM1673.
Definition tm := TM_from_str "1RB1RD_1RC0RF_1LD0RA_1RA0LE_0RB1LD_1LC---".
Definition tm' := TM_from_str "1RB0RF_1LC0RE_1RE0LD_0RA1LC_1RA1RC_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 89 205.
Time Qed.
End TM1673.


Module TM1674.
Definition tm := TM_from_str "1LB1LE_1RC0LD_1RD0RB_0LA1LB_1RB0LF_1RC---".
Definition tm' := TM_from_str "1RB0RE_0LC1LE_1LE1LD_1RE0LF_1RA0LB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEABDF") 1 6.
Time Qed.
End TM1674.


Module TM1675.
Definition tm := TM_from_str "1RB0LA_1LC1RA_1RD1LC_1LA1RE_1RF0RD_1RD---".
Definition tm' := TM_from_str "1RB0RC_1RC---_1LD1RA_1RE0LD_1LF1RD_1RC1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFCAB") 1 20.
Time Qed.
End TM1675.


Module TM1676.
Definition tm := TM_from_str "1LB0LE_1LC1LB_1RD1RC_0LA0RD_1LF1LA_1LD---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_1LB---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 7087 7088.
Time Qed.
End TM1676.


Module TM1677.
Definition tm := TM_from_str "1RB0RD_1LC1RF_1RD0LC_0RE---_1RF0LA_0LE0RA".
Definition tm' := TM_from_str "1RB0LA_0RC---_1RD0LE_0LC0RE_1RF0RB_1LA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 5 4.
Time Qed.
End TM1677.


Module TM1678.
Definition tm := TM_from_str "1LB0LC_0RC0RF_---0LD_1RE1LD_1LD0RB_1LA1RF".
Definition tm' := TM_from_str "1RB1LA_1LA0RC_0RF0RD_1LE1RD_1LC0LF_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECFABD") 4 1.
Time Qed.
End TM1678.


Module TM1679.
Definition tm := TM_from_str "1RB---_0RC0LD_1LD1RF_0LE0RB_1RB0LB_0RD0RA".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1679.


Module TM1680.
Definition tm := TM_from_str "1RB1LE_1LC0RF_1RB0RD_---1RE_1LA0LF_1RC1LA".
Definition tm' := TM_from_str "1RB0RC_1LA0RF_---1RD_1LE0LF_1RB1LD_1RA1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM1680.


Module TM1681.
Definition tm := TM_from_str "1RB0RA_1LC1RB_1LE1LD_1RB0LC_1RA1LF_1LC---".
Definition tm' := TM_from_str "1RB0LC_1LC1RB_1LD1LA_1RE1LF_1RB0RE_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM1681.


Module TM1682.
Definition tm := TM_from_str "1LB0RA_0LC1LD_1LD1RE_1RA1LC_1RF0RE_---0LB".
Definition tm' := TM_from_str "1RB1LD_1LC0RB_0LD1LA_1LA1RE_1RF0RE_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 11 9.
Time Qed.
End TM1682.


Module TM1683.
Definition tm := TM_from_str "1RB0RF_0LC0RA_1LE1LD_1LC0RE_1RB0LC_---1RE".
Definition tm' := TM_from_str "1RB0LC_0LC0RE_1LA1LD_1LC0RA_1RB0RF_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1683.


Module TM1684.
Definition tm := TM_from_str "1LB1LD_0RC1LA_0LA1RA_0LB0RE_1RC1RF_---0LD".
Definition tm' := TM_from_str "1RB1RF_0LC1RC_1LE1LD_0LE0RA_0RB1LC_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEBDAF") 14 1.
Time Qed.
End TM1684.


Module TM1685.
Definition tm := TM_from_str "1LB1LF_1LC0RA_0RD0LA_1RB1RE_0RA1RF_0RC---".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_0RA0LD_1LB1LF_0RD1RF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 21.
Time Qed.
End TM1685.


Module TM1686.
Definition tm := TM_from_str "1RB1LF_1RC0LF_0RD0RC_0LE0LA_1LB---_1LD0LA".
Definition tm' := TM_from_str "1RB0LE_0RC0RB_0LD0LF_1LA---_1LC0LF_1RA1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 8517 9167.
Time Qed.
End TM1686.


Module TM1687.
Definition tm := TM_from_str "1RB0RF_1RC---_1LD1RE_1LE0LD_0RA1LD_1LB0RC".
Definition tm' := TM_from_str "1RB---_1LC1RD_1LD0LC_0RE1LC_1RA0RF_1LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 4 11.
Time Qed.
End TM1687.


Module TM1688.
Definition tm := TM_from_str "1RB1RF_1LC0RE_1RB0LD_0RE1LD_1RA0LB_0RB---".
Definition tm' := TM_from_str "1RB0LC_1LA0RD_0RD1LC_1RE0LB_1RB1RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM1688.


Module TM1689.
Definition tm := TM_from_str "1RB0LB_1LC1RD_---1LD_0RE0LA_1RA1RF_1RB1LF".
Definition tm' := TM_from_str "1RB1LA_1LC1RD_---1LD_0RE0LF_1RF1RA_1RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1689.


Module TM1690.
Definition tm := TM_from_str "1RB0RA_0LB1LC_0LD0RC_1LE0LF_1RA1LD_1LD---".
Definition tm' := TM_from_str "1RB1LE_1RC0RB_0LC1LD_0LE0RD_1LA0LF_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 1507 1545.
Time Qed.
End TM1690.


Module TM1691.
Definition tm := TM_from_str "1LB0RB_1RC0LA_1LE1LD_---1RA_1RF1LC_1RB1RF".
Definition tm' := TM_from_str "1RB1LD_1RC1RB_1RD0LF_1LA1LE_---1RF_1LC0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEAB") 162 193.
Time Qed.
End TM1691.


Module TM1692.
Definition tm := TM_from_str "1LB0RA_0LC1RA_0RD1LE_1RA0LB_0LD1LF_1LB---".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LD1RB_0RA1LE_0LA1LF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 4 3.
Time Qed.
End TM1692.


Module TM1693.
Definition tm := TM_from_str "1LB1RA_0RA0LC_1LD1RB_1RB0LE_0LB1LF_1RA---".
Definition tm' := TM_from_str "1RB---_1LC1RB_0RB0LD_1LE1RC_1RC0LF_0LC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 3 1.
Time Qed.
End TM1693.


Module TM1694.
Definition tm := TM_from_str "1RB0RC_0LA0RE_1RD---_1LE0LF_1RF0LD_0RB1RA".
Definition tm' := TM_from_str "1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 4 1.
Time Qed.
End TM1694.


Module TM1695.
Definition tm := TM_from_str "1LB0RC_0RC---_1LF0LD_1RE1LC_1RF0RE_1LD1LA".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDABC") 4 1.
Time Qed.
End TM1695.


Module TM1696.
Definition tm := TM_from_str "1RB1RF_1LC0LA_1RE0LD_0RE0LB_0LB0RA_0RD---".
Definition tm' := TM_from_str "1RB0LE_0LC0RD_1LA0LD_1RC1RF_0RB0LC_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCAEBF") 1 4.
Time Qed.
End TM1696.


Module TM1697.
Definition tm := TM_from_str "1RB1LC_0LA0RB_0LD1RC_1LE1LD_1RB1RF_---1RE".
Definition tm' := TM_from_str "1RB1RF_0LC0RB_1RB1LD_0LE1RD_1LA1LE_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM1697.


Module TM1698.
Definition tm := TM_from_str "1LB1RA_1RC0LD_1RA0RB_0RC0LE_1RB1LF_---1LD".
Definition tm' := TM_from_str "1RB0RC_1LC1RB_1RA0LD_0RA0LE_1RC1LF_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 11 35.
Time Qed.
End TM1698.


Module TM1699.
Definition tm := TM_from_str "1RB0LA_0RC0RA_1LD1RE_1LA---_---1RF_1RB0RB".
Definition tm' := TM_from_str "1RB0RB_0RC0RE_1LD1RF_1LE---_1RB0LE_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1699.


Module TM1700.
Definition tm := TM_from_str "1RB1LE_0RC0LD_1LD1LA_0LA0RA_0LB1LF_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1LE_0LE0RE_1RB1LF_0LB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1700.


Module TM1701.
Definition tm := TM_from_str "1RB1LA_0RC1RC_1RD1RB_1RE0LA_1LF---_0RB0LF".
Definition tm' := TM_from_str "1RB0LF_1LC---_0RD0LC_0RE1RE_1RA1RD_1RD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 1 6.
Time Qed.
End TM1701.


Module TM1702.
Definition tm := TM_from_str "1RB1RA_0LC0RA_---1LD_1RE0LF_1RB1LE_1RB0LB".
Definition tm' := TM_from_str "1RB1LA_0LC0RE_---1LD_1RA0LF_1RB1RE_1RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1702.


Module TM1703.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC1LF_0RA---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM1703.


Module TM1704.
Definition tm := TM_from_str "1RB0LE_1RC0RA_0RD1RF_1LE0RA_0LA0LD_1RE---".
Definition tm' := TM_from_str "1RB---_0LC0LF_1RD0LB_1RE0RC_0RF1RA_1LB0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 1 5.
Time Qed.
End TM1704.


Module TM1705.
Definition tm := TM_from_str "1LB0RC_1RC1LE_0LF1RD_0LB0RD_1RA0LE_---0RA".
Definition tm' := TM_from_str "1RB1LF_0LC1RE_---0RD_1LA0RB_0LA0RE_1RD0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABEFC") 1 4.
Time Qed.
End TM1705.


Module TM1706.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LA_0RE---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM1706.


Module TM1707.
Definition tm := TM_from_str "1LB1RE_1LC0LB_1LD0RF_0LE---_1RF0RC_0RA0LA".
Definition tm' := TM_from_str "1RB0RE_0RC0LC_1LD1RA_1LE0LD_1LF0RB_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 53 39.
Time Qed.
End TM1707.


Module TM1708.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB1RD_0RA0LD".
Definition tm' := TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LB_0RD1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 32 22.
Time Qed.
End TM1708.


Module TM1709.
Definition tm := TM_from_str "1LB0RE_0LC1RE_0RD0LA_1RB1RF_1RC0LD_0RA---".
Definition tm' := TM_from_str "1RB1RF_0LC1RE_0RA0LD_1LB0RE_1RC0LA_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 4.
Time Qed.
End TM1709.


Module TM1710.
Definition tm := TM_from_str "1RB1RF_1LC1LD_1RE0LD_0LE0LB_1RA0RE_1RC---".
Definition tm' := TM_from_str "1RB0RA_1RC1RF_1LD1LE_1RA0LE_0LA0LC_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 157 107.
Time Qed.
End TM1710.


Module TM1711.
Definition tm := TM_from_str "1LB0RD_0RC1LE_1RA0LD_0LB1RF_1RC1LC_0LE---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA1LD_1RA1LA_0LC1RF_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM1711.


Module TM1712.
Definition tm := TM_from_str "1LB0LC_0RA0RD_1LD---_1RE0LA_0RF0RE_1RB0RE".
Definition tm' := TM_from_str "1RB0LE_0RC0RB_1RD0RB_0RE0RA_1LD0LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDFABC") 11 21.
Time Qed.
End TM1712.


Module TM1713.
Definition tm := TM_from_str "1RB1LD_1RC1LB_0LA0RC_0RC0LE_1LA0LF_---1LE".
Definition tm' := TM_from_str "1RB1LA_0LC0RB_1RA1LD_0RB0LE_1LC0LF_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 7.
Time Qed.
End TM1713.


Module TM1714.
Definition tm := TM_from_str "1RB0RB_1RC1RA_1LD1LE_---0LA_0LE1LF_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1714.


Module TM1715.
Definition tm := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RA---".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 954 982.
Time Qed.
End TM1715.


Module TM1716.
Definition tm := TM_from_str "1LB1RE_0RC1LB_1LE0RD_1RC0LC_1RA1RF_---1LD".
Definition tm' := TM_from_str "1RB0LB_1LC0RA_1RE1RD_---1LA_1LF1RC_0RB1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBACD") 4 1.
Time Qed.
End TM1716.


Module TM1717.
Definition tm := TM_from_str "1RB---_1RC1LB_0LB0RD_1RE1LC_0RC0RF_0RC1RA".
Definition tm' := TM_from_str "1RB1LC_0RC0RE_0LD0RA_1RC1LD_0RC1RF_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDCABE") 1 3.
Time Qed.
End TM1717.


Module TM1718.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LD0LC_1RA0RF_1RD---_0RE0LA".
Definition tm' := TM_from_str "1RB0RF_1RC0RE_1LD1RA_1LA0LD_1RA---_0RE0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 444 460.
Time Qed.
End TM1718.


Module TM1719.
Definition tm := TM_from_str "1LB1LE_1RC0LA_1LA0RD_0RC1RB_1LB1LF_1LA---".
Definition tm' := TM_from_str "1RB0LC_1LC0RE_1LA1LD_1LA1LF_0RB1RA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 385633 386261.
Time Qed.
End TM1719.


Module TM1720.
Definition tm := TM_from_str "1RB---_1LC0RF_1LE0RD_1RC0RD_0RB0LF_0LE1RA".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_0RE0LD_0LC1RF_1LB0RD_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEBACD") 5 1.
Time Qed.
End TM1720.


Module TM1721.
Definition tm := TM_from_str "1LB1RF_1RC0LB_1RD0LD_1LE0LC_---0RA_1RA1LC".
Definition tm' := TM_from_str "1RB0LB_1LC0LA_---0RD_1LF1RE_1RD1LA_1RA0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFABCE") 5 1.
Time Qed.
End TM1721.


Module TM1722.
Definition tm := TM_from_str "1LB1RF_1RC0LE_0LD0RD_1RC1LE_0LA1LA_0RC---".
Definition tm' := TM_from_str "1RB0LD_0LC0RC_1RB1LD_0LE1LE_1LA1RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 70 50.
Time Qed.
End TM1722.


Module TM1723.
Definition tm := TM_from_str "1RB0LF_1RC0RA_1RD0LE_1RE---_1RF1RC_1LA1LB".
Definition tm' := TM_from_str "1RB---_1RC1RF_1LD1LE_1RE0LC_1RF0RD_1RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 105 87.
Time Qed.
End TM1723.


Module TM1724.
Definition tm := TM_from_str "1RB1LF_1RC0RC_0LD1RC_1RA0LE_0RA1LA_---0LE".
Definition tm' := TM_from_str "1RB0RB_0LC1RB_1RE0LD_0RE1LE_1RA1LF_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 5.
Time Qed.
End TM1724.


Module TM1725.
Definition tm := TM_from_str "1LB0RA_1RC0LB_1RE0RD_1LA---_1LF0RE_1RA0LF".
Definition tm' := TM_from_str "1RB0RF_1LC0RB_1RD0LC_1LE0RD_1RA0LE_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 5 5.
Time Qed.
End TM1725.


Module TM1726.
Definition tm := TM_from_str "1RB1LD_1LC0RE_1RD1LC_0LC0RA_0RD1RF_1RC---".
Definition tm' := TM_from_str "1RB---_1RC1LB_0LB0RD_1RE1LC_1LB0RF_0RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 2 4.
Time Qed.
End TM1726.


Module TM1727.
Definition tm := TM_from_str "1RB0LD_0RC1RE_1RD1RF_1LA0LF_1RB---_0RA0LC".
Definition tm' := TM_from_str "1RB---_0RC1RA_1RD1RF_1LE0LF_1RB0LD_0RE0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1727.


Module TM1728.
Definition tm := TM_from_str "1LB0RD_1LC1LB_1RA1RE_---1RA_1RC0LF_1LE1LE".
Definition tm' := TM_from_str "1RB0LF_1RC1RA_1LD0RE_1LB1LD_---1RC_1LA1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEAF") 21 27.
Time Qed.
End TM1728.


Module TM1729.
Definition tm := TM_from_str "1RB1RE_1LC0RA_1RB0LD_1LE1LC_1RA0RF_---0LD".
Definition tm' := TM_from_str "1RB0LC_1LA0RE_1LD1LA_1RE0RF_1RB1RD_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM1729.


Module TM1730.
Definition tm := TM_from_str "1RB1LA_1LC1RE_1LD0LC_0RE0LE_1RF0RB_1RA---".
Definition tm' := TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LF0LE_0RA0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 19 20.
Time Qed.
End TM1730.


Module TM1731.
Definition tm := TM_from_str "1RB1LE_1LC0RD_0LF1LA_1RB1RD_0LA1LC_---1LA".
Definition tm' := TM_from_str "1RB1RA_1LC0RA_0LF1LD_1RB1LE_0LD1LC_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM1731.


Module TM1732.
Definition tm := TM_from_str "1LB1RC_1LC0LB_1RD1LC_1RF1RE_1RB0RD_1RA---".
Definition tm' := TM_from_str "1RB0RD_1LC0LB_1RD1LC_1RE1RA_1RF---_1LB1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 2 3.
Time Qed.
End TM1732.


Module TM1733.
Definition tm := TM_from_str "1LB1RD_1LC---_1RA1LC_1RE0RA_1LF0RB_1RB0LF".
Definition tm' := TM_from_str "1RB0LA_1LC---_1RD1LC_1LB1RE_1RF0RD_1LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 2 3.
Time Qed.
End TM1733.


Module TM1734.
Definition tm := TM_from_str "1LB1LF_0LC---_1LD1LC_1RE1RD_0LF0RE_1LC0LA".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_0LF---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 1 4.
Time Qed.
End TM1734.


Module TM1735.
Definition tm := TM_from_str "1LB---_1LC0RF_1LD1LB_1LE0LA_1LF0LB_1RB1RE".
Definition tm' := TM_from_str "1RB1RE_1LC0RA_1LD1LB_1LE0LF_1LA0LB_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 15 15.
Time Qed.
End TM1735.


Module TM1736.
Definition tm := TM_from_str "1LB0LE_1LC1LB_1RD1RC_0LA0RD_1LF1LA_1RD---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_1RB---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 764 757.
Time Qed.
End TM1736.


Module TM1737.
Definition tm := TM_from_str "1RB0LE_1RC1RB_1LD0RA_1LF1LC_0LC---_1RB0LA".
Definition tm' := TM_from_str "1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1737.


Module TM1738.
Definition tm := TM_from_str "1LB0RB_1RC0RF_0RD0LC_1RE---_1RA0LE_1LE1LF".
Definition tm' := TM_from_str "1RB---_1RC0LB_1LD0RD_1RF0RE_1LB1LE_0RA0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFABE") 6 1.
Time Qed.
End TM1738.


Module TM1739.
Definition tm := TM_from_str "1RB0RD_1LC0LD_0RB0LB_1LE1RF_1RA0LC_0RE---".
Definition tm' := TM_from_str "1RB0LD_1RC0RE_1LD0LE_0RC0LC_1LA1RF_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 5 4.
Time Qed.
End TM1739.


Module TM1740.
Definition tm := TM_from_str "1RB---_1LC1RF_0LD0LC_1RD0RE_1RB1RB_1RA0RE".
Definition tm' := TM_from_str "1RB1RB_1LC1RE_0LD0LC_1RD0RA_1RF0RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1740.


Module TM1741.
Definition tm := TM_from_str "1RB0RF_0RC1RB_1RD1RA_1LE0LE_0RA0LD_1RC---".
Definition tm' := TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF0RE_1RA---_0RA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFABCE") 134 162.
Time Qed.
End TM1741.


Module TM1742.
Definition tm := TM_from_str "1RB1RA_1RC1RF_1LD0RE_0RC0LD_1RA1LE_1LE---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_0RB0LC_1RE1LD_1RA1RE_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 9 8.
Time Qed.
End TM1742.


Module TM1743.
Definition tm := TM_from_str "1LB0RD_0LC0LA_1LD1RA_0RE---_0LA1RF_1RE0RC".
Definition tm' := TM_from_str "1RB0RF_0LC1RA_1LE0RD_0RB---_0LF0LC_1LD1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEFDBA") 1 6.
Time Qed.
End TM1743.


Module TM1744.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC1LF_1LC---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM1744.


Module TM1745.
Definition tm := TM_from_str "1RB1LC_1LC0RD_1RE0LD_1RC0LC_0LA0RF_1RA---".
Definition tm' := TM_from_str "1RB0LB_1RC0LA_0LD0RE_1RF1LB_1RD---_1LB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFBACE") 2 4.
Time Qed.
End TM1745.


Module TM1746.
Definition tm := TM_from_str "1RB1LB_1RC0LF_1RD---_1RE0RD_0LB0LA_0RC0LA".
Definition tm' := TM_from_str "1RB---_1RC0RB_0LD0LF_1RA0LE_0RA0LF_1RD1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDABCE") 1 6.
Time Qed.
End TM1746.


Module TM1747.
Definition tm := TM_from_str "1LB0LE_1LC0RE_1RD1RC_0LA0RD_0LF1LA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_1RD1RC_0LE0RD_1LB0LF_0LA1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 36 59.
Time Qed.
End TM1747.


Module TM1748.
Definition tm := TM_from_str "1RB1LE_0LC0RD_1LA0RD_1RC0RD_0LF---_0LB0RB".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1RF1LD_0LE---_0LF0RF_0LB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFBADE") 4 1.
Time Qed.
End TM1748.


Module TM1749.
Definition tm := TM_from_str "1RB0LE_1RC0LD_0RD0LB_1RE0RF_1LA0LE_1RA---".
Definition tm' := TM_from_str "1RB0LC_0RC0LA_1RD0RF_1LE0LD_1RA0LD_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 23 17.
Time Qed.
End TM1749.


Module TM1750.
Definition tm := TM_from_str "1RB1LA_0RC0RF_1LD---_0LD0LE_1RE0LA_1RB1RF".
Definition tm' := TM_from_str "1RB1RA_0RC0RA_1LD---_0LD0LE_1RE0LF_1RB1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1750.


Module TM1751.
Definition tm := TM_from_str "1LB0LF_0RC0RE_1LF0LD_1RE---_0RB0LC_1LA0LD".
Definition tm' := TM_from_str "1RB---_0RC0LD_0RD0RB_1LE0LA_1LF0LA_1LC0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 4 1.
Time Qed.
End TM1751.


Module TM1752.
Definition tm := TM_from_str "1RB1RE_1RC1RB_1LD1LC_0LE0LD_0RF0RA_0RA---".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0LD0LC_0RE0RF_0RF---_1RA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 662 820.
Time Qed.
End TM1752.


Module TM1753.
Definition tm := TM_from_str "1LB1RE_1RC0LB_1LC1LD_1RA1LD_1RF0RA_1RD---".
Definition tm' := TM_from_str "1RB0LA_1LB1LC_1RD1LC_1LA1RE_1RF0RD_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 4 3.
Time Qed.
End TM1753.


Module TM1754.
Definition tm := TM_from_str "1LB1LC_1RC1RA_0LE1RD_1RA0RB_---1LF_1LA0LF".
Definition tm' := TM_from_str "1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RE0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABFCD") 17 11.
Time Qed.
End TM1754.


Module TM1755.
Definition tm := TM_from_str "1LB0RA_1RC1LC_0RD1LD_1LE0LB_1LF---_1RA1LD".
Definition tm' := TM_from_str "1RB1LE_1LC0RB_1RD1LD_0RE1LE_1LF0LC_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 3 4.
Time Qed.
End TM1755.


Module TM1756.
Definition tm := TM_from_str "1LB1LA_0RC1RC_1RD1RB_1RE0LA_1LF---_0RB0LF".
Definition tm' := TM_from_str "1RB0LF_1LC---_0RD0LC_0RE1RE_1RA1RD_1LD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 1 4.
Time Qed.
End TM1756.


Module TM1757.
Definition tm := TM_from_str "1LB---_1LC0RB_1LD1RC_0LE1LF_1RB0LD_0LA1LE".
Definition tm' := TM_from_str "1RB0LD_1LC0RB_1LD1RC_0LA1LE_0LF1LA_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 10 19.
Time Qed.
End TM1757.


Module TM1758.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA0RF_0LE---".
Definition tm' := TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD0RF_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 709 739.
Time Qed.
End TM1758.


Module TM1759.
Definition tm := TM_from_str "1RB0LB_1RC1LB_1LC0RD_1LE1RD_1LF1LA_---1LE".
Definition tm' := TM_from_str "1RB1LA_1LB0RC_1LD1RC_1LF1LE_1RA0LA_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 15 21.
Time Qed.
End TM1759.


Module TM1760.
Definition tm := TM_from_str "1RB1RF_0LC0RB_1RB1LD_0LE1LE_1LA1LE_---1RA".
Definition tm' := TM_from_str "1RB1LC_0LA0RB_0LD1LD_1LE1LD_1RB1RF_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM1760.


Module TM1761.
Definition tm := TM_from_str "1LB1LE_1RC0LE_1RD0RC_1RA1RF_0LC0LA_1RB---".
Definition tm' := TM_from_str "1RB0RA_1RC1RF_1LD1LE_1RA0LE_0LA0LC_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 112 91.
Time Qed.
End TM1761.


Module TM1762.
Definition tm := TM_from_str "1RB---_1RC1LF_1LD1RE_1LB0LD_1RA0RC_1RB0LE".
Definition tm' := TM_from_str "1RB0LE_1RC1LA_1LD1RE_1LB0LD_1RF0RC_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1762.


Module TM1763.
Definition tm := TM_from_str "1LB1RC_1RA1RD_1RB0LC_---0RE_1LF0RA_1LC---".
Definition tm' := TM_from_str "1RB0LA_1RC1RD_1LB1RA_---0RE_1LF0RC_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBADEF") 32 20.
Time Qed.
End TM1763.


Module TM1764.
Definition tm := TM_from_str "1LB---_0RC1LC_0LA0RD_1RE0LB_0LF0RE_1RD1LD".
Definition tm' := TM_from_str "1RB1LB_1RC0LD_0LA0RC_0RE1LE_0LF0RB_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEBCA") 6 10.
Time Qed.
End TM1764.


Module TM1765.
Definition tm := TM_from_str "1RB0LE_1RC1RF_1LD0LC_1RF1LA_1RB0RE_---1RE".
Definition tm' := TM_from_str "1RB0RA_1RC1RF_1LD0LC_1RF1LE_1RB0LA_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1765.


Module TM1766.
Definition tm := TM_from_str "1LB0RB_0LC0RB_1RD1LE_0RA---_0LF0LD_0RA0LB".
Definition tm' := TM_from_str "1RB1LE_0RC---_1LD0RD_0LA0RD_0LF0LB_0RC0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 21 33.
Time Qed.
End TM1766.


Module TM1767.
Definition tm := TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_0RF0LE_1LB1RE".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RF_0RE0LD_1LA1RD_1RA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 19 32.
Time Qed.
End TM1767.


Module TM1768.
Definition tm := TM_from_str "1LB0RD_1RC1LF_0RD0RC_1LD1RE_0LB0LD_1LA---".
Definition tm' := TM_from_str "1RB1LE_0RC0RB_1LC1RD_0LA0LC_1LF---_1LA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 21 16.
Time Qed.
End TM1768.


Module TM1769.
Definition tm := TM_from_str "1LB1LD_1LC---_0LD0RC_1LE0LA_1LF1LE_1RC1RF".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_1LB---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 1 4.
Time Qed.
End TM1769.


Module TM1770.
Definition tm := TM_from_str "1RB0RF_1LC0RE_1RB0LD_1LC0LB_1RA1RC_0RB---".
Definition tm' := TM_from_str "1RB1RD_1RC0RF_1LD0RA_1RC0LE_1LD0LC_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 298 302.
Time Qed.
End TM1770.


Module TM1771.
Definition tm := TM_from_str "1LB0LC_1RC1LB_0LE1RD_0RB0RC_1LF0LA_---0LB".
Definition tm' := TM_from_str "1RB1LA_0LC1RE_1LF0LD_1LA0LB_0RA0RB_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 1 4.
Time Qed.
End TM1771.


Module TM1772.
Definition tm := TM_from_str "1LB0RC_1LC1LD_1RA0RB_0LE---_0RB0LF_1RB0LB".
Definition tm' := TM_from_str "1RB0LB_1LC1LD_1RF0RB_0LE---_0RB0LA_1LB0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 6.
Time Qed.
End TM1772.


Module TM1773.
Definition tm := TM_from_str "1RB0RB_1LC0RA_---0LD_1LE1LD_1RB1RF_0LC1RF".
Definition tm' := TM_from_str "1RB1RF_1LC0RE_---0LD_1LA1LD_1RB0RB_0LC1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1773.


Module TM1774.
Definition tm := TM_from_str "1LB---_1RC1RF_1LE0RD_0LC0RC_0LA1LA_1LC0RF".
Definition tm' := TM_from_str "1RB1RF_1LC0RE_0LD1LD_1LA---_0LB0RB_1LB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 4 1.
Time Qed.
End TM1774.


Module TM1775.
Definition tm := TM_from_str "1LB0LA_1RC0LA_1RE0LD_1LF0RE_1RD0RC_---0LB".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_---0LD_1RE0LF_1RA0LB_1LD0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEBAC") 5 1.
Time Qed.
End TM1775.


Module TM1776.
Definition tm := TM_from_str "1LB0RE_1RC1RB_0LD0RC_1LA0LE_0LF1LD_0RA---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_0LE1LC_0RF---_1LA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 1 6.
Time Qed.
End TM1776.


Module TM1777.
Definition tm := TM_from_str "1RB0LD_1RC1RA_1LA0RE_1LA1LC_0RF0LD_1RB---".
Definition tm' := TM_from_str "1RB1RC_1LC0RE_1RA0LD_1LC1LB_0RF0LD_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 41 18.
Time Qed.
End TM1777.


Module TM1778.
Definition tm := TM_from_str "1LB0LE_0RC0LA_1RA0RD_1RB1RF_1LA1RD_0RB---".
Definition tm' := TM_from_str "1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 1139 1183.
Time Qed.
End TM1778.


Module TM1779.
Definition tm := TM_from_str "1LB1RF_1LC0RD_1LD0RE_1RB0LC_0LB0RA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_1LF0RD_0LB0RE_1LB1RA_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFDA") 1 5.
Time Qed.
End TM1779.


Module TM1780.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LA_0LD---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM1780.


Module TM1781.
Definition tm := TM_from_str "1RB---_1RC0LD_1LD0RC_0LE1RC_0RB1LF_0LB1LA".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LD1RB_0RA1LE_0LA1LF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 13 10.
Time Qed.
End TM1781.


Module TM1782.
Definition tm := TM_from_str "1RB0LD_1LC0RF_1LE1LD_0LC---_1LA0LB_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1LE1LD_0LC---_1LF0LB_1RB0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1782.


Module TM1783.
Definition tm := TM_from_str "1RB1LC_1RC0RE_1LD0RB_1RA0LE_1LA1LF_0LC---".
Definition tm' := TM_from_str "1RB0RD_1LC0RA_1RE0LD_1LE1LF_1RA1LB_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 20 13.
Time Qed.
End TM1783.


Module TM1784.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LA_0RB1RF_1RA---".
Definition tm' := TM_from_str "1RB---_1LC1RF_0LE0RD_0RB0LB_1RD1LC_0RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEDFA") 1 5.
Time Qed.
End TM1784.


Module TM1785.
Definition tm := TM_from_str "1RB0RF_1LC1RE_1RD0LC_0LE0LE_1RA1LD_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1RE_1RD0LC_0LE0LE_1RF1LD_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1785.


Module TM1786.
Definition tm := TM_from_str "1LB1RE_0LC0RF_1RD1LB_0RA---_0RB1RD_0RA0LA".
Definition tm' := TM_from_str "1RB1LD_0RC---_1LD1RE_0LA0RF_0RD1RB_0RC0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 30 20.
Time Qed.
End TM1786.


Module TM1787.
Definition tm := TM_from_str "1RB0RA_1LC1RA_---0LD_1LE0LD_1LF0RB_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_1LC1RF_---0LD_1LE0LD_1LA0RB_1RB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1787.


Module TM1788.
Definition tm := TM_from_str "1RB1LE_0LC1RB_1LA0RD_1RC0RD_0LF---_0LB0RB".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1RF1LD_0LE---_0LF0RF_0LB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFBADE") 4 1.
Time Qed.
End TM1788.


Module TM1789.
Definition tm := TM_from_str "1RB0LC_1LC0RB_0LF0RD_0LA1LE_1RB---_0RA1LD".
Definition tm' := TM_from_str "1RB---_1LC0RB_0LE0RD_0LF1LA_0RF1LD_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1789.


Module TM1790.
Definition tm := TM_from_str "1LB---_1RC0LF_0LE0RD_1RE1RA_1LB0RF_0RC0LE".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABECD") 1 6.
Time Qed.
End TM1790.


Module TM1791.
Definition tm := TM_from_str "1LB1RC_1RC0LE_0RA1RD_0LB1RC_---1LF_0RD1LB".
Definition tm' := TM_from_str "1RB0LE_0RC1RD_1LA1RB_0LA1RB_---1LF_0RD1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 8 1.
Time Qed.
End TM1791.


Module TM1792.
Definition tm := TM_from_str "1LB---_1RC1LD_1RA0RB_1RC0LE_1RF0LF_0LB0LE".
Definition tm' := TM_from_str "1RB0LB_0LC0LA_1RE1LD_1RE0LA_1RF0RC_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCEDAB") 2 4.
Time Qed.
End TM1792.


Module TM1793.
Definition tm := TM_from_str "1LB---_0LC0RD_1RB1LC_1RE1LB_1RB0RF_0RB0RA".
Definition tm' := TM_from_str "1RB1LC_1RC0RE_0LD0RA_1RC1LD_0RC0RF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 4 9.
Time Qed.
End TM1793.


Module TM1794.
Definition tm := TM_from_str "1RB---_0LC0LA_1RF1RD_1LE0RD_1LB1LC_0LE0RF".
Definition tm' := TM_from_str "1RB1RF_0LC0RB_1LD1LA_0LA0LE_1RD---_1LC0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDAFCB") 11 10.
Time Qed.
End TM1794.


Module TM1795.
Definition tm := TM_from_str "1LB1RE_1LC---_1LD1RD_1RE1LA_0LD0RF_0RE0LF".
Definition tm' := TM_from_str "1RB1LC_0LA0RF_1LD1RB_1LE---_1LA1RA_0RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 11 36.
Time Qed.
End TM1795.


Module TM1796.
Definition tm := TM_from_str "1LB0LA_1RC1LA_0LF0RD_1RA1RE_---0RF_1RD0RC".
Definition tm' := TM_from_str "1RB1LE_0LC0RD_1RD0RB_1RE1RF_1LA0LE_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABDFC") 4 27.
Time Qed.
End TM1796.


Module TM1797.
Definition tm := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_0LE---".
Definition tm' := TM_from_str "1RB1RC_0LA---_1RD0RA_1RE0LA_1LF1LE_0RC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 984 954.
Time Qed.
End TM1797.


Module TM1798.
Definition tm := TM_from_str "1RB1RD_0LC1LE_1RA0LD_0RE1RF_1LF0RA_0LC---".
Definition tm' := TM_from_str "1RB0LD_1RC1RD_0LA1LF_0RF1RE_0LA---_1LE0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADFE") 2 6.
Time Qed.
End TM1798.


Module TM1799.
Definition tm := TM_from_str "1LB0LE_0RC0LB_1RE1RD_1LE0RF_1LA0RB_0LB---".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA0LD_1LB0RF_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEBF") 8 1.
Time Qed.
End TM1799.


Module TM1800.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RF1RE_1RB0RA_1RA---".
Definition tm' := TM_from_str "1RB0RD_1LC0LB_1RD1LC_1LB1RE_1RF1RA_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 2 3.
Time Qed.
End TM1800.


Module TM1801.
Definition tm := TM_from_str "1RB0RF_1RC1RB_1RD---_1LE0RA_1RB0LF_0LE1RD".
Definition tm' := TM_from_str "1RB0LE_1RC1RB_1RD---_1LA0RF_0LA1RD_1RB0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1801.


Module TM1802.
Definition tm := TM_from_str "1LB1RC_0RA0LB_0RD0LD_1RA0LE_1RD0LF_1LD---".
Definition tm' := TM_from_str "1RB0LE_1LC1RD_0RB0LC_0RA0LA_1RA0LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 12 19.
Time Qed.
End TM1802.


Module TM1803.
Definition tm := TM_from_str "1RB0LE_1LC1RF_0LD0LC_1RD0RA_1LB---_1RA0RA".
Definition tm' := TM_from_str "1RB0RB_1RC0LF_1LD1RA_0LE0LD_1RE0RB_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 37 49.
Time Qed.
End TM1803.


Module TM1804.
Definition tm := TM_from_str "1RB1RE_0LC1RC_0RA0LD_1RE1LF_1RA0LB_---1LC".
Definition tm' := TM_from_str "1RB1LF_1RC0LD_1RD1RB_0LE1RE_0RC0LA_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM1804.


Module TM1805.
Definition tm := TM_from_str "1LB0RB_1RC0LE_1RD1RD_0LB1RB_1LF1LA_---1RA".
Definition tm' := TM_from_str "1RB0LD_1RC1RC_0LA1RA_1LF1LE_1LA0RA_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 3 2.
Time Qed.
End TM1805.


Module TM1806.
Definition tm := TM_from_str "1LB0RE_0RC0LA_1RE0LD_0LB---_0RF1RD_1RA0RF".
Definition tm' := TM_from_str "1RB0LF_0RC1RF_1RD0RC_1LE0RB_0RA0LD_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 6 1.
Time Qed.
End TM1806.


Module TM1807.
Definition tm := TM_from_str "1RB0RB_1LC1RA_1RB1LD_0LB0LE_1LF1RE_---1LC".
Definition tm' := TM_from_str "1RB1LC_1LA1RD_0LB0LE_1RB0RB_1LF1RE_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBACEF") 1 1.
Time Qed.
End TM1807.


Module TM1808.
Definition tm := TM_from_str "1LB---_0LC1LC_1LD0LA_1RE1RF_1LA0RF_1RB0RE".
Definition tm' := TM_from_str "1RB0RF_0LC1LC_1LE0LD_1LB---_1RF1RA_1LD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 4.
Time Qed.
End TM1808.


Module TM1809.
Definition tm := TM_from_str "1LB0RE_1RC1LB_0LB0RD_1RA1LC_0RC0RF_0LD---".
Definition tm' := TM_from_str "1RB1LA_0LA0RC_1RD1LB_1LA0RE_0RB0RF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 3.
Time Qed.
End TM1809.


Module TM1810.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_0RF0LD_1RA---".
Definition tm' := TM_from_str "1RB---_1LC1RE_1LD0LC_1RB1RF_1RD0RB_0RA0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 141 77.
Time Qed.
End TM1810.


Module TM1811.
Definition tm := TM_from_str "1RB1RA_1LC0RA_1LD1LC_1RE0LB_0LB0RF_---0RD".
Definition tm' := TM_from_str "1RB0LC_0LC0RF_1LE0RD_1RC1RD_1LA1LE_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEABF") 1 4.
Time Qed.
End TM1811.


Module TM1812.
Definition tm := TM_from_str "1LB---_1RC0LF_0RE1LD_0LB0RE_0LA1RB_1LE1LD".
Definition tm' := TM_from_str "1RB0LE_0RC1LF_0LD1RA_1LA---_1LC1LF_0LA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABFCE") 16 17.
Time Qed.
End TM1812.


Module TM1813.
Definition tm := TM_from_str "1LB1RE_1RC0LB_0RE1LD_---0RB_1RA1LF_0LC0LF".
Definition tm' := TM_from_str "1RB0LA_0RC1LF_1RD1LE_1LA1RC_0LB0LE_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABFCE") 6 1.
Time Qed.
End TM1813.


Module TM1814.
Definition tm := TM_from_str "1RB1RF_1LC0RE_1RE0LD_0RA1LC_1RA1RC_1LD---".
Definition tm' := TM_from_str "1RB1RD_1RC1RF_1LD0RA_1RA0LE_0RB1LD_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 205 89.
Time Qed.
End TM1814.


Module TM1815.
Definition tm := TM_from_str "1RB0LC_1RC0RD_1RD0LC_1LE1RF_---1LA_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1815.


Module TM1816.
Definition tm := TM_from_str "1LB1LC_1RC0LD_1RE0LB_0RC0LB_0RF1RF_1RA---".
Definition tm' := TM_from_str "1RB0LE_0RC1RC_1RD---_1LE1LA_1RA0LF_0RA0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 6 1.
Time Qed.
End TM1816.


Module TM1817.
Definition tm := TM_from_str "1RB---_1RC0RA_0LD0RC_1LF1LE_1RF1LE_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1RC0RF_0LD0RC_1LA1LE_1RA1LE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1817.


Module TM1818.
Definition tm := TM_from_str "1LB1LC_0RA---_1LD0LA_1LE1LD_1RF1RE_0LC0RF".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_0RD---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECFAB") 1 4.
Time Qed.
End TM1818.


Module TM1819.
Definition tm := TM_from_str "1RB0RF_0LC1LD_1RD1LC_0RE0LB_0LE1LF_1RA---".
Definition tm' := TM_from_str "1RB1LA_0RC0LF_0LC1LD_1RE---_1RF0RD_0LA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 7 4.
Time Qed.
End TM1819.


Module TM1820.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_0RC---_1RA1RF".
Definition tm' := TM_from_str "1RB1RC_0RC---_1RD0RA_1RE1RD_1LF1LE_0RC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCABD") 4 1.
Time Qed.
End TM1820.


Module TM1821.
Definition tm := TM_from_str "1RB0RE_1LC1LB_1LD0LC_1RA0LA_0RF---_1RB1RF".
Definition tm' := TM_from_str "1RB0LB_1RC0RE_1LD1LC_1LA0LD_0RF---_1RC1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 67 26.
Time Qed.
End TM1821.


Module TM1822.
Definition tm := TM_from_str "1RB0LF_1RC0LA_1LD1RE_0RC0LD_0RB0LB_1LB---".
Definition tm' := TM_from_str "1RB0LE_1LC1RD_0RB0LC_0RA0LA_1RA0LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 10.
Time Qed.
End TM1822.


Module TM1823.
Definition tm := TM_from_str "1LB1LE_1RC1RE_1LA0RD_1RB1RB_1RD0RF_---0LC".
Definition tm' := TM_from_str "1RB1RB_1RC1RE_1LD0RA_1LB1LE_1RA0RF_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 394 358.
Time Qed.
End TM1823.


Module TM1824.
Definition tm := TM_from_str "1RB1RF_0LC0RB_1RB1LD_0LE1LE_1LA1RC_---1RA".
Definition tm' := TM_from_str "1RB1LC_0LA0RB_0LD1LD_1LE1RA_1RB1RF_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM1824.


Module TM1825.
Definition tm := TM_from_str "1LB0LA_1LC1RC_1RD0RA_0LC0RE_0RF1RC_---1RD".
Definition tm' := TM_from_str "1RB0RC_0LA0RE_1LD0LC_1LA1RA_0RF1RA_---1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 1 4.
Time Qed.
End TM1825.


Module TM1826.
Definition tm := TM_from_str "1RB1RA_1RC0LA_1LD1LC_0RE0LD_1RF---_0RB1RB".
Definition tm' := TM_from_str "1RB0LF_1LC1LB_0RD0LC_1RE---_0RA1RA_1RA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 10 6.
Time Qed.
End TM1826.


Module TM1827.
Definition tm := TM_from_str "1RB1LA_0LA0RC_1RD1LB_1RB0RE_0RB1RF_1LB---".
Definition tm' := TM_from_str "1RB0RE_0LC0RD_1RB1LC_1RA1LB_0RB1RF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDAEF") 1 1.
Time Qed.
End TM1827.


Module TM1828.
Definition tm := TM_from_str "1LB0RF_1LC0LA_0RD0LC_1RE0RD_1RB1RD_1RA---".
Definition tm' := TM_from_str "1RB---_1LC0RA_1LD0LB_0RE0LD_1RF0RE_1RC1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 94 88.
Time Qed.
End TM1828.


Module TM1829.
Definition tm := TM_from_str "1RB0LF_0LC0RB_1LA1LD_1LE1LD_1LC1RE_1RB---".
Definition tm' := TM_from_str "1RB---_0LC0RB_1LF1LD_1LE1LD_1LC1RE_1RB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1829.


Module TM1830.
Definition tm := TM_from_str "1LB0RE_0LC0RD_1RB1LC_1RA1LB_0RB0RF_1LB---".
Definition tm' := TM_from_str "1RB1LC_1LC0RE_0LD0RA_1RC1LD_0RC0RF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 1 4.
Time Qed.
End TM1830.


Module TM1831.
Definition tm := TM_from_str "1LB0RA_1LC1LC_0RD0LD_1RA1RE_0LC1RF_1RD---".
Definition tm' := TM_from_str "1RB1RE_1LC0RB_1LD1LD_0RA0LA_0LD1RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 2 3.
Time Qed.
End TM1831.


Module TM1832.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA1RF_1RC1RE_1RB0RA_---0LE".
Definition tm' := TM_from_str "1RB0RE_1LC0LB_1RE1RD_---0LA_1LB1RF_1RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFAD") 1 6.
Time Qed.
End TM1832.


Module TM1833.
Definition tm := TM_from_str "1RB0LE_1RC0RF_1LD0RA_1RC0LE_1LD0LE_0RC---".
Definition tm' := TM_from_str "1RB0LC_1LA0RD_1LA0LC_1RE0LC_1RB0RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBACF") 82 142.
Time Qed.
End TM1833.


Module TM1834.
Definition tm := TM_from_str "1RB0LD_1RC0RB_1LD0RE_1LA0LD_1RF---_1RA1LB".
Definition tm' := TM_from_str "1RB0RA_1LC0RE_1LD0LC_1RA0LC_1RF---_1RD1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 170 104.
Time Qed.
End TM1834.


Module TM1835.
Definition tm := TM_from_str "1RB0RF_1RC0RB_1LD0RA_1LE0LD_1RB0LC_1LE---".
Definition tm' := TM_from_str "1RB0LC_1RC0RB_1LD0RE_1LA0LD_1RB0RF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1835.


Module TM1836.
Definition tm := TM_from_str "1LB1LB_0LC1LC_1LD1LF_1RE1RD_0LA0RE_---1RA".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LD1LD_0LE1LE_1LA1LF_---1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 1 3.
Time Qed.
End TM1836.


Module TM1837.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB1RF_1LC1RA_0LA---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1RB_0LC1RF_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM1837.


Module TM1838.
Definition tm := TM_from_str "1RB1LC_1LA0RD_0LB0LF_1RB0RE_1RD1RA_0LC---".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_1RB1LD_0LB0LF_1RA1RC_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDAEF") 1 1.
Time Qed.
End TM1838.


Module TM1839.
Definition tm := TM_from_str "1LB1RE_1RC1LA_1LD0RC_0LA0RE_0RF0RD_---0LA".
Definition tm' := TM_from_str "1RB1LE_1LC0RB_0LE0RD_0RF0RC_1LA1RD_---0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 6.
Time Qed.
End TM1839.


Module TM1840.
Definition tm := TM_from_str "1RB0LE_0RC1LD_0LD1RD_1RE0LF_1RC1RA_---1LB".
Definition tm' := TM_from_str "1RB0LD_1RC1RF_0LA1RA_---1LE_0RC1LA_1RE0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FECABD") 3 7.
Time Qed.
End TM1840.


Module TM1841.
Definition tm := TM_from_str "1RB1LA_1RC1RB_1RD0LA_1LE1RE_0RF0LE_0RB---".
Definition tm' := TM_from_str "1RB0LF_1LC1RC_0RD0LC_0RE---_1RA1RE_1RE1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEABCD") 1 6.
Time Qed.
End TM1841.


Module TM1842.
Definition tm := TM_from_str "1RB0RD_0LC0LD_---1LA_0LB0RE_1RF1LD_1LC1RE".
Definition tm' := TM_from_str "1RB1LF_1LC1RA_---1LD_1RE0RF_0LC0LF_0LE0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECFAB") 7 1.
Time Qed.
End TM1842.


Module TM1843.
Definition tm := TM_from_str "1RB0RF_1RC0RA_1RD0LE_0LC---_0LF1LE_1RF1RB".
Definition tm' := TM_from_str "1RB0RF_1RC0LD_0LB---_0LE1LD_1RE1RA_1RA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 35 27.
Time Qed.
End TM1843.


Module TM1844.
Definition tm := TM_from_str "1LB1RE_0RC0LB_1RD1LC_1LC1RA_1RF0RD_1RD---".
Definition tm' := TM_from_str "1RB0RC_1RC---_1LD1RE_1RC1LD_1LF1RA_0RD0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDCAB") 11 4.
Time Qed.
End TM1844.


Module TM1845.
Definition tm := TM_from_str "1RB1LA_1LC0RC_1LD1RC_0LF1LE_1RB0LA_---0RB".
Definition tm' := TM_from_str "1RB0LE_1LC0RC_1LD1RC_0LF1LA_1RB1LE_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1845.


Module TM1846.
Definition tm := TM_from_str "1RB0RE_0LC1LE_0LE1LD_1RE0LF_1RA0LB_1RA---".
Definition tm' := TM_from_str "1RB0LC_1RC0RA_0LD1LA_0LA1LE_1RA0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 81 49.
Time Qed.
End TM1846.


Module TM1847.
Definition tm := TM_from_str "1LB0LC_1RC0LC_1LA0RD_0RB0RE_1RD0RF_0RC---".
Definition tm' := TM_from_str "1RB0RF_0RC0RA_1RD0LD_1LE0RB_1LC0LD_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDBAF") 286 181.
Time Qed.
End TM1847.


Module TM1848.
Definition tm := TM_from_str "1RB0RE_0RC1RA_1LC0LD_1RB1LD_0RB0RF_---1LB".
Definition tm' := TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RB0RE_0RB0RF_---1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM1848.


Module TM1849.
Definition tm := TM_from_str "1LB0RD_0RC0LA_1RD1RD_0RE1RF_1RA1LF_0LB---".
Definition tm' := TM_from_str "1RB1RB_0RC1RF_1RD1LF_1LE0RB_0RA0LD_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 3 1.
Time Qed.
End TM1849.


Module TM1850.
Definition tm := TM_from_str "1LB0LF_0RC1LE_1RF1RD_0RE0RC_1LA0RA_0LE---".
Definition tm' := TM_from_str "1RB1RF_0LC---_1LD0RD_1LE0LB_0RA1LC_0RC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFCB") 1 4.
Time Qed.
End TM1850.


Module TM1851.
Definition tm := TM_from_str "1RB0RC_1RC0RD_1LD1RA_1LB1RE_---1LF_0RC0LF".
Definition tm' := TM_from_str "1RB0RC_1LC1RF_1LA1RD_---1LE_0RB0LE_1RA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 59 59.
Time Qed.
End TM1851.


Module TM1852.
Definition tm := TM_from_str "1LB1RC_0RC1LD_1RA0RB_0LE---_1LF1LE_0RA0RE".
Definition tm' := TM_from_str "1RB0RC_1LC1RA_0RA1LD_0LE---_1LF1LE_0RB0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 5 1.
Time Qed.
End TM1852.


Module TM1853.
Definition tm := TM_from_str "1RB1RD_1RC---_0RD1RA_1LE0RC_1RF0LE_1RC1LF".
Definition tm' := TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA0RC_1RF1RD_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCDAB") 2 2.
Time Qed.
End TM1853.


Module TM1854.
Definition tm := TM_from_str "1LB---_1RC1LD_1RD0RC_1LE1RD_1LA1LF_1LC0LE".
Definition tm' := TM_from_str "1RB0RA_1LC1RB_1LE1LD_1LA0LC_1LF---_1RA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 12 1.
Time Qed.
End TM1854.


Module TM1855.
Definition tm := TM_from_str "1RB1RF_0LC0RB_1LE1LD_1LA1LD_0LA---_1RD1RA".
Definition tm' := TM_from_str "1RB1RC_1LC1LB_1RD1RA_0LE0RD_1LF1LB_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBFA") 14 8.
Time Qed.
End TM1855.


Module TM1856.
Definition tm := TM_from_str "1LB1RF_0RC0LB_1RE0RD_1RA---_1LB1LF_1RC0LE".
Definition tm' := TM_from_str "1RB---_1LC1RF_0RD0LC_1RE0RA_1LC1LF_1RD0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 4 1.
Time Qed.
End TM1856.


Module TM1857.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RB_0RB0RF_0LE---".
Definition tm' := TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RB_0RD0RF_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 35 19.
Time Qed.
End TM1857.


Module TM1858.
Definition tm := TM_from_str "1LB1RA_0RA0LC_1LD1RB_0LB0LE_0LB1LF_1RA---".
Definition tm' := TM_from_str "1RB---_1LC1RB_0RB0LD_1LE1RC_0LC0LF_0LC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 3 1.
Time Qed.
End TM1858.


Module TM1859.
Definition tm := TM_from_str "1LB1RF_0RC0LD_---1RD_1LE0RA_1LA0LD_1RA0RB".
Definition tm' := TM_from_str "1RB0RC_1LC1RA_0RF0LD_1LE0RB_1LB0LD_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFDEA") 5 3.
Time Qed.
End TM1859.


Module TM1860.
Definition tm := TM_from_str "1RB0LC_1LA0RE_1LD0RE_1LA0LF_1RB0RA_0LA---".
Definition tm' := TM_from_str "1RB0RC_1LC0RA_1RB0LD_1LE0RA_1LC0LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM1860.


Module TM1861.
Definition tm := TM_from_str "1LB---_1RC0LB_0RE0LD_0RF1RA_0LA1RD_1LB0RC".
Definition tm' := TM_from_str "1RB0LA_0RC0LE_0LD1RE_1LA---_0RF1RD_1LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 4 3.
Time Qed.
End TM1861.


Module TM1862.
Definition tm := TM_from_str "1LB0RE_1RC1LB_0LB0RD_1RA1LC_0RC1RF_1RB---".
Definition tm' := TM_from_str "1RB1LA_0LA0RC_1RD1LB_1LA0RE_0RB1RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 3.
Time Qed.
End TM1862.


Module TM1863.
Definition tm := TM_from_str "1RB1RE_0RC1RD_1LD0RA_0LE---_1RF0LB_0RA0LC".
Definition tm' := TM_from_str "1RB0LD_0RC0LE_1RD1RA_0RE1RF_1LF0RC_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 410 332.
Time Qed.
End TM1863.


Module TM1864.
Definition tm := TM_from_str "1RB0RD_1LC0RE_1RF0LD_1LA1LF_0LC0RA_0LE---".
Definition tm' := TM_from_str "1RB0LF_0LC---_0LA0RD_1RE0RF_1LA0RC_1LD1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFCB") 1 4.
Time Qed.
End TM1864.


Module TM1865.
Definition tm := TM_from_str "1RB1LB_0RC0LE_1LD0RA_1LE---_0LF0LD_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_0RC0LE_1LD0RF_1LE---_0LA0LD_1RB1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1865.


Module TM1866.
Definition tm := TM_from_str "1RB1RE_1RC0LB_1LD---_1RA1LD_1RF0RA_1LB1RE".
Definition tm' := TM_from_str "1RB0RF_1LC1RA_1RD0LC_1LE---_1RF1LE_1RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEAB") 4 5.
Time Qed.
End TM1866.


Module TM1867.
Definition tm := TM_from_str "1RB1LD_1LC0RE_1RB0LD_1RA0LA_1RC0RF_0RE---".
Definition tm' := TM_from_str "1RB0LC_1LA0RE_1RD0LD_1RB1LC_1RA0RF_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBACEF") 1 1.
Time Qed.
End TM1867.


Module TM1868.
Definition tm := TM_from_str "1RB0RD_0RC0RC_1LD0RA_0LE1RE_1RF0LC_1RA---".
Definition tm' := TM_from_str "1RB---_1RC0RE_0RD0RD_1LE0RB_0LF1RF_1RA0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 24 37.
Time Qed.
End TM1868.


Module TM1869.
Definition tm := TM_from_str "1RB1RF_0LC0RB_0RD1LC_1RA0LE_1LB---_1RB0RE".
Definition tm' := TM_from_str "1RB0RE_0LC0RB_0RD1LC_1RF0LE_1LB---_1RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1869.


Module TM1870.
Definition tm := TM_from_str "1LB1LE_1RC0LD_1RD0RB_0LA1LB_1RB0LF_0RD---".
Definition tm' := TM_from_str "1RB0RE_0LC1LE_1LE1LD_1RE0LF_1RA0LB_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEABDF") 1 6.
Time Qed.
End TM1870.


Module TM1871.
Definition tm := TM_from_str "1RB0LE_0RC1RE_1RD1RF_1LE0LE_0RA0LD_1RB---".
Definition tm' := TM_from_str "1RB---_0RC1RE_1RD1RA_1LE0LE_0RF0LD_1RB0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1871.


Module TM1872.
Definition tm := TM_from_str "1LB0RE_0LC1LF_1LD0LA_1RE0LC_1RC0RD_0LD---".
Definition tm' := TM_from_str "1RB0RC_1LC0LD_1RA0LB_1LE0RA_0LB1LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCAF") 2 3.
Time Qed.
End TM1872.


Module TM1873.
Definition tm := TM_from_str "1LB1RF_0RC1LB_1RA0LD_1LE---_0LB0RE_1RE0RD".
Definition tm' := TM_from_str "1RB0RE_0LC0RB_0RD1LC_1RF0LE_1LB---_1LC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEBA") 1 3.
Time Qed.
End TM1873.


Module TM1874.
Definition tm := TM_from_str "1LB1RC_1RA0LD_0RB0RF_0LE1LF_0RE1RA_1RC---".
Definition tm' := TM_from_str "1RB---_0RC0RA_1RD0LE_1LC1RB_0LF1LA_0RF1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCBEFA") 2 21.
Time Qed.
End TM1874.


Module TM1875.
Definition tm := TM_from_str "1LB0LA_0LC0LD_1RD0RD_0RE---_1LF0RF_1LA0LC".
Definition tm' := TM_from_str "1RB0RB_0RC---_1LD0RD_1LE0LA_1LF0LE_0LA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 13 1.
Time Qed.
End TM1875.


Module TM1876.
Definition tm := TM_from_str "1LB1RD_1LC---_0RA1LE_0RF0LC_0LD0LF_1RC0LB".
Definition tm' := TM_from_str "1RB0LD_0RC1LE_1LD1RF_1LB---_0LF0LA_0RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBFEA") 115 194.
Time Qed.
End TM1876.


Module TM1877.
Definition tm := TM_from_str "1RB0LF_1RC1RF_1RD---_1LE0RF_0RB0LE_1RB1LA".
Definition tm' := TM_from_str "1RB1LF_1RC1RA_1RD---_1LE0RA_0RB0LE_1RB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1877.


Module TM1878.
Definition tm := TM_from_str "1LB1LF_1RC0LA_0LB0RD_1RE1RC_1LA0LC_1LA---".
Definition tm' := TM_from_str "1RB0LC_0LA0RD_1LA1LF_1RE1RB_1LC0LB_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 4.
Time Qed.
End TM1878.


Module TM1879.
Definition tm := TM_from_str "1RB0LE_1RC0LD_1RD0LB_0LA0RC_1RB1LF_---1LA".
Definition tm' := TM_from_str "1RB1LF_1RC0LD_1RD0LB_0LE0RC_1RB0LA_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1879.


Module TM1880.
Definition tm := TM_from_str "1LB1RC_1LC0LB_1RD0RF_1RA1RE_1LC0RD_---1LE".
Definition tm' := TM_from_str "1RB0RF_1RC1RE_1LD1RA_1LA0LD_1LA0RB_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 12 12.
Time Qed.
End TM1880.


Module TM1881.
Definition tm := TM_from_str "1LB0LC_1RC1RD_1LA0RB_1LE0RB_1RF0LD_---1RE".
Definition tm' := TM_from_str "1RB1RD_1LC0RA_1LA0LB_1LE0RA_1RF0LD_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 53 48.
Time Qed.
End TM1881.


Module TM1882.
Definition tm := TM_from_str "1RB1LE_0RC0LD_1LD1LF_0LA0RF_0LB1LD_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1LA_0LE0RA_1RB1LF_0LB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1882.


Module TM1883.
Definition tm := TM_from_str "1LB1LE_1LC1LF_1RD1RC_0LE0RD_0LC1LA_1RC---".
Definition tm' := TM_from_str "1RB---_1RC1RB_0LD0RC_0LB1LE_1LF1LD_1LB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 7 1.
Time Qed.
End TM1883.


Module TM1884.
Definition tm := TM_from_str "1RB0LD_1LC1RA_1RE0RD_---1LB_1LA1RF_1RC0RE".
Definition tm' := TM_from_str "1RB0RC_1RC0RE_1LD1RA_1RF0LE_---1LF_1LB1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFBECA") 3 22.
Time Qed.
End TM1884.


Module TM1885.
Definition tm := TM_from_str "1RB1RC_1LC0RE_1RA0LD_1LC1LB_0RC1RF_0LC---".
Definition tm' := TM_from_str "1RB0LD_1RC1RA_1LA0RE_1LA1LC_0RA1RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 20 49.
Time Qed.
End TM1885.


Module TM1886.
Definition tm := TM_from_str "1RB0LF_0LC0RB_1LA1LD_1LE1LC_1LC1RE_1RB---".
Definition tm' := TM_from_str "1RB---_0LC0RB_1LF1LD_1LE1LC_1LC1RE_1RB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1886.


Module TM1887.
Definition tm := TM_from_str "1RB1RF_1RC1LC_1LD0RD_1RA0LE_0RA0LB_---1RD".
Definition tm' := TM_from_str "1RB1LB_1LC0RC_1RE0LD_0RE0LA_1RA1RF_---1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 10.
Time Qed.
End TM1887.


Module TM1888.
Definition tm := TM_from_str "1RB1RC_1RC0RD_0LD1RA_---0LE_0RA1LF_1RC1LD".
Definition tm' := TM_from_str "1RB0RC_0LC1RE_---0LD_0RE1LF_1RA1RB_1RB1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 5.
Time Qed.
End TM1888.


Module TM1889.
Definition tm := TM_from_str "1LB0LC_0LC0LA_0RD0RF_1RE0RB_1LB1RC_1RD---".
Definition tm' := TM_from_str "1RB---_1RC0RD_1LD1RF_0LF0LE_1LD0LF_0RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDFBCA") 3275 3220.
Time Qed.
End TM1889.


Module TM1890.
Definition tm := TM_from_str "1RB0LA_1LC---_1RE1LD_1RE1RA_1LC0RF_0RC1RD".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_1RB1LA_0RC1RA_1RF0LE_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCABD") 2 2.
Time Qed.
End TM1890.


Module TM1891.
Definition tm := TM_from_str "1LB1LD_1RC---_0LD0RC_1LE0LA_1LF1LE_1RC1RF".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_1RB---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 1 4.
Time Qed.
End TM1891.


Module TM1892.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LF_0RB1RD_0LE---".
Definition tm' := TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 34 22.
Time Qed.
End TM1892.


Module TM1893.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD1RA_0RA0LA_0RB0RF_0LC---".
Definition tm' := TM_from_str "1RB1RC_0RC0LC_1LD1RE_0LA0RB_0RD0RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 39 23.
Time Qed.
End TM1893.


Module TM1894.
Definition tm := TM_from_str "1LB1RF_1RC0LD_1RD1RA_1LE0LB_---0RA_1RA0LC".
Definition tm' := TM_from_str "1RB1RD_1LC0LF_---0RD_1LF1RE_1RD0LA_1RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFABCE") 3 5.
Time Qed.
End TM1894.


Module TM1895.
Definition tm := TM_from_str "1RB1LC_1LA0RD_1LA0LA_1RB1LE_1RF0LB_---1RE".
Definition tm' := TM_from_str "1RB1LE_1LC0RA_1RB1LD_1LC0LC_1RF0LB_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDAEF") 1 1.
Time Qed.
End TM1895.


Module TM1896.
Definition tm := TM_from_str "1RB0RF_0LC1LF_0LF1LD_0RD1LE_1RF---_1RA0LB".
Definition tm' := TM_from_str "1RB0LC_1RC0RA_0LD1LA_0LA1LE_0RE1LF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 77 45.
Time Qed.
End TM1896.


Module TM1897.
Definition tm := TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA0RC_1RF1RD_1RB---".
Definition tm' := TM_from_str "1RB---_1RC1LB_0RD1RF_1LE0RC_1RB0LE_1RA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM1897.


Module TM1898.
Definition tm := TM_from_str "1LB0RB_1RC0LA_1LE1LD_---1RA_1RF1LC_0RB1RF".
Definition tm' := TM_from_str "1RB0LF_1LC1LE_1RD1LB_0RA1RD_---1RF_1LA0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABECD") 46 35.
Time Qed.
End TM1898.


Module TM1899.
Definition tm := TM_from_str "1RB1LE_1LC---_1LD1RC_1RF1LE_1LB0LA_1RA0RF".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_1RD1LF_1LE---_1LA1RE_1LD0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEAFB") 12 5.
Time Qed.
End TM1899.


Module TM1900.
Definition tm := TM_from_str "1RB---_0LC1RE_---0LD_1RE1LD_1RA0RF_1LB1RF".
Definition tm' := TM_from_str "1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM1900.


Module TM1901.
Definition tm := TM_from_str "1RB---_1LC1RE_1LD0LC_1LA0LE_1RB0RF_1RE0RC".
Definition tm' := TM_from_str "1RB0RF_1LC1RA_1LD0LC_1LE0LA_1RB---_1RA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1901.


Module TM1902.
Definition tm := TM_from_str "1RB1LA_1LB0RC_1LD1RC_1LF1LE_1RA0LA_---0LC".
Definition tm' := TM_from_str "1RB0LB_1RC1LB_1LC0RD_1LE1RD_1LF1LA_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 21 15.
Time Qed.
End TM1902.


Module TM1903.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RF0LD_0RA1RE_1LB---_0LE1RD".
Definition tm' := TM_from_str "1RB0LA_0RC0LE_0LD1RE_1LA---_0RF1RD_1LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABEDC") 4 3.
Time Qed.
End TM1903.


Module TM1904.
Definition tm := TM_from_str "1RB0LF_1RC0RA_1LD1RE_1RF1RC_1RD---_1LA1LB".
Definition tm' := TM_from_str "1RB---_1RC1RF_1LD1LE_1RE0LC_1RF0RD_1LB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBAC") 103 85.
Time Qed.
End TM1904.


Module TM1905.
Definition tm := TM_from_str "1LB1RD_1RC0LE_1LD1RC_0RC0LA_0LD0LF_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0LF_1LD1RC_0RC0LE_1LB1RD_0LD0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 3 2.
Time Qed.
End TM1905.


Module TM1906.
Definition tm := TM_from_str "1LB0LE_0RC1RE_0RE1RD_1LE0RF_1LA0RB_1RE---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1LD0LB_0RE1RB_0RB1RF_1LB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 6 1.
Time Qed.
End TM1906.


Module TM1907.
Definition tm := TM_from_str "1RB1RE_0LC1RB_0RA0LD_1RE1LF_1RA0RB_---1LC".
Definition tm' := TM_from_str "1RB1LF_1RC0RD_1RD1RB_0LE1RD_0RC0LA_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM1907.


Module TM1908.
Definition tm := TM_from_str "1RB0LD_1RC0RF_1LD0RA_0RE0LD_0LC1LB_0RC---".
Definition tm' := TM_from_str "1RB0RF_1LC0RE_0RD0LC_0LB1LA_1RA0LC_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 86 180.
Time Qed.
End TM1908.


Module TM1909.
Definition tm := TM_from_str "1RB1LD_1RC0RC_1LA1RD_1RF0LE_0RA0LD_1RB---".
Definition tm' := TM_from_str "1RB0LF_1RC---_1RD0RD_1LE1RA_1RC1LA_0RE0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDAFB") 1 18.
Time Qed.
End TM1909.


Module TM1910.
Definition tm := TM_from_str "1RB1RA_1LC0RF_0LD0LC_1RE0LE_0RA0RF_0RB---".
Definition tm' := TM_from_str "1RB0LB_0RC0RF_1RD1RC_1LE0RF_0LA0LE_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 7818 8024.
Time Qed.
End TM1910.


Module TM1911.
Definition tm := TM_from_str "1LB---_1RC1LF_1RD0RC_1LE0RB_0LB0LD_0LE1LA".
Definition tm' := TM_from_str "1RB1LE_1RC0RB_1LD0RA_0LA0LC_0LD1LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 1 5.
Time Qed.
End TM1911.


Module TM1912.
Definition tm := TM_from_str "1LB---_1LC0LD_1RD1LF_0RF0RE_1RD1LE_0LB0LA".
Definition tm' := TM_from_str "1RB1LA_0RC0RA_0LD0LF_1LE0LB_1RB1LC_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEBAC") 2920 2971.
Time Qed.
End TM1912.


Module TM1913.
Definition tm := TM_from_str "1RB0RE_0LC0RA_1LE0LD_1LB1LF_1RA0RD_0LB---".
Definition tm' := TM_from_str "1RB0RE_1RC0RA_0LD0RB_1LA0LE_1LC1LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 62 88.
Time Qed.
End TM1913.


Module TM1914.
Definition tm := TM_from_str "1LB1RA_1RA0LC_1RA0LD_1RE1LD_1RC0RF_---0RA".
Definition tm' := TM_from_str "1RB0RF_1RC0LE_1LD1RC_1RC0LB_1RA1LE_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEAF") 3 2.
Time Qed.
End TM1914.


Module TM1915.
Definition tm := TM_from_str "1LB---_0LC0LD_0RD1LA_1RE1LE_1LC0RF_1RB0RF".
Definition tm' := TM_from_str "1RB1LB_1LC0RF_0RA1LD_1LE---_0LC0LA_1RE0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECABF") 55 55.
Time Qed.
End TM1915.


Module TM1916.
Definition tm := TM_from_str "1LB1RA_1RC0LE_---0RD_1RA1RF_1RD1LE_0RB0RA".
Definition tm' := TM_from_str "1RB1LA_1RC1RE_1LD1RC_1RF0LA_0RD0RC_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFBAE") 9 11.
Time Qed.
End TM1916.


Module TM1917.
Definition tm := TM_from_str "1LB0RB_1RC1RA_0LD1RB_0RB0LE_0RA0LF_---1LD".
Definition tm' := TM_from_str "1RB1RE_0LC1RA_0RA0LD_0RE0LF_1LA0RA_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 5.
Time Qed.
End TM1917.


Module TM1918.
Definition tm := TM_from_str "1RB1RC_0LC0LD_1RE1LD_0LB0LF_0RF---_0RA0RE".
Definition tm' := TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0LF_0LE0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 44 19.
Time Qed.
End TM1918.


Module TM1919.
Definition tm := TM_from_str "1LB0RA_1LC1LD_1RB1LA_---0LE_1RF0LC_1RF1RC".
Definition tm' := TM_from_str "1RB1LC_1LA1LD_1LB0RC_---0LE_1RF0LA_1RF1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBADEF") 22 36.
Time Qed.
End TM1919.


Module TM1920.
Definition tm := TM_from_str "1RB1LF_1RC0RB_0LD0LA_1RE0LE_0RA1LD_1LE---".
Definition tm' := TM_from_str "1RB0LB_0RC1LA_1RD1LF_1RE0RD_0LA0LC_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 14 1.
Time Qed.
End TM1920.


Module TM1921.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LA_0RB---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM1921.


Module TM1922.
Definition tm := TM_from_str "1LB0LA_1RC1RC_1RD1LC_1LA1RE_1RF0RD_1RB---".
Definition tm' := TM_from_str "1RB0RE_1RC---_1RD1RD_1RE1LD_1LF1RA_1LC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEAB") 30 39.
Time Qed.
End TM1922.


Module TM1923.
Definition tm := TM_from_str "1RB1LF_1RC0RB_0LC1LD_0LF1RE_1RB1LE_0LA---".
Definition tm' := TM_from_str "1RB1LA_1RC0RB_0LC1LD_0LE1RA_0LF---_1RB1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1923.


Module TM1924.
Definition tm := TM_from_str "1RB1LA_0LC0LC_0LA1LD_1RE0RF_1RC0RD_---1LB".
Definition tm' := TM_from_str "1RB0RE_0LC1LE_1RD1LC_0LB0LB_1RA0RF_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEAF") 2 5.
Time Qed.
End TM1924.


Module TM1925.
Definition tm := TM_from_str "1LB0RB_0RC0LC_1LA0LD_1RE1LE_0RF---_1RC0RA".
Definition tm' := TM_from_str "1RB1LB_0RC---_1RD0RE_1LE0LA_1LF0RF_0RD0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDABC") 4 1.
Time Qed.
End TM1925.


Module TM1926.
Definition tm := TM_from_str "1LB1LF_1RC0LE_1LE0RD_0RC1RB_1LB1LA_1LE---".
Definition tm' := TM_from_str "1RB0LC_1LC0RE_1LA1LD_1LA1LF_0RB1RA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 385633 386261.
Time Qed.
End TM1926.


Module TM1927.
Definition tm := TM_from_str "1RB0LC_1LC0RE_1RB1LD_1LA0RA_---0RF_1LA1RF".
Definition tm' := TM_from_str "1RB1LC_1LA0RE_1LD0RD_1RB0LA_---0RF_1LD1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBACEF") 1 1.
Time Qed.
End TM1927.


Module TM1928.
Definition tm := TM_from_str "1RB1LF_1RC0RC_1LD0RB_1LA0LE_1LD0LB_1RD---".
Definition tm' := TM_from_str "1RB---_1LC0LD_1RE1LA_1LB0LE_1RF0RF_1LB0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEFBDA") 4 5.
Time Qed.
End TM1928.


Module TM1929.
Definition tm := TM_from_str "1LB1RE_1LC0LB_1LD0LE_1LE---_1RA0RF_1RE1RF".
Definition tm' := TM_from_str "1RB1RA_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 507 509.
Time Qed.
End TM1929.


Module TM1930.
Definition tm := TM_from_str "1RB0RF_0LC1RC_1RA0LD_0RC1LE_1RB1LF_---0LD".
Definition tm' := TM_from_str "1RB1LF_0LC1RC_1RE0LD_0RC1LA_1RB0RF_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1930.


Module TM1931.
Definition tm := TM_from_str "1RB0LB_0LC0RF_---1LD_1RE0LA_1RB1LE_1RB1RF".
Definition tm' := TM_from_str "1RB1LA_0LC0RE_---1LD_1RA0LF_1RB1RE_1RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM1931.


Module TM1932.
Definition tm := TM_from_str "1RB1RC_1LC1LF_1RE0LD_1LB1LE_1RB0RA_---0LE".
Definition tm' := TM_from_str "1RB0RE_1LC1LF_1RA0LD_1LB1LA_1RB1RC_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM1932.


Module TM1933.
Definition tm := TM_from_str "1LB1LD_0RC1LA_1RA1RA_0LA0RE_0LC0RF_---1RD".
Definition tm' := TM_from_str "1RB1RB_1LC1LD_0RA1LB_0LB0RE_0LA0RF_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 3 1.
Time Qed.
End TM1933.


Module TM1934.
Definition tm := TM_from_str "1LB1RF_0LC0LE_1RD0RA_1RB0RC_1LC1LB_0RD---".
Definition tm' := TM_from_str "1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 4.
Time Qed.
End TM1934.


Module TM1935.
Definition tm := TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA0RB_0RD1RF_1RC---".
Definition tm' := TM_from_str "1RB---_0LC1RF_1LE0RD_0RB1LE_1RD0LE_0RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDBCFA") 4 8.
Time Qed.
End TM1935.


Module TM1936.
Definition tm := TM_from_str "1RB0LF_0LC0RD_0LE1LA_0RB1RA_1LC---_1RB0RE".
Definition tm' := TM_from_str "1RB0RF_0LC0RE_0LF1LD_1RB0LA_0RB1RD_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM1936.


Module TM1937.
Definition tm := TM_from_str "1RB0LE_1RC0LF_1LD0RA_0RB0LD_0LB---_1RA1LE".
Definition tm' := TM_from_str "1RB1LF_1RC0LF_1RD0LA_1LE0RB_0RC0LE_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 16 1.
Time Qed.
End TM1937.


Module TM1938.
Definition tm := TM_from_str "1RB1LD_1RC1LB_1RD0LF_1LE0RB_---1LA_0LC1LC".
Definition tm' := TM_from_str "1RB0LF_1LC0RE_---1LD_1RE1LB_1RA1LE_0LA1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 7 5.
Time Qed.
End TM1938.


Module TM1939.
Definition tm := TM_from_str "1LB0LE_0RC0LA_0RE0LD_1RB---_1LF1LB_1LA0LC".
Definition tm' := TM_from_str "1RB---_0RC0LF_0RD0LA_1LE1LB_1LF0LC_1LB0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 4 1.
Time Qed.
End TM1939.


Module TM1940.
Definition tm := TM_from_str "1LB---_1RC0LB_0RE1RD_1LB0RC_0LD1RF_0RD0RA".
Definition tm' := TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD0RF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABDCE") 707 735.
Time Qed.
End TM1940.


Module TM1941.
Definition tm := TM_from_str "1LB0RE_1RC0LE_1RA0RD_1RA---_1RC1LF_0RF0LA".
Definition tm' := TM_from_str "1RB---_1LC0RD_1RE0LD_1RE1LF_1RB0RA_0RF0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEADF") 165 87.
Time Qed.
End TM1941.


Module TM1942.
Definition tm := TM_from_str "1LB0LB_0RC0LA_1RF0RD_1RE---_1RA1RC_0RE0LE".
Definition tm' := TM_from_str "1RB---_1RC1RE_1LD0LD_0RE0LC_1RF0RA_0RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM1942.


Module TM1943.
Definition tm := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB1RF_1LA---".
Definition tm' := TM_from_str "1RB1RF_1LC1RE_1LD0LC_1RB1LD_1RA0RB_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 1.
Time Qed.
End TM1943.


Module TM1944.
Definition tm := TM_from_str "1RB0LC_1LA0RD_1LA0LB_1RE0LC_1RB0RF_0RB---".
Definition tm' := TM_from_str "1RB0RF_1LC0RE_1RB0LD_1LC0LB_1RA0LD_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM1944.


Module TM1945.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0RE_1LC1LE_0LF0LA_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RB_1LD0RF_1RB1LE_1LC1LF_0LA0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM1945.


Module TM1946.
Definition tm := TM_from_str "1LB0RD_1RC0LB_1RD1LC_0RA1RE_1RF1RA_1LE---".
Definition tm' := TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA0RC_1RF1RD_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 69 56.
Time Qed.
End TM1946.


Module TM1947.
Definition tm := TM_from_str "1RB0RA_1LB1LC_1RB1LD_0LE1LF_1LF0LD_1RA---".
Definition tm' := TM_from_str "1RB1LC_1LB1LA_0LD1LE_1LE0LC_1RF---_1RB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBACDE") 1 1.
Time Qed.
End TM1947.


Module TM1948.
Definition tm := TM_from_str "1LB1RA_1RC1LE_1LD0RC_1RA1RA_1LF0LB_1LA---".
Definition tm' := TM_from_str "1RB1RB_1LC1RB_1RF1LD_1LE0LC_1LB---_1LA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFADE") 22 23.
Time Qed.
End TM1948.


Module TM1949.
Definition tm := TM_from_str "1LB---_1LC1LD_1RD1RC_1LE1LB_1RF0LA_0LD0RF".
Definition tm' := TM_from_str "1RB0LF_0LC0RB_1LA1LD_1LE1LC_1RC1RE_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDECAB") 1 3.
Time Qed.
End TM1949.


Module TM1950.
Definition tm := TM_from_str "1LB0RE_0LC1LD_1RA0LF_0RA1LB_---1RF_0LD1RA".
Definition tm' := TM_from_str "1RB0LF_1LC0RE_0LA1LD_0RB1LC_---1RF_0LD1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 1 8.
Time Qed.
End TM1950.


Module TM1951.
Definition tm := TM_from_str "1LB1RD_0RC0LE_1RD0LB_0RE---_1RF0LC_1RA1RE".
Definition tm' := TM_from_str "1RB0LF_0RC---_1RD0LA_1RE1RC_1LF1RB_0RA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 5 1.
Time Qed.
End TM1951.


Module TM1952.
Definition tm := TM_from_str "1RB---_1RC1LB_1LD1RF_1RB0LE_1LC0LE_1RA0RC".
Definition tm' := TM_from_str "1RB0LD_1RC1LB_1LA1RE_1LC0LD_1RF0RC_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM1952.


Module TM1953.
Definition tm := TM_from_str "1RB---_0LB1RC_1LD1RF_1LA0LE_0RC1LD_1RB0RE".
Definition tm' := TM_from_str "1RB0RE_0LB1RC_1LD1RA_1LF0LE_0RC1LD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1953.


Module TM1954.
Definition tm := TM_from_str "1RB1RA_1LC1LF_0RD0LC_1RE---_0RF1RA_1RB1LB".
Definition tm' := TM_from_str "1RB1LB_1LC1LA_0RD0LC_1RE---_0RA1RF_1RB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1954.


Module TM1955.
Definition tm := TM_from_str "1LB0RD_0RC1LE_1RA0LD_0LB0RD_0RE0LF_1LC---".
Definition tm' := TM_from_str "1RB0LF_1LC0RF_0RA1LD_0RD0LE_1LA---_0LC0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAFDE") 6 1.
Time Qed.
End TM1955.


Module TM1956.
Definition tm := TM_from_str "1RB0RA_0LB0RC_1RD0LF_0LE1RA_---1RF_1LC1LD".
Definition tm' := TM_from_str "1RB0LD_0LC1RE_---1RD_1LA1LB_1RF0RE_0LF0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 4 1.
Time Qed.
End TM1956.


Module TM1957.
Definition tm := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RE_1RD---".
Definition tm' := TM_from_str "1RB---_1LC0LA_1RF0LD_0LE0RD_0RC0LB_1LE0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFEBDA") 20 44.
Time Qed.
End TM1957.


Module TM1958.
Definition tm := TM_from_str "1LB---_0LC1RE_0RD1LF_1RB1RE_0RF0RA_0LA0RD".
Definition tm' := TM_from_str "1RB1RF_0LC1RF_0RA1LD_0LE0RA_1LB---_0RD0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCAFD") 723 779.
Time Qed.
End TM1958.


Module TM1959.
Definition tm := TM_from_str "1RB1RE_1RC0RF_1RD0RE_1LE1LC_1RA0LD_1RE---".
Definition tm' := TM_from_str "1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 6 7.
Time Qed.
End TM1959.


Module TM1960.
Definition tm := TM_from_str "1LB1LF_1LC0LE_1RD0LB_1RB0RC_1LA0RD_0LC---".
Definition tm' := TM_from_str "1RB0RC_1LC0LD_1RA0LB_1LE0RA_1LB1LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 5 1.
Time Qed.
End TM1960.


Module TM1961.
Definition tm := TM_from_str "1RB0LD_1RC---_0LA1RE_0RC1LC_1RF1LA_1RA0RD".
Definition tm' := TM_from_str "1RB---_0LC1RE_1RA0LD_0RB1LB_1RF1LC_1RC0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 6.
Time Qed.
End TM1961.


Module TM1962.
Definition tm := TM_from_str "1RB1RB_1RC0RB_1LD0LA_1RB1LE_1LF0LD_1LC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LF0LA_1RB1RB_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM1962.


Module TM1963.
Definition tm := TM_from_str "1LB0RE_0LC1LE_0RD1LA_1RA---_1RC1RF_0RA0LC".
Definition tm' := TM_from_str "1RB1RF_0RC1LD_1RD---_1LE0RA_0LB1LA_0RD0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCAF") 181 198.
Time Qed.
End TM1963.


Module TM1964.
Definition tm := TM_from_str "1LB1LD_0RC0RE_0LD1RB_1LA0LD_1RD0RF_---1RC".
Definition tm' := TM_from_str "1RB0RF_1LC0LB_1LD1LB_0RE0RA_0LB1RD_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBAF") 5 1.
Time Qed.
End TM1964.


Module TM1965.
Definition tm := TM_from_str "1RB0LA_0RC0LA_1LB1RD_1RC1LE_1LF0LE_---0RC".
Definition tm' := TM_from_str "1RB1LE_1LC1RA_0RB0LD_1RC0LD_1LF0LE_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCBAEF") 4 5.
Time Qed.
End TM1965.


Module TM1966.
Definition tm := TM_from_str "1LB---_1LC1LD_1RD0RE_0RF0RC_0LB0LA_1RA1LA".
Definition tm' := TM_from_str "1RB0RF_0RC0RA_1RD1LD_1LE---_1LA1LB_0LE0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABFC") 47 49.
Time Qed.
End TM1966.


Module TM1967.
Definition tm := TM_from_str "1LB1RF_1RC0LD_1RD0LD_1LE0LB_---0RA_1RA1LC".
Definition tm' := TM_from_str "1RB0LC_1RC0LC_1LD0LA_---0RE_1LA1RF_1RE1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 5 1.
Time Qed.
End TM1967.


Module TM1968.
Definition tm := TM_from_str "1RB---_1RC0RB_0LD0LE_1RA1LC_1RA1LF_1LF1LD".
Definition tm' := TM_from_str "1RB0RA_0LC0LE_1RD1LB_1RA---_1RD1LF_1LF1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 7 6.
Time Qed.
End TM1968.


Module TM1969.
Definition tm := TM_from_str "1LB0RB_1RC0LA_1LF0LD_---1RE_0RB1RD_1RD1LC".
Definition tm' := TM_from_str "1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RD_1LA0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABDEC") 46 35.
Time Qed.
End TM1969.


Module TM1970.
Definition tm := TM_from_str "1RB0LC_1LA0RD_1LA0LB_1RE0LB_1RB0RF_0RB---".
Definition tm' := TM_from_str "1RB0LC_1RC0RF_1LD0RA_1RC0LE_1LD0LC_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEABF") 118 58.
Time Qed.
End TM1970.


Module TM1971.
Definition tm := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LB_0LC0RE_0LD1LB".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0RF_0LA---_0LB1LD_0LA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 22 32.
Time Qed.
End TM1971.


Module TM1972.
Definition tm := TM_from_str "1LB---_0LC1RE_0RD1LF_1RE0LB_1LB0RE_0LD1LA".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LD1RB_0RA1LE_0LA1LF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 4 3.
Time Qed.
End TM1972.


Module TM1973.
Definition tm := TM_from_str "1RB0LE_0LC1RD_1LC1LA_0RB0RD_1RB0LF_---0LA".
Definition tm' := TM_from_str "1RB0LF_0LC1RE_1LC1LD_1RB0LA_0RB0RE_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 1.
Time Qed.
End TM1973.


Module TM1974.
Definition tm := TM_from_str "1RB1LA_1LC1LB_0RD0LC_1RE---_0RF1LF_1RA1RF".
Definition tm' := TM_from_str "1RB---_0RC1LC_1RD1RC_1RE1LD_1LF1LE_0RA0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 71 37.
Time Qed.
End TM1974.


Module TM1975.
Definition tm := TM_from_str "1RB---_1RC0RA_0LD1LF_0LF1LE_1RF0LA_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1RC0RF_0LD1LA_0LA1LE_1RA0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1975.


Module TM1976.
Definition tm := TM_from_str "1LB0LE_1LC1LB_1RD1RC_0LA0RD_1LF1LA_0LB---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_0LF---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 18 11.
Time Qed.
End TM1976.


Module TM1977.
Definition tm := TM_from_str "1LB0LE_1LC1LF_1RD1LA_1RB1RD_1LA1RB_---0RE".
Definition tm' := TM_from_str "1RB1LD_1RC1RB_1LA1LF_1LC0LE_1LD1RC_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCABEF") 101 114.
Time Qed.
End TM1977.


Module TM1978.
Definition tm := TM_from_str "1LB0RD_1LC0RF_1RA0RF_1RB1RE_0RA---_0RC0LA".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0RD_0RC0LE_1LB0RA_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCAFD") 1 5.
Time Qed.
End TM1978.


Module TM1979.
Definition tm := TM_from_str "1RB1RE_1LC---_1LE1LD_1LC0RA_1RD0LF_0LB0RE".
Definition tm' := TM_from_str "1RB0LE_1LC0RD_1LA1LB_1RF1RA_0LF0RA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFCBAE") 2 2.
Time Qed.
End TM1979.


Module TM1980.
Definition tm := TM_from_str "1LB0LF_1RC0LA_0RE1RD_1RC---_1RA1RF_0RB0LE".
Definition tm' := TM_from_str "1RB1RF_1LC0LF_1RD0LB_0RA1RE_1RD---_0RC0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 25 11.
Time Qed.
End TM1980.


Module TM1981.
Definition tm := TM_from_str "1RB1RC_1RC1RF_0LD1RE_1LB1LD_1RA0RC_---0LE".
Definition tm' := TM_from_str "1RB0RD_1RC1RD_1RD1RF_0LE1RA_1LC1LE_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 120 12.
Time Qed.
End TM1981.


Module TM1982.
Definition tm := TM_from_str "1RB0LF_0LC0LA_0RD1LB_1RE0RB_1RB1RD_---1LC".
Definition tm' := TM_from_str "1RB0RC_1RC1RA_0LD0LE_0RA1LC_1RC0LF_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDABF") 28 1.
Time Qed.
End TM1982.


Module TM1983.
Definition tm := TM_from_str "1RB1RF_1LC1RE_1LD0LC_1RB1LD_1RA0RB_0RE---".
Definition tm' := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB1RF_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM1983.


Module TM1984.
Definition tm := TM_from_str "1RB1RC_1LC0RE_1RE0LD_0LB1LB_0RF1RA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RE_1RE0LD_0LB1LB_0RA1RF_1RB1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM1984.


Module TM1985.
Definition tm := TM_from_str "1LB---_1LC0RD_1RD0LE_1RF1RC_0RF1LC_1RB0RA".
Definition tm' := TM_from_str "1RB0RF_1LC0RE_1RE0LD_0RA1LC_1RA1RC_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCEDA") 6 2.
Time Qed.
End TM1985.


Module TM1986.
Definition tm := TM_from_str "1RB1LC_1LA1RB_1LA1LD_---1RE_1LF0RF_1RC0LE".
Definition tm' := TM_from_str "1RB0LF_1LC1LE_1RD1LB_1LC1RD_---1RF_1LA0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEFA") 2 2.
Time Qed.
End TM1986.


Module TM1987.
Definition tm := TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1RB_0RF0RB_0LC0RD".
Definition tm' := TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA---_0RF0RD_0LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 35 21.
Time Qed.
End TM1987.


Module TM1988.
Definition tm := TM_from_str "1RB1RC_1LC0RF_1RA0LD_0LE1LB_0RB---_0RC0LB".
Definition tm' := TM_from_str "1RB0LD_1RC1RA_1LA0RE_0LF1LC_0RA0LC_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADFE") 12 35.
Time Qed.
End TM1988.


Module TM1989.
Definition tm := TM_from_str "1RB---_1LC1RA_0LD0RC_1RE0LF_0RB0LC_1LC1LD".
Definition tm' := TM_from_str "1RB0LE_0RC0LD_1LD1RF_0LA0RD_1LD1LA_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 6 1.
Time Qed.
End TM1989.


Module TM1990.
Definition tm := TM_from_str "1LB---_1RC1RF_0LD0RC_1LE1LB_0LB1LA_1LD0RF".
Definition tm' := TM_from_str "1RB1RF_0LC0RB_1LD1LA_0LA1LE_1LA---_1LC0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 3.
Time Qed.
End TM1990.


Module TM1991.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_1RA---_1RA1RF".
Definition tm' := TM_from_str "1RB1RE_1RC---_1LD1LC_0RE0LD_1RF0RA_1RC1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM1991.


Module TM1992.
Definition tm := TM_from_str "1RB0RA_1LC0LE_1LF1LD_1RB0LC_---1RA_1RA1LB".
Definition tm' := TM_from_str "1RB0LC_1LC0LD_1LF1LA_---1RE_1RB0RE_1RE1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM1992.


Module TM1993.
Definition tm := TM_from_str "1RB1LC_1LA0RD_0LB1LF_1RE1LC_1RF0RB_0LA---".
Definition tm' := TM_from_str "1RB0RE_0LC---_1RE1LD_0LE1LB_1LC0RF_1RA1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEDFAB") 3256 2247.
Time Qed.
End TM1993.


Module TM1994.
Definition tm := TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA1LB_0RB1RF_0RA---".
Definition tm' := TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RF_0RD1RF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 31 23.
Time Qed.
End TM1994.


Module TM1995.
Definition tm := TM_from_str "1LB1LE_1RC1RB_1RD0RC_0LD0LA_0RC1LF_---0LA".
Definition tm' := TM_from_str "1RB1RA_1RC0RB_0LC0LD_1LA1LE_0RB1LF_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 11.
Time Qed.
End TM1995.


Module TM1996.
Definition tm := TM_from_str "1LB0RA_1LC1LA_1LD1LF_1RE---_0RA0RF_0LB1RE".
Definition tm' := TM_from_str "1RB---_0RC0RF_1LD0RC_1LE1LC_1LA1LF_0LD1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 282 106.
Time Qed.
End TM1996.


Module TM1997.
Definition tm := TM_from_str "1RB1LE_0RC---_0RD0RB_1LE1RA_0LF1RF_1RE0LA".
Definition tm' := TM_from_str "1RB0LC_0LA1RA_1RD1LB_0RE---_0RF0RD_1LB1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 1 4.
Time Qed.
End TM1997.


Module TM1998.
Definition tm := TM_from_str "1LB0RB_1RC1RD_1LF0LB_0RE---_0LB0RA_1RE0LC".
Definition tm' := TM_from_str "1RB0LE_0LC0RF_1RE1RD_0RB---_1LA0LC_1LC0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCEDBA") 3 2.
Time Qed.
End TM1998.


Module TM1999.
Definition tm := TM_from_str "1LB0RD_1RC0LF_1RA1RD_0RE---_0LA1RB_0LA1LE".
Definition tm' := TM_from_str "1RB0LD_1RC1RF_1LA0RF_0LC1LE_0LC1RA_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABFED") 5 2.
Time Qed.
End TM1999.


Module TM2000.
Definition tm := TM_from_str "1RB0LD_1RC0RA_0LA1RA_0RA1LE_1RC1LF_---0LD".
Definition tm' := TM_from_str "1RB1LF_0LC1RC_1RE0LD_0RC1LA_1RB0RC_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEBDAF") 1 5.
Time Qed.
End TM2000.


Module TM2001.
Definition tm := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1RF_0LE0RB_1RB0LB_0RD1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM2001.


Module TM2002.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB1RF_0RA0LD".
Definition tm' := TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LB_0RD1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 33 23.
Time Qed.
End TM2002.


Module TM2003.
Definition tm := TM_from_str "1RB0LE_0LB0RC_1RD---_1LA0RE_0RF0LE_0LD1RB".
Definition tm' := TM_from_str "1RB---_1LC0RD_1RF0LD_0RE0LD_0LB1RF_0LF0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 4 1.
Time Qed.
End TM2003.


Module TM2004.
Definition tm := TM_from_str "1LB---_1LC0LA_1RD1LB_1RE0RD_0LE1LF_0LB0RF".
Definition tm' := TM_from_str "1RB1LE_1RC0RB_0LC1LD_0LE0RD_1LA0LF_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEABCD") 11348 10586.
Time Qed.
End TM2004.


Module TM2005.
Definition tm := TM_from_str "1LB1LE_1RC1LD_1RA0RC_1LA0LB_0LF0RD_1LD---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_0LF0RD_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 10 33.
Time Qed.
End TM2005.


Module TM2006.
Definition tm := TM_from_str "1LB0LE_1RC0LD_1RD0RB_0LA0RC_1LD1LF_0LD---".
Definition tm' := TM_from_str "1RB0LC_1RC0RA_0LD0RB_1LA0LE_1LC1LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 19 1.
Time Qed.
End TM2006.


Module TM2007.
Definition tm := TM_from_str "1LB---_1RC1LB_1LA1RD_1RE0RC_1LF0RA_0RC0LF".
Definition tm' := TM_from_str "1RB0RD_1LC0RE_0RD0LC_1LE1RA_1LF---_1RD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDABC") 17 18.
Time Qed.
End TM2007.


Module TM2008.
Definition tm := TM_from_str "1LB0RD_0RC1LE_1RA0LD_0LB1LC_1RC1LF_1LD---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA1LD_1RA1LF_0LC1LA_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM2008.


Module TM2009.
Definition tm := TM_from_str "1LB1LF_1RC0LD_1LE0RD_0LE0RD_0RB0LA_1RD---".
Definition tm' := TM_from_str "1RB---_0LC0RB_0RE0LD_1LE1LA_1RF0LB_1LC0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 1 4.
Time Qed.
End TM2009.


Module TM2010.
Definition tm := TM_from_str "1RB---_1LC0LC_0RE0LD_0LB0RB_1RE1RF_1RA1LC".
Definition tm' := TM_from_str "1RB1LD_1RC---_1LD0LD_0RF0LE_0LC0RC_1RF1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 2 9.
Time Qed.
End TM2010.


Module TM2011.
Definition tm := TM_from_str "1RB1LC_1LA0RE_0LD0RA_1RC1LD_0RC1RF_1RD---".
Definition tm' := TM_from_str "1RB---_1RC1LB_0LB0RD_1RE1LC_1LD0RF_0RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECBFA") 29 32.
Time Qed.
End TM2011.


Module TM2012.
Definition tm := TM_from_str "1RB0LC_1LC0RE_---1LD_1RE0LD_1LC1RF_1RA1LB".
Definition tm' := TM_from_str "1RB0LA_1LC1RD_---1LA_1RF1LE_1LC0RB_1RE0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FECABD") 2 2.
Time Qed.
End TM2012.


Module TM2013.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_0LE---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM2013.


Module TM2014.
Definition tm := TM_from_str "1RB1RF_1RC1RA_1LD0LE_1RB0LC_0RB0RD_1RE---".
Definition tm' := TM_from_str "1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM2014.


Module TM2015.
Definition tm := TM_from_str "1LB---_1RC0RF_1LD0RB_0LE0LC_0LF0LA_1RB0LA".
Definition tm' := TM_from_str "1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 5.
Time Qed.
End TM2015.


Module TM2016.
Definition tm := TM_from_str "1LB0RA_1LC0LB_0RD1LB_1RA1RE_1RF1RD_1LA---".
Definition tm' := TM_from_str "1RB1RF_1LC---_1LD0RC_1LE0LD_0RF1LD_1RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 1 5.
Time Qed.
End TM2016.


Module TM2017.
Definition tm := TM_from_str "1LB0LD_1RC0LF_1LA1RC_---0RE_1RA1RB_1LC1LE".
Definition tm' := TM_from_str "1RB1RC_1LC0LF_1RE0LD_1LE1LA_1LB1RE_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEFAD") 10 1.
Time Qed.
End TM2017.


Module TM2018.
Definition tm := TM_from_str "1LB1RE_1RC0LB_0LD0RD_1RA1LB_0RA0RF_1RD---".
Definition tm' := TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA1RE_0RD0RF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 1 3.
Time Qed.
End TM2018.


Module TM2019.
Definition tm := TM_from_str "1RB1RE_0LC---_1LD1LC_0RE0LD_1RF0RA_1RC1RF".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 8 6.
Time Qed.
End TM2019.


Module TM2020.
Definition tm := TM_from_str "1RB1LE_1RC1LD_0LB0RC_0LA0LA_1LA0RF_---1RE".
Definition tm' := TM_from_str "1RB1LC_0LA0RB_0LD0LD_1RA1LE_1LD0RF_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 5 4.
Time Qed.
End TM2020.


Module TM2021.
Definition tm := TM_from_str "1RB---_1RC0RA_0LD1LF_1RE1LD_1RE0LC_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1RC0RF_0LD1LA_1RE1LD_1RE0LC_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2021.


Module TM2022.
Definition tm := TM_from_str "1RB0LC_0LA0RE_0LD1LA_1RA1LD_1RF---_1RC0RE".
Definition tm' := TM_from_str "1RB0RF_0LC1LD_1RD1LC_1RE0LB_0LD0RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 7 4.
Time Qed.
End TM2022.


Module TM2023.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD0LF_0RC---".
Definition tm' := TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC0LF_1RA1LC_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 7 4.
Time Qed.
End TM2023.


Module TM2024.
Definition tm := TM_from_str "1RB0RF_1RC---_1LD1RA_0LE0LD_1RE0RF_1RC1RC".
Definition tm' := TM_from_str "1RB1RB_1LC1RE_0LD0LC_1RD0RA_1RF0RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 43 35.
Time Qed.
End TM2024.


Module TM2025.
Definition tm := TM_from_str "1LB---_0LC0RD_1RB1LC_1RE1LB_1LC0RF_0RB1RA".
Definition tm' := TM_from_str "1RB1LD_1LC0RE_1RD1LC_0LC0RA_0RD1RF_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDCABE") 4 7.
Time Qed.
End TM2025.


Module TM2026.
Definition tm := TM_from_str "1RB1LB_0LC1RD_1RD1LC_0RE0LA_0RA1RF_0RC---".
Definition tm' := TM_from_str "1RB1LA_0RC0LD_0RD1RF_1RE1LE_0LA1RB_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 6415 6475.
Time Qed.
End TM2026.


Module TM2027.
Definition tm := TM_from_str "1LB0LF_1LC1LE_1RD0LB_1RB0RC_1LA0RE_1LB---".
Definition tm' := TM_from_str "1RB0RC_1LC1LD_1RA0LB_1LE0RD_1LB0LF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 5 1.
Time Qed.
End TM2027.


Module TM2028.
Definition tm := TM_from_str "1LB0RD_0LC---_1RD0LF_1RE1RF_0LC1LA_0RA1RB".
Definition tm' := TM_from_str "1RB0LD_1RC1RD_0LA1LF_0RF1RE_0LA---_1LE0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEABCD") 1 9.
Time Qed.
End TM2028.


Module TM2029.
Definition tm := TM_from_str "1LB1LA_1RC1RD_0LA1RB_1RB1LE_1RF0LD_---0RE".
Definition tm' := TM_from_str "1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 34849 33945.
Time Qed.
End TM2029.


Module TM2030.
Definition tm := TM_from_str "1RB1RA_1RC0LF_1LD0RE_0RE0LD_0RF---_1RA1LF".
Definition tm' := TM_from_str "1RB0LE_1LC0RD_0RD0LC_0RE---_1RF1LE_1RA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 7 6.
Time Qed.
End TM2030.


Module TM2031.
Definition tm := TM_from_str "1LB1RA_1RC0LC_0LA0RD_1RE---_0RF0RF_0RB1LD".
Definition tm' := TM_from_str "1RB0LB_0LC0RD_1LA1RC_1RE---_0RF0RF_0RA1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 103 106.
Time Qed.
End TM2031.


Module TM2032.
Definition tm := TM_from_str "1RB1RD_0RC0LD_1LD1RA_0LE0RF_1RB0LB_0RB---".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB1RD_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2032.


Module TM2033.
Definition tm := TM_from_str "1RB0RD_1LC0RA_1LE0LD_0RB1LF_1RB0LB_0LC---".
Definition tm' := TM_from_str "1RB0LB_1LC0RE_1LA0LD_0RB1LF_1RB0RD_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2033.


Module TM2034.
Definition tm := TM_from_str "1RB0LC_0RC0LE_1LD0RF_1LE---_0LA0LD_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_0RC0LE_1LD0RA_1LE---_0LF0LD_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2034.


Module TM2035.
Definition tm := TM_from_str "1RB0RF_1LC1LB_0RD0LC_0RB1RE_1RA1RD_1LA---".
Definition tm' := TM_from_str "1RB1RE_1RC0RF_1LD1LC_0RE0LD_0RC1RA_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 6 7.
Time Qed.
End TM2035.


Module TM2036.
Definition tm := TM_from_str "1LB1RD_1LC0LB_0LD0RD_1RE0RF_1RA0RE_0LB---".
Definition tm' := TM_from_str "1RB0RA_1LC1RE_1LD0LC_0LE0RE_1RA0RF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 20 3.
Time Qed.
End TM2036.


Module TM2037.
Definition tm := TM_from_str "1LB0RA_0RC0LC_1LD1RA_1RA1LE_0LC0LF_1LC---".
Definition tm' := TM_from_str "1RB1LE_1LC0RB_0RD0LD_1LA1RB_0LD0LF_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 3 1.
Time Qed.
End TM2037.


Module TM2038.
Definition tm := TM_from_str "1LB---_1RC0LC_1RD0LB_1LC0RE_1RF1RE_1RC1RA".
Definition tm' := TM_from_str "1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCABDE") 5 1.
Time Qed.
End TM2038.


Module TM2039.
Definition tm := TM_from_str "1RB1LC_1RC1RA_1LD0LA_0RE0LD_1RF---_0RB0LB".
Definition tm' := TM_from_str "1RB---_0RC0LC_1RD1RF_1LE0LF_0RA0LE_1RC1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEAB") 8 8.
Time Qed.
End TM2039.


Module TM2040.
Definition tm := TM_from_str "1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC0RF_1RC---".
Definition tm' := TM_from_str "1RB---_1RC0LC_0LD0RF_1RE1LD_0LE1LB_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 21 1.
Time Qed.
End TM2040.


Module TM2041.
Definition tm := TM_from_str "1LB1RA_1RA0LC_---0LD_1RE1LD_1RB0RF_---0RA".
Definition tm' := TM_from_str "1RB0RF_1RC0LD_1LB1RC_---0LE_1RA1LE_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 3 2.
Time Qed.
End TM2041.


Module TM2042.
Definition tm := TM_from_str "1RB---_1RC1LB_1LD1RF_1RB0LE_1LB0LE_1RA0RC".
Definition tm' := TM_from_str "1RB0LD_1RC1LB_1LA1RE_1LB0LD_1RF0RC_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM2042.


Module TM2043.
Definition tm := TM_from_str "1LB1RC_0RA0LD_0RD---_1RE0LF_1RA1RD_1RC0LB".
Definition tm' := TM_from_str "1RB0LF_0RC---_1RD0LA_1RE1RC_1LF1RB_0RE0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 3 1.
Time Qed.
End TM2043.


Module TM2044.
Definition tm := TM_from_str "1LB0RE_1RC1LC_0RA1LD_0LC1LC_---1RF_0LC1RA".
Definition tm' := TM_from_str "1RB1LB_0RC1LD_1LA0RE_0LB1LB_---1RF_0LB1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 21 6.
Time Qed.
End TM2044.


Module TM2045.
Definition tm := TM_from_str "1RB---_1RC0RB_1LD1RC_1LD1LE_1RB1LF_0LA0LD".
Definition tm' := TM_from_str "1RB1LE_1RC0RB_1LD1RC_1LD1LA_0LF0LD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2045.


Module TM2046.
Definition tm := TM_from_str "1LB0RC_1LC0LE_1RD0LF_1RA1RD_0LA1LA_1LE---".
Definition tm' := TM_from_str "1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 120 87.
Time Qed.
End TM2046.


Module TM2047.
Definition tm := TM_from_str "1LB1LF_1RC---_1RD1RC_1RE0RD_0LE0LA_0RD1LE".
Definition tm' := TM_from_str "1RB1RA_1RC0RB_0LC0LD_1LF1LE_0RB1LC_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFABCE") 1 11.
Time Qed.
End TM2047.


Module TM2048.
Definition tm := TM_from_str "1RB1RA_1LC0RD_1RD0LC_0RE0RF_0LB1RA_1RD---".
Definition tm' := TM_from_str "1RB0LA_0RC0RF_0LD1RE_1LA0RB_1RD1RE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDABCF") 1 3.
Time Qed.
End TM2048.


Module TM2049.
Definition tm := TM_from_str "1LB1LE_1RC0RB_1RD0LC_1LA0RD_1LF---_1LC1RB".
Definition tm' := TM_from_str "1RB0LA_1LC0RB_1LF1LD_1LE---_1LA1RF_1RA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 5 1.
Time Qed.
End TM2049.


Module TM2050.
Definition tm := TM_from_str "1LB1LA_1RC0LC_1LD0RB_1RF1RE_---1LB_0LA1RD".
Definition tm' := TM_from_str "1RB1RF_0LC1RA_1LD1LC_1RE0LE_1LA0RD_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEAFB") 66 59.
Time Qed.
End TM2050.


Module TM2051.
Definition tm := TM_from_str "1RB0RF_0LC0RD_1LA1LC_1RF1RE_1RB1LA_---1LB".
Definition tm' := TM_from_str "1RB1LD_0LC0RE_1LD1LC_1RB0RF_1RF1RA_---1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 1.
Time Qed.
End TM2051.


Module TM2052.
Definition tm := TM_from_str "1RB0LE_0RC---_0LD0RD_1RE0LA_0RF0LC_1LC1RA".
Definition tm' := TM_from_str "1RB0LE_0RC0LD_1LD1RE_0LA0RA_1RF0LB_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDABC") 79 113.
Time Qed.
End TM2052.


Module TM2053.
Definition tm := TM_from_str "1RB0RD_0LC1LE_0RD0LB_1RA0RD_1LF0RA_1LB---".
Definition tm' := TM_from_str "1RB0RA_1RC0RA_0LD1LE_0RA0LC_1LF0RB_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 6 1.
Time Qed.
End TM2053.


Module TM2054.
Definition tm := TM_from_str "1RB1LD_1LC0RD_0RB0LC_1LE1LD_0RF---_1RA1RF".
Definition tm' := TM_from_str "1RB1RA_1RC1LE_1LD0RE_0RC0LD_1LF1LE_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 8 9.
Time Qed.
End TM2054.


Module TM2055.
Definition tm := TM_from_str "1LB1RF_0LC1LE_1LD1LA_1RE0RE_0LA0RD_0LD---".
Definition tm' := TM_from_str "1RB0RB_0LC0RA_1LE1RD_0LA---_0LF1LB_1LA1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEFABD") 1 7.
Time Qed.
End TM2055.


Module TM2056.
Definition tm := TM_from_str "1RB0RB_0RC0RF_1LD1RD_1LE1RA_---0LF_1RB0LF".
Definition tm' := TM_from_str "1RB0LA_0RC0RA_1LD1RD_1LE1RF_---0LA_1RB0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2056.


Module TM2057.
Definition tm := TM_from_str "1RB1LC_0RC0LF_1LD1LE_0LA0RB_1RB---_0LD0RA".
Definition tm' := TM_from_str "1RB---_0RC0LF_1LD1LA_0LE0RB_1RB1LC_0LD0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2057.


Module TM2058.
Definition tm := TM_from_str "1RB0RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0LE---".
Definition tm' := TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB0RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2058.


Module TM2059.
Definition tm := TM_from_str "1RB---_1RC0RA_0LD1LF_0RB1LE_1RF0LA_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1RC0RF_0LD1LA_0RB1LE_1RA0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2059.


Module TM2060.
Definition tm := TM_from_str "1LB1LE_1LC1RB_1RD1LA_0RE0RD_0LF0LC_1RA---".
Definition tm' := TM_from_str "1RB1LE_0RC0RB_0LD0LA_1RE---_1LF1LC_1LA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 21 26.
Time Qed.
End TM2060.


Module TM2061.
Definition tm := TM_from_str "1RB---_1RC1LC_1LD1RF_0RA0LE_0LD0RE_1RA1LD".
Definition tm' := TM_from_str "1RB1LB_1LC1RF_0RE0LD_0LC0RD_1RA---_1RE1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 11 2.
Time Qed.
End TM2061.


Module TM2062.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0RD_1RA0RE_1LA0LF_1LE---".
Definition tm' := TM_from_str "1RB0RA_1LC0RD_1RA1LD_1RC0RE_1LC0LF_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 4 5.
Time Qed.
End TM2062.


Module TM2063.
Definition tm := TM_from_str "1LB1RA_1RC1LE_1RD1LC_1LA0RA_1LF0LC_---0LB".
Definition tm' := TM_from_str "1RB1LA_1LC0RC_1LD1RC_1RA1LE_1LF0LA_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 271 286.
Time Qed.
End TM2063.


Module TM2064.
Definition tm := TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_0LF1RC_0RB---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 86 109.
Time Qed.
End TM2064.


Module TM2065.
Definition tm := TM_from_str "1RB---_1LC0RD_1RD0LC_0RE0RC_0LB1RF_1RB1RA".
Definition tm' := TM_from_str "1RB0LA_0RC0RA_0LD1RE_1LA0RB_1RD1RF_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDABCE") 1 3.
Time Qed.
End TM2065.


Module TM2066.
Definition tm := TM_from_str "1RB0RA_0LC0LF_1RE0LD_0RE0LF_1RA---_1RC1LC".
Definition tm' := TM_from_str "1RB---_1RC0RB_0LD0LF_1RA0LE_0RA0LF_1RD1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 5 1.
Time Qed.
End TM2066.


Module TM2067.
Definition tm := TM_from_str "1RB---_1LC0RE_1LE0LD_0LC0RE_0RF0LF_1RB1LA".
Definition tm' := TM_from_str "1RB1LF_1LC0RE_1LE0LD_0LC0RE_0RA0LA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2067.


Module TM2068.
Definition tm := TM_from_str "1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LE---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 5 6.
Time Qed.
End TM2068.


Module TM2069.
Definition tm := TM_from_str "1RB1LA_1RC1RB_1RD---_1RE1LA_1LF0RB_0RE0LF".
Definition tm' := TM_from_str "1RB1LF_1LC0RD_0RB0LC_1RE1RD_1RA---_1RD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 1 8.
Time Qed.
End TM2069.


Module TM2070.
Definition tm := TM_from_str "1LB1LA_0LC0RD_1RD0LF_0RE0RC_1RB1RD_1LA---".
Definition tm' := TM_from_str "1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDABCE") 8 13.
Time Qed.
End TM2070.


Module TM2071.
Definition tm := TM_from_str "1RB0RB_1LC0RA_0RF0LD_1LE1LD_0LC1RE_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_0RA0LD_1LE1LD_0LC1RE_1RB0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2071.


Module TM2072.
Definition tm := TM_from_str "1RB0LD_0RC1RA_1RD0RF_1LA1LE_1RB0LE_1RB---".
Definition tm' := TM_from_str "1RB---_0RC1RE_1RD0RA_1LE1LF_1RB0LD_1RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM2072.


Module TM2073.
Definition tm := TM_from_str "1LB0RD_1RC0LD_1RA0RC_1RC1LE_0RE0LF_1LB---".
Definition tm' := TM_from_str "1RB0RA_1LC0RD_1RA0LD_1RA1LE_0RE0LF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 165 87.
Time Qed.
End TM2073.


Module TM2074.
Definition tm := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_0RB---".
Definition tm' := TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 776 1070.
Time Qed.
End TM2074.


Module TM2075.
Definition tm := TM_from_str "1LB0LF_0RC1RE_1RE1RD_1LE1RD_1LA0RB_1LA---".
Definition tm' := TM_from_str "1RB1RF_1LC0RE_1LE0LD_1LC---_0RA1RB_1LB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEAFBD") 6 1.
Time Qed.
End TM2075.


Module TM2076.
Definition tm := TM_from_str "1RB0LE_0RC0LD_1LD1RE_0LA0RF_1RF0LB_0RD---".
Definition tm' := TM_from_str "1RB0LE_0RC---_0LD0RB_1RE0LA_0RF0LC_1LC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFCAB") 117 83.
Time Qed.
End TM2076.


Module TM2077.
Definition tm := TM_from_str "1RB1LF_0LC1LC_0LD1RC_1LA0RE_1RD0RE_0LB---".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1RE1LD_0LE---_0LF1LF_0LB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEFBAD") 6 1.
Time Qed.
End TM2077.


Module TM2078.
Definition tm := TM_from_str "1RB0LE_1LC0RD_1LA1LB_1RB1RA_0LF0RD_1LC---".
Definition tm' := TM_from_str "1RB1RD_1LC0RA_1LD1LB_1RB0LE_0LF0RA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM2078.


Module TM2079.
Definition tm := TM_from_str "1RB---_1RC0RC_1LD1RE_1RB1LE_1RA0LF_0RD0LE".
Definition tm' := TM_from_str "1RB0LF_1RC---_1RD0RD_1LE1RA_1RC1LA_0RE0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 1 18.
Time Qed.
End TM2079.


Module TM2080.
Definition tm := TM_from_str "1LB1LC_0RC0LB_1RD1LC_0RE1LD_1RA1RF_---1RE".
Definition tm' := TM_from_str "1RB1RF_1LC1LD_0RD0LC_1RE1LD_0RA1LE_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 3 4.
Time Qed.
End TM2080.


Module TM2081.
Definition tm := TM_from_str "1LB0LA_1LC0RE_0LD0RA_1LE0LA_1RB1LF_0RB---".
Definition tm' := TM_from_str "1RB1LF_1LC0RA_0LE0RD_1LB0LD_1LA0LD_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 5.
Time Qed.
End TM2081.


Module TM2082.
Definition tm := TM_from_str "1LB0RF_1LC1LC_1RD0LD_1RE0LC_0RA---_0RC1RA".
Definition tm' := TM_from_str "1RB0LB_1RC0LA_0RD---_1LE0RF_1LA1LA_0RA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 68 95.
Time Qed.
End TM2082.


Module TM2083.
Definition tm := TM_from_str "1LB---_1RC0RB_1LF1LD_0LA0RE_1LC0LF_1RB1LE".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_0LF0RD_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCEDA") 6 1.
Time Qed.
End TM2083.


Module TM2084.
Definition tm := TM_from_str "1RB0LD_1RC0RF_0LA1RA_0RA1LE_1RC1LF_---0LD".
Definition tm' := TM_from_str "1RB1LF_0LC1RC_1RE0LD_0RC1LA_1RB0RF_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEBDAF") 1 5.
Time Qed.
End TM2084.


Module TM2085.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RD1LB_0LA1RE_0RA1RF_0LD---".
Definition tm' := TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA0RB_0RD1RF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 3 4.
Time Qed.
End TM2085.


Module TM2086.
Definition tm := TM_from_str "1LB0RE_1RC0LC_0RE0LD_0RA0LB_1RF---_1LC0RD".
Definition tm' := TM_from_str "1RB0LB_0RC0LE_1RD---_1LB0RE_0RF0LA_1LA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABECD") 5 1.
Time Qed.
End TM2086.


Module TM2087.
Definition tm := TM_from_str "1LB0RD_0RC0LB_1LB1RA_1LC1RE_1RD0LF_---1LE".
Definition tm' := TM_from_str "1RB0LF_1LC1RA_1LE1RD_1LE0RB_0RC0LE_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECBAF") 8 2.
Time Qed.
End TM2087.


Module TM2088.
Definition tm := TM_from_str "1LB1RC_1LC0LE_1RD0RE_0LE1RA_0RA0RF_0LA---".
Definition tm' := TM_from_str "1RB0RC_0LC1RE_0RE0RD_0LE---_1LF1RA_1LA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 1 5.
Time Qed.
End TM2088.


Module TM2089.
Definition tm := TM_from_str "1LB0RF_1RC0LC_0LD0RC_0LE---_1LA1LE_1RD1RF".
Definition tm' := TM_from_str "1RB1RA_0LC---_1LD1LC_1LE0RA_1RF0LF_0LB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 4 1.
Time Qed.
End TM2089.


Module TM2090.
Definition tm := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA0LE".
Definition tm' := TM_from_str "1RB0LF_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 4 8.
Time Qed.
End TM2090.


Module TM2091.
Definition tm := TM_from_str "1LB1RE_1RC1LA_1LD0RC_0LA1RE_0RF0RD_---0LA".
Definition tm' := TM_from_str "1RB1LE_1LC0RB_0LE1RD_0RF0RC_1LA1RD_---0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 8 5.
Time Qed.
End TM2091.


Module TM2092.
Definition tm := TM_from_str "1LB1LC_0LC0LA_0LD0RC_1RE0LF_1RA---_0LA1LE".
Definition tm' := TM_from_str "1RB0LF_1RC---_1LD1LE_0LE0LC_0LA0RE_0LC1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 1622 1848.
Time Qed.
End TM2092.


Module TM2093.
Definition tm := TM_from_str "1LB0LB_0RC0LA_1RE0LD_0RC---_0RF1RB_1RA1RC".
Definition tm' := TM_from_str "1RB0LF_0RC1RE_1RD1RA_1LE0LE_0RA0LD_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 5 1.
Time Qed.
End TM2093.


Module TM2094.
Definition tm := TM_from_str "1RB1LC_1LC---_1LD1RC_1RF1LE_1LB0LD_1RA0RF".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_1RD1LE_1LE---_1LA1RE_1LD0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEAFB") 12 5.
Time Qed.
End TM2094.


Module TM2095.
Definition tm := TM_from_str "1LB1RA_1LC0LB_0RC1RD_0RE0LA_1RA0RF_1RE---".
Definition tm' := TM_from_str "1RB0RF_1LC1RB_1LD0LC_0RD1RE_0RA0LB_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 6 1.
Time Qed.
End TM2095.


Module TM2096.
Definition tm := TM_from_str "1RB1RD_1RC0RA_1LD0RB_1RC1LE_0LC0LF_0LE---".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_1RB1LD_0LB0LF_1RA1RC_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 127 99.
Time Qed.
End TM2096.


Module TM2097.
Definition tm := TM_from_str "1LB1RE_0RC0LE_1RA0LD_0LB0LA_0LF---_1LD0RB".
Definition tm' := TM_from_str "1RB0LF_1LC1RD_0RA0LD_0LE---_1LF0RC_0LC0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAFDE") 6 1.
Time Qed.
End TM2097.


Module TM2098.
Definition tm := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LB_0LC1LD_0LD1LB".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0RF_0LA---_0LB1LD_0LA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 22 34.
Time Qed.
End TM2098.


Module TM2099.
Definition tm := TM_from_str "1LB1LF_1RC1RB_1RD0RC_0LE0LA_---0LA_0RC1LE".
Definition tm' := TM_from_str "1RB1RA_1RC0RB_0LD0LE_---0LE_1LA1LF_0RB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 11.
Time Qed.
End TM2099.


Module TM2100.
Definition tm := TM_from_str "1LB0RE_1LC0LA_1LD1LE_1RB0LC_1RA1LF_0RA---".
Definition tm' := TM_from_str "1RB0LC_1LC0LE_1LA1LD_1RE1LF_1LB0RD_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 6 3.
Time Qed.
End TM2100.


Module TM2101.
Definition tm := TM_from_str "1RB0RF_1LC0RE_1RB0LD_1LC0LD_1RA1RE_0RB---".
Definition tm' := TM_from_str "1RB0LC_1LA0RD_1LA0LC_1RE1RD_1RB0RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM2101.


Module TM2102.
Definition tm := TM_from_str "1LB1LA_1RC1LF_0LD0RC_1LE1RD_0LA1RE_0RD---".
Definition tm' := TM_from_str "1RB1LF_0LC0RB_1LD1RC_0LE1RD_1LA1LE_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 4 3.
Time Qed.
End TM2102.


Module TM2103.
Definition tm := TM_from_str "1RB---_1RC0RF_1LD0RB_0LE0LC_0LF0LC_1RB1LA".
Definition tm' := TM_from_str "1RB1LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2103.


Module TM2104.
Definition tm := TM_from_str "1LB1LE_1LC0RC_0RD0LA_1RB1RE_0RC1RF_0LD---".
Definition tm' := TM_from_str "1RB1RE_1LC0RC_0RA0LD_1LB1LE_0RC1RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 19.
Time Qed.
End TM2104.


Module TM2105.
Definition tm := TM_from_str "1RB0LC_0LA1RB_1RD1LB_0RE---_0RF0RD_1LB1RC".
Definition tm' := TM_from_str "1RB1LE_0RC---_0RD0RB_1LE1RA_0LF1RE_1RE0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEABCD") 4 1.
Time Qed.
End TM2105.


Module TM2106.
Definition tm := TM_from_str "1LB1RD_0LC0LE_1RD0LC_1RA0RD_---1LF_1LC1LA".
Definition tm' := TM_from_str "1RB0LA_1RC0RB_1LD1RB_0LA0LE_---1LF_1LA1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 14 10.
Time Qed.
End TM2106.


Module TM2107.
Definition tm := TM_from_str "1RB0RD_1RC1RA_1LD0RB_1RF0LE_1LA1LD_---1RB".
Definition tm' := TM_from_str "1RB1RE_1LC0RA_1RF0LD_1LE1LC_1RA0RC_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 30 16.
Time Qed.
End TM2107.


Module TM2108.
Definition tm := TM_from_str "1RB---_1RC0RA_0LD1RB_1RA0LE_0RA0LF_1RD1LD".
Definition tm' := TM_from_str "1RB1LB_1RC0LF_1RD---_1RE0RC_0LB1RD_0RC0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBFA") 6 1.
Time Qed.
End TM2108.


Module TM2109.
Definition tm := TM_from_str "1RB1RE_1RC0RD_1LB0RA_0RC1LE_0LF---_1LB0LC".
Definition tm' := TM_from_str "1RB0RC_1LA0RF_0RB1LD_0LE---_1LA0LB_1RA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 74 160.
Time Qed.
End TM2109.


Module TM2110.
Definition tm := TM_from_str "1LB0RF_1RC1LE_1RD0RC_0LB0RA_0LD1LB_---0RB".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_0LA0RE_0LC1LA_1LA0RF_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 9 5.
Time Qed.
End TM2110.


Module TM2111.
Definition tm := TM_from_str "1RB1RF_1RC0LC_0LD0RA_1RE1LD_0LE1LB_0LC---".
Definition tm' := TM_from_str "1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC1RF_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDABF") 1 21.
Time Qed.
End TM2111.


Module TM2112.
Definition tm := TM_from_str "1LB0RE_0RC0RA_1RE0LD_1RB0LD_1LF1RB_---0LC".
Definition tm' := TM_from_str "1RB0LA_0RC0RF_1RD0LA_1LE1RB_---0LC_1LB0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 4 1.
Time Qed.
End TM2112.


Module TM2113.
Definition tm := TM_from_str "1LB1RA_0RA0LC_1LD1RB_1RA0LE_0LB1LF_1RA---".
Definition tm' := TM_from_str "1RB0LE_1LC1RB_0RB0LD_1LA1RC_0LC1LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 3 1.
Time Qed.
End TM2113.


Module TM2114.
Definition tm := TM_from_str "1RB1RF_0LC0RB_1RA0LD_1RC0LE_---1LF_0RA0LD".
Definition tm' := TM_from_str "1RB0LE_1RC0LA_1RD1RF_0LB0RD_---1LF_0RC0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBAEF") 4 1.
Time Qed.
End TM2114.


Module TM2115.
Definition tm := TM_from_str "1LB1RD_0LC1LB_1LD0RF_1RA0RE_---1LB_1RC0RB".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEBCDA") 1 4.
Time Qed.
End TM2115.


Module TM2116.
Definition tm := TM_from_str "1RB0RD_0RC1RB_1LD1RF_1LE0RE_1RB0LE_---1RA".
Definition tm' := TM_from_str "1RB0LA_0RC1RB_1LD1RE_1LA0RA_---1RF_1RB0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2116.


Module TM2117.
Definition tm := TM_from_str "1RB0LE_1RC0LD_1RD0LB_0LA0RC_0RD1LF_---1LA".
Definition tm' := TM_from_str "1RB0LE_0LC0RA_1RE0LD_0RB1LF_1RA0LB_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEABDF") 1 6.
Time Qed.
End TM2117.


Module TM2118.
Definition tm := TM_from_str "1RB0LE_1RC1RB_0RD0RA_0LE---_1LF1RF_0RE1LA".
Definition tm' := TM_from_str "1RB1RA_0RC0RF_0LD---_1LE1RE_0RD1LF_1RA0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 58 41.
Time Qed.
End TM2118.


Module TM2119.
Definition tm := TM_from_str "1RB0RA_0LC0LE_---0LD_1RE1LC_1RA1LF_1LD1LD".
Definition tm' := TM_from_str "1RB1LE_1RC1LF_1RD0RC_0LE0LB_---0LA_1LA1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM2119.


Module TM2120.
Definition tm := TM_from_str "1LB0RF_0RC0LD_1LE1RA_1LC---_1RA0LF_1LA0RA".
Definition tm' := TM_from_str "1RB0LF_1LC0RF_0RE0LD_1LE---_1LA1RB_1LB0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEDAF") 3 1.
Time Qed.
End TM2120.


Module TM2121.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC0LF_0RD---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RE_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM2121.


Module TM2122.
Definition tm := TM_from_str "1RB0LD_1RC0RA_0RD0RB_1LE1RF_1LB0LE_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RF_0RD0RB_1LE1RA_1LB0LE_1RB0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2122.


Module TM2123.
Definition tm := TM_from_str "1RB---_1LC1RE_0RC0LD_0RA0LF_1RA1LC_0LC0RB".
Definition tm' := TM_from_str "1RB1LD_1RC---_1LD1RA_0RD0LE_0RB0LF_0LD0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 1 13.
Time Qed.
End TM2123.


Module TM2124.
Definition tm := TM_from_str "1RB1RF_1LC---_1RD1RC_1LE1LD_0RF0LE_1RC0RA".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 3 5.
Time Qed.
End TM2124.


Module TM2125.
Definition tm := TM_from_str "1LB0LE_1RC1LF_1LA0RD_0RC0LE_1RD---_0LC0LD".
Definition tm' := TM_from_str "1RB1LF_1LC0RE_1LA0LD_1RE---_0RB0LD_0LB0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 20 21.
Time Qed.
End TM2125.


Module TM2126.
Definition tm := TM_from_str "1LB0RE_0RC0LB_1RA0LD_1RE1LF_1RC0LF_0LC---".
Definition tm' := TM_from_str "1RB1LF_1RC0LF_1RD0LA_1LE0RB_0RC0LE_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECABF") 4 1.
Time Qed.
End TM2126.


Module TM2127.
Definition tm := TM_from_str "1RB1RC_0LC0LE_0RA0LD_1RE0LF_1RA1LC_---1LC".
Definition tm' := TM_from_str "1RB0LF_1RC1LE_1RD1RE_0LE0LB_0RC0LA_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM2127.


Module TM2128.
Definition tm := TM_from_str "1LB0RC_1LC1LB_0RD0LF_1RA0RE_---1RC_1RD0LA".
Definition tm' := TM_from_str "1RB0RE_1LC0RD_1LD1LC_0RA0LF_---1RD_1RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 1 10.
Time Qed.
End TM2128.


Module TM2129.
Definition tm := TM_from_str "1RB0LF_1RC0RB_1LD0LE_0LA0LC_1LC0RA_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RB_1LD0LE_0LF0LC_1LC0RF_1RB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2129.


Module TM2130.
Definition tm := TM_from_str "1LB1RF_0LC0LB_1RD0RA_1LE---_1RA1LE_1RE1RC".
Definition tm' := TM_from_str "1RB1RE_1RC1LB_1LD1RA_0LE0LD_1RF0RC_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 22 17.
Time Qed.
End TM2130.


Module TM2131.
Definition tm := TM_from_str "1RB0RA_1LC1RE_1RA1LD_0LB0LB_0RD0RF_1RA---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RE_0LC0LC_0RD0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 4 5.
Time Qed.
End TM2131.


Module TM2132.
Definition tm := TM_from_str "1LB0RA_0RC1LE_1LF0LD_1RA1LC_0RF---_1LD1RF".
Definition tm' := TM_from_str "1RB1LF_1LC0RB_0RF1LD_0RE---_1LA1RE_1LE0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFADE") 4 1.
Time Qed.
End TM2132.


Module TM2133.
Definition tm := TM_from_str "1RB1RD_1LC1LB_0RD0LC_1RE1RA_0RF1RA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1LB_0RD0LC_1RE1RF_0RA1RF_1RB1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2133.


Module TM2134.
Definition tm := TM_from_str "1LB0RF_1LC0LA_1RD0LB_0RE0RC_0RA1RE_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0LF_1RD0LB_0RE0RC_0RF1RE_1LB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 5 1.
Time Qed.
End TM2134.


Module TM2135.
Definition tm := TM_from_str "1LB---_1RC1LF_1LD1LC_0RE1LF_0RF1RE_1LA0LD".
Definition tm' := TM_from_str "1RB1LD_1LC1LB_0RF1LD_1LE0LC_1LA---_0RD1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCFD") 15 30.
Time Qed.
End TM2135.


Module TM2136.
Definition tm := TM_from_str "1LB1LB_0LC1LC_1LD1RA_1RE1RF_0LA0RE_---1RD".
Definition tm' := TM_from_str "1RB1RF_0LC0RB_1LD1LD_0LE1LE_1LA1RC_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 1 3.
Time Qed.
End TM2136.


Module TM2137.
Definition tm := TM_from_str "1RB---_1RC0RF_1LD0RF_1LE0LE_1RB0LD_1RB1RA".
Definition tm' := TM_from_str "1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2137.


Module TM2138.
Definition tm := TM_from_str "1RB0LE_1LC0RC_1LD1RC_1LF1LA_1RB1LE_---1LD".
Definition tm' := TM_from_str "1RB1LA_1LC0RC_1LD1RC_1LF1LE_1RB0LA_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2138.


Module TM2139.
Definition tm := TM_from_str "1RB0RA_1LC1RE_1RA1LD_0LB1LF_0RD0RC_0RE---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RF_0LC1LE_0RF---_0RD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADFE") 2 7.
Time Qed.
End TM2139.


Module TM2140.
Definition tm := TM_from_str "1LB0LF_1RC1LB_1RF1RD_0RE0RA_0RC---_1LA0RC".
Definition tm' := TM_from_str "1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABEFC") 5387 5810.
Time Qed.
End TM2140.


Module TM2141.
Definition tm := TM_from_str "1LB0LB_0RC1LF_0LA1RD_0RE1RC_1RB---_0LD0LE".
Definition tm' := TM_from_str "1RB---_0RC1LE_0LD1RF_1LB0LB_0LF0LA_0RA1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCFAE") 999 935.
Time Qed.
End TM2141.


Module TM2142.
Definition tm := TM_from_str "1LB---_0LC0LC_0LD0RA_1LE0RE_0RF0LA_1RD1LF".
Definition tm' := TM_from_str "1RB1LA_1LC0RC_0RA0LD_1LE---_0LF0LF_0LB0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 363 346.
Time Qed.
End TM2142.


Module TM2143.
Definition tm := TM_from_str "1RB0RA_0RC0RA_0LD0LF_1LE0LB_1RB1LC_1LD---".
Definition tm' := TM_from_str "1RB1LC_0RC0RE_0LD0LF_1LA0LB_1RB0RE_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2143.


Module TM2144.
Definition tm := TM_from_str "1LB1LD_0RC1LA_0LA0RD_1RE0LF_1RB0RE_0LC---".
Definition tm' := TM_from_str "1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDABF") 4 1.
Time Qed.
End TM2144.


Module TM2145.
Definition tm := TM_from_str "1RB1LD_1RC---_1LD1RA_0RC0LE_0LF0RC_1RF0LD".
Definition tm' := TM_from_str "1RB---_1LC1RF_0RB0LD_0LE0RB_1RE0LC_1RA1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 9 2.
Time Qed.
End TM2145.


Module TM2146.
Definition tm := TM_from_str "1RB0LA_0RC0LD_1LD1RD_1LA1RE_1RB0RF_---0RA".
Definition tm' := TM_from_str "1RB0RF_0RC0LD_1LD1RD_1LE1RA_1RB0LE_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2146.


Module TM2147.
Definition tm := TM_from_str "1LB0RA_0LC1RA_0RD1LE_1RA0LB_0LD1LF_0LB---".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LD1RB_0RA1LE_0LA1LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 4 3.
Time Qed.
End TM2147.


Module TM2148.
Definition tm := TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RC---".
Definition tm' := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 449 430.
Time Qed.
End TM2148.


Module TM2149.
Definition tm := TM_from_str "1RB1LE_1RC0RF_1LD0RA_1RB0LA_0RE0LC_1RC---".
Definition tm' := TM_from_str "1RB0LD_1RC0RF_1LA0RD_1RB1LE_0RE0LC_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM2149.


Module TM2150.
Definition tm := TM_from_str "1RB1LA_1LA0RC_---0RD_1LE1RD_0LF0LF_1RB0LA".
Definition tm' := TM_from_str "1RB0LC_1LC0RD_1RB1LC_---0RE_1LF1RE_0LA0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM2150.


Module TM2151.
Definition tm := TM_from_str "1LB0LD_1LC0LA_1RD0RF_0LF0RE_1RD1RE_---1LB".
Definition tm' := TM_from_str "1RB0RC_0LC0RE_---1LD_1LA0LF_1RB1RE_1LD0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDABEC") 1 3.
Time Qed.
End TM2151.


Module TM2152.
Definition tm := TM_from_str "1LB0LF_1RC1LF_---1RD_0RE0RB_1LF0RD_1RA1LA".
Definition tm' := TM_from_str "1RB1LB_1LC0LA_1RD1LA_---1RE_0RF0RC_1LA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 9 5.
Time Qed.
End TM2152.


Module TM2153.
Definition tm := TM_from_str "1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD".
Definition tm' := TM_from_str "1RB1LB_1RC---_1LD1LF_1LE0LD_0LA1RF_1LC0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 315075 337226.
Time Qed.
End TM2153.


Module TM2154.
Definition tm := TM_from_str "1LB1RE_1RC1LA_1LD0RC_0LA1RE_0RF0RD_---0LC".
Definition tm' := TM_from_str "1RB1LE_1LC0RB_0LE1RD_0RF0RC_1LA1RD_---0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 8 1.
Time Qed.
End TM2154.


Module TM2155.
Definition tm := TM_from_str "1LB0LA_1RC1LF_0LD0RD_0RB1LE_0LA---_1RC0LD".
Definition tm' := TM_from_str "1RB0LC_0LC0RC_0RF1LD_0LE---_1LF0LE_1RB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 54 38.
Time Qed.
End TM2155.


Module TM2156.
Definition tm := TM_from_str "1LB1LE_1RC---_1LF0RD_1RE1RD_1LA0RF_1RE0LC".
Definition tm' := TM_from_str "1RB---_1LC0RF_1RD0LB_1LE0RC_1LA1LD_1RD1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABFDC") 118 133.
Time Qed.
End TM2156.


Module TM2157.
Definition tm := TM_from_str "1LB0RB_0LC0RE_1LD0RA_1RB0LE_0RA1LF_0LA---".
Definition tm' := TM_from_str "1RB0LE_0LC0RE_1LA0RD_1LB0RB_0RD1LF_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 4.
Time Qed.
End TM2157.


Module TM2158.
Definition tm := TM_from_str "1LB0RB_0LC1RB_1RD0LE_1RA---_0RF1LF_1RA1LC".
Definition tm' := TM_from_str "1RB---_1LC0RC_0LD1RC_1RA0LE_0RF1LF_1RB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 4 35.
Time Qed.
End TM2158.


Module TM2159.
Definition tm := TM_from_str "1RB---_0RC0RC_0RD1LA_1RE0LE_0LF0RA_1LD1RF".
Definition tm' := TM_from_str "1RB0LB_0LC0RD_1LA1RC_1RE---_0RF0RF_0RA1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 363 349.
Time Qed.
End TM2159.


Module TM2160.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1LB_0RB0RF_0LC---".
Definition tm' := TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RB_0RD0RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 31 21.
Time Qed.
End TM2160.


Module TM2161.
Definition tm := TM_from_str "1LB0LE_1LC---_1RD1LA_1LE0RD_1RF1LC_0RA1RF".
Definition tm' := TM_from_str "1RB1LE_1LC0RB_1RD1LA_0RE1RD_1LF0LC_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 2 3.
Time Qed.
End TM2161.


Module TM2162.
Definition tm := TM_from_str "1LB---_1LC1RF_0LD0RE_1RE0LE_0RB1RA_0RC0LD".
Definition tm' := TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA0RB_0RD0LA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 8 1.
Time Qed.
End TM2162.


Module TM2163.
Definition tm := TM_from_str "1RB1RE_1RC0LF_1LD1LC_---0RA_1LB1RA_1RF0LA".
Definition tm' := TM_from_str "1RB0LF_1LC1LB_---0RD_1RA1RE_1LA1RD_1RF0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 74 56.
Time Qed.
End TM2163.


Module TM2164.
Definition tm := TM_from_str "1RB0RF_1RC1RF_1LD1RC_---0LE_1LA0LE_0RA0LC".
Definition tm' := TM_from_str "1RB1RF_1LC1RB_---0LD_1LE0LD_1RA0RF_0RE0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 177 133.
Time Qed.
End TM2164.


Module TM2165.
Definition tm := TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RB0RE_0RB0RF_---0LA".
Definition tm' := TM_from_str "1RB0RE_0RC1RA_1LC0LD_1RB1LD_0RB0RF_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM2165.


Module TM2166.
Definition tm := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0RD---".
Definition tm' := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 606 370.
Time Qed.
End TM2166.


Module TM2167.
Definition tm := TM_from_str "1RB---_1LC0RD_1RD0LC_0RE0RC_0LB1RF_0LF1RA".
Definition tm' := TM_from_str "1RB0LA_0RC0RA_0LD1RE_1LA0RB_0LE1RF_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDABCE") 1 3.
Time Qed.
End TM2167.


Module TM2168.
Definition tm := TM_from_str "1LB0RF_1RC0LA_1RE0RD_1RE---_1RA1RC_1LF1RA".
Definition tm' := TM_from_str "1RB0LD_1RC0RF_1RD1RB_1LA0RE_1LE1RD_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABFCE") 15 16.
Time Qed.
End TM2168.


Module TM2169.
Definition tm := TM_from_str "1RB0RA_0LC0LE_1RD1LB_1RA---_0RB1LF_1LF1LC".
Definition tm' := TM_from_str "1RB---_1RC0RB_0LD0LE_1RA1LC_0RC1LF_1LF1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 3 6.
Time Qed.
End TM2169.


Module TM2170.
Definition tm := TM_from_str "1RB---_1RC0RD_1LD1RF_0LF1LE_0RE0LC_0RB0RA".
Definition tm' := TM_from_str "1RB0RC_1LC1RE_0LE1LD_0RD0LB_0RA0RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 864 828.
Time Qed.
End TM2170.


Module TM2171.
Definition tm := TM_from_str "1LB1LF_0RC0LA_1RA0RD_0RE0RF_1RB0LA_1RD---".
Definition tm' := TM_from_str "1RB0RD_1LC1LF_0RA0LB_0RE0RF_1RC0LB_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 1 9.
Time Qed.
End TM2171.


Module TM2172.
Definition tm := TM_from_str "1RB1RA_1RC0RB_1LD1RD_---0LE_0LF0LF_1LA1LF".
Definition tm' := TM_from_str "1RB0RA_1LC1RC_---0LD_0LE0LE_1LF1LE_1RA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 5 4.
Time Qed.
End TM2172.


Module TM2173.
Definition tm := TM_from_str "1LB1LA_1RC0LA_1LE1RD_1RE0RD_1LF0RB_---1LE".
Definition tm' := TM_from_str "1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 1 5.
Time Qed.
End TM2173.


Module TM2174.
Definition tm := TM_from_str "1RB1LC_0LA0RB_0LD1RD_1LE1LD_1RB1RF_---1RE".
Definition tm' := TM_from_str "1RB1RF_0LC0RB_1RB1LD_0LE1RE_1LA1LE_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM2174.


Module TM2175.
Definition tm := TM_from_str "1RB1RB_1RC1RF_1LD0RA_1LA1LE_1RA0LD_1RE---".
Definition tm' := TM_from_str "1RB---_1RC0LF_1RD1RD_1RE1RA_1LF0RC_1LC1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 103 111.
Time Qed.
End TM2175.


Module TM2176.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_0LD---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC0RF_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM2176.


Module TM2177.
Definition tm := TM_from_str "1RB0RC_1LC0RA_1RB0RD_0LB1LE_0LF---_1LD0LF".
Definition tm' := TM_from_str "1RB0RC_1LA0RF_0LB1LD_0LE---_1LC0LE_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBACDE") 1 1.
Time Qed.
End TM2177.


Module TM2178.
Definition tm := TM_from_str "1RB---_1RC0LF_1LD1LC_0RE0LD_1RB0RF_1RA1RE".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2178.


Module TM2179.
Definition tm := TM_from_str "1RB0RB_1LC1RE_1LD1LC_1RB0RF_1RD1RA_---0LC".
Definition tm' := TM_from_str "1RB0RF_1LC1RD_1LA1LC_1RA1RE_1RB0RB_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM2179.


Module TM2180.
Definition tm := TM_from_str "1LB1RE_0LC0RC_1RD1LF_0RA---_0RA0LB_0LE0LD".
Definition tm' := TM_from_str "1RB1LE_0RC---_1LD1RF_0LA0RA_0LF0LB_0RC0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 19 31.
Time Qed.
End TM2180.


Module TM2181.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LA_0RB1RF_1RB---".
Definition tm' := TM_from_str "1RB---_0LC0RD_1RD1LB_0RE0LE_1LB1RF_0RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 3.
Time Qed.
End TM2181.


Module TM2182.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC0LF_0RB---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RE_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM2182.


Module TM2183.
Definition tm := TM_from_str "1LB0LF_1RC1LF_0LD0RC_0RB1LE_1RD0LA_1LA---".
Definition tm' := TM_from_str "1RB0LE_0RC1LA_1RD1LF_0LB0RD_1LC0LF_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDBAF") 4 1.
Time Qed.
End TM2183.


Module TM2184.
Definition tm := TM_from_str "1LB0LE_1RC1LA_1RD0RC_1RA0RA_1LA1LF_1RB---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1RD0RD_1LA0LE_1LD1LF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 9 9.
Time Qed.
End TM2184.


Module TM2185.
Definition tm := TM_from_str "1RB1RC_0LC0RD_1RE1LD_0LB1RB_0RF---_0RA0RE".
Definition tm' := TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0RF_0LE1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 40 21.
Time Qed.
End TM2185.


Module TM2186.
Definition tm := TM_from_str "1LB1RE_1RC1LF_0LD0RB_0LF0RE_0RC---_0LA1LD".
Definition tm' := TM_from_str "1RB1LE_0LC0RA_0LE0RD_0RB---_0LF1LC_1LA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 1 8.
Time Qed.
End TM2186.


Module TM2187.
Definition tm := TM_from_str "1RB0LC_1LC1LB_---1LD_0RE1RA_1RB1RF_0RA1RE".
Definition tm' := TM_from_str "1RB1RE_1LC1LB_---1LD_0RA1RF_0RF1RA_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2187.


Module TM2188.
Definition tm := TM_from_str "1LB1RA_0LC0LA_0RD0RF_1RE0RB_0LA1RC_1RD---".
Definition tm' := TM_from_str "1RB---_1RC0RE_0LD1RF_1LE1RD_0LF0LD_0RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 3039 2988.
Time Qed.
End TM2188.


Module TM2189.
Definition tm := TM_from_str "1RB1LF_1LC0RD_0RD0LC_0RE---_1RA1RE_1RE1LF".
Definition tm' := TM_from_str "1RB1LA_1RC1RB_1RD1LA_1LE0RF_0RF0LE_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 6 1.
Time Qed.
End TM2189.


Module TM2190.
Definition tm := TM_from_str "1RB0RA_1LC0LE_1LF1LD_1RB0LC_---1RD_1RA1LB".
Definition tm' := TM_from_str "1RB0LC_1LC0LD_1LE1LA_---1RA_1RF1LB_1RB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM2190.


Module TM2191.
Definition tm := TM_from_str "1RB1LC_1LA1RD_0LD---_0LE1LE_0LB0RF_1RB1RD".
Definition tm' := TM_from_str "1RB1RE_1LC1RE_1RB1LD_0LE---_0LF1LF_0LB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM2191.


Module TM2192.
Definition tm := TM_from_str "1RB---_0RC0RE_1RD1RA_1LE0LD_1RB0LF_1LD0RA".
Definition tm' := TM_from_str "1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2192.


Module TM2193.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LA_0RB1RF_0RA---".
Definition tm' := TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LA0RB_0RD1RF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 31 21.
Time Qed.
End TM2193.


Module TM2194.
Definition tm := TM_from_str "1RB1LD_1RC1LB_1LA1RF_1RB1RE_---0LA_1RD0RC".
Definition tm' := TM_from_str "1RB1RE_1RC1LB_1LD1RF_1RB1LA_---0LD_1RA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM2194.


Module TM2195.
Definition tm := TM_from_str "1LB0RD_0RC---_0LF1LD_0LE0RB_1RF1LC_0RA0LD".
Definition tm' := TM_from_str "1RB1LE_0RC0LF_1LD0RF_0RE---_0LB1LF_0LA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 29 41.
Time Qed.
End TM2195.


Module TM2196.
Definition tm := TM_from_str "1LB---_0RC1LE_0LE1RD_1RA0RC_1RD1LF_1LB0LC".
Definition tm' := TM_from_str "1RB1LE_1RC0RF_1LD---_0RF1LA_1LD0LF_0LA1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFBAE") 3 1.
Time Qed.
End TM2196.


Module TM2197.
Definition tm := TM_from_str "1RB0LA_1LC0RD_---1LA_---1RE_1RF1LB_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1LC0RE_---1LD_1RB0LD_---1RF_1RA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM2197.


Module TM2198.
Definition tm := TM_from_str "1RB1LC_1LA0RE_1LD0LF_0LB0LC_1RB1LA_---1LD".
Definition tm' := TM_from_str "1RB1LC_1LC0RA_1RB1LD_1LE0LF_0LB0LD_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM2198.


Module TM2199.
Definition tm := TM_from_str "1LB1RE_0RB0LC_0RD0LF_1RA---_1RD1LB_0LB0RD".
Definition tm' := TM_from_str "1RB1LD_1RC---_1LD1RA_0RD0LE_0RB0LF_0LD0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBAF") 1 9.
Time Qed.
End TM2199.


Module TM2200.
Definition tm := TM_from_str "1LB1RF_1RC0LE_0LD0RC_0LE---_1LA1LE_1RD1RF".
Definition tm' := TM_from_str "1RB1RA_0LC---_1LD1LC_1LE1RA_1RF0LC_0LB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 4 1.
Time Qed.
End TM2200.


Module TM2201.
Definition tm := TM_from_str "1RB0RC_0LC0LA_1RF1LD_1RE0LD_1RB1RD_0RA---".
Definition tm' := TM_from_str "1RB1RD_0LC0LE_1RF1LD_1RA0LD_1RB0RC_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2201.


Module TM2202.
Definition tm := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RD---".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1LD0LC_1RB1LD_1RA0RB_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 1.
Time Qed.
End TM2202.


Module TM2203.
Definition tm := TM_from_str "1LB1RD_0LC0RC_1RD1LE_0RA0LB_0LD0LF_0RA---".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD1RB_0LA0RA_0LB0LF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 19 31.
Time Qed.
End TM2203.


Module TM2204.
Definition tm := TM_from_str "1LB0RE_0LC---_1RD1LF_0RA0LE_0LC0RE_0LD1LB".
Definition tm' := TM_from_str "1RB1LE_0RC0LF_1LD0RF_0LA---_0LB1LD_0LA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 22 32.
Time Qed.
End TM2204.


Module TM2205.
Definition tm := TM_from_str "1LB1LA_0RC0RE_0LA0RD_1RC1LE_0LA1RF_---1RD".
Definition tm' := TM_from_str "1RB1LE_0LC0RA_1LD1LC_0RB0RE_0LC1RF_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBAEF") 4 1.
Time Qed.
End TM2205.


Module TM2206.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1LF_0RB1RD_0RC---".
Definition tm' := TM_from_str "1RB0LB_0RC1LF_1LD1RE_0LA0RB_0RD1RB_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 34 22.
Time Qed.
End TM2206.


Module TM2207.
Definition tm := TM_from_str "1RB1LD_0RC1RE_1LD0RA_0LA0LD_1RC0RF_1RB---".
Definition tm' := TM_from_str "1RB---_0RC1RF_1LD0RE_0LE0LD_1RB1LD_1RC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM2207.


Module TM2208.
Definition tm := TM_from_str "1RB0RF_1LC1LE_1RD1LB_1LC1RE_1RA0LC_---0RC".
Definition tm' := TM_from_str "1RB1LC_1LA1RD_1LA1LD_1RE0LA_1RC0RF_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECABDF") 2 2.
Time Qed.
End TM2208.


Module TM2209.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RB_1LD0LF_1RB1LE_1LC0LD_1LA1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM2209.


Module TM2210.
Definition tm := TM_from_str "1RB0RB_1LC1RB_---0LD_1RE0LF_1RB0RA_1RE1LF".
Definition tm' := TM_from_str "1RB0RF_1LC1RB_---0LD_1RA0LE_1RA1LE_1RB0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2210.


Module TM2211.
Definition tm := TM_from_str "1RB1RD_0LC0RA_0LD1LC_1LA0LE_1RB0RF_0RE---".
Definition tm' := TM_from_str "1RB0RF_0LC0RE_0LD1LC_1LE0LA_1RB1RD_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2211.


Module TM2212.
Definition tm := TM_from_str "1LB1RE_1RC0LD_1LE0RD_0LE0LF_0RB0LA_1RE---".
Definition tm' := TM_from_str "1RB---_0RC0LE_1RD0LF_1LB0RF_1LC1RB_0LB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDFBA") 4 1.
Time Qed.
End TM2212.


Module TM2213.
Definition tm := TM_from_str "1LB0LA_1LC1LA_0RD0RE_0LA1RC_1RC0RF_---1RD".
Definition tm' := TM_from_str "1RB0RF_0RC0RA_0LD1RB_1LE0LD_1LB1LD_---1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCAF") 1 22.
Time Qed.
End TM2213.


Module TM2214.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RF_1LC1LF_1RA---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM2214.


Module TM2215.
Definition tm := TM_from_str "1LB---_1RB0LC_0LD1RA_1LE0RE_0RF0LA_1RD1LF".
Definition tm' := TM_from_str "1RB1LA_1LC0RC_0RA0LD_1LE---_1RE0LF_0LB1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 423 402.
Time Qed.
End TM2215.


Module TM2216.
Definition tm := TM_from_str "1RB1LA_0LC0LE_1RD1LB_1RE1RC_1LF0RD_---0LA".
Definition tm' := TM_from_str "1RB1RF_1LC0RA_---0LD_1RE1LD_0LF0LB_1RA1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 1646 1567.
Time Qed.
End TM2216.


Module TM2217.
Definition tm := TM_from_str "1LB0LF_1RC1LE_1RD1LC_0LB0RD_1RD0LA_---1LA".
Definition tm' := TM_from_str "1RB1LD_1RC1LB_0LA0RC_1RC0LE_1LA0LF_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 21 15.
Time Qed.
End TM2217.


Module TM2218.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB1LF_1LC1RB_1RB---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1RC_0LC1LF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM2218.


Module TM2219.
Definition tm := TM_from_str "1RB---_1LC0RD_1LD0LB_0RE1RB_1RB1RF_0LF0RA".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA1RB_0LE0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2219.


Module TM2220.
Definition tm := TM_from_str "1LB1RD_1LC0LF_1RA1LC_1RE0RA_1RC---_1RB0LF".
Definition tm' := TM_from_str "1RB0LA_1LC0LA_1RD1LC_1LB1RE_1RF0RD_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 2 3.
Time Qed.
End TM2220.


Module TM2221.
Definition tm := TM_from_str "1LB0RC_1RC0LB_0RD1LB_0LF1RE_0RA0RF_0LE---".
Definition tm' := TM_from_str "1RB0LA_0RC1LA_0LD1RE_0LE---_0RF0RD_1LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCED") 1 8.
Time Qed.
End TM2221.


Module TM2222.
Definition tm := TM_from_str "1RB0LD_1RC---_1RD1RF_1LE0RB_1RF0LA_1LE0RE".
Definition tm' := TM_from_str "1RB---_1RC1RF_1LD0RA_1RF0LE_1RA0LC_1LD0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 907 1198.
Time Qed.
End TM2222.


Module TM2223.
Definition tm := TM_from_str "1RB1LE_1LC1RB_0LA1RD_0RB0LC_0LD0LF_1RD---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_1RC1LF_0LB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDBFA") 5 1.
Time Qed.
End TM2223.


Module TM2224.
Definition tm := TM_from_str "1RB0RF_0LC1LE_0LE1LD_1RE0LF_1RA0LB_1RA---".
Definition tm' := TM_from_str "1RB0LC_1RC0RF_0LD1LA_0LA1LE_1RA0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 81 49.
Time Qed.
End TM2224.


Module TM2225.
Definition tm := TM_from_str "1RB---_1LC0RC_0RE0LD_1LC1LD_0LD1RF_1RB0RA".
Definition tm' := TM_from_str "1RB0RF_1LC0RC_0RE0LD_1LC1LD_0LD1RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2225.


Module TM2226.
Definition tm := TM_from_str "1RB0LE_0RC1RA_1RD0RA_1RE---_0LF1LA_0RA1LF".
Definition tm' := TM_from_str "1RB---_0LC1LD_0RD1LC_1RE0LB_0RF1RD_1RA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 1 8.
Time Qed.
End TM2226.


Module TM2227.
Definition tm := TM_from_str "1RB1LC_1LB1LA_0RD0LE_1RA1RD_0LF0RD_---0LC".
Definition tm' := TM_from_str "1RB1RA_1RC1LD_1LC1LB_0RA0LE_0LF0RA_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 5 4.
Time Qed.
End TM2227.


Module TM2228.
Definition tm := TM_from_str "1LB0RE_1LC1RF_1RD0LA_1LF0RA_0LD---_1RB0RC".
Definition tm' := TM_from_str "1RB0LD_1LC0RD_1RE0RA_1LE0RF_1LA1RC_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABFC") 1 5.
Time Qed.
End TM2228.


Module TM2229.
Definition tm := TM_from_str "1LB---_0LC1LE_1LD1LA_1RE0RE_0LF0RD_1RE1LB".
Definition tm' := TM_from_str "1RB1LC_0LA0RE_0LD1LB_1LE1LF_1RB0RB_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEBA") 1 3.
Time Qed.
End TM2229.


Module TM2230.
Definition tm := TM_from_str "1LB0LF_0RC0LB_1RE1RD_1LE0RF_1LA0RB_1LA---".
Definition tm' := TM_from_str "1RB1RF_1LC0RE_1LE0LD_1LC---_0RA0LE_1LB0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEAFBD") 8 1.
Time Qed.
End TM2230.


Module TM2231.
Definition tm := TM_from_str "1RB0LE_1LC1RA_0LF1LD_0RB0LC_---1RD_1RB1LA".
Definition tm' := TM_from_str "1RB1LE_1LC1RE_0LA1LD_0RB0LC_1RB0LF_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM2231.


Module TM2232.
Definition tm := TM_from_str "1RB---_1LC1RB_0LE1RD_0RB0LC_1RB1LF_0LD0LA".
Definition tm' := TM_from_str "1RB1LE_1LC1RB_0LA1RD_0RB0LC_0LD0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2232.


Module TM2233.
Definition tm := TM_from_str "1RB0RA_0LC0LD_---0LD_1LE1LF_1RA1RE_0RA1LC".
Definition tm' := TM_from_str "1RB1RA_1RC0RB_0LD0LE_---0LE_1LA1LF_0RB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 1 8.
Time Qed.
End TM2233.


Module TM2234.
Definition tm := TM_from_str "1RB1LC_0RC0RB_0LD0LA_1RE---_1LF1RA_1RB1LE".
Definition tm' := TM_from_str "1RB1LE_0RC0RB_0LD0LF_1RE---_1LA1RF_1RB1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2234.


Module TM2235.
Definition tm := TM_from_str "1LB1LC_0RA---_1RD1LF_0RE0RD_1LE0LC_0RD0LA".
Definition tm' := TM_from_str "1RB1LD_0RC0RB_1LC0LA_0RB0LE_1LF1LA_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 26 20.
Time Qed.
End TM2235.


Module TM2236.
Definition tm := TM_from_str "1RB1LC_0LC1RE_---0LD_0RE1LA_1RF1RB_1RB0RE".
Definition tm' := TM_from_str "1RB0RE_0LC1RE_---0LD_0RE1LF_1RA1RB_1RB1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2236.


Module TM2237.
Definition tm := TM_from_str "1RB0LE_1LC0RD_0LB1LA_0RB1LA_1RB0LF_---0LA".
Definition tm' := TM_from_str "1RB0LF_1LC0RE_0LB1LD_1RB0LA_0RB1LD_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 1.
Time Qed.
End TM2237.


Module TM2238.
Definition tm := TM_from_str "1LB1RF_1RC0LD_1RD1RA_1LE0LB_---0RA_0LE0LC".
Definition tm' := TM_from_str "1RB1RD_1LC0LF_---0RD_1LF1RE_0LC0LA_1RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFABCE") 1 7.
Time Qed.
End TM2238.


Module TM2239.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_0LA---_1RA0LD".
Definition tm' := TM_from_str "1RB1RE_0LC---_1LD1LC_0RE0LD_1RF0RA_1RC0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM2239.


Module TM2240.
Definition tm := TM_from_str "1RB0LC_1RC0RA_0LD1LA_---1LE_0LF0LA_0LA0LA".
Definition tm' := TM_from_str "1RB0RF_0LC1LF_---1LD_0LE0LF_0LF0LF_1RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 29 36.
Time Qed.
End TM2240.


Module TM2241.
Definition tm := TM_from_str "1RB0RE_1LC1RB_1LD0LD_0RE0LC_1RA1RF_0RA---".
Definition tm' := TM_from_str "1RB1RF_1RC0RA_1LD1RC_1LE0LE_0RA0LD_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 8 11.
Time Qed.
End TM2241.


Module TM2242.
Definition tm := TM_from_str "1LB1LA_1RC0LB_1LA1LD_1RE0RC_---0RF_1RC1RD".
Definition tm' := TM_from_str "1RB1RE_1LC1LE_1LD1LC_1RB0LD_1RF0RB_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEFA") 14 18.
Time Qed.
End TM2242.


Module TM2243.
Definition tm := TM_from_str "1LB1RD_1LC1RE_0RA0LC_---0RE_1RB0RF_1RC1RE".
Definition tm' := TM_from_str "1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEFA") 887 985.
Time Qed.
End TM2243.


Module TM2244.
Definition tm := TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1LB_0RF1RD_0LC0RD".
Definition tm' := TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA---_0RF1RB_0LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 30 22.
Time Qed.
End TM2244.


Module TM2245.
Definition tm := TM_from_str "1RB0RF_1LC0RA_1RB1LD_0LE---_0LB0RF_1LB1RE".
Definition tm' := TM_from_str "1RB1LC_1LA0RE_0LD---_0LB0RF_1RB0RF_1LB1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM2245.


Module TM2246.
Definition tm := TM_from_str "1RB1RE_1LC1RE_1RF1LD_0LE---_0LF1LF_0LB0RA".
Definition tm' := TM_from_str "1RB1LF_0LC0RE_1LA1RD_0LB1LB_1RC1RD_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECAFDB") 1 6.
Time Qed.
End TM2246.


Module TM2247.
Definition tm := TM_from_str "1LB0LE_0RC1RE_1RE1RD_1LE1RF_1LA0RB_0LC---".
Definition tm' := TM_from_str "1RB1RE_1LC0RD_1LD0LB_0RA1RB_1LB1RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEBF") 6 1.
Time Qed.
End TM2247.


Module TM2248.
Definition tm := TM_from_str "1LB1LA_0RC0RE_0LA0RD_1RC1LC_1RC1RF_---1RE".
Definition tm' := TM_from_str "1RB1RF_0LC0RE_1LD1LC_0RB0RA_1RB1LB_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEAF") 4 1.
Time Qed.
End TM2248.


Module TM2249.
Definition tm := TM_from_str "1LB1RD_0LC0LB_1RC0RA_1RE0RA_1RF---_1RA0LB".
Definition tm' := TM_from_str "1RB---_1RC0LD_1LD1RF_0LE0LD_1RE0RC_1RA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 164 108.
Time Qed.
End TM2249.


Module TM2250.
Definition tm := TM_from_str "1RB0RA_1RC1RA_0LD0LE_0RA1LC_1RC0LF_---1LD".
Definition tm' := TM_from_str "1RB0LF_0LC0LA_0RD1LB_1RE0RD_1RB1RD_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCAF") 1 24.
Time Qed.
End TM2250.


Module TM2251.
Definition tm := TM_from_str "1RB0LE_1LC0RE_1RF0LD_1LA0LF_0LC0RA_0LE---".
Definition tm' := TM_from_str "1RB0LF_0LC---_0LA0RD_1RE0LC_1LA0RC_1LD0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFCB") 1 4.
Time Qed.
End TM2251.


Module TM2252.
Definition tm := TM_from_str "1RB0LC_1RC0LA_1RD0RF_0LE0RE_---1LF_0RB1LA".
Definition tm' := TM_from_str "1RB0RD_0LC0RC_---1LD_0RE1LF_1RA0LF_1RE0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEABCD") 1 6.
Time Qed.
End TM2252.


Module TM2253.
Definition tm := TM_from_str "1LB0LF_1RC1LF_1RD0RC_0LD1LE_0LA1RC_1LA---".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_0LC1LD_0LE1RB_1LA0LF_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 2 5.
Time Qed.
End TM2253.


Module TM2254.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0LD_0RC0RF_1LC---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0RF_1RC0LE_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM2254.


Module TM2255.
Definition tm := TM_from_str "1LB1RF_0LC1RB_1RA0LD_---1LE_0RA1LC_0RB1RF".
Definition tm' := TM_from_str "1RB0LD_1LC1RF_0LA1RC_---1LE_0RB1LA_0RC1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 6 14.
Time Qed.
End TM2255.


Module TM2256.
Definition tm := TM_from_str "1LB1LF_0RC1LE_1RD1RC_0LE1RB_---0LA_1RA0LB".
Definition tm' := TM_from_str "1RB1RA_0LC1RE_---0LD_1LE1LF_0RA1LC_1RD0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM2256.


Module TM2257.
Definition tm := TM_from_str "1LB1LD_1RC1RB_1LC1RA_---0LE_0RB0LF_0LD0RB".
Definition tm' := TM_from_str "1RB1RA_1LB1RC_1LA1LD_---0LE_0RA0LF_0LD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 6.
Time Qed.
End TM2257.


Module TM2258.
Definition tm := TM_from_str "1RB0LB_0RC0RA_1RD0RF_1LE---_1RB1LF_0LE0LD".
Definition tm' := TM_from_str "1RB1LE_0RC0RF_1RD0RE_1LA---_0LA0LD_1RB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2258.


Module TM2259.
Definition tm := TM_from_str "1LB1RD_1RC0LC_0RD1LC_1LF0RE_0LF1RA_1LB---".
Definition tm' := TM_from_str "1RB0LB_0RC1LB_1LD0RE_1LA---_0LD1RF_1LA1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCED") 35 4.
Time Qed.
End TM2259.


Module TM2260.
Definition tm := TM_from_str "1RB1RC_1LC0RF_1RA0LD_1LE1LB_1RA---_0RC0LB".
Definition tm' := TM_from_str "1RB0LD_1RC1RA_1LA0RE_1LF1LC_0RA0LC_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADFE") 10 33.
Time Qed.
End TM2260.


Module TM2261.
Definition tm := TM_from_str "1LB1LB_1RC0LE_0LF1RD_1LA0RB_1LA1LC_---0LA".
Definition tm' := TM_from_str "1RB0LF_0LC1RE_---0LD_1LA1LA_1LD0RA_1LD1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABEFC") 1 4.
Time Qed.
End TM2261.


Module TM2262.
Definition tm := TM_from_str "1RB1RE_0LC1RC_0RA0LD_1RE1LF_1RA0RA_---1LC".
Definition tm' := TM_from_str "1RB1LF_1RC0RC_1RD1RB_0LE1RE_0RC0LA_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM2262.


Module TM2263.
Definition tm := TM_from_str "1LB1RC_0RA0LB_1LB0RD_1LA1RE_1RD0LF_---1LE".
Definition tm' := TM_from_str "1RB0LF_1LC1RA_1LE1RD_1LE0RB_0RC0LE_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEDBAF") 8 2.
Time Qed.
End TM2263.


Module TM2264.
Definition tm := TM_from_str "1RB0RF_0LC1LE_1RA1RD_0LE1RA_0RA1LB_---1RD".
Definition tm' := TM_from_str "1RB1RD_1RC0RF_0LA1LE_0LE1RB_0RB1LC_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 3 10.
Time Qed.
End TM2264.


Module TM2265.
Definition tm := TM_from_str "1RB0LE_1RC0RC_1LD1RC_1LF1LA_1RB1LE_---1LD".
Definition tm' := TM_from_str "1RB1LA_1RC0RC_1LD1RC_1LF1LE_1RB0LA_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2265.


Module TM2266.
Definition tm := TM_from_str "1LB---_1LC1LE_1RD0LB_1RB0RC_1LF0RE_1LB0LA".
Definition tm' := TM_from_str "1RB0RC_1LC1LD_1RA0LB_1LE0RD_1LB0LF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 5 1.
Time Qed.
End TM2266.


Module TM2267.
Definition tm := TM_from_str "1LB0RB_1LC0RA_0LD1LD_1LE---_1RF1RB_0LB0RF".
Definition tm' := TM_from_str "1RB1RC_0LC0RB_1LE0RD_1LC0RC_0LF1LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEFAB") 1 4.
Time Qed.
End TM2267.


Module TM2268.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_1LA---_1RA1RF".
Definition tm' := TM_from_str "1RB1RE_1LC---_1LD1LC_0RE0LD_1RF0RA_1RC1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM2268.


Module TM2269.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB1RF_0RA1RB".
Definition tm' := TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC1RD_0RD1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABFE") 35 23.
Time Qed.
End TM2269.


Module TM2270.
Definition tm := TM_from_str "1RB1RA_1LC0RE_---1LD_1RB0LD_0RA1RF_1RA0RC".
Definition tm' := TM_from_str "1RB0LA_1LC0RD_---1LA_0RF1RE_1RF0RC_1RB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM2270.


Module TM2271.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0LF_1LC0RE_0RE---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA0RD_0LC0LF_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM2271.


Module TM2272.
Definition tm := TM_from_str "1LB0LF_0RC1RE_1RE1RD_1LE0RF_1LA0RB_1LA---".
Definition tm' := TM_from_str "1RB1RF_1LC0RE_1LE0LD_1LC---_0RA1RB_1LB0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEAFBD") 6 1.
Time Qed.
End TM2272.


Module TM2273.
Definition tm := TM_from_str "1LB1RE_1LC0LB_1RD0LB_1RA0RC_0RB0RF_0RE---".
Definition tm' := TM_from_str "1RB0RD_1LC1RE_1LD0LC_1RA0LC_0RC0RF_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 7 3.
Time Qed.
End TM2273.


Module TM2274.
Definition tm := TM_from_str "1RB---_0RC0RF_1LD1RE_0LE1RA_1RB0LF_0RC0RD".
Definition tm' := TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA1RF_0RC0RD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2274.


Module TM2275.
Definition tm := TM_from_str "1LB0LC_1RC1LD_0LD0RB_0LA0RE_1RF---_0LB0LC".
Definition tm' := TM_from_str "1RB---_0LC0LF_1RF1LD_0LE0RA_1LC0LF_0LD0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECFDAB") 1198 1261.
Time Qed.
End TM2275.


Module TM2276.
Definition tm := TM_from_str "1RB1LE_0RC1RC_1LD0RD_0LE0LA_1RF1LD_1RB---".
Definition tm' := TM_from_str "1RB---_0RC1RC_1LD0RD_0LE0LF_1RA1LD_1RB1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2276.


Module TM2277.
Definition tm := TM_from_str "1LB1LE_1RC0LD_0LA0RC_1LE---_1LF1LA_1RA1RF".
Definition tm' := TM_from_str "1RB1RA_1LC1LE_1RF0LD_1LE---_1LA1LB_0LB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFDEA") 4 1.
Time Qed.
End TM2277.


Module TM2278.
Definition tm := TM_from_str "1LB1LE_1RC1LF_1LD1RC_---1LE_1LA1RF_0LD0RE".
Definition tm' := TM_from_str "1RB1LF_1LC1RB_---1LD_1LE1RF_1LA1LD_0LC0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 328112 323711.
Time Qed.
End TM2278.


Module TM2279.
Definition tm := TM_from_str "1RB1LC_1LA0RD_0LB1LB_1RE1RF_1RB1RE_---0LA".
Definition tm' := TM_from_str "1RB1RA_1LC0RE_1RB1LD_0LB1LB_1RA1RF_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM2279.


Module TM2280.
Definition tm := TM_from_str "1LB0LE_0LC---_1RD0RC_0RA0RD_1LE1LF_1RE0LB".
Definition tm' := TM_from_str "1RB0LC_1LB1LA_0LD---_1RE0RD_0RF0RE_1LC0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEBA") 5 1.
Time Qed.
End TM2280.


Module TM2281.
Definition tm := TM_from_str "1LB1LD_1LC0RE_1RD0LA_1RB0LA_1RC1RF_1RE---".
Definition tm' := TM_from_str "1RB0LD_1RC0LD_1LA0RE_1LC1LB_1RA1RF_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCABEF") 4 4.
Time Qed.
End TM2281.


Module TM2282.
Definition tm := TM_from_str "1LB1RE_0RC0LC_0LE0LD_1RB---_0RF0LA_1LE1RF".
Definition tm' := TM_from_str "1RB---_0RC0LC_0LD0LA_0RE0LF_1LD1RE_1LB1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 4 1.
Time Qed.
End TM2282.


Module TM2283.
Definition tm := TM_from_str "1RB0RD_1RC1LA_1RD0LC_1LE0RF_---1LC_1RA1RA".
Definition tm' := TM_from_str "1RB1LF_1RC0LB_1LD0RE_---1LB_1RF1RF_1RA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 18 14.
Time Qed.
End TM2283.


Module TM2284.
Definition tm := TM_from_str "1LB1LF_0LC0RD_1LD0LC_0RE0RA_1RB1RF_1RD---".
Definition tm' := TM_from_str "1RB1RE_0LC0RD_1LD0LC_0RA0RF_1RD---_1LB1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 6 15.
Time Qed.
End TM2284.


Module TM2285.
Definition tm := TM_from_str "1RB---_1LC1LD_1LE0RD_0LA0LE_1RF1LB_1RC0RF".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0RE_1LC1LE_0LF0LA_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDCEAB") 5 1.
Time Qed.
End TM2285.


Module TM2286.
Definition tm := TM_from_str "1RB---_1RC1RA_1RD0LF_1RE0LF_1LC0RB_1LE1LD".
Definition tm' := TM_from_str "1RB0LD_1LC0RE_1RA0LD_1LB1LA_1RC1RF_1RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FECABD") 8 7.
Time Qed.
End TM2286.


Module TM2287.
Definition tm := TM_from_str "1RB1RD_1LC0LE_1RA0LB_0RA0RB_1LC0RF_1RE---".
Definition tm' := TM_from_str "1RB---_1LC0RA_1RE0LD_1LC0LB_1RD1RF_0RE0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDCFBA") 2 2.
Time Qed.
End TM2287.


Module TM2288.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RD_1LC0LF_0RC---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RE_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM2288.


Module TM2289.
Definition tm := TM_from_str "1RB1LE_0RC0LD_1LD1RC_0LA1RB_0LB0LF_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_1RB1LF_0LB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM2289.


Module TM2290.
Definition tm := TM_from_str "1RB1RA_0LC1RD_0LD1LC_1RE0RB_1RF---_1RA1RD".
Definition tm' := TM_from_str "1RB0RE_1RC---_1RD1RA_1RE1RD_0LF1RA_0LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 7 21.
Time Qed.
End TM2290.


Module TM2291.
Definition tm := TM_from_str "1LB---_1RC0LB_0RD1LB_0LA1RE_0RF1RA_1LB0RC".
Definition tm' := TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA---_0RF1RD_1LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 3 4.
Time Qed.
End TM2291.


Module TM2292.
Definition tm := TM_from_str "1RB0LC_1RC0RF_0LD1LA_1RE1LD_0LC0LC_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RA_0LD1LF_1RE1LD_0LC0LC_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2292.


Module TM2293.
Definition tm := TM_from_str "1RB1RD_0LC0LE_0RD1LB_1RA0RB_1LB0LF_---1LC".
Definition tm' := TM_from_str "1RB0RC_1RC1RA_0LD0LE_0RA1LC_1LC0LF_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 28 1.
Time Qed.
End TM2293.


Module TM2294.
Definition tm := TM_from_str "1RB0LC_1LC0RA_1LA0RD_0LB0RE_1LB1RF_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_1LF0RD_0LB0RE_1LB1RA_1RB0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2294.


Module TM2295.
Definition tm := TM_from_str "1RB1LE_0LC1RB_1LA0RD_1RC0RD_0LF---_0LB1LB".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1RF1LD_0LE---_0LF1LF_0LB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFBADE") 4 1.
Time Qed.
End TM2295.


Module TM2296.
Definition tm := TM_from_str "1LB0RF_0RC---_0LD0RD_1RC1LE_0LA0LE_1RF1RD".
Definition tm' := TM_from_str "1RB1LC_0LA0RA_0LD0LC_1LE0RF_0RB---_1RF1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBACF") 4 1.
Time Qed.
End TM2296.


Module TM2297.
Definition tm := TM_from_str "1RB---_1RC0RB_1LD0LE_0LF0LC_1LC0RA_1RB1LE".
Definition tm' := TM_from_str "1RB1LE_1RC0RB_1LD0LE_0LA0LC_1LC0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2297.


Module TM2298.
Definition tm := TM_from_str "1RB0RF_1LC1RE_1RD0LC_0LE0RE_1RA1LD_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1RE_1RD0LC_0LE0RE_1RF1LD_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2298.


Module TM2299.
Definition tm := TM_from_str "1RB1LF_1RC1RA_1LD0RB_---0LE_1RF1LE_0LA0LC".
Definition tm' := TM_from_str "1RB1RF_1LC0RA_---0LD_1RE1LD_0LF0LB_1RA1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 1639 1567.
Time Qed.
End TM2299.


Module TM2300.
Definition tm := TM_from_str "1RB1LD_1RC1RE_1LA0LD_1RB0LA_0RF---_1RD1LB".
Definition tm' := TM_from_str "1RB0LD_1RC1RE_1LD0LA_1RB1LA_0RF---_1RA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM2300.


Module TM2301.
Definition tm := TM_from_str "1LB0LF_1RC0LA_0LE1RD_0RE0RD_1LE1LB_---0LB".
Definition tm' := TM_from_str "1RB0LE_0LC1RD_1LC1LA_0RC0RD_1LA0LF_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABDCF") 1 3.
Time Qed.
End TM2301.


Module TM2302.
Definition tm := TM_from_str "1LB1RE_1RC0LB_0RE1LD_---0RB_1RA1LF_0LC0LE".
Definition tm' := TM_from_str "1RB0LA_0RC1LF_1RD1LE_1LA1RC_0LB0LC_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABFCE") 6 1.
Time Qed.
End TM2302.


Module TM2303.
Definition tm := TM_from_str "1RB0RA_1LC0RD_1LD0LC_1RA0LE_1LC0LF_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1LD0LC_1RE0LF_1RB0RE_1LC0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM2303.


Module TM2304.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC1LF_0RB---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB1LF_1RC0RF_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM2304.


Module TM2305.
Definition tm := TM_from_str "1RB0LE_1RC1LE_0RD0RC_1LD1RB_---0LF_1RB0LA".
Definition tm' := TM_from_str "1RB0LF_1RC1LE_0RD0RC_1LD1RB_---0LA_1RB0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2305.


Module TM2306.
Definition tm := TM_from_str "1LB0RD_1RC1LF_0RA1LC_---1RE_0LB1RA_0LC1LA".
Definition tm' := TM_from_str "1RB1LF_0RC1LB_1LA0RD_---1RE_0LA1RC_0LB1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 14 6.
Time Qed.
End TM2306.


Module TM2307.
Definition tm := TM_from_str "1RB1RE_1LC0RA_---0LD_1LE1LF_1RA0RC_1RB0LD".
Definition tm' := TM_from_str "1RB0LD_1LC0RF_---0LD_1LE1LA_1RF0RC_1RB1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2307.


Module TM2308.
Definition tm := TM_from_str "1LB0LC_0RC1LF_0LF1RD_1RE0RC_1LB---_1RD1LA".
Definition tm' := TM_from_str "1RB1LE_1RC0RF_1LD---_0RF1LA_1LD0LF_0LA1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDFBCA") 3 1.
Time Qed.
End TM2308.


Module TM2309.
Definition tm := TM_from_str "1LB0RB_1RC0LA_1LF0LD_---1RE_0RB1RE_1RE1LC".
Definition tm' := TM_from_str "1RB1LD_0RC1RB_1RD0LF_1LA0LE_---1RB_1LC0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEBA") 4 1.
Time Qed.
End TM2309.


Module TM2310.
Definition tm := TM_from_str "1LB1RD_0LC0RF_1RD1LE_0RA0LB_0LD1LB_0RB---".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD1RB_0LA0RF_0LB1LD_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 20 32.
Time Qed.
End TM2310.


Module TM2311.
Definition tm := TM_from_str "1RB1RF_0LC0RB_1LE0LD_1RC---_0LA1LA_1LC0RF".
Definition tm' := TM_from_str "1RB---_1LC0LA_0LD1LD_1RE1RF_0LB0RE_1LB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBACF") 4 1.
Time Qed.
End TM2311.


Module TM2312.
Definition tm := TM_from_str "1LB1LF_1RC0RB_---0LD_1RE0LD_1LA0RE_1LD1RB".
Definition tm' := TM_from_str "1RB0LA_1LC0RB_1LE1LD_1LA1RE_1RF0RE_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEFABD") 5 1.
Time Qed.
End TM2312.


Module TM2313.
Definition tm := TM_from_str "1LB1LA_1RC1RD_0LD0RC_1RE1RD_1LF1RF_---0LA".
Definition tm' := TM_from_str "1RB1RC_0LC0RB_1RD1RC_1LE1RE_---0LF_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 4 3.
Time Qed.
End TM2313.


Module TM2314.
Definition tm := TM_from_str "1RB---_1LC0RD_0LF0RB_1RE0LB_0RB1RA_0RD1LF".
Definition tm' := TM_from_str "1RB0LC_0RC1RF_1LD0RA_0LE0RC_0RA1LE_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 5 1.
Time Qed.
End TM2314.


Module TM2315.
Definition tm := TM_from_str "1RB1LC_0LA0RE_0LD0RA_1RC1LD_0RC0RF_1LB---".
Definition tm' := TM_from_str "1RB1LA_0LA0RC_1RD1LB_0LC0RE_0RB0RF_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBAEF") 6 9.
Time Qed.
End TM2315.


Module TM2316.
Definition tm := TM_from_str "1RB0LA_0RC0RA_1LD1RE_1LD0LA_---1RF_1RB0RB".
Definition tm' := TM_from_str "1RB0RB_0RC0RE_1LD1RF_1LD0LE_1RB0LE_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM2316.


Module TM2317.
Definition tm := TM_from_str "1LB1RB_1RC0RB_1LD0LA_1RB1LE_1LF0LD_1LC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LF0LA_1LB1RB_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 4 1.
Time Qed.
End TM2317.


Module TM2318.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LD_0RB1RF_0RA---".
Definition tm' := TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RB_0RD1RF_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 33 23.
Time Qed.
End TM2318.


Module TM2319.
Definition tm := TM_from_str "1LB1LC_1RA---_0LE1RD_1RE0RC_1LA1LF_1LE0RF".
Definition tm' := TM_from_str "1RB0RD_1LC1LF_1LE1LD_0LB1RA_1RC---_1LB0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEDABF") 6 1.
Time Qed.
End TM2319.


Module TM2320.
Definition tm := TM_from_str "1LB---_1LC1RF_0LD0RE_1RE0LE_0RB0RA_0RC0LD".
Definition tm' := TM_from_str "1RB0LB_0RC0RF_1LD1RE_0LA0RB_0RD0LA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 8 1.
Time Qed.
End TM2320.


Module TM2321.
Definition tm := TM_from_str "1RB1RE_1RC1RB_0LD1RE_0LE1LD_1RF0RC_1RA---".
Definition tm' := TM_from_str "1RB0RE_1RC---_1RD1RA_1RE1RD_0LF1RA_0LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 22 1.
Time Qed.
End TM2321.


Module TM2322.
Definition tm := TM_from_str "1RB0LA_1LC0RD_---1LA_1RE1RE_1RF0RB_1RA1LE".
Definition tm' := TM_from_str "1RB1RB_1RC0RE_1RD1LB_1RE0LD_1LF0RA_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 455 384.
Time Qed.
End TM2322.


Module TM2323.
Definition tm := TM_from_str "1LB1RA_1LC1LF_1LD---_1LE0LE_1RA1LD_1LA0RF".
Definition tm' := TM_from_str "1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEFAD") 63 82.
Time Qed.
End TM2323.


Module TM2324.
Definition tm := TM_from_str "1RB1LE_0RC0RA_0LD0LF_1LE0LB_1RB1LC_1LD---".
Definition tm' := TM_from_str "1RB1LC_0RC0RE_0LD0LF_1LA0LB_1RB1LA_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2324.


Module TM2325.
Definition tm := TM_from_str "1RB1LD_1LC0RC_1LA1RC_0LF0LE_1RB1LE_---0RB".
Definition tm' := TM_from_str "1RB1LA_1LC0RC_1LD1RC_1RB1LE_0LF0LA_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 1.
Time Qed.
End TM2325.


Module TM2326.
Definition tm := TM_from_str "1LB---_1RC1RD_1RA0RC_1RE1RD_1LF1LE_0RB0LF".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RE1RA_1RF0RE_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 1 4.
Time Qed.
End TM2326.


Module TM2327.
Definition tm := TM_from_str "1RB1LE_0RC0LD_1LD1RC_0LA1RB_0LB0LF_1RC---".
Definition tm' := TM_from_str "1RB---_1LC1RB_0LE1RD_0RB0LC_1RD1LF_0LD0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDBCFA") 1 5.
Time Qed.
End TM2327.


Module TM2328.
Definition tm := TM_from_str "1RB1LD_1RC0LF_1LA0RA_0RC0LE_1LA0LC_---1LB".
Definition tm' := TM_from_str "1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 9.
Time Qed.
End TM2328.


Module TM2329.
Definition tm := TM_from_str "1RB0RF_1RC1RA_1LD0LE_1RB0LC_0RB0RD_1RE---".
Definition tm' := TM_from_str "1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB0RF_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM2329.


Module TM2330.
Definition tm := TM_from_str "1RB0LD_1RC0RA_1LA1RC_0RB0LE_1RA1LF_---1LD".
Definition tm' := TM_from_str "1RB0RC_1LC1RB_1RA0LD_0RA0LE_1RC1LF_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 2 6.
Time Qed.
End TM2330.


Module TM2331.
Definition tm := TM_from_str "1LB0RD_0RC0LA_1RD0LB_0RE1RF_1RA1LF_0LB---".
Definition tm' := TM_from_str "1RB0LE_0RC1RF_1RD1LF_1LE0RB_0RA0LD_0LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 5 1.
Time Qed.
End TM2331.


Module TM2332.
Definition tm := TM_from_str "1RB0RC_1LC1RE_0LE0LD_1LC0LE_0RA0RF_1RA---".
Definition tm' := TM_from_str "1RB---_1RC0RD_1LD1RF_0LF0LE_1LD0LF_0RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 790 828.
Time Qed.
End TM2332.


Module TM2333.
Definition tm := TM_from_str "1LB1LA_1RC1RB_0LD0RC_1LA0LE_1LF1LD_0LA---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_0LF---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 826 591.
Time Qed.
End TM2333.


Module TM2334.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RD0LD_1RE1LC_1RA0RF_1RA---".
Definition tm' := TM_from_str "1RB0RF_1LC1RE_1LD0LC_1RE0LE_1RA1LD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 11 6.
Time Qed.
End TM2334.


Module TM2335.
Definition tm := TM_from_str "1LB0RC_1RC0LF_1RE0RD_1RB---_1RA1LA_0RD0LA".
Definition tm' := TM_from_str "1RB1LB_1LC0RF_1RF0LD_0RE0LB_1RC---_1RA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFEAD") 1 8.
Time Qed.
End TM2335.


Module TM2336.
Definition tm := TM_from_str "1LB0RD_1LC1LA_0LD0RF_1LE0LA_1RC---_1RC1RF".
Definition tm' := TM_from_str "1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 1 4.
Time Qed.
End TM2336.


Module TM2337.
Definition tm := TM_from_str "1RB1RE_0LC0LD_1RA1LA_0RE1LC_1RF0LB_0RB---".
Definition tm' := TM_from_str "1RB1LB_1RC1RD_0LA0LE_1RF0LC_0RD1LA_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 4 17.
Time Qed.
End TM2337.


Module TM2338.
Definition tm := TM_from_str "1LB1RA_1RC1LE_1LD0RC_1RA1LF_1LA0LB_0RA---".
Definition tm' := TM_from_str "1RB1LF_1LC1RB_1RE1LD_1LB0LC_1LA0RE_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEADF") 20 23.
Time Qed.
End TM2338.


Module TM2339.
Definition tm := TM_from_str "1RB0RB_1LC1RB_---0LD_0RA0LE_1RF1LF_1RA1LD".
Definition tm' := TM_from_str "1RB1LE_1RC0RC_1LD1RC_---0LE_0RB0LF_1RA1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 6 2.
Time Qed.
End TM2339.


Module TM2340.
Definition tm := TM_from_str "1RB0LB_1RC1LC_1LD1RE_---0LA_1RB0RF_1RA0LF".
Definition tm' := TM_from_str "1RB0RF_1RC1LC_1LD1RA_---0LE_1RB0LB_1RE0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2340.


Module TM2341.
Definition tm := TM_from_str "1RB0LC_1LA0LD_1LB1RF_---1LE_1RF0RC_1LA1RE".
Definition tm' := TM_from_str "1RB0RD_1LC1RA_1RE0LD_1LE1RB_1LC0LF_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEDFAB") 2 2.
Time Qed.
End TM2341.


Module TM2342.
Definition tm := TM_from_str "1RB1LF_1RC0RB_0LC1LD_0LE1LA_0LF---_1RB1LE".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_0LC1LD_0LF1LE_1RB1LA_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM2342.


Module TM2343.
Definition tm := TM_from_str "1RB1LB_1RC0LF_1RD---_1RE0RD_0LB1RD_0RC0LA".
Definition tm' := TM_from_str "1RB0RA_0LC1RA_1RE0LD_0RE0LF_1RA---_1RC1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCEABD") 1 10.
Time Qed.
End TM2343.


Module TM2344.
Definition tm := TM_from_str "1RB---_1LC0RC_0LD0RC_1RE1LF_0RB0LC_0LE0LA".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0RD_0LA0RD_0LB0LF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 6 1.
Time Qed.
End TM2344.


Module TM2345.
Definition tm := TM_from_str "1RB---_1RC0RB_1LD1LF_1RB1LE_1LC0LD_0LA0RE".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_0LF0RD_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM2345.


Module TM2346.
Definition tm := TM_from_str "1LB0LD_1RC1RF_1RE1RD_0RB1LA_1LA---_1RB0LF".
Definition tm' := TM_from_str "1RB1RD_1LC---_1LE0LD_0RE1LC_1RA1RF_1RE0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEADBF") 1 4.
Time Qed.
End TM2346.


Module TM2347.
Definition tm := TM_from_str "1LB0RA_0LC0LD_0RC1RA_1LE0LD_1LF---_1RA0LA".
Definition tm' := TM_from_str "1RB0LB_1LC0RB_0LF0LD_1LE0LD_1LA---_0RF1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFDEA") 5 1.
Time Qed.
End TM2347.


Module TM2348.
Definition tm := TM_from_str "1LB1RA_0LC1RE_0RD1LF_1RE---_0RA0LB_0LE1LD".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_0RA1LF_0LB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 6 1.
Time Qed.
End TM2348.


Module TM2349.
Definition tm := TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_1LC---".
Definition tm' := TM_from_str "1RB1RE_1LC---_1LD1LC_0RE0LD_1RF0RA_1RC1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCDAB") 36 50.
Time Qed.
End TM2349.


Module TM2350.
Definition tm := TM_from_str "1RB0LA_1LC---_1RD1LC_1LA1RE_1RD0RF_1RA1RE".
Definition tm' := TM_from_str "1RB1RF_1RC0LB_1LD---_1RE1LD_1LB1RF_1RE0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 7 26.
Time Qed.
End TM2350.


Module TM2351.
Definition tm := TM_from_str "1LB0LD_1LC0LB_0LD0LE_1RE0RE_0RF---_1LA0RA".
Definition tm' := TM_from_str "1RB0RB_0RC---_1LD0RD_1LE0LA_1LF0LE_0LA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 3 17.
Time Qed.
End TM2351.


Module TM2352.
Definition tm := TM_from_str "1RB0LE_1LC1RA_0LF1LD_0RB0LC_---0RC_1RD1LA".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD1RE_0LA1LB_1RC0LF_---0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDBFA") 9 1.
Time Qed.
End TM2352.


Module TM2353.
Definition tm := TM_from_str "1LB0LC_1RC1LE_0RE0RD_1RC1LD_0LA0LF_1LA---".
Definition tm' := TM_from_str "1RB1LA_0RC0RA_0LD0LF_1LE0LB_1RB1LC_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBACF") 2886 2971.
Time Qed.
End TM2353.


Module TM2354.
Definition tm := TM_from_str "1RB1LB_1LB1RC_1RF1LD_0RF0LE_0LD0RF_1RA---".
Definition tm' := TM_from_str "1RB---_1RC1LC_1LC1RD_1RA1LE_0RA0LF_0LE0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 2 9.
Time Qed.
End TM2354.


Module TM2355.
Definition tm := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA0LC".
Definition tm' := TM_from_str "1RB0LD_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 6 8.
Time Qed.
End TM2355.


Module TM2356.
Definition tm := TM_from_str "1RB---_0RC1LB_1RD1RF_1LE1LD_0RA0LE_1RC0LB".
Definition tm' := TM_from_str "1RB0LF_1RC1RA_1LD1LC_0RE0LD_1RF---_0RB1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 14 8.
Time Qed.
End TM2356.


Module TM2357.
Definition tm := TM_from_str "1RB0LF_1RC0RE_1RD---_1RE1LD_1LF1RB_0LB0LA".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RF_0LF0LE_1RF0LD_1RA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 31 40.
Time Qed.
End TM2357.


Module TM2358.
Definition tm := TM_from_str "1RB---_1RC0RB_1LD1RF_1RB1LE_0LC0LF_0RE0RA".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RE_0LC0LE_0RD0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM2358.


Module TM2359.
Definition tm := TM_from_str "1RB1LB_1LC1RC_1LD0RA_1RE0RF_0LC0RD_---1LE".
Definition tm' := TM_from_str "1RB0RF_0LC0RA_1LA0RD_1RE1LE_1LC1RC_---1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECABF") 1 4.
Time Qed.
End TM2359.


Module TM2360.
Definition tm := TM_from_str "1RB1LC_1LA0RD_0LB0LF_1RB0RE_1RD1RD_0LC---".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_1RB1LD_0LB0LF_1RA1RA_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDAEF") 1 1.
Time Qed.
End TM2360.


Module TM2361.
Definition tm := TM_from_str "1LB0LA_1LC0RC_0RD0LA_1RB1RE_0RC1RF_0LD---".
Definition tm' := TM_from_str "1RB1RE_1LC0RC_0RA0LD_1LB0LD_0RC1RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 19.
Time Qed.
End TM2361.


Module TM2362.
Definition tm := TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1LB_0RF0RB_0LC0RD".
Definition tm' := TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA---_0RF0RD_0LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 31 21.
Time Qed.
End TM2362.


Module TM2363.
Definition tm := TM_from_str "1LB1LC_0RA1LA_0RD0LA_1RA0RE_0LD1RF_---1RD".
Definition tm' := TM_from_str "1RB0RE_1LC1LD_0RB1LB_0RA0LB_0LA1RF_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 7 1.
Time Qed.
End TM2363.


Module TM2364.
Definition tm := TM_from_str "1RB0RC_0LC0RA_1LF1LD_0LE---_1LA0RB_1RE1LC".
Definition tm' := TM_from_str "1RB1LD_1LC0RF_1RF0RD_1LA1LE_0LB---_0LD0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFDEBA") 2 3.
Time Qed.
End TM2364.


Module TM2365.
Definition tm := TM_from_str "1LB0LD_1RC1RF_0LA1RB_0RA0LE_---1LA_0RB0LB".
Definition tm' := TM_from_str "1RB1RF_0LC1RA_1LA0LD_0RC0LE_---1LC_0RA0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 1 5.
Time Qed.
End TM2365.


Module TM2366.
Definition tm := TM_from_str "1RB1RF_1LC1LD_1RD0LB_0LC0RE_1RB1RA_1RC---".
Definition tm' := TM_from_str "1RB1RE_1LC1LD_1RD0LB_0LC0RA_1RB1RF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2366.


Module TM2367.
Definition tm := TM_from_str "1RB1LD_1LB1RC_1RF1LD_0RF0LE_0LD0RE_1RA---".
Definition tm' := TM_from_str "1RB---_1RC1LE_1LC1RD_1RA1LE_0RA0LF_0LE0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 4 11.
Time Qed.
End TM2367.


Module TM2368.
Definition tm := TM_from_str "1RB0RF_1LC1RD_1RE1RB_1RC---_1LF1LA_1RA0LE".
Definition tm' := TM_from_str "1RB1RE_1LC1LD_1RD0LB_1RE0RC_1LA1RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 20 12.
Time Qed.
End TM2368.


Module TM2369.
Definition tm := TM_from_str "1LB0LD_1RC0LA_1RD1LC_0LF0RE_1RD1RE_---1LB".
Definition tm' := TM_from_str "1RB1LA_0LC0RE_---1LD_1RA0LF_1RB1RE_1LD0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDABEC") 1 3.
Time Qed.
End TM2369.


Module TM2370.
Definition tm := TM_from_str "1LB1LC_0LC0RC_1RD1LE_0RA0LB_0LD0LF_0RE---".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD1LA_0LA0RA_0LB0LF_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 21 39.
Time Qed.
End TM2370.


Module TM2371.
Definition tm := TM_from_str "1LB0RC_1LC0RA_1RD0LD_0RB0LE_---0LF_1RF0RA".
Definition tm' := TM_from_str "1RB0LB_0RC0LD_1LA0RF_---0LE_1RE0RF_1LC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCABDE") 1 8.
Time Qed.
End TM2371.


Module TM2372.
Definition tm := TM_from_str "1LB1RE_1RC1LA_1LD0RC_0LA1RE_1RF0RD_---0LE".
Definition tm' := TM_from_str "1RB1LE_1LC0RB_0LE1RD_1RF0RC_1LA1RD_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 8 3.
Time Qed.
End TM2372.


Module TM2373.
Definition tm := TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0LA_0LE1RF".
Definition tm' := TM_from_str "1RB1RC_0LC0LC_1RE1LD_0LB1RD_0RF---_0RA0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEFABD") 22 39.
Time Qed.
End TM2373.


Module TM2374.
Definition tm := TM_from_str "1RB1RA_1RC1LD_1LC0LA_---0LE_0LD0LF_0RA1RF".
Definition tm' := TM_from_str "1RB1LD_1LB0LC_1RA1RC_---0LE_0LD0LF_0RC1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 10 3.
Time Qed.
End TM2374.


Module TM2375.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD1RA_0RA0LA_0RB1RF_1RA---".
Definition tm' := TM_from_str "1RB---_1LC1RF_0LE0RD_0RB0LB_1RD1RB_0RC1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEDFA") 1 5.
Time Qed.
End TM2375.


Module TM2376.
Definition tm := TM_from_str "1LB0RD_1LC1LB_1RA1RE_---1RA_1RC0LF_1RB1LE".
Definition tm' := TM_from_str "1RB0LF_1RC1RA_1LD0RE_1LB1LD_---1RC_1RD1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBEAF") 24 26.
Time Qed.
End TM2376.


Module TM2377.
Definition tm := TM_from_str "1RB0LD_0LC1RE_1RD0RB_1LA1RD_1RF0RC_---0RC".
Definition tm' := TM_from_str "1RB0RD_1LC1RB_1RD0LB_0LA1RE_1RF0RA_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 5 1.
Time Qed.
End TM2377.


Module TM2378.
Definition tm := TM_from_str "1RB1LE_0RC0RF_0LD0RE_1LA---_0LA0LB_1RB1RD".
Definition tm' := TM_from_str "1RB1RD_0RC0RA_0LD0RF_1LE---_1RB1LF_0LE0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM2378.


Module TM2379.
Definition tm := TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RF_0RB0RF_0LC---".
Definition tm' := TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA0RB_0RD0RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 35 21.
Time Qed.
End TM2379.


Module TM2380.
Definition tm := TM_from_str "1RB1LF_0LC0RB_1RB1RD_1LE---_1LA1RE_1LD0LA".
Definition tm' := TM_from_str "1RB1RC_0LA0RB_1LD---_1LE1RD_1RB1LF_1LC0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM2380.


Module TM2381.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LA_1LC---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM2381.


Module TM2382.
Definition tm := TM_from_str "1LB1RA_1RC1LE_1RA0RD_0LB0RD_1LF0LB_1LA---".
Definition tm' := TM_from_str "1RB0RF_1LC1RB_1RA1LD_1LE0LC_1LB---_0LC0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAFDE") 22 21.
Time Qed.
End TM2382.


Module TM2383.
Definition tm := TM_from_str "1RB0LC_1RC0RB_1LD---_1RE0RA_1LF0RF_1RD1LA".
Definition tm' := TM_from_str "1RB0RA_1LC---_1RE0RD_1RA0LB_1LF0RF_1RC1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 5 1.
Time Qed.
End TM2383.


Module TM2384.
Definition tm := TM_from_str "1LB0RE_1RC1LD_1RA0LD_1LC0LC_0RA0RF_---0RD".
Definition tm' := TM_from_str "1RB0LD_1LC0RE_1RA1LD_1LA0LA_0RB0RF_---0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 5 1.
Time Qed.
End TM2384.


Module TM2385.
Definition tm := TM_from_str "1LB1RD_1LC0LE_0RC1RA_0RB0RF_0LC1LF_1RD---".
Definition tm' := TM_from_str "1RB---_0RC0RA_1LD0LF_0RD1RE_1LC1RB_0LD1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDBFA") 2 21.
Time Qed.
End TM2385.


Module TM2386.
Definition tm := TM_from_str "1LB0RF_0RC0LB_1RA1RD_1RE0RE_1RC1LE_1RD---".
Definition tm' := TM_from_str "1RB---_1RC0RC_1RD1LC_1RE1RB_1LF0RA_0RD0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDBCA") 3 1.
Time Qed.
End TM2386.


Module TM2387.
Definition tm := TM_from_str "1LB1RE_1LC0LE_0RD---_1RA0RD_1RD0LF_1LA1LE".
Definition tm' := TM_from_str "1RB0RA_1LC1RD_1LF0LD_1RA0LE_1LB1LD_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFADE") 6 1.
Time Qed.
End TM2387.


Module TM2388.
Definition tm := TM_from_str "1LB1LE_1RC0LC_0LA0RD_1RB0RF_0LC1LE_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0LC_0LD0RF_1LB1LE_0LC1LE_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCFEA") 17 1.
Time Qed.
End TM2388.


Module TM2389.
Definition tm := TM_from_str "1LB1RD_1LC0LB_0LD0RF_1RE1LC_1RA0RE_---1RC".
Definition tm' := TM_from_str "1RB0RA_1LC1RE_1LD0LC_0LE0RF_1RA1LD_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 17 4.
Time Qed.
End TM2389.


Module TM2390.
Definition tm := TM_from_str "1RB1RF_0LC0LE_1RA0LD_1RC0LE_---1LF_0RA0LD".
Definition tm' := TM_from_str "1RB0LE_1RC0LA_1RD1RF_0LB0LE_---1LF_0RC0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBAEF") 4 1.
Time Qed.
End TM2390.


Module TM2391.
Definition tm := TM_from_str "1LB0RF_0RC0LB_1RD0RD_1RE1LD_1RA1RC_1RA---".
Definition tm' := TM_from_str "1RB1LA_1RC1RE_1LD0RF_0RE0LD_1RA0RA_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 4 1.
Time Qed.
End TM2391.


Module TM2392.
Definition tm := TM_from_str "1LB1LF_0RC0LB_1RE1RD_1RA---_0RA0LF_1RC0LE".
Definition tm' := TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB0LF_1RD0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 1 9.
Time Qed.
End TM2392.


Module TM2393.
Definition tm := TM_from_str "1RB0RD_1RC1RF_1LD0RB_0RC0LE_1LA1LD_1RB---".
Definition tm' := TM_from_str "1RB---_1RC1RA_1LD0RB_0RC0LE_1LF1LD_1RB0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2393.


Module TM2394.
Definition tm := TM_from_str "1LB---_1RC1LB_1LA1RD_1RE0RC_1LF0RA_1RA0LF".
Definition tm' := TM_from_str "1RB0RF_1LC0RD_1RD0LC_1LE---_1RF1LE_1LD1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 17 18.
Time Qed.
End TM2394.


Module TM2395.
Definition tm := TM_from_str "1LB0RE_0RC1LD_1RC1RA_0LC0LD_1RD0RF_---0RA".
Definition tm' := TM_from_str "1RB0RF_0LC0LB_1RC1RD_1LE0RA_0RC1LB_---0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECBAF") 2 2.
Time Qed.
End TM2395.


Module TM2396.
Definition tm := TM_from_str "1RB0LC_0LB1LA_1RD0LA_0RE1RF_1LC0RC_0RA---".
Definition tm' := TM_from_str "1RB0LE_0RC1RD_1LA0RA_0RE---_1RF0LA_0LF1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 495 478.
Time Qed.
End TM2396.


Module TM2397.
Definition tm := TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA1LB_0RB1RD_0RA---".
Definition tm' := TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RF_0RD1RB_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 30 22.
Time Qed.
End TM2397.


Module TM2398.
Definition tm := TM_from_str "1LB---_0LC1LE_0LD1LF_1RE0RA_1RF0RE_0RB0RD".
Definition tm' := TM_from_str "1RB0RA_0RC0RE_0LD1LA_0LE1LB_1RA0RF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDEAB") 1 6.
Time Qed.
End TM2398.


Module TM2399.
Definition tm := TM_from_str "1RB1LC_0LA0RD_1LA0LC_0LF1RE_1RD0RE_---0RB".
Definition tm' := TM_from_str "1RB0RA_0LC1RA_---0RD_0LE0RB_1RD1LF_1LE0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDFBAC") 1 5.
Time Qed.
End TM2399.


Module TM2400.
Definition tm := TM_from_str "1RB---_0RC1RF_1RD1RF_1LE1LF_0RA0LE_1RC0LD".
Definition tm' := TM_from_str "1RB0LC_1RC1RA_1LD1LA_0RE0LD_1RF---_0RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 25 19.
Time Qed.
End TM2400.


Module TM2401.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_1LA---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM2401.


Module TM2402.
Definition tm := TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_1RC1LF_0LB1LA".
Definition tm' := TM_from_str "1RB1LE_1LC1RB_0LA1RD_0RB0LC_0LD1LF_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDBCAE") 1 5.
Time Qed.
End TM2402.


Module TM2403.
Definition tm := TM_from_str "1RB1LF_1RC0RB_0LC1LD_0LF1LE_1RB1LE_0LA---".
Definition tm' := TM_from_str "1RB1LA_1RC0RB_0LC1LD_0LE1LA_0LF---_1RB1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2403.


Module TM2404.
Definition tm := TM_from_str "1RB---_1LC1RA_1RD0RC_1LE0RC_0LF0LD_0RA0LD".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_0LD0LB_0RE0LB_1RF---_1LA1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 5 1.
Time Qed.
End TM2404.


Module TM2405.
Definition tm := TM_from_str "1LB0RB_0LC1RF_1RD1LE_0RA0LB_0LD1LB_0RA---".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0RD_0LA1RF_0LB1LD_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 22 30.
Time Qed.
End TM2405.


Module TM2406.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA0RC_1LE0LD_0LF0LE_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RB_1LD0RC_1RB1LE_1LF0LE_0LA0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM2406.


Module TM2407.
Definition tm := TM_from_str "1RB---_1LC0RD_0LD0LC_1RE0LF_0RF0RA_1RB0RC".
Definition tm' := TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2407.


Module TM2408.
Definition tm := TM_from_str "1LB1RF_0RC0LB_1LD1RB_1RE---_1RA1LE_1RD0RA".
Definition tm' := TM_from_str "1RB1LA_1LC1RF_0RD0LC_1LE1RC_1RA---_1RE0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 8 7.
Time Qed.
End TM2408.


Module TM2409.
Definition tm := TM_from_str "1RB1LC_0LB1LA_1RD0LE_0RD0RA_1LF0LC_1RA---".
Definition tm' := TM_from_str "1RB---_1RC1LD_0LC1LB_1RE0LF_0RE0RB_1LA0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 4 3.
Time Qed.
End TM2409.


Module TM2410.
Definition tm := TM_from_str "1LB0LF_0RC0LB_1RF1RD_0LD0RE_1RF---_1LA0RB".
Definition tm' := TM_from_str "1RB---_1LC0RD_1LD0LB_0RE0LD_1RB1RF_0LF0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 6 1.
Time Qed.
End TM2410.


Module TM2411.
Definition tm := TM_from_str "1LB---_0LC1RE_1LD0LF_1LE1LF_1RB0RE_0RA1LC".
Definition tm' := TM_from_str "1RB0RA_0LC1RA_1LF0LD_0RE1LC_1LB---_1LA1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFAD") 1 5.
Time Qed.
End TM2411.


Module TM2412.
Definition tm := TM_from_str "1LB1RF_1RC1LC_0RD0RC_1RA0LE_0LA0RB_0LD---".
Definition tm' := TM_from_str "1RB1LB_0RC0RB_1RD0LE_1LA1RF_0LD0RA_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 5 302.
Time Qed.
End TM2412.


Module TM2413.
Definition tm := TM_from_str "1LB1LA_1RC0RD_1RE0LD_1LA0LC_0RF---_0RD0RB".
Definition tm' := TM_from_str "1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFADBC") 5 1.
Time Qed.
End TM2413.


Module TM2414.
Definition tm := TM_from_str "1RB---_1LC0RB_1LF1LD_1RE1RB_0LC0RE_0LD0LA".
Definition tm' := TM_from_str "1RB1RF_0LC0RB_1LD1LA_0LA0LE_1RF---_1LC0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCABD") 11 10.
Time Qed.
End TM2414.


Module TM2415.
Definition tm := TM_from_str "1LB0LA_1LC1LA_1RD0RC_1RF0RE_1LA1RC_1RE---".
Definition tm' := TM_from_str "1RB0RA_1RC0RD_1RD---_1LE1RA_1LF0LE_1LA1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABDC") 424 405.
Time Qed.
End TM2415.


Module TM2416.
Definition tm := TM_from_str "1LB1RF_1RC0LC_1RD0LB_1LE0LD_---0RA_1RA1LD".
Definition tm' := TM_from_str "1RB0LF_1LC0LB_---0RD_1LF1RE_1RD1LB_1RA0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFABCE") 5 1.
Time Qed.
End TM2416.


Module TM2417.
Definition tm := TM_from_str "1LB---_0LC0RE_1LD0RF_1RB0LF_1RC1LB_0RB1RA".
Definition tm' := TM_from_str "1RB1LE_1LC0RD_1RE0LD_0RE1RF_0LB0RA_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEBCAD") 1 4.
Time Qed.
End TM2417.


Module TM2418.
Definition tm := TM_from_str "1RB0LE_1RC---_1RD1RC_1LA0RA_0RB0LF_1RD1LF".
Definition tm' := TM_from_str "1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEABDF") 2 6.
Time Qed.
End TM2418.


Module TM2419.
Definition tm := TM_from_str "1LB0LB_0RC0LA_1RE1RD_0RE---_1RF0RC_1LA1RF".
Definition tm' := TM_from_str "1RB1RF_1RC0RA_1LD1RC_1LE0LE_0RA0LD_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 2008 2206.
Time Qed.
End TM2419.


Module TM2420.
Definition tm := TM_from_str "1RB0RD_0RC0LF_1LD1RF_1LE0RE_1RB0LE_---1RA".
Definition tm' := TM_from_str "1RB0LA_0RC0LE_1LD1RE_1LA0RA_---1RF_1RB0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2420.


Module TM2421.
Definition tm := TM_from_str "1RB0LF_1LC0RE_---1LD_1LA1LB_1RB1LA_1LA0LE".
Definition tm' := TM_from_str "1RB1LE_1LC0RA_---1LD_1LE1LB_1RB0LF_1LE0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2421.


Module TM2422.
Definition tm := TM_from_str "1RB1LE_1RC---_1RD1LE_1LE1RA_0LF0RA_0RA0LE".
Definition tm' := TM_from_str "1RB---_1RC1LD_1LD1RE_0LF0RE_1RA1LD_0RE0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 13 4.
Time Qed.
End TM2422.


Module TM2423.
Definition tm := TM_from_str "1LB0RE_1RC1RC_0RA1LD_0LC1LC_---1RF_0LC1RA".
Definition tm' := TM_from_str "1RB1RB_0RC1LD_1LA0RE_0LB1LB_---1RF_0LB1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 21 4.
Time Qed.
End TM2423.


Module TM2424.
Definition tm := TM_from_str "1RB1RE_1LC0LA_1LD0LC_1RA0RF_1RD---_1RB1RB".
Definition tm' := TM_from_str "1RB1RB_1LC0LE_1LD0LC_1RE0RA_1RB1RF_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM2424.


Module TM2425.
Definition tm := TM_from_str "1RB---_1LC0RC_0RE0LD_1LC1LD_0LB1RF_1RB0RA".
Definition tm' := TM_from_str "1RB0RF_1LC0RC_0RE0LD_1LC1LD_0LB1RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2425.


Module TM2426.
Definition tm := TM_from_str "1RB1RC_1LC0RF_1RE0LD_1LC1RB_---1RA_1RB0RD".
Definition tm' := TM_from_str "1RB0RD_1LC0RA_1RE0LD_1LC1RB_---1RF_1RB1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2426.


Module TM2427.
Definition tm := TM_from_str "1LB0RE_0LC0LA_0LD1LC_1RE0LF_1RA0RD_1LE---".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE1LD_1RA0LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 278 253.
Time Qed.
End TM2427.


Module TM2428.
Definition tm := TM_from_str "1RB1LF_1LC0RC_0RD0LC_0RE---_1RA1RE_1RE1LF".
Definition tm' := TM_from_str "1RB1LA_1RC1RB_1RD1LA_1LE0RE_0RF0LE_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 6 1.
Time Qed.
End TM2428.


Module TM2429.
Definition tm := TM_from_str "1LB1LC_1RC0RF_1LE0RD_1RE1RA_1RB0RA_---0LA".
Definition tm' := TM_from_str "1RB0RE_1LC0RF_1RA0RD_1LA1LB_---0LD_1RC1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABFCE") 1 12.
Time Qed.
End TM2429.


Module TM2430.
Definition tm := TM_from_str "1LB0LA_1LC0LE_1RD0RF_1LA1RE_0LC0LC_1RC---".
Definition tm' := TM_from_str "1RB---_1RC0RA_1LD1RF_1LE0LD_1LB0LF_0LB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 34 39.
Time Qed.
End TM2430.


Module TM2431.
Definition tm := TM_from_str "1LB1LE_0RC0LD_1LD1RC_0LA1RB_0LB0LF_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_1LB1LF_0LB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 7 1.
Time Qed.
End TM2431.


Module TM2432.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB1RF_1LC1LF_0LA---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC1RF_0LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM2432.


Module TM2433.
Definition tm := TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA0LD_0RB1RC_0RA---".
Definition tm' := TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RF_0RD1RA_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 80 206.
Time Qed.
End TM2433.


Module TM2434.
Definition tm := TM_from_str "1RB0RF_1LC1RA_1RD0LC_1LE---_1RB1LE_1RC1RA".
Definition tm' := TM_from_str "1RB1RF_1RC0LB_1LD---_1RE1LD_1LB1RF_1RE0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEBCDA") 5 4.
Time Qed.
End TM2434.


Module TM2435.
Definition tm := TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LA---_1RB0RF_1RC1RE".
Definition tm' := TM_from_str "1RB1RF_1RC0LB_1LD---_1RE1LD_1LB1RF_1RE0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 5 4.
Time Qed.
End TM2435.


Module TM2436.
Definition tm := TM_from_str "1LB1RF_1RC1LC_0RE0LD_0RB0LC_1RF---_1RA0LF".
Definition tm' := TM_from_str "1RB---_1RC0LB_1LD1RB_1RE1LE_0RA0LF_0RD0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 6 1.
Time Qed.
End TM2436.


Module TM2437.
Definition tm := TM_from_str "1RB0RE_0LC1LE_0RD0LB_1RA0RD_1LF0RD_1LB---".
Definition tm' := TM_from_str "1RB0RA_1RC0RE_0LD1LE_0RA0LC_1LF0RA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 6 1.
Time Qed.
End TM2437.


Module TM2438.
Definition tm := TM_from_str "1RB1RF_0LC1LB_1RD1LA_0RE0RD_1RA1RD_---0LC".
Definition tm' := TM_from_str "1RB1RF_1RC1RE_0LD1LC_1RF1LB_---0LD_0RA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDFAE") 2 6.
Time Qed.
End TM2438.


Module TM2439.
Definition tm := TM_from_str "1LB---_0LC0RD_1RB1LC_1RE1LB_0RB0RF_0RB1RA".
Definition tm' := TM_from_str "1RB1LC_0RC0RE_0LD0RA_1RC1LD_0RC1RF_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDABE") 4 11.
Time Qed.
End TM2439.


Module TM2440.
Definition tm := TM_from_str "1RB1RC_1RC0RA_0LD1RA_---0LE_0RA1LF_1RC1LD".
Definition tm' := TM_from_str "1RB0RE_0LC1RE_---0LD_0RE1LF_1RA1RB_1RB1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 5.
Time Qed.
End TM2440.


Module TM2441.
Definition tm := TM_from_str "1RB---_1RC0RB_1LD1RC_1RB1LE_1LC1LF_0LA0LD".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LC1LE_0LF0LA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM2441.


Module TM2442.
Definition tm := TM_from_str "1RB0LA_1LC1RE_1RD1LD_0RE1RA_0RB1RF_---0RE".
Definition tm' := TM_from_str "1RB1LB_0RC1RE_0RD1RF_1LA1RC_1RD0LE_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDABCF") 6 2.
Time Qed.
End TM2442.


Module TM2443.
Definition tm := TM_from_str "1LB0RF_1RC0LB_0LE0RD_1RA---_1RD1LB_0RC1RF".
Definition tm' := TM_from_str "1RB0LA_0LC0RD_1RD1LA_1RE---_1LA0RF_0RB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABDCF") 1 3.
Time Qed.
End TM2443.


Module TM2444.
Definition tm := TM_from_str "1RB0RB_1LC0RA_1RF0LD_1LE1LD_0LC1RE_0LB---".
Definition tm' := TM_from_str "1RB0LE_0LC---_1LA0RD_1RC0RC_1LF1LE_0LA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCAEFB") 1 4.
Time Qed.
End TM2444.


Module TM2445.
Definition tm := TM_from_str "1RB1LC_1LC0RA_1RB1LD_1LE1LF_0LB0LD_---0RE".
Definition tm' := TM_from_str "1RB1LC_1LA0RE_1LD1LF_0LB0LC_1RB1LA_---0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM2445.


Module TM2446.
Definition tm := TM_from_str "1LB---_1RC0LF_1LE1RD_0RB0LB_0RC0LE_1RB0LA".
Definition tm' := TM_from_str "1RB0LE_1LC1RD_0RB0LC_0RA0LA_1RA0LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABDCE") 101 42.
Time Qed.
End TM2446.


Module TM2447.
Definition tm := TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA1LF".
Definition tm' := TM_from_str "1RB1LA_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 17 15.
Time Qed.
End TM2447.


Module TM2448.
Definition tm := TM_from_str "1RB0RD_1RC1RA_1LD0RB_1RF0LE_1LA1LD_---0LB".
Definition tm' := TM_from_str "1RB1RE_1LC0RA_1RF0LD_1LE1LC_1RA0RC_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 32 16.
Time Qed.
End TM2448.


Module TM2449.
Definition tm := TM_from_str "1LB0LF_1RC1LD_1RA1RC_1LA1LE_1RD0LB_---0RC".
Definition tm' := TM_from_str "1RB1LD_1RC1RB_1LA0LF_1LC1LE_1RD0LA_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 7 7.
Time Qed.
End TM2449.


Module TM2450.
Definition tm := TM_from_str "1RB0RE_0RC1LD_0LD---_1LE1RF_1RD0LB_1RA0RF".
Definition tm' := TM_from_str "1RB0LC_1LA1RE_0RD1LB_0LB---_1RF0RE_1RC0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDBAE") 3 1.
Time Qed.
End TM2450.


Module TM2451.
Definition tm := TM_from_str "1LB0RF_1LC0LA_1RD0LB_0RE0RC_0RA0RE_1RE---".
Definition tm' := TM_from_str "1RB---_0RC0RB_1LD0RA_1LE0LC_1RF0LD_0RB0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFBA") 93 97.
Time Qed.
End TM2451.


Module TM2452.
Definition tm := TM_from_str "1LB0LC_0LC1LA_1RD0LF_0RD0RE_1RB0LE_0LA---".
Definition tm' := TM_from_str "1RB0LA_0LC1LE_1RF0LD_0LE---_1LB0LC_0RF0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFAD") 1 5.
Time Qed.
End TM2452.


Module TM2453.
Definition tm := TM_from_str "1RB---_0RC1RB_1LC1RD_1RA0LE_1RB0LF_0RD1LF".
Definition tm' := TM_from_str "1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2453.


Module TM2454.
Definition tm := TM_from_str "1RB0LE_1LC0RD_1LA0LC_1RB0RD_1LF---_1LB1RC".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1LD0LC_1RB0LE_1LF---_1LB1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM2454.


Module TM2455.
Definition tm := TM_from_str "1LB1RE_1RC1LA_1LD0RC_0LA1LA_0RF0RA_---0LC".
Definition tm' := TM_from_str "1RB1LD_1LC0RB_0LD1LD_1LA1RE_0RF0RD_---0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 8 1.
Time Qed.
End TM2455.


Module TM2456.
Definition tm := TM_from_str "1LB1RE_1RC0LD_0LB0RC_1LA1LD_1RF1RE_0LD---".
Definition tm' := TM_from_str "1RB1RA_0LC---_1LD1LC_1LE1RA_1RF0LC_0LE0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFCAB") 7 2.
Time Qed.
End TM2456.


Module TM2457.
Definition tm := TM_from_str "1RB1RE_1RC---_1LD1LC_0RE0LD_1RF0RA_1RC0LA".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFCDAB") 2 2.
Time Qed.
End TM2457.


Module TM2458.
Definition tm := TM_from_str "1RB1LD_0RC1RC_1RD0RD_1LE1LA_0RF0LE_1RB---".
Definition tm' := TM_from_str "1RB---_0RC1RC_1RD0RD_1LE1LF_0RA0LE_1RB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2458.


Module TM2459.
Definition tm := TM_from_str "1LB1RA_0RA0LC_1LD1RB_0RE0LE_0LB1LF_1RA---".
Definition tm' := TM_from_str "1RB---_1LC1RB_0RB0LD_1LE1RC_0RF0LF_0LC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 3 1.
Time Qed.
End TM2459.


Module TM2460.
Definition tm := TM_from_str "1RB0RA_0LC0LE_1RD0LD_0RE1LC_1RA1LF_1LD---".
Definition tm' := TM_from_str "1RB0LB_0RC1LA_1RD1LF_1RE0RD_0LA0LC_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 18 1.
Time Qed.
End TM2460.


Module TM2461.
Definition tm := TM_from_str "1RB1LF_1RC0RB_0LC1LD_0LF1LE_1RB1RC_0LA---".
Definition tm' := TM_from_str "1RB1RC_1RC0RB_0LC1LD_0LE1LA_0LF---_1RB1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2461.


Module TM2462.
Definition tm := TM_from_str "1RB1LF_1LC1RA_1RD0LC_0RB1LE_---0RB_0LE0LF".
Definition tm' := TM_from_str "1RB0LA_0RC1LD_1LA1RE_---0RC_1RC1LF_0LD0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECABDF") 5 6.
Time Qed.
End TM2462.


Module TM2463.
Definition tm := TM_from_str "1RB0LF_1LB0LC_1RD0LA_0RE0RD_0LB1LC_---0LC".
Definition tm' := TM_from_str "1RB0LE_0RC0RB_0LD1LA_1LD0LA_1RD0LF_---0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDABCF") 1 3.
Time Qed.
End TM2463.


Module TM2464.
Definition tm := TM_from_str "1RB0LA_1LC0RB_0LD1LA_0RE---_1RE1RF_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LE1LD_1RB0LD_0RF---_1RF1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM2464.


Module TM2465.
Definition tm := TM_from_str "1RB1LA_1LC0RC_1RD0RD_1LE1RD_---0LF_0RB0LA".
Definition tm' := TM_from_str "1RB0RB_1LC1RB_---0LD_0RE0LF_1LA0RA_1RE1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FEABCD") 4 1.
Time Qed.
End TM2465.


Module TM2466.
Definition tm := TM_from_str "1LB---_1RC0LD_1LD0RC_0LE1LB_0RB1LF_0LB1LA".
Definition tm' := TM_from_str "1RB0LC_1LC0RB_0LD1LA_0RA1LE_0LA1LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 729 705.
Time Qed.
End TM2466.


Module TM2467.
Definition tm := TM_from_str "1LB1RE_1LC1RD_0RB0LC_1LC0RA_1RA0LF_---1LE".
Definition tm' := TM_from_str "1RB0LF_1LC1RA_1LE1RD_1LE0RB_0RC0LE_---1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCEDAF") 3 2.
Time Qed.
End TM2467.


Module TM2468.
Definition tm := TM_from_str "1RB1LE_1RC1LF_1RD0RC_0LE0LB_---0LA_0RF1LA".
Definition tm' := TM_from_str "1RB0RA_0LC0LE_---0LD_1RE1LC_1RA1LF_0RF1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM2468.


Module TM2469.
Definition tm := TM_from_str "1RB0LF_1LC1RB_1RE1LD_1LB0LC_1LA0RE_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1RB_1RE1LD_1LB0LC_1LF0RE_1RB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2469.


Module TM2470.
Definition tm := TM_from_str "1RB0LD_1RC1RD_0LD1LF_0RF1RE_0LA---_1LE0RB".
Definition tm' := TM_from_str "1RB1RC_0LC1LF_0RF1RD_0LE---_1RA0LC_1LD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 6 2.
Time Qed.
End TM2470.


Module TM2471.
Definition tm := TM_from_str "1RB0LC_1LA0LD_1LB1LE_0LA1RE_0RF---_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_1LC0LE_1RB0LD_1LB1LF_0LC1RF_0RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM2471.


Module TM2472.
Definition tm := TM_from_str "1LB0RF_0LC0RE_1LD---_1RB0LF_1RA1LB_0RB1RC".
Definition tm' := TM_from_str "1RB1LC_1LC0RF_0LD0RA_1LE---_1RC0LF_0RC1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 1 4.
Time Qed.
End TM2472.


Module TM2473.
Definition tm := TM_from_str "1RB0RF_1RC0LC_0LD0RA_1LB1LE_0LC1LE_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0LC_0LD0RF_1LB1LE_0LC1LE_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2473.


Module TM2474.
Definition tm := TM_from_str "1LB0LE_1RC0RB_1LE0LD_---1RB_1RB1LF_1LC1LA".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LF_1LC1LE_1LB0LA_---1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFAD") 4 1.
Time Qed.
End TM2474.


Module TM2475.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LA_1LD---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC0RF_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM2475.


Module TM2476.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_1RF---_1RA0LD".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEFB") 951 982.
Time Qed.
End TM2476.


Module TM2477.
Definition tm := TM_from_str "1LB0RA_1RC0LD_1LE0RD_0LE1LF_0RB0LA_1RE---".
Definition tm' := TM_from_str "1RB---_0RC0LE_1RD0LF_1LB0RF_1LC0RE_0LB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDFBA") 4 1.
Time Qed.
End TM2477.


Module TM2478.
Definition tm := TM_from_str "1RB0LF_1RC0RD_1RD1RE_0LE0LB_0RC0LA_---1LE".
Definition tm' := TM_from_str "1RB1RC_0LC0LE_0RA0LD_1RE0LF_1RA0RB_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM2478.


Module TM2479.
Definition tm := TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RB---".
Definition tm' := TM_from_str "1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2479.


Module TM2480.
Definition tm := TM_from_str "1RB1RA_0LC0RB_1RB1LD_0LE1LF_1LA---_1LA1LD".
Definition tm' := TM_from_str "1RB1LC_0LA0RB_0LD1LF_1LE---_1RB1RE_1LE1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM2480.


Module TM2481.
Definition tm := TM_from_str "1LB0RF_0RC0LC_1LE1RD_1LB0RB_1RA0LD_1RC---".
Definition tm' := TM_from_str "1RB0LF_1LC0RE_0RD0LD_1LA1RF_1RD---_1LC0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDFAE") 4 2.
Time Qed.
End TM2481.


Module TM2482.
Definition tm := TM_from_str "1RB1LC_1RC0LE_1LD1RE_1LB0LD_1RF0RC_1RA---".
Definition tm' := TM_from_str "1RB---_1RC1LD_1RD0LF_1LE1RF_1LC0LE_1RA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 12 14.
Time Qed.
End TM2482.


Module TM2483.
Definition tm := TM_from_str "1RB---_1RC0RB_1LD0LF_1RB1LE_1LC0LD_0LA1RB".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 1 1.
Time Qed.
End TM2483.


Module TM2484.
Definition tm := TM_from_str "1RB1RE_1LC1RF_1RA0LD_0LB0LD_0RC---_0LF0LA".
Definition tm' := TM_from_str "1RB0LD_1RC1RE_1LA1RF_0LC0LD_0RA---_0LF0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 9 15.
Time Qed.
End TM2484.


Module TM2485.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_0LE---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM2485.


Module TM2486.
Definition tm := TM_from_str "1RB---_1LC0RB_0LD1LD_1RE1LF_1RB1RC_0RA0LF".
Definition tm' := TM_from_str "1RB1RC_1LC0RB_0LD1LD_1RA1LE_0RF0LE_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2486.


Module TM2487.
Definition tm := TM_from_str "1RB1LF_1RC0RB_0LD0LA_0LE0LE_0RA1LD_1LE---".
Definition tm' := TM_from_str "1RB0RA_0LC0LE_0LD0LD_0RE1LC_1RA1LF_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 5.
Time Qed.
End TM2487.


Module TM2488.
Definition tm := TM_from_str "1LB0RD_1LC1RD_1RD0LB_0RA0RE_1RF0LD_---1LD".
Definition tm' := TM_from_str "1RB0LD_0RC0RE_1LD0RB_1LA1RB_1RF0LB_---1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 5 1.
Time Qed.
End TM2488.


Module TM2489.
Definition tm := TM_from_str "1RB1LF_0LC0RC_0RA1LD_0LE---_1LA0LE_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_0LC0RC_0RF1LD_0LE---_1LF0LE_1RB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2489.


Module TM2490.
Definition tm := TM_from_str "1LB0LD_1RC0RE_1LF1RD_0LB0LB_1RB---_1LA0LF".
Definition tm' := TM_from_str "1RB---_1RC0RA_1LD1RF_1LE0LD_1LB0LF_0LB0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFAD") 33 39.
Time Qed.
End TM2490.


Module TM2491.
Definition tm := TM_from_str "1RB0LA_1LC1RA_1RD1LC_1LA1RE_1RF0RD_1RC---".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RF_1RE0LD_1LB1RD_1RA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEBCFA") 1 20.
Time Qed.
End TM2491.


Module TM2492.
Definition tm := TM_from_str "1RB0RB_1LC0RE_1RB1LD_0LB0LF_1RA0RA_1LD---".
Definition tm' := TM_from_str "1RB1LC_1LA0RD_0LB0LF_1RE0RE_1RB0RB_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBACDF") 1 1.
Time Qed.
End TM2492.


Module TM2493.
Definition tm := TM_from_str "1RB0LC_1LA1RB_1RD1LC_1RA1RE_1RF0RB_---1RE".
Definition tm' := TM_from_str "1RB1LA_1RC1RE_1RD0LA_1LC1RD_1RF0RD_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 31 19.
Time Qed.
End TM2493.


Module TM2494.
Definition tm := TM_from_str "1RB0RD_1LC1LF_0RA1LB_0LF0RE_---1RA_1RB0LB".
Definition tm' := TM_from_str "1RB0LB_1LC1LA_0RD1LB_1RB0RE_0LA0RF_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 1.
Time Qed.
End TM2494.


Module TM2495.
Definition tm := TM_from_str "1LB1LE_1RC1LA_1RD1RC_1RA0LF_---1RF_1LD0RD".
Definition tm' := TM_from_str "1RB1LD_1RC1RB_1RD0LF_1LA1LE_---1RF_1LC0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 185 193.
Time Qed.
End TM2495.


Module TM2496.
Definition tm := TM_from_str "1LB1LF_0RC0LD_1RD1RC_0LE1RB_---0LA_1LA0LA".
Definition tm' := TM_from_str "1RB1RA_0LC1RE_---0LD_1LE1LF_0RA0LB_1LD0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM2496.


Module TM2497.
Definition tm := TM_from_str "1RB---_1RC0RA_0LD0LF_1RF0LE_1LF1LD_1RA1LC".
Definition tm' := TM_from_str "1RB0LF_1RC1LE_1RD---_1RE0RC_0LA0LB_1LB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEAFB") 20 11.
Time Qed.
End TM2497.


Module TM2498.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RA_1RF1LF_1LC---".
Definition tm' := TM_from_str "1RB1LB_1LC---_1RD0RA_1LF1RE_1RC0RD_1LC0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DFCEAB") 2 5.
Time Qed.
End TM2498.


Module TM2499.
Definition tm := TM_from_str "1LB1LA_1RC1RB_0LD0RC_1LA0LE_1LF1LD_1LC---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_1LE1LC_1LB---_1LA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 559 308.
Time Qed.
End TM2499.


Module TM2500.
Definition tm := TM_from_str "1RB0RB_1LC1RD_1RE0LD_1LC1LE_0LF0RA_---1RD".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_---1RD_1LA1LB_1RF0RF_1LA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFADBC") 2 4.
Time Qed.
End TM2500.


Module TM2501.
Definition tm := TM_from_str "1RB1RC_0LC0RD_1RE1LD_0LB0LF_0RF---_0RA0RE".
Definition tm' := TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0RF_0LE0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 42 21.
Time Qed.
End TM2501.


Module TM2502.
Definition tm := TM_from_str "1LB1RF_0LC1RB_1RA0LD_---1LE_0RF1LC_0RB1RF".
Definition tm' := TM_from_str "1RB0LD_1LC1RF_0LA1RC_---1LE_0RF1LA_0RC1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 6 14.
Time Qed.
End TM2502.


Module TM2503.
Definition tm := TM_from_str "1RB---_1LC1LE_1LD1RC_1RF1LB_0LA0LD_1RC0RF".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LC1LE_0LF0LA_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDCAEB") 4 2.
Time Qed.
End TM2503.


Module TM2504.
Definition tm := TM_from_str "1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RA_1RB---".
Definition tm' := TM_from_str "1RB---_0RC0RE_1RD1RA_1LE0LD_1RB0LF_1LD0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM2504.


Module TM2505.
Definition tm := TM_from_str "1RB1RB_1LC0RE_---0LD_1LA1LF_1RF1RA_1LD0LB".
Definition tm' := TM_from_str "1RB1RD_1LC0LE_1LD1LB_1RE1RE_1LF0RA_---0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFCAB") 18 9.
Time Qed.
End TM2505.


Module TM2506.
Definition tm := TM_from_str "1RB0LC_1LA1RB_0RB0LD_1RE1LD_---0RF_1RB0RB".
Definition tm' := TM_from_str "1RB0RB_1LC1RB_1RB0LD_0RB0LE_1RF1LE_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEFA") 1 1.
Time Qed.
End TM2506.


Module TM2507.
Definition tm := TM_from_str "1RB0RC_1RC0RF_1LD1RA_1RE0LD_1LB1RD_---1LE".
Definition tm' := TM_from_str "1RB0LA_1LC1RA_1RE0RD_---1LB_1LA1RF_1RC0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCEABD") 22 1.
Time Qed.
End TM2507.


Module TM2508.
Definition tm := TM_from_str "1RB0RA_0LC0LE_0LD0RB_0RE1LC_1RA1LF_1LD---".
Definition tm' := TM_from_str "1RB1LF_1RC0RB_0LD0LA_0LE0RC_0RA1LD_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEAF") 7 1.
Time Qed.
End TM2508.


Module TM2509.
Definition tm := TM_from_str "1LB1RA_0LC1LF_0RD1LD_1RE---_1RA0RE_1LA0LB".
Definition tm' := TM_from_str "1RB---_1RC0RB_1LD1RC_0LF1LE_1LC0LD_0RA1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFABE") 12 10.
Time Qed.
End TM2509.


Module TM2510.
Definition tm := TM_from_str "1RB---_1LC0RB_1LE0LD_1LA0LD_1RF0LE_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_1LC0RB_1LF0LD_1LE0LD_1RB---_1RA0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM2510.


Module TM2511.
Definition tm := TM_from_str "1RB0RF_1LC---_1LD1RC_1RF1LE_1LB0LD_0LA0RA".
Definition tm' := TM_from_str "1RB1LF_0LC0RC_1RD0RB_1LE---_1LA1RE_1LD0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEAFB") 1 5.
Time Qed.
End TM2511.


Module TM2512.
Definition tm := TM_from_str "1RB1RF_1RC---_1RD0LA_1LE1LD_0RF0LE_1RC0RA".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCDA") 948 982.
Time Qed.
End TM2512.


Module TM2513.
Definition tm := TM_from_str "1LB1RA_1RC1LE_0LD0RC_1RE1LF_1LA0LB_0RB---".
Definition tm' := TM_from_str "1RB1LF_1LC0LD_1LD1RC_1RE1LB_0LA0RE_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 11 11.
Time Qed.
End TM2513.


Module TM2514.
Definition tm := TM_from_str "1RB1LA_1LC0RE_1LF1LD_1RB0LC_1LB1RA_---0LA".
Definition tm' := TM_from_str "1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM2514.


Module TM2515.
Definition tm := TM_from_str "1RB0LF_1RC1LC_1RD1RE_0LB1RC_0RC0LA_---1LE".
Definition tm' := TM_from_str "1RB1RD_0LC1RA_1RA1LA_0RA0LE_1RC0LF_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECABDF") 2 5.
Time Qed.
End TM2515.


Module TM2516.
Definition tm := TM_from_str "1LB---_1LC0LC_0LD0RD_1RE0LF_1RB0RE_0RA1LA".
Definition tm' := TM_from_str "1RB0RA_1LC0LC_0LD0RD_1RA0LE_0RF1LF_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 6.
Time Qed.
End TM2516.


Module TM2517.
Definition tm := TM_from_str "1RB0RA_1LC0RA_0LD0LB_0RE0LB_1RF---_1LB1RE".
Definition tm' := TM_from_str "1RB---_1LC1RA_1LE0RD_1RC0RD_0LF0LC_0RA0LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEFAB") 1 5.
Time Qed.
End TM2517.


Module TM2518.
Definition tm := TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RF_1LD1RB_1LE0LD_1RB0LB_1RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2518.


Module TM2519.
Definition tm := TM_from_str "1LB1LD_1LC0RF_0LD0LB_1LE---_1RB0LA_1LA1RE".
Definition tm' := TM_from_str "1RB0LF_1LC0RE_0LD0LB_1LA---_1LF1RA_1LB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 18 49.
Time Qed.
End TM2519.


Module TM2520.
Definition tm := TM_from_str "1LB0RA_1RC0LF_1RE0LD_0RE0LB_0RA1RD_---1LD".
Definition tm' := TM_from_str "1RB0LF_1RC0LE_0RD1RE_1LA0RD_0RC0LA_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABECF") 5 1.
Time Qed.
End TM2520.


Module TM2521.
Definition tm := TM_from_str "1RB1LE_1RC0RB_1LD0RA_1RB0LA_0RE0LF_1LD---".
Definition tm' := TM_from_str "1RB0LD_1RC0RB_1LA0RD_1RB1LE_0RE0LF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM2521.


Module TM2522.
Definition tm := TM_from_str "1LB0RB_1RC0LA_1LF0LD_1LE1RD_---1RA_1RD1LC".
Definition tm' := TM_from_str "1RB1LF_1LC1RB_---1RD_1LE0RE_1RF0LD_1LA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFBCA") 4 1.
Time Qed.
End TM2522.


Module TM2523.
Definition tm := TM_from_str "1RB1LA_1RC1RB_1LD1LF_0RE0LD_1RF---_0RA1LC".
Definition tm' := TM_from_str "1RB1RA_1LC1LE_0RD0LC_1RE---_0RF1LB_1RA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 10 11.
Time Qed.
End TM2523.


Module TM2524.
Definition tm := TM_from_str "1RB0RC_1LC0RE_1RA1LD_0LC1RA_0RF1LB_---0RA".
Definition tm' := TM_from_str "1RB1LD_1RC0RA_1LA0RE_0LA1RB_0RF1LC_---0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCADEF") 6006 6502.
Time Qed.
End TM2524.


Module TM2525.
Definition tm := TM_from_str "1RB1LB_1RC1LE_1RD1RF_0LE1RE_0RC0LA_---0RC".
Definition tm' := TM_from_str "1RB1RF_0LC1RC_0RA0LD_1RE1LE_1RA1LC_---0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 4.
Time Qed.
End TM2525.


Module TM2526.
Definition tm := TM_from_str "1LB1RA_1RC1LE_1RD1LC_0LD0RA_1LF0LC_---0LB".
Definition tm' := TM_from_str "1RB1LA_0LB0RC_1LD1RC_1RA1LE_1LF0LA_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 1 4.
Time Qed.
End TM2526.


Module TM2527.
Definition tm := TM_from_str "1LB1RA_0LC1RE_1RD1LF_1RE---_0RA0LB_0LE1LD".
Definition tm' := TM_from_str "1RB1LF_1RC---_0RD0LE_1LE1RD_0LA1RC_0LC1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 6 2.
Time Qed.
End TM2527.


Module TM2528.
Definition tm := TM_from_str "1LB0RF_0RC0LB_1RA1RD_1RE1RD_1RC1LE_1RD---".
Definition tm' := TM_from_str "1RB---_1RC1RB_1RD1LC_1RE1RB_1LF0RA_0RD0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDBCA") 3 1.
Time Qed.
End TM2528.


Module TM2529.
Definition tm := TM_from_str "1LB0RE_0RC1LF_0LA1RD_1RC0LB_1RB---_0LD0LE".
Definition tm' := TM_from_str "1RB0LE_0LC1RA_1LE0RD_1RE---_0RB1LF_0LA0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEBADF") 967 904.
Time Qed.
End TM2529.


Module TM2530.
Definition tm := TM_from_str "1LB0RF_1RC0LB_0LE0RD_1RA---_1RD1LB_0RC1RD".
Definition tm' := TM_from_str "1RB---_1LC0RF_1RD0LC_0LE0RA_1RA1LC_0RD1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 32 45.
Time Qed.
End TM2530.


Module TM2531.
Definition tm := TM_from_str "1RB1RF_1LC1RE_1LD0LC_1RB1LD_1RA0RB_0RA---".
Definition tm' := TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB1RF_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM2531.


Module TM2532.
Definition tm := TM_from_str "1RB---_1RC0RA_0LD1LF_0LA1LE_1RF0LA_1RB0LC".
Definition tm' := TM_from_str "1RB0LC_1RC0RF_0LD1LA_0LF1LE_1RA0LF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2532.


Module TM2533.
Definition tm := TM_from_str "1RB0LC_0LA0RC_1RD0RF_1LE1RB_1RF0LE_0RA---".
Definition tm' := TM_from_str "1RB0LA_0RC---_1RD0LE_0LC0RE_1RF0RB_1LA1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 8 4.
Time Qed.
End TM2533.


Module TM2534.
Definition tm := TM_from_str "1LB0RF_0RC0LD_1RE1LD_1RE0RA_1RA0LE_0RB---".
Definition tm' := TM_from_str "1RB0LA_1LC0RE_0RF0LD_1RA0RB_0RC---_1RA1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCFDAE") 7 1.
Time Qed.
End TM2534.


Module TM2535.
Definition tm := TM_from_str "1LB0RC_1RA0LE_1RD1RB_0LC0RF_1LB0LE_0RA---".
Definition tm' := TM_from_str "1RB0LC_1LA0RD_1LA0LC_1RE1RA_0LD0RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BADECF") 21 14.
Time Qed.
End TM2535.


Module TM2536.
Definition tm := TM_from_str "1RB1RD_1LC---_1LE1LD_1RE0LF_1RA0RA_---0LC".
Definition tm' := TM_from_str "1RB0LF_1RC0RC_1RD1RA_1LE---_1LB1LA_---0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 5 31.
Time Qed.
End TM2536.


Module TM2537.
Definition tm := TM_from_str "1LB0LE_1LC0RE_1RD1RC_0LA0RD_0LF1LA_0RB---".
Definition tm' := TM_from_str "1RB1RA_0LC0RB_1LF0LD_0LE1LC_0RF---_1LA0RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CFABDE") 990 975.
Time Qed.
End TM2537.


Module TM2538.
Definition tm := TM_from_str "1RB0LD_0LC1RE_---1RD_1LA1LB_1RF0RE_1RD0RA".
Definition tm' := TM_from_str "1RB0RC_1LC1LD_1RD0LB_0LF1RE_1RA0RE_---1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDFBEA") 3 1.
Time Qed.
End TM2538.


Module TM2539.
Definition tm := TM_from_str "1RB0LA_0RC1LF_0RD1LC_1LD0LE_1RB1LF_---1LA".
Definition tm' := TM_from_str "1RB1LE_0RC1LE_0RD1LC_1LD0LA_---1LF_1RB0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2539.


Module TM2540.
Definition tm := TM_from_str "1LB1LC_1RC1LA_0RD0RC_0LE1LB_1LD0LF_0LB---".
Definition tm' := TM_from_str "1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LA---_1LA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 221 184.
Time Qed.
End TM2540.


Module TM2541.
Definition tm := TM_from_str "1RB1LA_1LC0RC_1RE0LD_0RE0LA_1RF---_1RB1RF".
Definition tm' := TM_from_str "1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2541.


Module TM2542.
Definition tm := TM_from_str "1LB0RD_1LC0RD_1RA0LC_1RE0LB_1RB0RF_0RB---".
Definition tm' := TM_from_str "1RB0RF_1LC0RE_1RD0LC_1LB0RE_1RA0LB_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 5 1.
Time Qed.
End TM2542.


Module TM2543.
Definition tm := TM_from_str "1LB1LC_1RC0LF_1RD1RC_1LE0RC_---0LA_0LE1RD".
Definition tm' := TM_from_str "1RB1RA_1LC0RA_---0LD_1LE1LA_1RA0LF_0LC1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 10 7.
Time Qed.
End TM2543.


Module TM2544.
Definition tm := TM_from_str "1LB0LA_1RC0LA_1LB0RD_1RE1RB_0LD0RF_0RC---".
Definition tm' := TM_from_str "1RB0LC_1LA0RD_1LA0LC_1RE1RA_0LD0RF_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 21 14.
Time Qed.
End TM2544.


Module TM2545.
Definition tm := TM_from_str "1RB1LD_1LC1RA_1RD0LC_1RE0LE_1LF0LD_---0RB".
Definition tm' := TM_from_str "1RB0LB_1LC0LA_---0RD_1LF1RE_1RD1LA_1RA0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDFABC") 9 1.
Time Qed.
End TM2545.


Module TM2546.
Definition tm := TM_from_str "1LB0RA_1LC1LF_1LD0LA_1RE0LC_1LA0RD_0LD---".
Definition tm' := TM_from_str "1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 1 5.
Time Qed.
End TM2546.


Module TM2547.
Definition tm := TM_from_str "1RB1LA_0LA1RC_1RB0LD_1RE1LC_1RF0RA_---1RD".
Definition tm' := TM_from_str "1RB0LD_0LC1RA_1RB1LC_1RE1LA_1RF0RC_---1RD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBADEF") 1 1.
Time Qed.
End TM2547.


Module TM2548.
Definition tm := TM_from_str "1LB1LE_1RC1LB_1RE0LD_0LC1LC_1LF0RB_---1LA".
Definition tm' := TM_from_str "1RB0LF_1LC0RE_---1LD_1LE1LB_1RA1LE_0LA1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFBC") 14 29.
Time Qed.
End TM2548.


Module TM2549.
Definition tm := TM_from_str "1LB---_1LC0RD_0LD0LB_1RE0LC_1RF1RA_0RB0RC".
Definition tm' := TM_from_str "1RB0LE_1RC1RF_0RD0RE_1LE0RA_0LA0LD_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 19 1.
Time Qed.
End TM2549.


Module TM2550.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_1LB1LC_---1RA_1RB1RC".
Definition tm' := TM_from_str "1RB1RC_1LC0RD_1RE0LD_1LB1LC_---1RF_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2550.


Module TM2551.
Definition tm := TM_from_str "1RB1RF_1RC0LD_1LB0RE_1LB0LB_1RA0RE_1LE---".
Definition tm' := TM_from_str "1RB0LC_1LA0RD_1LA0LA_1RE0RD_1RA1RF_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 115 113.
Time Qed.
End TM2551.


Module TM2552.
Definition tm := TM_from_str "1LB0RB_0LC0LB_0RD0LA_1RE---_0RF0RC_1RB1RA".
Definition tm' := TM_from_str "1RB1RD_0LC0LB_0RE0LD_1LB0RB_1RF---_0RA0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 1 4.
Time Qed.
End TM2552.


Module TM2553.
Definition tm := TM_from_str "1RB0RE_1LC1RD_1LD0LC_1RA0RF_1LF---_1RB1RB".
Definition tm' := TM_from_str "1RB1RB_1LC1RD_1LD0LC_1RE0RA_1RB0RF_1LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM2553.


Module TM2554.
Definition tm := TM_from_str "1RB0LE_1LC0RE_1RF0LD_1LA1LF_0LC0RA_0LE---".
Definition tm' := TM_from_str "1RB0LF_0LC---_0LA0RD_1RE0LC_1LA0RC_1LD1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEAFCB") 1 4.
Time Qed.
End TM2554.


Module TM2555.
Definition tm := TM_from_str "1RB1LD_1RC0RF_1LA1RC_1RE0LA_1LC1LE_---0RB".
Definition tm' := TM_from_str "1RB0LD_1LC1LB_1LD1RC_1RE1LA_1RC0RF_---0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DECABF") 2 4.
Time Qed.
End TM2555.


Module TM2556.
Definition tm := TM_from_str "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA0RF_0LD---".
Definition tm' := TM_from_str "1RB0LB_1RC0RE_1LD1RB_1LA0LD_1RB0RF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDAEF") 442 465.
Time Qed.
End TM2556.


Module TM2557.
Definition tm := TM_from_str "1LB0LD_0RC1LF_0LE0RD_1RB1LE_0LB---_0LA0LD".
Definition tm' := TM_from_str "1RB1LD_0RC1LE_0LD0RA_0LB---_0LF0LA_1LB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 4 1.
Time Qed.
End TM2557.


Module TM2558.
Definition tm := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_1RB---".
Definition tm' := TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 1 6.
Time Qed.
End TM2558.


Module TM2559.
Definition tm := TM_from_str "1RB---_1LC0RF_0RE0LD_1LE1LA_1RB0LF_0LC0RA".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDAE") 1 1.
Time Qed.
End TM2559.


Module TM2560.
Definition tm := TM_from_str "1LB0RB_0LC1LD_1RD1LE_0RA0LB_0LD1LF_0LC---".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD0RD_0LA1LB_0LB1LF_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 23 35.
Time Qed.
End TM2560.


Module TM2561.
Definition tm := TM_from_str "1LB---_0RC1LF_1LA1RD_0RE0LB_1RB0LA_0LD0LE".
Definition tm' := TM_from_str "1RB0LD_0RC1LE_1LD1RF_1LB---_0LF0LA_0RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCFAE") 695 655.
Time Qed.
End TM2561.


Module TM2562.
Definition tm := TM_from_str "1RB1LF_1LC1LA_1RE1RD_1LA0LE_1LD0RC_1LB---".
Definition tm' := TM_from_str "1RB1RC_1LC0RA_1LD0LB_1RE1LF_1LA1LD_1LE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEACBF") 6 1.
Time Qed.
End TM2562.


Module TM2563.
Definition tm := TM_from_str "1LB0LF_1LC1RC_0RD0RA_0LA0RE_1RB1RC_1LD---".
Definition tm' := TM_from_str "1RB1RC_1LC1RC_0RF0RD_1LB0LE_1LF---_0LD0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCFAE") 29 37.
Time Qed.
End TM2563.


Module TM2564.
Definition tm := TM_from_str "1LB1RD_0LC0LB_1RC0RA_1RE0RA_1RA1RF_---1LB".
Definition tm' := TM_from_str "1RB0RC_1RC1RF_1LD1RA_0LE0LD_1RE0RC_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEABF") 127 73.
Time Qed.
End TM2564.


Module TM2565.
Definition tm := TM_from_str "1RB---_1RC1RE_0LD0RC_1LF1LE_1LD0RB_0LA0LD".
Definition tm' := TM_from_str "1RB1RD_0LC0RB_1LE1LD_1LC0RA_0LF0LC_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 36 26.
Time Qed.
End TM2565.


Module TM2566.
Definition tm := TM_from_str "1LB0LF_0RC1RC_1RE0RD_1RB1LD_1LF1LE_---0LA".
Definition tm' := TM_from_str "1RB1LA_0RC1RC_1RD0RA_1LE1LD_---0LF_1LB0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCADE") 4 1.
Time Qed.
End TM2566.


Module TM2567.
Definition tm := TM_from_str "1LB0RD_0RC0LE_1RA0LD_0LB0RC_1LC1LF_1LA---".
Definition tm' := TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_1LB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCAEDF") 6 1.
Time Qed.
End TM2567.


Module TM2568.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1RE_1RA0LC_0RD0RF_1RB---".
Definition tm' := TM_from_str "1RB0RA_1LC1RE_1RA1LD_1RC0LB_0RD0RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 4 5.
Time Qed.
End TM2568.


Module TM2569.
Definition tm := TM_from_str "1RB0LE_1RC0RB_1LD1RE_1LA0LD_1RB0RF_0LD---".
Definition tm' := TM_from_str "1RB0RF_1RC0RB_1LD1RA_1LE0LD_1RB0LA_0LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2569.


Module TM2570.
Definition tm := TM_from_str "1RB1LD_1RC0RC_1LA1RC_1LF0LE_1RB1LE_---1LA".
Definition tm' := TM_from_str "1RB1LA_1RC0RC_1LD1RC_1RB1LE_1LF0LA_---1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEAF") 1 1.
Time Qed.
End TM2570.


Module TM2571.
Definition tm := TM_from_str "1RB---_1RC1RB_1LD1LC_0RE0LD_1RB0RF_1RA1RE".
Definition tm' := TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 760 746.
Time Qed.
End TM2571.


Module TM2572.
Definition tm := TM_from_str "1RB0LA_1RC1RD_1LB1RA_---0RE_1LF0RC_1LF0LA".
Definition tm' := TM_from_str "1RB1RC_1LA1RF_---0RD_1LE0RB_1LE0LF_1RA0LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 1 15.
Time Qed.
End TM2572.


Module TM2573.
Definition tm := TM_from_str "1RB0LC_1LA0RD_1LA0LC_1RE0LB_1RB0RF_0RB---".
Definition tm' := TM_from_str "1RB0LC_1RC0RF_1LD0RA_1RC0LE_1LD0LE_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEABF") 118 58.
Time Qed.
End TM2573.


Module TM2574.
Definition tm := TM_from_str "1LB0RB_0LC0RB_1RD1LE_0RA0LF_0LD1LB_0LC---".
Definition tm' := TM_from_str "1RB1LE_0RC0LF_1LD0RD_0LA0RD_0LB1LD_0LA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 22 32.
Time Qed.
End TM2574.


Module TM2575.
Definition tm := TM_from_str "1RB1LA_1RC0RF_1RD---_0LE1RB_0LA0RD_1LD1RF".
Definition tm' := TM_from_str "1RB---_0LC1RE_0LD0RB_1RE1LD_1RA0RF_1LB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 1 6.
Time Qed.
End TM2575.


Module TM2576.
Definition tm := TM_from_str "1RB0LA_1RC1RB_0LD0RD_1RE1LA_1LF0RB_---0LE".
Definition tm' := TM_from_str "1RB1RA_0LC0RC_1RE1LD_1RA0LD_1LF0RA_---0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 159 185.
Time Qed.
End TM2576.


Module TM2577.
Definition tm := TM_from_str "1RB1RC_0LC1RA_0RA0LD_1RE0LF_1LE1RB_---1LC".
Definition tm' := TM_from_str "1RB0LF_1LB1RC_0LE1RD_1RC1RE_0RD0LA_---1LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEABF") 4 1.
Time Qed.
End TM2577.


Module TM2578.
Definition tm := TM_from_str "1RB---_0LB0LC_1RD0LF_1RE1RC_1RA0RA_0RD1LC".
Definition tm' := TM_from_str "1RB0LF_1RC1RA_1RD0RD_1RE---_0LE0LA_0RB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEABCF") 4 1.
Time Qed.
End TM2578.


Module TM2579.
Definition tm := TM_from_str "1RB0LC_1LA1RE_1RD1LD_0RB0LA_1RA1RF_0RA---".
Definition tm' := TM_from_str "1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCABEF") 591 900.
Time Qed.
End TM2579.


Module TM2580.
Definition tm := TM_from_str "1RB1LF_1RC0RD_1LD0RA_0LE0LC_0RB0LA_1RB---".
Definition tm' := TM_from_str "1RB---_1RC0RD_1LD0RE_0LF0LC_1RB1LA_0RB0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM2580.


Module TM2581.
Definition tm := TM_from_str "1RB---_1RC1RD_1RD0RC_0LE1RF_0LF1LE_1RA0RD".
Definition tm' := TM_from_str "1RB0RA_0LC1RD_0LD1LC_1RE0RB_1RF---_1RA1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFABCD") 3 7.
Time Qed.
End TM2581.


Module TM2582.
Definition tm := TM_from_str "1LB1LF_0RC0RE_1LD1RB_1LB1RF_---1LC_1RD0LA".
Definition tm' := TM_from_str "1RB0LF_1LC1RA_0RE0RD_---1LE_1LB1RC_1LC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCEBDA") 120 126.
Time Qed.
End TM2582.


Module TM2583.
Definition tm := TM_from_str "1LB0LA_1LC0RE_0LD0RD_1LE0LA_1RB1LF_0RB---".
Definition tm' := TM_from_str "1RB1LF_1LC0RA_0LD0RD_1LA0LE_1LB0LE_0RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 5.
Time Qed.
End TM2583.


Module TM2584.
Definition tm := TM_from_str "1LB0LD_1LC0RB_0RA0LC_1RE0RD_1RF---_1RB1RA".
Definition tm' := TM_from_str "1RB1RD_1LC0RB_0RD0LC_1LB0LE_1RF0RE_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCEFA") 13 13.
Time Qed.
End TM2584.


Module TM2585.
Definition tm := TM_from_str "1RB---_1RC0RB_1LD0LE_0LF0LC_1LC0RA_1RB0LA".
Definition tm' := TM_from_str "1RB0LF_1RC0RB_1LD0LE_0LA0LC_1LC0RF_1RB---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2585.


Module TM2586.
Definition tm := TM_from_str "1LB1LE_1RC0LB_0RD0RD_1RA1RD_1LF1LE_---1LC".
Definition tm' := TM_from_str "1RB0LA_0RC0RC_1RD1RC_1LA1LE_1LF1LE_---1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 3 2.
Time Qed.
End TM2586.


Module TM2587.
Definition tm := TM_from_str "1LB---_0LC1LE_1LD1LA_1RE0RE_0LF0RD_1LB1LB".
Definition tm' := TM_from_str "1RB0RB_0LC0RA_1LD1LD_0LE1LB_1LA1LF_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEABC") 1 3.
Time Qed.
End TM2587.


Module TM2588.
Definition tm := TM_from_str "1RB1LF_1LC0RE_1LE0LD_0LC0RF_0RA0LA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RE_1LE0LD_0LC0RA_0RF0LF_1RB1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2588.


Module TM2589.
Definition tm := TM_from_str "1LB0RA_1RC0LB_1RE1RD_1RA1LE_1LF0LE_---0RC".
Definition tm' := TM_from_str "1RB0LA_1RC1RE_1LD0LC_---0RB_1RF1LC_1LA0RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABECD") 14 20.
Time Qed.
End TM2589.


Module TM2590.
Definition tm := TM_from_str "1RB0LE_1LC0RE_0RF0LD_1LA0RD_0LC1LF_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RF_0RA0LD_1LE0RD_1RB0LF_0LC1LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDFA") 1 1.
Time Qed.
End TM2590.


Module TM2591.
Definition tm := TM_from_str "1RB---_1LC0RD_0LD0LB_1RE0LD_0LF0RF_0RB0RA".
Definition tm' := TM_from_str "1RB0LA_0LC0RC_0RE0RD_1RE---_1LF0RA_0LA0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 1 4.
Time Qed.
End TM2591.


Module TM2592.
Definition tm := TM_from_str "1RB0LD_1LC0RE_---0LD_1LA1LB_1RF0RF_1LA1RD".
Definition tm' := TM_from_str "1RB0RB_1LC1RD_1RE0LD_1LC1LE_1LF0RA_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CEFDAB") 3 3.
Time Qed.
End TM2592.


Module TM2593.
Definition tm := TM_from_str "1RB1RA_1LC1LF_0RD0LC_1RE---_0RF1LA_1RB1LB".
Definition tm' := TM_from_str "1RB1LB_1LC1LA_0RD0LC_1RE---_0RA1LF_1RB1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2593.


Module TM2594.
Definition tm := TM_from_str "1LB1RF_1LC0RD_0LD0LC_0RE0RA_1RB---_1RD0RA".
Definition tm' := TM_from_str "1RB0RF_0RC0RF_1RD---_1LE0RB_0LB0LE_1LD1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEBCA") 8517 9008.
Time Qed.
End TM2594.


Module TM2595.
Definition tm := TM_from_str "1LB0RA_0RC---_1LF0LD_1RE1LC_1RF0RE_1LD0LA".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF0RE_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFDABC") 4 1.
Time Qed.
End TM2595.


Module TM2596.
Definition tm := TM_from_str "1LB0LA_0RC1LA_1RD0LB_1RE0RD_1LC1RF_1RE---".
Definition tm' := TM_from_str "1RB0LD_1RC0RB_1LA1RF_0RA1LE_1LD0LE_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EDABCF") 5 1.
Time Qed.
End TM2596.


Module TM2597.
Definition tm := TM_from_str "1LB1RB_1RC1LE_1LA1RD_0RC0RA_1LF0LC_---1LA".
Definition tm' := TM_from_str "1RB1LD_1LC1RE_1LA1RA_1LF0LB_0RB0RC_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABEDF") 103 188.
Time Qed.
End TM2597.


Module TM2598.
Definition tm := TM_from_str "1LB1LA_0RC0LE_1LC1LD_0RB1RF_1RD1LE_---0LA".
Definition tm' := TM_from_str "1RB1LA_0RC1RE_0RD0LA_1LD1LB_---0LF_1LC1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FCDBAE") 6 1.
Time Qed.
End TM2598.


Module TM2599.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RD_1RE0LD_0RE0LB_0LB0RF_1RB1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2599.


Module TM2600.
Definition tm := TM_from_str "1RB1RF_0LC1RA_1RA0LD_1RC0LE_---1LF_0RA0LD".
Definition tm' := TM_from_str "1RB0LE_1RC0LA_1RD1RF_0LB1RC_---1LF_0RC0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDBAEF") 4 1.
Time Qed.
End TM2600.


Module TM2601.
Definition tm := TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RA_1RF1LB_0LE---".
Definition tm' := TM_from_str "1RB1LC_0LA---_1LD0LC_1RE0RA_1LC1RF_1RD0RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ECDFAB") 1 3.
Time Qed.
End TM2601.


Module TM2602.
Definition tm := TM_from_str "1RB1LF_1RC0LD_0RD0RC_1LD0LE_1RB0LA_---1RB".
Definition tm' := TM_from_str "1RB0LE_1RC0LD_0RD0RC_1LD0LA_1RB1LF_---1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2602.


Module TM2603.
Definition tm := TM_from_str "1RB1LC_0RC0RE_0LD0LF_1LA0LB_1RB1LE_1LD---".
Definition tm' := TM_from_str "1RB1LA_0RC0RA_0LD0LF_1LE0LB_1RB1LC_1LD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2603.


Module TM2604.
Definition tm := TM_from_str "1LB1LA_1RC0RF_1RD1RD_0LA0RE_0RB1RE_---0LA".
Definition tm' := TM_from_str "1RB0RF_1RC1RC_0LD0RE_1LA1LD_0RA1RE_---0LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 3 2.
Time Qed.
End TM2604.


Module TM2605.
Definition tm := TM_from_str "1RB1RA_1RC0RD_0LD1RD_---0LE_0RA1LF_1RA1LD".
Definition tm' := TM_from_str "1RB0RC_0LC1RC_---0LD_0RE1LF_1RA1RE_1RE1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EABCDF") 1 5.
Time Qed.
End TM2605.


Module TM2606.
Definition tm := TM_from_str "1RB1RC_1LC0RF_1LA1LD_0RE0LC_---1LB_1RB0RD".
Definition tm' := TM_from_str "1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2606.


Module TM2607.
Definition tm := TM_from_str "1RB0RF_1LC1RE_---1LD_0RE1LA_1RF1RA_0LD0LB".
Definition tm' := TM_from_str "1RB1RD_0LC0LE_0RA1LD_1RE0RB_1LF1RA_---1LC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFCAB") 1 10.
Time Qed.
End TM2607.


Module TM2608.
Definition tm := TM_from_str "1RB0LC_1LC1RD_1LA1LC_1RB0RE_0RF1RB_---1RE".
Definition tm' := TM_from_str "1RB0RE_1LC1RA_1LD1LC_1RB0LC_0RF1RB_---1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM2608.


Module TM2609.
Definition tm := TM_from_str "1LB---_1RC0LC_0RD1LC_1LA0RE_0LA1RF_1LB1RD".
Definition tm' := TM_from_str "1RB0LB_0RC1LB_1LD0RE_1LA---_0LD1RF_1LA1RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DABCEF") 35 4.
Time Qed.
End TM2609.


Module TM2610.
Definition tm := TM_from_str "1RB---_0RC0LB_0LD1RC_1LE0RA_1RD1LF_1LB0LA".
Definition tm' := TM_from_str "1RB1LC_1LA0RF_1LD0LF_0RE0LD_0LB1RE_1RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FDEBAC") 3 1.
Time Qed.
End TM2610.


Module TM2611.
Definition tm := TM_from_str "1LB0LD_1LC1RA_0RD0LE_1LF0RC_1RC---_1LA1LF".
Definition tm' := TM_from_str "1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EFBCAD") 6 1.
Time Qed.
End TM2611.


Module TM2612.
Definition tm := TM_from_str "1RB---_1RC0RB_1LD1RF_1RB1LE_1RD0LC_0RE0RA".
Definition tm' := TM_from_str "1RB0RA_1LC1RE_1RA1LD_1RC0LB_0RD0RF_1RA---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 4 5.
Time Qed.
End TM2612.


Module TM2613.
Definition tm := TM_from_str "1RB0LD_1RC0RB_1LA0RB_1LE1LE_0LC0LF_0LA---".
Definition tm' := TM_from_str "1RB0RA_1LC0RA_1RA0LD_1LE1LE_0LB0LF_0LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CABDEF") 5 4.
Time Qed.
End TM2613.


Module TM2614.
Definition tm := TM_from_str "1RB1RD_0LC0RE_1LB1LD_1RB1RF_1RA0RC_---1LB".
Definition tm' := TM_from_str "1RB1RF_0LC0RD_1LB1LA_1RE0RC_1RB1RA_---1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCADF") 1 1.
Time Qed.
End TM2614.


Module TM2615.
Definition tm := TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_1LA---_1RA0LD".
Definition tm' := TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1LC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDAEFB") 59 36.
Time Qed.
End TM2615.


Module TM2616.
Definition tm := TM_from_str "1RB0LC_1LA0RD_1LA0LB_1RE1RA_1RB0RF_0RB---".
Definition tm' := TM_from_str "1RB1RD_1RC0RF_1LD0RA_1RC0LE_1LD0LC_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCEABF") 298 302.
Time Qed.
End TM2616.


Module TM2617.
Definition tm := TM_from_str "1RB---_0RC1LB_1RD1RC_1RE1LD_1LF1LE_0RA0LF".
Definition tm' := TM_from_str "1RB1LA_1LC1LB_0RD0LC_1RE---_0RF1LE_1RA1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DEFABC") 39 77.
Time Qed.
End TM2617.


Module TM2618.
Definition tm := TM_from_str "1LB0LC_1RC1LA_1LE1LD_1RF0LB_---1RA_1RB0RD".
Definition tm' := TM_from_str "1RB0RF_1RC1LE_1LD1LF_---1RE_1LB0LC_1RA0LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCFDA") 2 5.
Time Qed.
End TM2618.


Module TM2619.
Definition tm := TM_from_str "1RB1RC_1RC1LF_1LD0RA_---0LE_0LF0LF_1LB1LC".
Definition tm' := TM_from_str "1RB1LE_1LC0RF_---0LD_0LE0LE_1LA1LB_1RA1RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 5 4.
Time Qed.
End TM2619.


Module TM2620.
Definition tm := TM_from_str "1LB1LC_0LC0RC_1RD1LE_0RA0LB_0LD1LF_0RB---".
Definition tm' := TM_from_str "1RB1LE_0RC0LD_1LD1LA_0LA0RA_0LB1LF_0RD---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDABEF") 20 40.
Time Qed.
End TM2620.


Module TM2621.
Definition tm := TM_from_str "1RB0LF_1LC1LB_0RD0LC_1RE---_0RF1RA_1RB1RD".
Definition tm' := TM_from_str "1RB1RD_1LC1LB_0RD0LC_1RE---_0RA1RF_1RB0LA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2621.


Module TM2622.
Definition tm := TM_from_str "1RB0RE_0RC0LB_1LD1RA_1LB---_1RB0RF_---1RE".
Definition tm' := TM_from_str "1RB0RF_0RC0LB_1LD1RE_1LB---_1RB0RA_---1RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2622.


Module TM2623.
Definition tm := TM_from_str "1LB1LC_1RC0LB_1LD1RD_0LE1RE_1RF0RC_1RA---".
Definition tm' := TM_from_str "1RB0LA_1LC1RC_0LD1RD_1RE0RB_1RF---_1LA1LB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 4 3.
Time Qed.
End TM2623.


Module TM2624.
Definition tm := TM_from_str "1LB0RC_1RC1LA_0RD0RC_0LE1LB_1LD0LF_0LB---".
Definition tm' := TM_from_str "1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LA---_1LA0RB".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FABCDE") 165397 144708.
Time Qed.
End TM2624.


Module TM2625.
Definition tm := TM_from_str "1RB0RE_1LC0LA_1LD0LC_1RA0LB_1RD0RF_0RA---".
Definition tm' := TM_from_str "1RB0RF_1RC0LD_1RD0RA_1LE0LC_1LB0LE_0RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEBAF") 18 14.
Time Qed.
End TM2625.


Module TM2626.
Definition tm := TM_from_str "1RB0RE_0RC1RA_1LC0LD_1RB1LD_0RB1RF_---0RC".
Definition tm' := TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RB0RE_0RB1RF_---0RC".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBCAEF") 1 1.
Time Qed.
End TM2626.


Module TM2627.
Definition tm := TM_from_str "1RB0LC_1LA0RE_1LD0LC_1LB1LF_1RB0RB_1RA---".
Definition tm' := TM_from_str "1RB0RB_1LC0RA_1RB0LD_1LE0LD_1LB1LF_1RC---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CBDEAF") 1 1.
Time Qed.
End TM2627.


Module TM2628.
Definition tm := TM_from_str "1RB1LE_1LC0RA_1RB0LD_1LB0RE_0LF---_0LB1LA".
Definition tm' := TM_from_str "1RB0LC_1LA0RD_1LB0RE_1RB1LE_0LF---_0LB1LD".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DBACEF") 1 1.
Time Qed.
End TM2628.


Module TM2629.
Definition tm := TM_from_str "1LB0LF_1LC0RC_0RD0LA_1RB1RE_0RC1RE_1RA---".
Definition tm' := TM_from_str "1RB---_1LC0LA_1LD0RD_0RE0LB_1RC1RF_0RD1RF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "BCDEFA") 1 5.
Time Qed.
End TM2629.


Module TM2630.
Definition tm := TM_from_str "1RB1RF_1LC0LA_1RE0LD_0RE0LD_0LB0RA_0RD---".
Definition tm' := TM_from_str "1RB0LE_0LC0RD_1LA0LD_1RC1RF_0RB0LE_0RE---".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "DCAEBF") 1 4.
Time Qed.
End TM2630.


Module TM2631.
Definition tm := TM_from_str "1RB0RF_1LC0RC_0RE0LD_0RE1LB_0LB1RA_1RB---".
Definition tm' := TM_from_str "1RB---_1LC0RC_0RE0LD_0RE1LB_0LB1RF_1RB0RA".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2631.


Module TM2632.
Definition tm := TM_from_str "1LB1RA_1RA0LC_---0LD_1RE1LD_1RF0RF_0LF0RA".
Definition tm' := TM_from_str "1RB0RB_0LB0RC_1LD1RC_1RC0LE_---0LF_1RA1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "CDEFAB") 1 4.
Time Qed.
End TM2632.


Module TM2633.
Definition tm := TM_from_str "1RB1LC_1LC0RE_0LF0LD_1LA1LE_1RB1LE_---0LA".
Definition tm' := TM_from_str "1RB1LA_1LC0RA_0LF0LD_1LE1LA_1RB1LC_---0LE".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "EBCDAF") 1 1.
Time Qed.
End TM2633.


Module TM2634.
Definition tm := TM_from_str "1RB1LA_0RC1RC_1RD0RA_1LE1LD_0RF0LE_1RB---".
Definition tm' := TM_from_str "1RB---_0RC1RC_1RD0RF_1LE1LD_0RA0LE_1RB1LF".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "FBCDEA") 1 1.
Time Qed.
End TM2634.


Module TM2635.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA1RE_1LC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LC---_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDCE") 0 0.
Time Qed.
End TM2635.


Module TM2636.
Definition tm := TM_from_str "1RB0RA_0LC1RA_1RE1LD_1LC0LF_---0RB_1LC0LF".
Definition tm' := TM_from_str "1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDED") 0 0.
Time Qed.
End TM2636.


Module TM2637.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LF_1LE---_1LA0LA_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA0LA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2637.


Module TM2638.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LF_1LE---_1LF1RA_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2638.


Module TM2639.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2639.


Module TM2640.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RE_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RE_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2640.


Module TM2641.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LF_1LE---_1LA0LF_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA0LA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2641.


Module TM2642.
Definition tm := TM_from_str "1RB---_1RC1LE_1LD1RF_1LE0LD_1RC1LB_1RA0RC".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDBE") 0 0.
Time Qed.
End TM2642.


Module TM2643.
Definition tm := TM_from_str "1RB0RA_0LC1RF_1RE1LD_1LC0LD_---0RB_1RB0RA".
Definition tm' := TM_from_str "1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2643.


Module TM2644.
Definition tm := TM_from_str "1RB---_1RC1LE_1LD1RF_1LE0LD_1RC1LE_1RA0RC".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDBE") 0 0.
Time Qed.
End TM2644.


Module TM2645.
Definition tm := TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RF_1LD1RE".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEC") 0 0.
Time Qed.
End TM2645.


Module TM2646.
Definition tm := TM_from_str "1RB1LD_1RC0RF_1LA1RC_1LE0LA_1LC---_1RC0RF".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LC---_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEB") 0 0.
Time Qed.
End TM2646.


Module TM2647.
Definition tm := TM_from_str "1RB1LC_0RC0RF_1LD0LA_1LE---_1LA1RA_0RC0RF".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEB") 0 0.
Time Qed.
End TM2647.


Module TM2648.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LF_1LE---_1LA1RA_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2648.


Module TM2649.
Definition tm := TM_from_str "1RB---_0LC1RF_0LD1LC_1RE1LB_1RB---_0RB0RE".
Definition tm' := TM_from_str "1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDAE") 0 0.
Time Qed.
End TM2649.


Module TM2650.
Definition tm := TM_from_str "1RB1RD_1LC0RF_1RA1LD_0RE0LB_---1RF_1RA1LD".
Definition tm' := TM_from_str "1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEC") 0 0.
Time Qed.
End TM2650.


Module TM2651.
Definition tm := TM_from_str "1RB---_1RC1LF_1LD1RE_1LB0LD_1RA0RC_1RC1LB".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEB") 0 0.
Time Qed.
End TM2651.


Module TM2652.
Definition tm := TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RB---".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2652.


Module TM2653.
Definition tm := TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1RC1LB_1RA0RC".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDBE") 0 0.
Time Qed.
End TM2653.


Module TM2654.
Definition tm := TM_from_str "1RB1LC_0RC0RF_1LD0LA_1LE---_1LA1RE_0RC0RF".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RE_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEB") 0 0.
Time Qed.
End TM2654.


Module TM2655.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LF_1LE---_1LA1RF_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2655.


Module TM2656.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LF_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA0LA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2656.


Module TM2657.
Definition tm := TM_from_str "1RB---_0LC1RF_0LD1LC_1RE1LB_1RB---_0RB0RA".
Definition tm' := TM_from_str "1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDAE") 0 0.
Time Qed.
End TM2657.


Module TM2658.
Definition tm := TM_from_str "1RB0RF_0LC1RA_1RE1LD_1LC0LD_---0RB_1RB0RA".
Definition tm' := TM_from_str "1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2658.


Module TM2659.
Definition tm := TM_from_str "1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RF_1RA1LD".
Definition tm' := TM_from_str "1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEC") 0 0.
Time Qed.
End TM2659.


Module TM2660.
Definition tm := TM_from_str "1RB1RD_1LC0RF_1RA1LD_0RE0LB_---1RC_1RA1LD".
Definition tm' := TM_from_str "1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEC") 0 0.
Time Qed.
End TM2660.


Module TM2661.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RF_1LA1RF".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RE_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEE") 0 0.
Time Qed.
End TM2661.


Module TM2662.
Definition tm := TM_from_str "1RB0RF_0LC1RA_1RE1LD_1LC0LD_---0RB_1RB0RF".
Definition tm' := TM_from_str "1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2662.


Module TM2663.
Definition tm := TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1RC1LE_1RA0RC".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDBE") 0 0.
Time Qed.
End TM2663.


Module TM2664.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RF_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2664.


Module TM2665.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LA1RC".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LC---_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEC") 0 0.
Time Qed.
End TM2665.


Module TM2666.
Definition tm := TM_from_str "1RB---_0LC1RE_0LD1LC_1RA1LF_0RB0RA_0LC1RE".
Definition tm' := TM_from_str "1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEB") 0 0.
Time Qed.
End TM2666.


Module TM2667.
Definition tm := TM_from_str "1RB---_0LC1RF_0LE1LD_0LE1LC_1RA1LB_0RB0RA".
Definition tm' := TM_from_str "1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCCDE") 0 0.
Time Qed.
End TM2667.


Module TM2668.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LF_1LE---_1LA1RE_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RE_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2668.


Module TM2669.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LA1RF".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LC---_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEC") 0 0.
Time Qed.
End TM2669.


Module TM2670.
Definition tm := TM_from_str "1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RF_1RB---".
Definition tm' := TM_from_str "1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2670.


Module TM2671.
Definition tm := TM_from_str "1RB---_0LC1RF_0LE1LD_0LE1LD_1RA1LB_0RB0RA".
Definition tm' := TM_from_str "1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCCDE") 0 0.
Time Qed.
End TM2671.


Module TM2672.
Definition tm := TM_from_str "1RB0RF_0LC1RF_1RE1LD_1LC0LD_---0RB_1RB0RA".
Definition tm' := TM_from_str "1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2672.


Module TM2673.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LF0LE_1RB1LD_1LC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LC---_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDAE") 0 0.
Time Qed.
End TM2673.


Module TM2674.
Definition tm := TM_from_str "1RB---_1RC1LB_1LD1RF_1LB0LE_1LB0LE_1RA0RC".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDDE") 0 0.
Time Qed.
End TM2674.


Module TM2675.
Definition tm := TM_from_str "1RB---_1RC1LF_1LD1RE_1LB0LD_1RA0RC_1RC1LF".
Definition tm' := TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEB") 0 0.
Time Qed.
End TM2675.


Module TM2676.
Definition tm := TM_from_str "1RB1LF_0RC0RB_1LD0LA_1LE---_1LA1RA_1LD0LA".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEC") 0 0.
Time Qed.
End TM2676.


Module TM2677.
Definition tm := TM_from_str "1RB---_0LC1RE_0LD1LC_1RA1LB_0RF0RA_0LC1RE".
Definition tm' := TM_from_str "1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEB") 0 0.
Time Qed.
End TM2677.


Module TM2678.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA0LA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2678.


Module TM2679.
Definition tm := TM_from_str "1RB1LC_0RC0RF_1LD0LA_1LE---_1LA0LA_0RC0RF".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA0LA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEB") 0 0.
Time Qed.
End TM2679.


Module TM2680.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA1RC_1LC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LC---_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDCE") 0 0.
Time Qed.
End TM2680.


Module TM2681.
Definition tm := TM_from_str "1RB1LF_0RC0RB_1LD0LA_1LE---_1LA0LA_1LD0LA".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA0LA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEC") 0 0.
Time Qed.
End TM2681.


Module TM2682.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RF_1LA1RE".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RE_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEE") 0 0.
Time Qed.
End TM2682.


Module TM2683.
Definition tm := TM_from_str "1RB1LC_1LC1RA_0LF0LD_0RE1RD_1RB1LC_---0LC".
Definition tm' := TM_from_str "1RB1LC_1LC1RA_0LE0LD_0RA1RD_---0LC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDAE") 0 0.
Time Qed.
End TM2683.


Module TM2684.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA1RE_1LE---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LC---_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDCE") 0 0.
Time Qed.
End TM2684.


Module TM2685.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA0LF_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA0LA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2685.


Module TM2686.
Definition tm := TM_from_str "1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA1RC_1LE---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LC---_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDCE") 0 0.
Time Qed.
End TM2686.


Module TM2687.
Definition tm := TM_from_str "1RB0RA_0LC1RA_1RE1LD_1LC0LF_---0RB_1LC0LD".
Definition tm' := TM_from_str "1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDED") 0 0.
Time Qed.
End TM2687.


Module TM2688.
Definition tm := TM_from_str "1RB1LC_0RC0RB_1LD0LF_1LE---_1LF0LA_1RB1LC".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA0LA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEA") 0 0.
Time Qed.
End TM2688.


Module TM2689.
Definition tm := TM_from_str "1RB1LF_0RC0RB_1LD0LA_1LE---_1LA1RE_1LD0LA".
Definition tm' := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RE_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEC") 0 0.
Time Qed.
End TM2689.


Module TM2690.
Definition tm := TM_from_str "1RB1RF_1LC0RC_1RA1LD_0RE0LB_---1RC_0RE0LB".
Definition tm' := TM_from_str "1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDED") 0 0.
Time Qed.
End TM2690.


Module TM2691.
Definition tm := TM_from_str "1RB---_0LC1RE_0LD1LC_1RA1LF_0RF0RA_0LC1RE".
Definition tm' := TM_from_str "1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEB") 0 0.
Time Qed.
End TM2691.


Module TM2692.
Definition tm := TM_from_str "1RB1LC_1LB1RA_0LF0LD_0RE1RD_1RB1LC_---0LC".
Definition tm' := TM_from_str "1RB1LC_1LB1RA_0LE0LD_0RA1RD_---0LC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDAE") 0 0.
Time Qed.
End TM2692.


Module TM2693.
Definition tm := TM_from_str "1RB1LE_1RC0RB_1LD1RC_1RB1LE_1LF0LA_1LC---".
Definition tm' := TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LC---_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCADE") 0 0.
Time Qed.
End TM2693.


Module TM2694.
Definition tm := TM_from_str "1RB1RD_1LC0RC_1RA1LD_0RE0LF_---1RC_1LC0RC".
Definition tm' := TM_from_str "1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC_------".
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  solve_eqv tm tm' (mp_from_str "ABCDEB") 0 0.
Time Qed.
End TM2694.


