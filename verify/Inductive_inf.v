Require Export Ascii String.
Require Export PeanoNat NArith.
From BusyCoq Require Import Inductive BBinf.

Module Inductive_inf := Inductive BBinf.
Export Inductive_inf.

Fixpoint Decimal_uint_to_str x:string :=
match x with
| Decimal.Nil => ""
| Decimal.D0 x => "0" ++ Decimal_uint_to_str x
| Decimal.D1 x => "1" ++ Decimal_uint_to_str x
| Decimal.D2 x => "2" ++ Decimal_uint_to_str x
| Decimal.D3 x => "3" ++ Decimal_uint_to_str x
| Decimal.D4 x => "4" ++ Decimal_uint_to_str x
| Decimal.D5 x => "5" ++ Decimal_uint_to_str x
| Decimal.D6 x => "6" ++ Decimal_uint_to_str x
| Decimal.D7 x => "7" ++ Decimal_uint_to_str x
| Decimal.D8 x => "8" ++ Decimal_uint_to_str x
| Decimal.D9 x => "9" ++ Decimal_uint_to_str x
end.

Definition N_to_str x :=
  Decimal_uint_to_str (N.to_uint x).

Definition Q'_from_char(x:ascii):BBinf.Q :=
((N_of_ascii x)-(N_of_ascii "A"%char))%N.

Definition dir_from_char(x:ascii):option dir :=
match x with
| "L"%char => Some L
| "R"%char => Some R
| _ => None
end.

Definition Sym'_from_char(x:ascii):BBinf.Sym :=
((N_of_ascii x)-(N_of_ascii "0"%char))%N.

Definition trans'_from_char(c0 c1 c2:ascii):option (BBinf.Sym * dir * BBinf.Q) :=
  match (Sym'_from_char c0),(dir_from_char c1),(Q'_from_char c2) with
  | o, Some d, s => Some (o,d,s)
  | _,_,_ => None
  end.

Definition trans'_from_str(x:string): string*(option (BBinf.Sym * dir * BBinf.Q)) :=
match x with
| (String c0 (String c1 (String c2 x0))) =>
  (x0,trans'_from_char c0 c1 c2)
| _ => (x,None)
end.

Definition skip_sep(x:string): option string :=
match x with
| String ("_"%char) x0 => Some x0
| _ => None
end.

Definition skip_trans_from_str(x:string): string :=
match x with
| (String c0 (String c1 (String c2 x0))) =>
  x0
| _ => x
end.

Fixpoint TM'_from_str_rec(x:string)(T:nat)(q s:N):=
match T with
| O => None
| Datatypes.S T0 =>
  match q with
  | N0 =>
    match skip_sep x with
    | Some x0 => None
    | None =>
    match s with
    | N0 => let (x0,tr):=trans'_from_str x in tr
    | _ => let (x0,tr):=trans'_from_str x in TM'_from_str_rec x0 T0 q (N.pred s)
    end
    end
  | _ =>
    match skip_sep x with
    | Some x0 =>
      TM'_from_str_rec x0 T0 (N.pred q) s
    | None =>
      let x0:=skip_trans_from_str x in
      TM'_from_str_rec x0 T0 q s
    end
  end
end.

Definition TM'_from_str(x:string):TM :=
  fun '(q,s)=>
  TM'_from_str_rec x (Datatypes.S (String.length x)) q s.

Open Scope string.
Open Scope list.

Fixpoint Decimal_uint_of_str x :=
match x with
| String "0" x0 => Decimal.D0 (Decimal_uint_of_str x0)
| String "1" x0 => Decimal.D1 (Decimal_uint_of_str x0)
| String "2" x0 => Decimal.D2 (Decimal_uint_of_str x0)
| String "3" x0 => Decimal.D3 (Decimal_uint_of_str x0)
| String "4" x0 => Decimal.D4 (Decimal_uint_of_str x0)
| String "5" x0 => Decimal.D5 (Decimal_uint_of_str x0)
| String "6" x0 => Decimal.D6 (Decimal_uint_of_str x0)
| String "7" x0 => Decimal.D7 (Decimal_uint_of_str x0)
| String "8" x0 => Decimal.D8 (Decimal_uint_of_str x0)
| String "9" x0 => Decimal.D9 (Decimal_uint_of_str x0)
| _ => Decimal.Nil
end.

Definition pr{A}(x:A)(s:string):A :=
  x.

Fixpoint parse_args(ls:list string)(cfg:Config)(tm:option TM)(T:N): unit :=
match ls with
| "--maxT"::h0::t => parse_args t cfg tm (N.of_uint (Decimal_uint_of_str h0))
| "--max-repeater-len"::h0::t => parse_args t (upd_config [set_max_repeater_len (Nat.of_uint (Decimal_uint_of_str h0))] cfg) tm T
| "--max-repeater-size"::h0::t => parse_args t (upd_config [set_max_repeater_size (Some (N.of_uint (Decimal_uint_of_str h0)))] cfg) tm T
| "--block-size"::h0::t =>
  let n:=Nat.of_uint (Decimal_uint_of_str h0) in
  let cfg:=
  upd_config [
    set_max_repeater_size (Some (N.of_nat n));
    set_max_repeater_len n;
    set_fixed_block_size (Some n)
    ] cfg in
  parse_args t cfg tm T
| "--arithseq"::t => parse_args t (upd_config [set_enable_arithseq true] cfg) tm T
| "--exploop"::t => parse_args t (config_exploop cfg) tm T
| h::t =>
  parse_args t cfg (Some (TM'_from_str (pr h h))) T
| [] =>
  match tm with
  | None => pr tt "
Usage:
--maxT n: max amount of simulator steps
--max-repeater-len n: max length of a repeater
--max-repeater-size n: max length of a repeater, counted by amount of symbols
--block-size n: only allow repeater of n symbols
--arithseq: enable detection of arithmetic sequence
--exploop: enable detection of exponential loops at top level
"
  | Some tm =>
  match hlin_layers_steps tm cfg T with
  | inr ((_,(w1,w0),_)::_) =>
    if check_nonhalt (fst w0) then pr tt "nonhalting" else
    match get_halts_at tm (fst w0) with
    | Some (q,s) =>
      pr tt ("halts at " ++ N_to_str q ++ " " ++ N_to_str s)
    | _ => pr tt "failed to decide"
    end
  | _ => pr tt "failed to decide"
  end
  end
end.

Definition exec ls := parse_args ls default_config None (10^9).

Require Import Extraction ExtrOCamlInt63 ExtrOCamlPArray ExtrOcamlNativeString.
Extract Constant PArray.array "'a" => "'a Parray.t".
Extraction NoInline PArray.array.
Extract Constant pr =>
  "fun x s ->
     Printf.printf ""[%.3f s] %s\n%!"" (Sys.time ()) s;
     x".
Time Extraction "Inductive" exec.



