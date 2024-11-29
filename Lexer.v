From Coq Require Import ZArith.
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.

(* Adpated from Software Foundations, Volume 1: 
  https://softwarefoundations.cis.upenn.edu/lf-current/Preface.html
*)

Definition isLayout (c : ascii) : bool :=
  let n := nat_of_ascii c in
  match n with
  | 9 => true  (* Tab  *)
  | 10 => true (* Newline *)
  | 11 => true (* Vertical tab *)
  | 13 => true (* Carriage Return *)
  | 32 => true (* Space *)
  | _ => false
  end.

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (97 <=? n) (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     andb (48 <=? n) (n <=? 57).

Inductive character_group := digit | alpha | layout | other.

Definition classifyChar (c : ascii) : character_group :=
  if isDigit c then
    digit 
  else if isAlpha c then
    alpha
  else if isLayout c then
    layout  
  else
    other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.

Fixpoint tokenize_helper (cls : character_group) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "("      =>
      tk ++ ["("]::(tokenize_helper other [] xs')
    | _, _, ")"      =>
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, layout, _    =>
      tk ++ (tokenize_helper layout [] xs')
    | alpha,alpha,x  =>
      tokenize_helper alpha (x::acc) xs'
    | digit,digit,x  =>
      tokenize_helper digit (x::acc) xs'
    | other,other,x  =>
      tokenize_helper other (x::acc) xs'
    | _,tp,x         =>
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper layout [] (list_of_string s)).
