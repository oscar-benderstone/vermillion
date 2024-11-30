Require Import PeanoNat.
Require Import String.
(*Require Import ExtrOcamlBasic.*)
(*Require Import ExtrOcamlString.*)

(*Require Import Lexer.*)
Require Import Grammar.
Require Import Parser.
Require Import Main.

Open Scope string_scope.

(* Abstract Syntax for Welkin *)
Inductive ast :=
  | Path : list string -> ast
  | Connection : ast * ast * ast -> ast
  | Graph : list string * list ast -> ast
  | Term : list ast -> ast.

(* First, we provide the types of grammar symbols 
   and their decidable equalities. *)
Module Json_Types <: SYMBOL_TYPES.
  
  Inductive terminal' :=
  (*| Num *)
  | Unit 
  | Dot
  | LeftArrow
  | RightArrow
  | Dash
  | LeftBrace 
  | RightBrace 
  | Comma.
  
  Definition terminal := terminal'.
  
  Inductive nonterminal' :=
  | path 
  (*| name*)
  | link 
  | graph
  | term
  | terms.
  
  Definition nonterminal := nonterminal'.

  Lemma t_eq_dec : forall (t t' : terminal),
      {t = t'} + {t <> t'}.
  Proof. decide equality. Defined.
  
  Lemma nt_eq_dec : forall (nt nt' : nonterminal),
      {nt = nt'} + {nt <> nt'}.
  Proof. decide equality. Defined.

  Definition showT (a : terminal) : string :=
    match a with
    (*| Num        => "Num"*)
    | Unit       => "Unit"
    | Dot        => "."
    | LeftArrow  => "<-"
    | RightArrow => "->"
    | Dash       => "-"
    | LeftBrace  => "{"
    | RightBrace => "}" 
    | Comma      => ","
    end.

  Definition showNT (x : nonterminal) : string :=
    match x with
    | path  => "path"
    | link  => "link"
    | graph => "graph"
    | term  => "term"
    | terms  => "terms"
    end.

  Definition t_semty (a : terminal) : Type :=
    match a with
    (*| Num   => nat*)
    (*| Str   => string*)
    | Unit  => string
    | _     => unit
    end.

  Definition nt_semty (x : nonterminal) : Type :=
    match x with
    | path    => list string
    | link    => ast * ast * ast
    | graph   => list string * ast
    | term    => list ast
    | terms    => list ast
    end.

End Json_Types.

(* Next, we generate grammar definitions for those types,
   and we package the types and their accompanying defs
   into a single module *)
Module Export G <: Grammar.T.
  Module Export SymTy := Json_Types.
  Module Export Defs  := DefsFn SymTy.
End G.

(* The parser generator itself. *)
Module Export PG := Make G.


Definition prod (lhs : nonterminal) (rhs : list symbol) 
  (action : action_ty (lhs, rhs)) :=
  existT action_ty (lhs, rhs) action.

(* Now we can define a grammar as a record 
   containing a start symbol and a list of productions. *)
Definition welkin_grammar: grammar :=
  {| start := link ; 

    prods := [
  
      prod link [ NT path; T Dash; NT path; T RightArrow; NT path]
     


  ]
  |}.

Definition tok (a : terminal) (v : t_semty a) : token :=
  existT _ a v.

(* Example input to the parser:
  
   a - b -> c

*)
Definition example_prog : list token :=
  [tok Unit "a" ; tok Dash tt ; tok Unit "b" ; tok Unit "c"].
