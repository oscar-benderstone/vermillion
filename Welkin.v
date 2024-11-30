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
  | Link : ast * ast * ast -> ast
  | Graph : nat * list string * list ast -> ast
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
  | a
  | path 
  | dots
  | import
  | name
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
    | a => "a"
    | dots => "dots"
    | path  => "path"
    | import => "import"
    | name => "name"
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
    | a => string
    | dots   => nat
    | import => nat
    | path   => list string
    | name   => nat * list string 
    | link   => ast * ast * ast
    | graph  => list string * ast
    | term   => list ast
    | terms  => list ast
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
  {| start := name; 

    prods := [
  
      (*prod link [ NT path; T Dash; T Unit; T RightArrow; T Unit]*)
      (*(fun tup => *)
      (*  match tup with*)
      (*  | (source, (_, (connector, (_, (target, _))))) =>*)
      (*      (Path source, Path [connector], Path [target])*)
      (*  end*)
      (*);*)

      (*name: import.unit.path*)
      (*import: ".".dots | empty*)
      (*dots: ".".dots | empty*)
      (*path: ".".unit.path | empty *)

      prod name [ NT import ; T Unit ; NT path]
      (fun tup =>
        match tup with
        | (_dots, (_unit, (_path, _))) => (_dots, _unit :: _path)
        end
      );

      prod import [ T Dot ; NT dots ]
      (fun tup =>
        match tup with
        | (dot, (_dots, _)) => 1 + _dots 
        end
      );

      prod import [ ]
      (fun _ => 0);

      prod dots [ T Dot ; NT dots ]
      (fun tup =>
        match tup with 
        | (dot, (_dots, _)) => 1 + _dots 
          end
      );

      prod dots [ ]
      (fun _ => 0);

      prod path [ T Dot; T Unit ; NT path ]
      (fun tup =>
        match tup with
        | (base, (_unit, (_path, _))) =>
            _unit :: _path
        end
      );

      prod path [ ]
      (fun _ => [])

  ]
  |}.

Definition tok (a : terminal) (v : t_semty a) : token :=
  existT _ a v.

(* ..a.b.c *)
Definition simple_name : list token :=
  [tok Dot tt ; tok Dot tt ; tok Unit "a" ; tok Dot tt ; tok Unit "b" ; tok Dot tt ; tok Unit "c"].

Compute (match parseTableOf welkin_grammar with
         | inl msg => inl msg
         | inr tbl => inr (parse tbl (NT name) simple_name)
         end).

Definition simple_path : list token :=
  [tok Unit "a" ; tok Dot tt ; tok Unit "b" ; tok Dot tt].

Compute (match parseTableOf welkin_grammar with
         | inl msg => inl msg
         | inr tbl => inr (parse tbl (NT terms) simple_path)
         end).


Definition simple_link : list token :=
  [tok Unit "a" ; tok Dot tt ; tok Unit "b" ; tok Dot tt; tok Dash tt ; tok Unit "b" ; tok Dot tt ; tok Unit "c" ; tok Dot tt ; tok Unit "c" ; tok RightArrow tt ; tok Unit "c"].


Compute (match parseTableOf welkin_grammar with
         | inl msg => inl msg
         | inr tbl => inr (parse tbl (NT name) simple_link )
         end).
