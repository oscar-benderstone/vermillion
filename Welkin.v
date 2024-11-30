(* Adapted from Vermillion files:
  - ./Example.v
  - ./Evaluation/VermillionJsonParser.v
 *)

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
  | Name : nat * list string -> ast
  | Graph : nat * list string * list ast -> ast
  | Chain : list(ast * option(ast) * ast) -> ast
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
  | dots
  | import
  | name
  | contents
  | link
  | chain
  | graph
  | graph_opt  
  | term
  | Start.
  
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
    | dots         => "dots"
    | path         => "path"
    | import       => "import"
    | name         => "name"
    | contents     => "contents"
    | link         => "link"
    | chain        => "chain"
    | graph        => "graph"
    | graph_opt    => "graph_opt"
    | term         => "term"
    | Start        => "start"
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
    | dots          => nat
    | import        => nat
    | path          => list string
    | name          => nat * list string 
    | contents      => list ast
    | link          => list (option(ast) * ast)
    | chain         => list (ast * option(ast) * ast)
    | graph         => nat * list string * list ast
    | graph_opt     => option(nat * list string * list ast)
    | term          => ast
    | Start         => list ast
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

Compute nt_semty Start.


Definition prod (lhs : nonterminal) (rhs : list symbol) 
  (action : action_ty (lhs, rhs)) :=
  existT action_ty (lhs, rhs) action.

(* Now we can define a grammar as a record 
   containing a start symbol and a list of productions. *)
Definition welkin_grammar: grammar :=
  {| start := Start; 

    prods := [

      (*start: term "," start end | empty*)
      (*term: graph chain*)
      (*chain: link chain | empty*)
      (*link: "-" graph? "->" graph |
              "<-" graph? "-" graph |
              "-" graph? "-" graph
      *)
      (*graph?: graph | empty *)
      (*graph: name contents | contents *)
      (*name: import.unit.path*)
      (*contents: "{" term "}" | emtpy *)
      (*import: ".".dots | empty*)
      (*dots: ".".dots | empty*)
      (*path: ".".unit.path*)
      (*unit: string | identifier*)
      (*string: STRING*)
      (*identifier: IDENTIFIER*)
      (*end: "," | empty*)

      prod Start [NT term ; T Comma ; NT Start ]
      (fun tup =>
      match tup with 
      | (_term, (_, (_start, _))) => _term :: _start
      end);

      prod Start []
      (fun _ => []);

      prod term [ NT graph ]
      (fun tup =>
        match tup with
        | (_graph, _) => Graph _graph
        end
      );

      (*prod term [ NT graph ; NT chain]*)
      (*(fun tup => *)
      (*match tup with *)
      (*| (_graph, (_chain, _)) => match _chain with*)
      (*  | [] => Graph _graph*)
      (*  | _link :: xs => Chain []*)
      (*  end*)
      (*end);*)

      (*prod chain [ NT link ; NT chain]*)
      (*(fun tup =>*)
      (*  match tup with*)
      (*  | (_link, (_chain, _)) => _link ++ _chain*)
      (*  end*)
      (*);*)
      (**)
      (*prod chain []*)
      (*(fun _ => []);*)
      (**)
      (*prod link [ T Dash; NT graph_opt; T RightArrow; NT graph]*)
      (*(fun tup => tup*)
      (*);*)
      (**)
      (*prod link [ NT graph; T LeftArrow ; NT graph_opt; T Dash; NT graph]*)
      (*(fun tup => *)
      (*  match tup with*)
      (*  | (target, (_, (connector, (_, (source, _))))) =>*)
      (*      let _connector := option_map Graph connector*)
      (*      in *)
      (*      [(Graph source, _connector, Graph target)]*)
      (*  end*)
      (*);*)
      (**)
      (**)
      (*prod link [ NT graph; T Dash ; NT graph_opt; T Dash; NT graph]*)
      (*(fun tup => *)
      (*  match tup with*)
      (*  | (source, (_, (connector, (_, (target, _))))) =>*)
      (*      let _connector := option_map Graph connector*)
      (*      in *)
      (*      [(Graph source, _connector, Graph target);*)
      (*       (Graph target, _connector, Graph source)*)
      (*      ]*)
      (*  end*)
      (*);*)

      prod graph_opt [ NT graph ]
      (fun tup => 
      match tup with 
      | (_graph, _) => Some _graph 
      end);

      prod graph_opt []
      (fun _ => None);

      prod graph [ NT name ; NT contents]
      (fun tup =>
        match tup with
        | (_name, (_contents, _)) => (_name, _contents)
        end
      );


      prod contents [ T LeftBrace ; NT Start ; T RightBrace ]
      (fun tup =>
        match tup with
        | (_, (_start, _)) => _start
        end
      );
      
      prod contents []
      (fun _ => []);

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

Definition parse_welkin (input : list token):=
  match parseTableOf welkin_grammar with
   | inl msg => inl msg
   | inr tbl => inr (parse tbl (NT Start) input)
   end.

(* ..a.b.c *)
Definition simple_name :=
  [tok Dot tt ; tok Dot tt ; tok Unit "a" ; tok Dot tt ; tok Unit "b" ; tok Dot tt ; tok Unit "c" ; tok Comma tt ].

Compute parse_welkin simple_name.

(* ..a.b.c, .d.ee.f, ...g.h.i.j *)
Definition simple_list :=
  [tok Dot tt ; tok Dot tt ; tok Unit "a" ; tok Dot tt ; tok Unit "b" ; tok Dot tt ; tok Unit "c" ; tok Comma tt ;
  tok Dot tt ; tok Unit "d" ; tok Dot tt ; tok Unit "ee" ; tok Dot tt ; tok Unit "f" ; tok Comma tt ;
  tok Dot tt ; tok Dot tt ; tok Dot tt ; tok Unit "g" ; tok Dot tt ; tok Unit "h" ; tok Dot tt ; tok Unit "i" ; tok Dot tt ; tok Unit "j" ; tok Comma tt 
  ].

Compute parse_welkin simple_list.

Definition simple_link : list token :=
  [tok Unit "a" ; tok Dot tt ; tok Unit "b" ; tok Dot tt; tok Dash tt ; tok Unit "b" ; tok Dot tt ; tok Unit "c" ; tok Dot tt ; tok Unit "c" ; tok RightArrow tt ; tok Unit "c"].
