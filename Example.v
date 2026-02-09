Require Import String.
Require Import Grammar.
Require Import Main.
Require Import Generator.
Open Scope string_scope.

(*
Original, naive grammar:
 
    start ::= (term ",")* term
    term ::= arc | graph | base
    arc ::= (term "-" term "->")+ term
          | (term "<-" term "-")+ term
          | (term "-" term "-")+ term
    graph ::= unit? "{" term* "}"
    base ::= unit | string
    unit ::= int
*)

(* AST nodes *)
Inductive base :=
| int.

Inductive graph :=
| contents: list graph -> graph
| arc: graph * graph * graph -> graph.

Definition empty_graph := contents [].

Module Welkin_Types <: SYMBOL_TYPES. 
  Inductive terminal' :=
  | Comma | Dash | LeftArrow | RightArrow | LeftBracket | RightBracket | String.
  
  Definition terminal := terminal'.
  
  Inductive nonterminal' :=
  | Terms | TermChain | Term | Arc | Graph | End.
  
  Definition nonterminal := nonterminal'.

  Lemma t_eq_dec : forall (t t' : terminal),
      {t = t'} + {t <> t'}.
  Proof. decide equality. Defined.
  
  Lemma nt_eq_dec : forall (nt nt' : nonterminal),
      {nt = nt'} + {nt <> nt'}.
  Proof. decide equality. Defined.

  Definition showT (a : terminal) : string :=
    match a with
    | Comma    => ","
    | Dash     => "-"
    | LeftArrow => "->"
    | RightArrow => "<-"
    | LeftBracket => "{"
    | RightBracket => "}"
    | String => "String"
    end.

  Definition showNT (x : nonterminal) : string :=
    match x with
    | Terms => "Terms"
    | TermChain => "TermChain"
    | Term => "Term"
    | Arc => "Arc"
    | Graph => "Graph"
    | End => "End"
    end.
  
  (* A Num token carries a natural number -- no other token
     carries a meaningful semantic value. *)
  Definition t_semty (a : terminal) : Type :=
    match a with
    | String => string
    | _  => unit
    end.

  Definition nt_semty (x : nonterminal) : Type := graph.

End Welkin_Types.


Module Export G <: Grammar.T.
  Module Export SymTy := Welkin_Types.
  Module Export Defs  := DefsFn SymTy.
End G.

Module Export Gen := GeneratorFn G.

Definition rule := existT action_ty.

Definition welkin_grammar : grammar :=
  {| start := Terms;
     prods := [

      (* terms := term "," terms *)
      rule (Terms, [NT Term; NT TermChain])
        (fun x => empty_graph);

      rule (TermChain, [T Comma; NT Term])
        (fun x => empty_graph);

      rule (TermChain, [])
        (fun x => empty_graph);

      rule (End, [T Comma])
        (fun x => empty_graph);
      rule (End, [])
        (fun x => empty_graph);

      (* terms := arc | graph *)
      rule (Term, [T LeftBracket; T RightBracket])
        (fun x => empty_graph)
    ]
  |}.

(* Now we create a module that gives us access to
   the top-level parser generator functions:

   parseTableOf : grammar -> option parse_table

   parse : parse_table -> symbol -> list terminal -> 
           sum parse_failure (tree * list terminal) *)
Module Import PG := Make G.

Definition tok (a : terminal) (v : t_semty a) : token :=
  existT _ a v.

Definition welkin_example : list token :=
  [tok LeftBracket tt; tok RightBracket tt].

Compute (match parseTableOf welkin_grammar with
         | inl msg => inl msg
         | inr tbl => inr (parse tbl (NT Terms) welkin_example)
         end).

Print nullable_gamma.



