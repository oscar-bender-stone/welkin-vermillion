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

Module Welkin_Types <: SYMBOL_TYPES. 
  Inductive terminal' :=
  | Comma | Dash | LeftArrow | RightArrow | LeftBracket | RightBracket | String.
  
  Definition terminal := terminal'.
  
  Inductive nonterminal' :=
  | Term | Arc | Graph.
  
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
    | Term => "Term"
    | Arc => "Arc"
    | Graph => "Graph"
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

(*Print nullable_gamma.*)



