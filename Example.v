Require Import String.
Require Import Grammar.
Require Import Main.
Require Import Generator.
Require Import ZArith.

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

Inductive graph :=
| contents: list graph -> graph
| arc: graph * graph * graph -> graph.

Definition empty_graph := contents [].

Module Welkin_Types <: SYMBOL_TYPES. 
  Inductive terminal' :=
  | Comma
  | Hyphen | ArrowLeft | ArrowRight
  | LeftBracket | RightBracket
  | String | Int.
  
  Definition terminal := terminal'.
  
  Inductive nonterminal' :=
  | Graph | UnitOpt
  | Terms | TermChain | TermChainEnd | Term   (* List Logic *)
  | Arc
  | ArcStartDecision    (* Was ArcTail: Decides between '<-' and '-' *)
  | ArcRightOrEdge      (* Was ArcHyphenSplit: Decides between '->' and '-' *)
  | ArcLArrowChain      (* The rest of the ( ... <- ... - ) chain *)
  | ArcLArrowLoop       (* The repeating part of the LArrow chain *)
  | ArcRArrowChain      (* The rest of the ( ... - ... -> ) chain *)
  | ArcRArrowLoop       (* The repeating part of the RArrow chain *)
  | ArcEdgeChain        (* The rest of the ( ... - ... - ) chain *)
  | ArcEdgeLoop         (* The repeating part of the Edge chain *)
  | Base | Unit.
  
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
    | Hyphen => "-"
    | ArrowLeft => "->"
    | ArrowRight => "<-"
    | LeftBracket => "{"
    | RightBracket => "}"
    | String => "String"
    | Int => "Int"
    end.

  Definition showNT (x : nonterminal) : string :=
    match x with
    | Graph            => "Graph"
    | UnitOpt          => "UnitOpt"
    | Terms            => "Terms"
    | TermChain        => "TermChain"
    | TermChainEnd     => "TermChainEnd"
    | Term             => "Term"
    | Arc              => "Arc"
    | ArcStartDecision => "ArcStartDecision"
    | ArcRightOrEdge   => "ArcRightOrEdge"
    | ArcLArrowChain   => "ArcLArrowChain"
    | ArcLArrowLoop    => "ArcLArrowLoop"
    | ArcRArrowChain   => "ArcRArrowChain"
    | ArcRArrowLoop    => "ArcRArrowLoop"
    | ArcEdgeChain     => "ArcEdgeChain"
    | ArcEdgeLoop      => "ArcEdgeLoop"
    | Base             => "Base"
    | Unit             => "Unit"
    end. 
  (* A Num token carries a natural number -- no other token
     carries a meaningful semantic value. *)
  Definition t_semty (a : terminal) : Type :=
    match a with
    | String => string
    | Int => Z
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
  {| start := Terms;  (* <--- FIXED: Start is now the list of terms *)
     prods := [

       (* --- TERMS (Comma List) --- *)
       (* Matches: epsilon | term | term, term | term, *)
       
       (* Terms := Term TermChain | epsilon *)
       (* If input is empty, we match epsilon. If we see a Term start, we parse Term. *)
       rule (Terms, [NT Term; NT TermChain]) (fun x => empty_graph);
       rule (Terms, [])                      (fun x => empty_graph);

       (* TermChain := "," TermChainEnd | epsilon *)
       (* After a term, if we see a comma, consume it. If not, we are done. *)
       rule (TermChain, [T Comma; NT TermChainEnd]) (fun x => empty_graph);
       rule (TermChain, [])                         (fun x => empty_graph);

       (* TermChainEnd := Terms *)
       (* After the comma, we loop back to Terms. *)
       (* If there is another term, Terms parses it. *)
       (* If the input ends (trailing comma), Terms parses epsilon. *)
       rule (TermChainEnd, [NT Terms]) (fun x => empty_graph);


       (* --- ARC (Decision Tree) --- *)
       (* 1. Arc := Term ArcStartDecision *)
       rule (Arc, [NT Term; NT ArcStartDecision])
         (fun x => empty_graph);

       (* 2. ArcStartDecision: Check token after first term *)
       rule (ArcStartDecision, [T ArrowLeft; NT Term; T Hyphen; NT ArcLArrowChain])
         (fun x => empty_graph);
       rule (ArcStartDecision, [T Hyphen; NT Term; NT ArcRightOrEdge])
         (fun x => empty_graph);

       (* 3. ArcRightOrEdge: Check token after "term - term" *)
       rule (ArcRightOrEdge, [T ArrowRight; NT ArcRArrowChain])
         (fun x => empty_graph);
       rule (ArcRightOrEdge, [T Hyphen; NT ArcEdgeChain])
         (fun x => empty_graph);


       (* --- ARC CHAINS (Loops) --- *)

       (* -- Left Arrow Chain (Uses <-) -- *)
       rule (ArcLArrowChain, [NT Term; NT ArcLArrowLoop]) (fun x => empty_graph);
       rule (ArcLArrowLoop, [T ArrowLeft; NT Term; T Hyphen; NT ArcLArrowChain])
            (fun x => empty_graph);
       rule (ArcLArrowLoop, []) (fun x => empty_graph); 


       (* -- Right Arrow Chain (Uses ->) -- *)
       rule (ArcRArrowChain, [NT Term; NT ArcRArrowLoop]) (fun x => empty_graph);
       rule (ArcRArrowLoop, [T Hyphen; NT Term; T ArrowRight; NT ArcRArrowChain])
            (fun x => empty_graph);
       rule (ArcRArrowLoop, []) (fun x => empty_graph); 


       (* -- Edge Chain (Uses -) -- *)
       rule (ArcEdgeChain, [NT Term; NT ArcEdgeLoop]) (fun x => empty_graph);
       rule (ArcEdgeLoop, [T Hyphen; NT Term; T Hyphen; NT ArcEdgeChain])
            (fun x => empty_graph);
       rule (ArcEdgeLoop, []) (fun x => empty_graph);


       (* --- BASIC DEFINITIONS --- *)
       rule (Base, [NT Unit])   (fun x => empty_graph);
       rule (Base, [T String])  (fun x => empty_graph);
       rule (Unit, [T Int])     (fun x => empty_graph);

       (* Note: Term logic here assumes a Term is enclosed in braces or is a base unit *)
       (* Adjust this rule if a "Term" is just a Base/Arc without brackets *)
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



