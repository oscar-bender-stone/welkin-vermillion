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
  {| start := Graph;
     prods := [

       (* --- GRAPH --- *)
       (* Graph := unit? "{" Terms "}" *)
       rule (Graph, [NT UnitOpt; T LeftBracket; NT Terms; T RightBracket])
         (fun x => empty_graph);

       rule (UnitOpt, [NT Unit]) (fun x => empty_graph);
       rule (UnitOpt, [])        (fun x => empty_graph);


       (* --- TERMS (Comma List) --- *)
       (* Logic: Term -> Check Chain -> (Optional: Comma -> Check End) *)

       (* Terms := Term TermChain | epsilon *)
       rule (Terms, [NT Term; NT TermChain]) (fun x => empty_graph);
       rule (Terms, [])                      (fun x => empty_graph);

       (* TermChain := "," TermChainEnd | epsilon *)
       rule (TermChain, [T Comma; NT TermChainEnd]) (fun x => empty_graph);
       rule (TermChain, [])                         (fun x => empty_graph);

       (* TermChainEnd := Terms *)
       rule (TermChainEnd, [NT Terms]) (fun x => empty_graph);


       (* --- ARC (Decision Tree) --- *)
       (* Path 1 (RArrow): (term - term ->)+ term *)
       (* Path 2 (LArrow): (term <- term -)+ term *)
       (* Path 3 (Edge):   (term - term -)+ term *)

       (* 1. Arc := Term ArcStartDecision *)
       rule (Arc, [NT Term; NT ArcStartDecision])
         (fun x => empty_graph);

       (* 2. ArcStartDecision: Check token after first term *)
       
       (* Case '<-': Path 2 (LArrow) *)
       (* ArcStartDecision := "<-" Term "-" ArcLArrowChain *)
       rule (ArcStartDecision, [T ArrowLeft; NT Term; T Hyphen; NT ArcLArrowChain])
         (fun x => empty_graph);

       (* Case '-': Path 1 (RArrow) or Path 3 (Edge) *)
       (* ArcStartDecision := "-" Term ArcRightOrEdge *)
       rule (ArcStartDecision, [T Hyphen; NT Term; NT ArcRightOrEdge])
         (fun x => empty_graph);

       (* 3. ArcRightOrEdge: Check token after "term - term" *)
       
       (* Case '->': Path 1 (RArrow) *)
       (* ArcRightOrEdge := "->" ArcRArrowChain *)
       rule (ArcRightOrEdge, [T ArrowRight; NT ArcRArrowChain])
         (fun x => empty_graph);

       (* Case '-': Path 3 (Edge) *)
       (* ArcRightOrEdge := "-" ArcEdgeChain *)
       rule (ArcRightOrEdge, [T Hyphen; NT ArcEdgeChain])
         (fun x => empty_graph);


       (* --- ARC CHAINS (Loops) --- *)
       (* Logic: Parse the required Term, then check if we loop or stop. *)

       (* -- Left Arrow Chain (Uses <-) -- *)
       (* ArcLArrowChain := Term ArcLArrowLoop *)
       rule (ArcLArrowChain, [NT Term; NT ArcLArrowLoop]) (fun x => empty_graph);

       (* Loop: "<-" Term "-" ... *)
       rule (ArcLArrowLoop, [T ArrowLeft; NT Term; T Hyphen; NT ArcLArrowChain])
            (fun x => empty_graph);
       rule (ArcLArrowLoop, []) (fun x => empty_graph); (* Stop *)


       (* -- Right Arrow Chain (Uses ->) -- *)
       (* ArcRArrowChain := Term ArcRArrowLoop *)
       rule (ArcRArrowChain, [NT Term; NT ArcRArrowLoop]) (fun x => empty_graph);
       
       (* Loop: "-" Term "->" ... *)
       (* Note: Pattern is (term - term ->), so loop starts with '-' *)
       rule (ArcRArrowLoop, [T Hyphen; NT Term; T ArrowRight; NT ArcRArrowChain])
            (fun x => empty_graph);
       rule (ArcRArrowLoop, []) (fun x => empty_graph); (* Stop *)


       (* -- Edge Chain (Uses -) -- *)
       (* ArcEdgeChain := Term ArcEdgeLoop *)
       rule (ArcEdgeChain, [NT Term; NT ArcEdgeLoop]) (fun x => empty_graph);

       (* Loop: "-" Term "-" ... *)
       rule (ArcEdgeLoop, [T Hyphen; NT Term; T Hyphen; NT ArcEdgeChain])
            (fun x => empty_graph);
       rule (ArcEdgeLoop, []) (fun x => empty_graph); (* Stop *)


       (* --- BASIC DEFINITIONS --- *)
       rule (Base, [NT Unit])   (fun x => empty_graph);
       rule (Base, [T String])  (fun x => empty_graph);
       rule (Unit, [T Int])     (fun x => empty_graph);

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



