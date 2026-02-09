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
    graph ::= unit? { term* }
    base ::= unit | string
    unit ::= int
*)

Inductive base :=
| int.

Inductive term :=
| arc : term * term * term -> term.

(* Abstract syntax for the language that Grammar 3.11 represents.
   The values that our parser produces will be ASTs with these types. *)
Inductive exp :=
| Cmp_exp : nat -> nat -> exp.

Inductive stmt :=
| If_stmt    : exp -> stmt -> stmt -> stmt
| Begin_stmt : list stmt -> stmt
| Print_stmt : exp -> stmt.

(* First, we provide the types of grammar symbols 
   and their decidable equalities. *)
Module G311_Types <: SYMBOL_TYPES.
  
  Inductive terminal' :=
  | If | Then | Else | Begin | Print | End | Semi | Num | Eq.
  
  Definition terminal := terminal'.
  
  Inductive nonterminal' :=
  | S | L | E.
  
  Definition nonterminal := nonterminal'.

  Lemma t_eq_dec : forall (t t' : terminal),
      {t = t'} + {t <> t'}.
  Proof. decide equality. Defined.
  
  Lemma nt_eq_dec : forall (nt nt' : nonterminal),
      {nt = nt'} + {nt <> nt'}.
  Proof. decide equality. Defined.

  Definition showT (a : terminal) : string :=
    match a with
    | If    => "If"
    | Then  => "Then"
    | Else  => "Else"
    | Begin => "Begin"
    | Print => "Print"
    | End   => "End"
    | Semi  => ";"
    | Num   => "Num"
    | Eq    => "="
    end.

  Definition showNT (x : nonterminal) : string :=
    match x with
    | S => "S"
    | L => "L"
    | E => "E"
    end.
  
  (* A Num token carries a natural number -- no other token
     carries a meaningful semantic value. *)
  Definition t_semty (a : terminal) : Type :=
    match a with
    | Num => nat
    | _   => unit
    end.

  Definition nt_semty (x : nonterminal) : Type :=
    match x with
    | S => stmt
    | L => list stmt
    | E => exp
    end.

End G311_Types.

(* Next, we generate grammar definitions for those types,
   and we package the types and their accompanying defs
   into a single module *)
Module Export G <: Grammar.T.
  Module Export SymTy := G311_Types.
  Module Export Defs  := DefsFn SymTy.
End G.

(* Now we can instantiate the generator with our grammar module *)
Module Export Gen := GeneratorFn G.


(* Now we can represent the grammar from the textbook
   as a record with "start" and "prods" fields. *)
Definition g311 : grammar :=
  {| start := S ;
     prods := [existT action_ty
                      (S, [T If; NT E; T Then; NT S; T Else; NT S])
                      (fun tup =>
                         match tup with
                         | (_, (e, (_, (s1, (_, (s2, _)))))) =>
                           If_stmt e s1 s2
                         end);
                 
               existT action_ty
                      (S, [T Begin; NT S; NT L])
                      (fun tup =>
                         match tup with
                         | (_, (s, (ss, _))) =>
                           Begin_stmt (s :: ss)
                         end);
                      
               existT action_ty
                      (S, [T Print; NT E])
                      (fun tup =>
                         match tup with
                         | (_, (e, _)) =>
                           Print_stmt e
                         end);
                 
               existT action_ty
                      (L, [T End])
                      (fun _ => []);
                         
               existT action_ty
                      (L, [T Semi; NT S; NT L])
                      (fun tup =>
                         match tup with
                         | (_, (s, (ss, _))) =>
                           s :: ss
                         end);
                 
               existT action_ty
                      (E, [T Num; T Eq; T Num])
                      (fun tup =>
                         match tup with
                         | (n1, (_, (n2, _))) =>
                           Cmp_exp n1 n2
                         end)]
  |}.

(* Now we create a module that gives us access to
   the top-level parser generator functions:

   parseTableOf : grammar -> option parse_table

   parse : parse_table -> symbol -> list terminal -> 
           sum parse_failure (tree * list terminal) *)
Module Import PG := Make G.

Definition tok (a : terminal) (v : t_semty a) : token :=
  existT _ a v.

(* Example input to the parser:

   if 2 = 5 then
     print 2 = 5
   else 
     print 42 = 42

*)
Definition example_prog : list token :=
  [tok If tt; tok Num 2; tok Eq tt; tok Num 5; tok Then tt;
     tok Print tt; tok Num 2; tok Eq tt; tok Num 5;
   tok Else tt;
     tok Print tt; tok Num 42; tok Eq tt; tok Num 42].

(* Now we can generate an LL(1) parse table for the grammar
   and use it to parse the example input. *)
Compute (match parseTableOf g311 with
         | inl msg => inl msg
         | inr tbl => inr (parse tbl (NT S) example_prog)
         end).

(* Malformed input -- missing an equals sign operand *)
Definition buggy_prog : list token :=
  [tok If tt; tok Num 2; tok Eq tt; tok Num 5; tok Then tt;
     tok Print tt; tok Num 2; tok Eq tt;
   tok Else tt;
     tok Print tt; tok Num 42; tok Eq tt; tok Num 42].

Compute (match parseTableOf g311 with
         | inl msg => inl msg
         | inr tbl => inr (parse tbl (NT S) buggy_prog)
         end).

Definition duplicate_redundant_grammar : grammar :=
  {| start := S ;
     prods := [existT action_ty
                      (S, [T Print; NT E])
                      (fun tup =>
                         match tup with
                         | (_, (e, _)) =>
                           Print_stmt e
                         end);

               (* This production appears twice,
                  with the same semantic action *)
               existT action_ty
                      (E, [T Num; T Eq; T Num])
                      (fun tup =>
                         match tup with
                         | (n1, (_, (n2, _))) =>
                           Cmp_exp n1 n2
                         end);

               existT action_ty
                      (E, [T Num; T Eq; T Num])
                      (fun tup =>
                         match tup with
                         | (n1, (_, (n2, _))) =>
                           Cmp_exp n1 n2
                         end)]
  |}.

Compute (match parseTableOf duplicate_redundant_grammar with
         | inl msg => inl msg
         | inr tbl => inr (parse tbl (NT S) example_prog)
         end).

Definition non_LL1_grammar : grammar :=
  {| start := S ;
     prods := [existT action_ty
                      (S, [T Print; NT E])
                      (fun tup =>
                         match tup with
                         | (_, (e, _)) =>
                           Print_stmt e
                         end);

               existT action_ty
                      (S, [T Print; NT E; T Semi])
                      (fun tup =>
                         match tup with
                         | (_, (e, (s, _))) =>
                           Print_stmt e
                         end);
               
               existT action_ty
                      (E, [T Num; T Eq; T Num])
                      (fun tup =>
                         match tup with
                         | (n1, (_, (n2, _))) =>
                           Cmp_exp n1 n2
                         end)]
  |}.

Compute (match parseTableOf non_LL1_grammar with
         | inl msg => inl msg
         | inr tbl => inr (parse tbl (NT S) example_prog)
         end).


(**
    Inductive nullable_sym (g : grammar) : symbol -> Prop :=
    | NullableSym : forall x ys f,
        In (existT _ (x, ys) f) g.(prods)
        -> nullable_gamma g  
        -> nullable_sym g (NT x)
(* Note, this means, if we want to write an empty production, we need to explicitly state it as going to empty set [] *)
(* Specification of nullable_grammar *)
    with nullable_gamma (g : grammar) : list symbol -> Prop :=
         | NullableNil  : nullable_gamma g [] (* rhs is blank, that's empty *)
         | NullableCons : forall hd: symbol tl: [symbol],
             nullable_sym g hd
             -> nullable_gamma g tl
             -> nullable_gamma g (hd :: tl).
**)

Print nullable_gamma.

Theorem terminals_are_not_nullable : forall (g: grammar) (t: terminal), ~ nullable_sym g (T t).
Proof. unfold not. intros. inversion H. Qed.




