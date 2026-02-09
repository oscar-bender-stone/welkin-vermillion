(* SPDX-FileCopyrightText: 2026 Oscar Bender-Stone <oscar-bender-stone@protonmail.com> *)
(* SPDX-FileContributor: Gemini (Google) *)
(* SPDX-License-Identifier: BSD-3-Clause*)


Require Import String.
Require Import Ascii.
Require Import List.
Require Import ZArith.
Require Import PeanoNat. (* Required for =? operator *)
(* Adjust imports to match your setup *)
Require Import Grammar.
Require Import Main.
Require Import Generator.

Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

(* ========================================================================== *)
(* 1. THE AST (Graph)                                                         *)
(* ========================================================================== *)

Definition path := list string.

Inductive graph_elem :=
| GNode (p : path)                 (* "a.b" *)
| GArc  (src : path) (dst : path). (* "a -> b" *)

Definition graph := list graph_elem.

(* ========================================================================== *)
(* 2. GLOBAL TYPE DEFINITIONS                                                 *)
(* ========================================================================== *)

Inductive terminal_def :=
| RawChar (c : ascii)
| Dot | Comma | Hyphen | Arrow 
| Space | Tab | CR | LF.

Inductive nonterminal_def :=
| Terms | Term | Path | Unit
| Identifier | IdentifierChar
| WS.

Definition t_semty_def (a : terminal_def) : Type :=
  match a with
  | RawChar _ => ascii
  | _ => unit
  end.

Definition nt_semty_def (x : nonterminal_def) : Type :=
  match x with
  | Terms          => graph
  | Term           => graph_elem
  | Path           => path
  | Unit           => string
  | Identifier     => string
  | IdentifierChar => ascii
  | WS             => unit
  end.

Lemma t_eq_dec_def : forall (t t' : terminal_def), {t = t'} + {t <> t'}.
Proof. decide equality. apply ascii_dec. Defined.

Lemma nt_eq_dec_def : forall (nt nt' : nonterminal_def), {nt = nt'} + {nt <> nt'}.
Proof. decide equality. Defined.

(* ========================================================================== *)
(* 3. THE MODULES                                                             *)
(* ========================================================================== *)

Module Welkin_Types <: SYMBOL_TYPES 
  with Definition terminal := terminal_def
  with Definition nonterminal := nonterminal_def
  with Definition t_semty := t_semty_def
  with Definition nt_semty := nt_semty_def.

  Definition terminal := terminal_def.
  Definition nonterminal := nonterminal_def.
  Definition t_semty := t_semty_def.
  Definition nt_semty := nt_semty_def.

  Definition t_eq_dec := t_eq_dec_def.
  Definition nt_eq_dec := nt_eq_dec_def.

  Definition showT (a : terminal) : string := "tok".
  Definition showNT (x : nonterminal) : string := "nt".
End Welkin_Types.

Module Export G <: Grammar.T 
  with Module SymTy := Welkin_Types.
  Module Export SymTy := Welkin_Types.
  Module Export Defs  := DefsFn SymTy.
End G.
Module Export Gen := GeneratorFn G.

(* ========================================================================== *)
(* 4. GRAMMAR DEFINITION                                                      *)
(* ========================================================================== *)

Definition rule := existT action_ty.

(* Meta-programming for Chars *)
Definition all_ascii : list ascii :=
  let fix loop n := match n with 0 => [] | S m => ascii_of_nat m :: loop m end in loop 256.

(* Robust Char Identification (avoid pattern matching errors) *)
Definition is_structure (c : ascii) : bool :=
  let n := nat_of_ascii c in
  if (n =? 46)%nat then true (* . *)
  else if (n =? 44)%nat then true (* , *)
  else if (n =? 45)%nat then true (* - *)
  else if (n =? 62)%nat then true (* > *)
  else if (n =? 32)%nat then true (* Space *)
  else if (n =? 9)%nat  then true (* Tab *)
  else if (n =? 10)%nat then true (* LF *)
  else if (n =? 13)%nat then true (* CR *)
  else false.

Definition valid_ident_chars : list ascii :=
  List.filter (fun c => negb (is_structure c)) all_ascii.

Definition make_char_rules : list production :=
  List.map (fun c => 
    rule (IdentifierChar, [T (RawChar c)]) 
         (fun args => match args with (v, _) => v end)
  ) valid_ident_chars.

Definition welkin_grammar : grammar :=
  {| start := Terms;
     prods := [
       (* WS *)
       rule (WS, [T Space; NT WS]) (fun _ => tt);
       rule (WS, [T Tab; NT WS])   (fun _ => tt);
       rule (WS, [T CR; NT WS])    (fun _ => tt);
       rule (WS, [T LF; NT WS])    (fun _ => tt);
       rule (WS, [])               (fun _ => tt);

       (* Terms *)
       rule (Terms, [NT WS; NT Term; NT WS; NT Terms]) 
            (fun args => match args with (_, (t, (_, (ts, _)))) => t :: ts end);
            
       rule (Terms, [NT WS]) 
            (fun _ => []);

       (* Term: Arc *)
       rule (Term, [NT Path; T Hyphen; T Arrow; NT Path]) 
            (fun args => match args with (p1, (_, (_, (p2, _)))) => GArc p1 p2 end);

       (* Term: Node *)
       rule (Term, [NT Path]) 
            (fun args => match args with (p, _) => GNode p end);

       (* Path: Unit . Path *)
       rule (Path, [NT Unit; T Dot; NT Path]) 
            (fun args => match args with (u, (_, (p, _))) => u :: p end);
            
       (* Path: Unit *)
       rule (Path, [NT Unit]) 
            (fun args => match args with (u, _) => [u] end);

       (* Identifier *)
       rule (Identifier, [NT IdentifierChar; NT Identifier]) 
            (fun args => match args with (c, (s, _)) => String c s end);

       rule (Identifier, [NT IdentifierChar]) 
            (fun args => match args with (c, _) => String c EmptyString end);

       (* Unit *)
       rule (Unit, [NT Identifier]) 
            (fun args => match args with (s, _) => s end)

     ] ++ make_char_rules
  |}.

(* ========================================================================== *)
(* 5. TOKENIZER                                                               *)
(* ========================================================================== *)

Definition tok (a : terminal) (v : t_semty a) : token :=
  existT _ a v.

(* Robust Tokenizer using numeric checks *)
Definition char_to_token (c : ascii) : token :=
  let n := nat_of_ascii c in
  if (n =? 46)%nat then tok Dot tt
  else if (n =? 44)%nat then tok Comma tt
  else if (n =? 45)%nat then tok Hyphen tt
  else if (n =? 62)%nat then tok Arrow tt
  else if (n =? 32)%nat then tok Space tt
  else if (n =? 9)%nat  then tok Tab tt
  else if (n =? 10)%nat then tok LF tt
  else if (n =? 13)%nat then tok CR tt
  else tok (RawChar c) c.

Fixpoint tokenize (s : string) : list token :=
  match s with
  | EmptyString => []
  | String c s' => char_to_token c :: tokenize s'
  end.

Module Import PG := Make G.

(* --- Execution --- *)

(* The %string delimiter forces Coq to read this as a string, fixing the scope error *)
Definition input : string := "std.io -> sys.net"%string.

Compute (match parseTableOf welkin_grammar with
         | inl msg => inl msg
         | inr tbl => inr (parse tbl (NT Terms) (tokenize input))
         end).
