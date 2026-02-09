(* SPDX-FileCopyrightText: 2026 Oscar Bender-Stone <oscar-bender-stone@protonmail.com> *)
(* SPDX-FileContributor: Gemini (Google) *)
(* SPDX-License-Identifier: BSD-3-Clause*)


Require Import String.
Require Import Ascii.
Require Import List.
Require Import ZArith.
Require Import PeanoNat.
Require Import Grammar.
Require Import Main.
Require Import Generator.

Import ListNotations.
Open Scope string_scope.

(* ========================================================================== *)
(* 1. AST                                                                     *)
(* ========================================================================== *)

Definition path := list string.

Inductive graph_elem :=
| GNode (p : path)
| GArc  (src : path) (dst : path).

Definition graph := list graph_elem.

(* ========================================================================== *)
(* 2. INTERFACE (Scanner Agnostic)                                            *)
(* ========================================================================== *)

Inductive terminal_def :=
| TokId
| Dot | Comma | Hyphen | Arrow 
| Space | Tab | CR | LF.

Inductive nonterminal_def :=
| Terms | Term | Path | Unit
| Identifier
| WS.

(* Map terminals to their runtime payload types. *)
Definition t_semty_def (a : terminal_def) : Type :=
  match a with
  | TokId => string
  | _     => unit
  end.

Definition nt_semty_def (x : nonterminal_def) : Type :=
  match x with
  | Terms          => graph
  | Term           => graph_elem
  | Path           => path
  | Unit           => string
  | Identifier     => string
  | WS             => unit
  end.

Lemma t_eq_dec_def : forall (t t' : terminal_def), {t = t'} + {t <> t'}.
Proof. decide equality. Defined.

Lemma nt_eq_dec_def : forall (nt nt' : nonterminal_def), {nt = nt'} + {nt <> nt'}.
Proof. decide equality. Defined.

(* ========================================================================== *)
(* 3. MODULE CONFIGURATION                                                    *)
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

  Definition showT (a : terminal) : string := 
    match a with TokId => "id" | _ => "tok" end.
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

       (* Term *)
       rule (Term, [NT Path; T Hyphen; T Arrow; NT Path]) 
            (fun args => match args with (p1, (_, (_, (p2, _)))) => GArc p1 p2 end);
       rule (Term, [NT Path]) 
            (fun args => match args with (p, _) => GNode p end);

       (* Path *)
       rule (Path, [NT Unit; T Dot; NT Path]) 
            (fun args => match args with (u, (_, (p, _))) => u :: p end);
       rule (Path, [NT Unit]) 
            (fun args => match args with (u, _) => [u] end);

       (* Unit *)
       rule (Unit, [NT Identifier]) 
            (fun args => match args with (s, _) => s end);

       (* Identifier: Bridges Grammar to Scanner via TokId *)
       rule (Identifier, [T TokId]) 
            (fun args => match args with (s, _) => s end)
     ]
  |}.

(* ========================================================================== *)
(* 5. SCANNER IMPLEMENTATION                                                  *)
(* ========================================================================== *)

Definition tok (a : terminal) (v : t_semty a) : token :=
  existT _ a v.

(* Numeric comparison prevents char_scope/string_scope ambiguity *)
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

(* Consumes characters until a structure char is found *)
Fixpoint span_ident (s : string) : string * string :=
  match s with
  | EmptyString => ("", "")
  | String c rest =>
      if is_structure c then ("", s)
      else 
        let (id, remaining) := span_ident rest in
        (String c id, remaining)
  end.

Fixpoint tokenize (s : string) : list token :=
  match s with
  | EmptyString => []
  | String c rest =>
      let n := nat_of_ascii c in
      (* Check structure tokens first *)
      if (n =? 46)%nat then tok Dot tt :: tokenize rest
      else if (n =? 44)%nat then tok Comma tt :: tokenize rest
      else if (n =? 45)%nat then tok Hyphen tt :: tokenize rest
      else if (n =? 62)%nat then tok Arrow tt :: tokenize rest
      else if (n =? 32)%nat then tok Space tt :: tokenize rest
      else if (n =? 9)%nat  then tok Tab tt :: tokenize rest
      else if (n =? 10)%nat then tok LF tt :: tokenize rest
      else if (n =? 13)%nat then tok CR tt :: tokenize rest
      else 
        (* Lex identifier using maximal munch *)
        let (id, remaining) := span_ident s in
        (* If id is empty but we aren't at structure/EOF, consume 1 char to advance (error recovery) 
           or treat as identifier. Here we assume valid id chars. *)
        match id with
        | EmptyString => tokenize remaining (* Skip unknown char *)
        | _ => tok TokId id :: tokenize remaining
        end
  end.

Module Import PG := Make G.

(* --- Execution --- *)

Definition input : string := "std.io -> sys.net"%string.

Compute (match parseTableOf welkin_grammar with
         | inl msg => inl msg
         | inr tbl => inr (parse tbl (NT Terms) (tokenize input))
         end).
