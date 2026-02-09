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
(* 1. AST (Renamed to avoid 'Graph' keyword collisions)                       *)
(* ========================================================================== *)

(* Recursive Graph structure: Name + Contents *)
Inductive WGraph :=
| MkGraph (name : string) (contents : list WGraph).

(* Graph Elements: Nodes or Arcs between Graphs *)
Inductive Welem :=
| WNode (g : WGraph)
| WArc  (src : WGraph) (dst : WGraph).

Definition result_list := list Welem.

(* Helper: Converts ["std"; "io"] -> MkGraph "std" [MkGraph "io" []] *)
Fixpoint path_to_wgraph (p : list string) : WGraph :=
  match p with
  | [] => MkGraph "" [] (* Should not occur with valid grammar *)
  | [x] => MkGraph x []
  | x :: xs => MkGraph x [path_to_wgraph xs]
  end.

(* ========================================================================== *)
(* 2. INTERFACE                                                               *)
(* ========================================================================== *)

Inductive terminal_def :=
| TokId
| Dot | Hyphen | Arrow 
| Space | Tab | CR | LF.

Inductive nonterminal_def :=
| Start         
| ElemList      (* List of elements (nodes/arcs) *)
| Term          (* A single element *)
| EdgeOpt       (* Optional edge target *)
| Op            
| OpTail        
| Path          (* Raw list of strings *)
| PathTail      
| Unit          
| Identifier
| WS.

Definition t_semty_def (a : terminal_def) : Type :=
  match a with
  | TokId => string
  | _     => unit
  end.

Definition nt_semty_def (x : nonterminal_def) : Type :=
  match x with
  | Start          => result_list
  | ElemList       => result_list
  | Term           => Welem
  | EdgeOpt        => option WGraph 
  | Op             => unit
  | OpTail         => unit
  | Path           => list string
  | PathTail       => list string
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
    match a with 
    | TokId => "Id" 
    | Dot => "." | Hyphen => "-" | Arrow => ">"
    | Space => "_" | Tab => "\t" | CR => "\r" | LF => "\n"
    end.
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
  {| start := Start;
     prods := [
       (* --- WS --- *)
       rule (WS, [T Space; NT WS]) (fun _ => tt);
       rule (WS, [T Tab; NT WS])   (fun _ => tt);
       rule (WS, [T CR; NT WS])    (fun _ => tt);
       rule (WS, [T LF; NT WS])    (fun _ => tt);
       rule (WS, [])               (fun _ => tt);

       (* --- START --- *)
       rule (Start, [NT WS; NT ElemList])
            (fun args => match args with (_, (l, _)) => l end);

       (* --- ELEMENT LIST --- *)
       rule (ElemList, [NT Term; NT ElemList])
            (fun args => match args with (t, (l, _)) => t :: l end);
       
       rule (ElemList, []) 
            (fun _ => []);

       (* --- TERM --- *)
       (* Path returns list string. We convert to recursive WGraph here. *)
       rule (Term, [NT Path; NT WS; NT EdgeOpt]) 
            (fun args => match args with (raw_p, (_, (opt, _))) => 
                           let g1 := path_to_wgraph raw_p in
                           match opt with
                           | Some g2 => WArc g1 g2
                           | None    => WNode g1
                           end
                         end);

       (* --- EDGE --- *)
       (* EdgeOpt returns option WGraph *)
       rule (EdgeOpt, [NT Op; NT WS; NT Path; NT WS])
            (fun args => match args with (_, (_, (raw_p, (_, _)))) => 
                           Some (path_to_wgraph raw_p) 
                         end);

       rule (EdgeOpt, [])
            (fun _ => None);

       (* --- FLEXIBLE ARROWS --- *)
       rule (Op, [T Hyphen; NT OpTail]) (fun _ => tt);
       rule (OpTail, [T Arrow]) (fun _ => tt);
       rule (OpTail, [T Hyphen; NT OpTail]) (fun _ => tt);
       rule (OpTail, []) (fun _ => tt);


       (* --- PATH --- *)
       rule (Path, [NT Unit; NT PathTail])
            (fun args => match args with (u, (tail, _)) => u :: tail end);

       rule (PathTail, [T Dot; NT Path])
            (fun args => match args with (_, (p, _)) => p end);
            
       rule (PathTail, [])
            (fun _ => []);

       (* --- PRIMITIVES --- *)
       rule (Unit, [NT Identifier]) 
            (fun args => match args with (s, _) => s end);

       rule (Identifier, [T TokId]) 
            (fun args => match args with (s, _) => s end)
     ]
  |}.

(* ========================================================================== *)
(* 5. SCANNER IMPLEMENTATION                                                  *)
(* ========================================================================== *)

Definition tok (a : terminal) (v : t_semty a) : token :=
  existT _ a v.

Definition is_structure (c : ascii) : bool :=
  let n := nat_of_ascii c in
  if (n =? 46)%nat then true (* . *)
  else if (n =? 45)%nat then true (* - *)
  else if (n =? 62)%nat then true (* > *)
  else if (n =? 32)%nat then true (* Space *)
  else if (n =? 9)%nat  then true (* Tab *)
  else if (n =? 10)%nat then true (* LF *)
  else if (n =? 13)%nat then true (* CR *)
  else false.

Fixpoint span_ident (s : string) : string * string :=
  match s with
  | EmptyString => ("", "")
  | String c rest =>
      if is_structure c then ("", s)
      else 
        let (id, remaining) := span_ident rest in
        (String c id, remaining)
  end.

Fixpoint tokenize_aux (fuel : nat) (s : string) : list token :=
  match fuel with
  | 0 => []
  | S n =>
    match s with
    | EmptyString => []
    | String c rest =>
        let code := nat_of_ascii c in
        if (code =? 46)%nat then tok Dot tt :: tokenize_aux n rest
        else if (code =? 45)%nat then tok Hyphen tt :: tokenize_aux n rest
        else if (code =? 62)%nat then tok Arrow tt :: tokenize_aux n rest
        else if (code =? 32)%nat then tok Space tt :: tokenize_aux n rest
        else if (code =? 9)%nat  then tok Tab tt :: tokenize_aux n rest
        else if (code =? 10)%nat then tok LF tt :: tokenize_aux n rest
        else if (code =? 13)%nat then tok CR tt :: tokenize_aux n rest
        else 
          let (id, remaining) := span_ident s in
          match id with
          | EmptyString => tokenize_aux n rest
          | _ => tok TokId id :: tokenize_aux n remaining
          end
    end
  end.

Definition tokenize (s : string) : list token :=
  tokenize_aux (String.length s) s.

Module Import PG := Make G.

(* --- Execution --- *)

Definition input : string := "std.io -> sys.net"%string.

Compute (match parseTableOf welkin_grammar with
         | inl msg => inl msg
         | inr tbl => inr (parse tbl (NT Start) (tokenize input))
         end).
