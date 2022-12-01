(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)

open Tds
open Ast
open Type

type t1 = Ast.AstType.programme
type t2 = Ast.AstPlacement.programme


(* analyse_placement_bloc : tds -> info_ast option -> AstType.bloc -> AstPlacement.bloc *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc en un bloc de type AstPlacement.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_placement_bloc li depl reg =
  (* TODO: Rajouter commentaire *)
  match li with
  | [] -> ([], 0)
  | i::q ->
    let (ni, taille) = analyse_placement_instruction i depl reg in
    let (nq, taille_q) = analyse_placement_bloc q (depl+taille) reg in
    (ni::nq, taille+taille_q)
(* analyse_placement_instruction : tds -> info_ast option -> AstType.instruction -> AstPlacement.instruction *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstPlacement.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_placement_instruction i depl reg =
  match i with
  | AstType.Declaration(ia, e) ->
    begin
      modifier_adresse_variable depl reg ia;
      (AstPlacement.Declaration(ia, e), getTaille (get_type_var_info_ast ia))
    end
  | AstType.Affectation(ia,e) -> (AstPlacement.Affectation(ia, e), 0)
  | AstType.AffichageBool(e) -> (AstPlacement.AffichageBool(e), 0)
  | AstType.AffichageInt(e) -> (AstPlacement.AffichageInt(e), 0)
  | AstType.AffichageRat(e) -> (AstPlacement.AffichageRat(e), 0)
  | AstType.Conditionnelle (c,bt,be) ->
    let nbt = analyse_placement_bloc bt depl reg in
    let nbe = analyse_placement_bloc be depl reg in
    (AstPlacement.Conditionnelle(c, nbt, nbe), 0)
  | AstType.TantQue (c, b) ->
    let nb = analyse_placement_bloc b depl reg in
    (AstPlacement.TantQue(c, nb), 0)
  | AstType.Retour (e, ia) ->
    let (t_ret, ltp) = get_type_fun_info_ast ia in
    let tt_ret = getTaille t_ret in
    let t_param = List.fold_right (fun tp qsum -> (getTaille tp) + qsum) ltp 0 in
    (AstPlacement.Retour(e, tt_ret, t_param), 0)
  | AstType.Empty -> (AstPlacement.Empty, 0)


(* TODO: commentaires *)
(* analyse_placement_parametre : tds -> (typ * string) -> (typ * info_ast) *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre (t, n) : type (t) et nom (n) du paramètre à analyser *)
(* Vérifie la bonne utilisation du paramètre et le tranforme en paramètre de type (typ * info_ast) *)
let rec analyse_placement_parametres lp depl reg =
  match lp with
  | [] -> []
  | ia::qlp ->
    begin
      let t = getTaille (get_type_var_info_ast ia) in
      modifier_adresse_variable (depl-t) reg ia;
      ia::(analyse_placement_parametres qlp (depl-t) reg)
    end

(* TODO: commentaires *)
(* analyse_placement_fonction : tds -> AstType.fonction -> AstPlacement.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstPlacement.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_placement_fonction (AstType.Fonction(ia, lp, b)) =
  let lpia = analyse_placement_parametres (List.rev lp) 0 "LB" in
  let nb = analyse_placement_bloc b 3 "LB" in
  AstPlacement.Fonction(ia, lpia, nb)

(* analyser : AstType.programme -> AstPlacement.programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstPlacement.programme *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstType.Programme (fonctions, prog)) =
  let nlf = List.map (analyse_placement_fonction) fonctions in
  let nb = analyse_placement_bloc prog 0 "SB" in
  AstPlacement.Programme (nlf,nb)
