(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)

open Tds
open Ast
open Type

type t1 = Ast.AstType.programme
type t2 = Ast.AstPlacement.programme


(* analyse_placement_bloc : AstType.bloc -> int -> string -> AstPlacement.bloc *)
(* Paramètre li : liste d'instructions à analyser *)
(* Paramètre depl : déplacement par rapport à la base de référence *)
(* Paramètre reg : la base de référence dans la pile *)
(* Transmet la taille du bloc et transforme le bloc en un bloc de type AstPlacement.bloc *)
let rec analyse_placement_bloc li depl reg =
  match li with
  | [] -> ([], 0)
  | i::q ->
    (* Transformation de la liste d'instructions et récupération de la taille totale du bloc *)
    let (ni, taille) = analyse_placement_instruction i depl reg in
    let (nq, taille_q) = analyse_placement_bloc q (depl+taille) reg in
    (ni::nq, taille+taille_q)
(* analyse_placement_instruction : AstType.instruction -> int -> string -> AstPlacement.instruction *)
(* Paramètre i : l'instruction à analyser *)
(* Paramètre depl : déplacement par rapport à la base de référence *)
(* Paramètre reg : la base de référence dans la pile *)
(* Transmet la taille de l'instruction et transforme l'instruction en une instruction de type AstPlacement.instruction *)
and analyse_placement_instruction i depl reg =
  match i with
  | AstType.Declaration(ia, e) ->
    begin
      (* Ecriture de l'adresse de la variable dans la pile *)
      modifier_adresse_variable depl reg ia;
      (AstPlacement.Declaration(ia, e), getTaille (get_type_var_info_ast ia))
    end
  | AstType.Affectation(a,e) -> (AstPlacement.Affectation(a, e), 0)
  | AstType.AffichageBool(e) -> (AstPlacement.AffichageBool(e), 0)
  | AstType.AffichageInt(e) -> (AstPlacement.AffichageInt(e), 0)
  | AstType.AffichageRat(e) -> (AstPlacement.AffichageRat(e), 0)
  | AstType.Conditionnelle (c,bt,be) ->
    (* Transformation des blocs *)
    let nbt = analyse_placement_bloc bt depl reg in
    let nbe = analyse_placement_bloc be depl reg in
    (AstPlacement.Conditionnelle(c, nbt, nbe), 0)
  | AstType.TantQue (c, b) ->
    (* Transformation du bloc *)
    let nb = analyse_placement_bloc b depl reg in
    (AstPlacement.TantQue(c, nb), 0)
  | AstType.Retour (e, ia) ->
    (* Récupération du type de retour de la fonction *)
    let (t_ret, ltp) = get_type_fun_info_ast ia in
    (* Récupération de la taille associée au type de retour *)
    let tt_ret = getTaille t_ret in
    (* Taille des paramètres de la fonction *)
    let t_param = List.fold_right (fun tp qsum -> (getTaille tp) + qsum) ltp 0 in
    (AstPlacement.Retour(e, tt_ret, t_param), 0)
  | AstType.Empty -> (AstPlacement.Empty, 0)



(* analyse_placement_parametre : info_ast list -> int -> string -> info_ast list *)
(* Paramètre lp : la liste des paramètres *)
(* Paramètre depl : déplacement par rapport à la base de référence *)
(* Paramètre reg : la base de référence dans la pile *)
(* Modification des paramètres pour leur donner leur adresse dans la pile *)
let rec analyse_placement_parametres lp depl reg =
  match lp with
  | [] -> []
  | ia::qlp ->
    begin
      (* Récupération de la taille associée au type du paramètre *)
      let t = getTaille (get_type_var_info_ast ia) in
      (* On donne au paramètre son adresse dans la pile *)
      modifier_adresse_variable (depl-t) reg ia;
      (* On renvoie la liste des paramètres modifiés*)
      ia::(analyse_placement_parametres qlp (depl-t) reg)
    end


(* analyse_placement_fonction : AstType.fonction -> AstPlacement.fonction *)
(* Paramètre : la fonction à analyser *)
(* Transforme la fonction en une fonction de type AstPlacement.fonction *)
let analyse_placement_fonction (AstType.Fonction(ia, lp, b)) =
  (* Transformation de la liste de paramètres *)
  let lpia = analyse_placement_parametres (List.rev lp) 0 "LB" in
  (* Transformation du bloc de la fonction *)
  let nb = analyse_placement_bloc b 3 "LB" in
  AstPlacement.Fonction(ia, lpia, nb)

(* analyser : AstType.programme -> AstPlacement.programme *)
(* Paramètre : le programme à analyser *)
(* Transforme le programme en un programme de type AstPlacement.programme *)
let analyser (AstType.Programme (fonctions, prog)) =
  (* Transformation de la liste de fonctions *)
  let nlf = List.map (analyse_placement_fonction) fonctions in
  (* Transformation du bloc du programme *)
  let nb = analyse_placement_bloc prog 0 "SB" in
  AstPlacement.Programme (nlf,nb)
