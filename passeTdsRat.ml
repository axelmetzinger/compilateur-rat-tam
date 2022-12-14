(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Tds
open Exceptions
open Ast
open Printf

type t1 = Ast.AstSyntax.programme
type t2 = Ast.AstTds.programme

(* analyse_tds_affectable : tds -> AstSyntax.affectable -> bool -> AstTds.affectable *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Paramètre ecriture : true si l'affectable est utilisé en écriture, false sinon *)
(* Vérifie la bonne utilisation des affectable et transforme l'affectable
en un affectable de type AstTds.affectable *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_affectable tds a ecriture =
  match a with
  | AstSyntax.Ident nom -> 
    begin
      match (chercherGlobalement tds nom) with
      (* L'identifiant recherché n'existe pas *)
      | None -> raise (IdentifiantNonDeclare nom)
      (* L'identifiant est trdans la tds *)
      | Some ia ->
        (* Récupération de l'information associée à l'identifiant *)
        let info = info_ast_to_info ia in
        begin
          match info with
          (* C'est une information sur une variable *)
          | InfoVar _ -> AstTds.Ident(ia)
          (* C'est une information sur une constante *)
          | InfoConst(nom, _) ->
            if ecriture then raise (MauvaiseUtilisationIdentifiant nom)
            else AstTds.Const(ia)
          (* C'est une information sur une fonction *)
          | _ -> raise (MauvaiseUtilisationIdentifiant nom)
        end
    end
  | AstSyntax.DeRef da ->
    (* Analyse de l'affectable et renvoie du nouveau DeRef *)
    let nda = analyse_tds_affectable tds da ecriture in
    AstTds.DeRef(nda)

(* analyse_tds_expression : tds -> AstSyntax.expression -> AstTds.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme l'expression
en une expression de type AstTds.expression *)
(* Erreur si mauvaise utilisation des identifiants et accès à l'adresse d'une constante ou d'une fonction *)
and analyse_tds_expression tds e =
  match e with
  | AstSyntax.AppelFonction(nom, le) ->
    begin
      match (chercherGlobalement tds nom) with
      (* L'identifiant recherché n'existe pas *)
      |None -> raise (IdentifiantNonDeclare nom)
      (* L'identifiant est trdans la tds *)
      | Some ia ->
        (* Récupération de l'information associée à l'identifiant *)
        let info = info_ast_to_info ia in
        begin
          match info with
          (* C'est une information sur une fonction*)
          | InfoFun(_, _, _) ->
            (* Création d'une nouvelle liste d'expressions *)
            let nle = List.map (analyse_tds_expression tds) le in
            AstTds.AppelFonction(ia, nle)
          (* C'est une information sur une constante ou une variable *)
          | _ -> raise (MauvaiseUtilisationIdentifiant nom)
        end
    end
  | AstSyntax.Affectable(a) ->
    (* Analyse de l'affectable et renvoie du nouveau *)
    let na = analyse_tds_affectable tds a false in
    AstTds.Affectable(na)
  | AstSyntax.Booleen(b) -> AstTds.Booleen(b)
  | AstSyntax.Entier(i) -> AstTds.Entier(i)
  | AstSyntax.Unaire (op, e) ->
    (* Analyse de l'expression *)
    let ne = analyse_tds_expression tds e in
    AstTds.Unaire(op, ne)
  | AstSyntax.Binaire (op, e1, e2) ->
    (* Analyse des expressions de l'opération binaire *)
    let ne1 = analyse_tds_expression tds e1 in
    let ne2 = analyse_tds_expression tds e2 in
    AstTds.Binaire(op, ne1, ne2)
  | AstSyntax.Ternaire (c, e1, e2) ->
    (* Analyse de la condition *)
    let nc = analyse_tds_expression tds c in
    (* Analyse des expressions de l'opération ternaire *)
    let ne1 = analyse_tds_expression tds e1 in
    let ne2 = analyse_tds_expression tds e2 in
    AstTds.Ternaire(nc, ne1, ne2)
  | AstSyntax.New t -> AstTds.New(t)
  | AstSyntax.Adresse nom ->
    begin
      match (chercherGlobalement tds nom) with
      (* L'identifiant recherché n'existe pas *)
      |None -> raise (IdentifiantNonDeclare nom)
      (* L'identifiant est dans la tds *)
      | Some ia ->
        begin
          match info_ast_to_info ia with
          | InfoVar _ ->
            (* L'identifiant correspond à une variable,
               on peut alors récupérer son adresse *)
            AstTds.Adresse(ia)
          | _ ->
            (* Impossible de récupérer l'adresse d'une constante ou d'une fonction *)
            raise (AccesAdresseInvalide nom)
        end
    end
  | AstSyntax.Null -> AstTds.Null


(* analyse_tds_instruction : tds -> info_ast option -> string list -> AstSyntax.instruction -> AstTds.instruction *)
(* Paramètre tds    : la table des symboles courante *)
(* Paramètre oia    : None si l'instruction i est dans le bloc principal,
                      Some ia où ia est l'information associée à la fonction dans laquelle est l'instruction i sinon *)
(* Paramètre lloop  : liste des noms des boucles dans lesquelles est incluse l'instruction i *)
(* Paramètre i      : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme l'instruction
   en une instruction de type AstTds.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_instruction tds oia lloop i =
  match i with
  | AstSyntax.Declaration (t, n, e) ->
      begin
        match chercherLocalement tds n with
        | None ->
            (* L'identifiant n'est pas trouvé dans la tds locale,
            il n'a donc pas été déclaré dans le bloc courant *)
            (* Vérification de la bonne utilisation des identifiants dans l'expression *)
            (* et obtention de l'expression transformée *)
            let ne = analyse_tds_expression tds e in
            (* Création de l'information associée à l'identfiant *)
            let info = InfoVar (n, Undefined, 0, "") in
            (* Création du pointeur sur l'information *)
            let ia = info_to_info_ast info in
            (* Ajout de l'information (pointeur) dans la tds *)
            ajouter tds n ia;
            (* Renvoie de la nouvelle déclaration où le nom a été remplacé par l'information
            et l'expression remplacée par l'expression issue de l'analyse *)
            AstTds.Declaration (t, ia, ne)
        | Some _ ->
            (* L'identifiant est trouvé dans la tds locale,
            il a donc déjà été déclaré dans le bloc courant *)
            raise (DoubleDeclaration n)
      end
  | AstSyntax.Affectation (a,e) ->
      let na = analyse_tds_affectable tds a true in
      let ne = analyse_tds_expression tds e in
      AstTds.Affectation (na, ne)
  | AstSyntax.Constante (n,v) ->
      begin
        match chercherLocalement tds n with
        | None ->
          (* L'identifiant n'est pas trouvé dans la tds locale,
             il n'a donc pas été déclaré dans le bloc courant *)
          (* Ajout dans la tds de la constante *)
          ajouter tds n (info_to_info_ast (InfoConst (n,v)));
          (* Suppression du noeud de déclaration des constantes devenu inutile *)
          AstTds.Empty
        | Some _ ->
          (* L'identifiant est trouvé dans la tds locale,
          il a donc déjà été déclaré dans le bloc courant *)
          raise (DoubleDeclaration n)
      end
  | AstSyntax.Affichage e ->
      (* Vérification de la bonne utilisation des identifiants dans l'expression *)
      (* et obtention de l'expression transformée *)
      let ne = analyse_tds_expression tds e in
      (* Renvoie du nouvel affichage où l'expression remplacée par l'expression issue de l'analyse *)
      AstTds.Affichage (ne)
  | AstSyntax.Conditionnelle (c,t,e) ->
      (* Analyse de la condition *)
      let nc = analyse_tds_expression tds c in
      (* Analyse du bloc then *)
      let tast = analyse_tds_bloc tds oia lloop t in
      (* Analyse du bloc else *)
      let east = analyse_tds_bloc tds oia lloop e in
      (* Renvoie la nouvelle structure de la conditionnelle *)
      AstTds.Conditionnelle (nc, tast, east)
  | AstSyntax.TantQue (c,b) ->
      (* Analyse de la condition *)
      let nc = analyse_tds_expression tds c in
      (* Analyse du bloc *)
      let bast = analyse_tds_bloc tds oia lloop b in
      (* Renvoie la nouvelle structure de la boucle *)
      AstTds.TantQue (nc, bast)
  | AstSyntax.Loop (nom, b) ->
    (* Si la nouvelle loop est imbriquée dans une loop de même nom alors affichage d'un avertissement *)
    (* Pas d'avertissement si deux boucle non nommée sont imbriquées *)
    if (nom <> "_" && List.exists (fun x -> x = nom) lloop)
      then eprintf "\027[31m/!\\ Attention : loop de même nom imbriqués (`%s`)\027[0m\n" nom;
    (* Analyse du bloc *)
    let nb = analyse_tds_bloc tds oia (nom::lloop) b in
    (* Renvoie la nouvelle structure de la boucle *)
    AstTds.Loop(nom, nb)
  | AstSyntax.Continue(n) ->
    (* Lève une exception si l'instruction `continue` se trouve hors d'une `loop` *)
    if (lloop = []) then raise (ContinueHorsLoop n)
    (* S'il n'y a pas de nom spécifié ou que le nom existe alors renvoie du nouveau continue *)
    else if (n = "" || List.exists (fun x -> x = n) lloop) then AstTds.Continue(n)
    (* Lève une exception si le nom de la boucle passé en paramètre n'existe pas *)
    else raise (IdentifiantNonDeclare n)
  | AstSyntax.Break(n) ->
    (* Lève une exception si l'instruction `break` se trouve hors d'une `loop` *)
    if (lloop = []) then raise (BreakHorsLoop n)
    (* S'il n'y a pas de nom spécifié ou que le nom existe alors renvoie du nouveau break *)
    else if (n = "" || List.exists (fun x -> x = n) lloop) then AstTds.Break(n)
    (* Lève une exception si le nom de la boucle passé en paramètre n'existe pas *)
    else raise (IdentifiantNonDeclare n)
  | AstSyntax.Retour (e) ->
      begin
      (* On récupère l'information associée à la fonction à laquelle le return est associée *)
      match oia with
        (* Il n'y a pas d'information -> l'instruction est dans le bloc principal : exception *)
      | None -> raise RetourDansMain
        (* Il y a une information -> l'instruction est dans une fonction *)
      | Some ia ->
        (* Analyse de l'expression *)
        let ne = analyse_tds_expression tds e in
        AstTds.Retour (ne,ia)
      end

(* analyse_tds_bloc : tds -> info_ast option -> string list -> AstSyntax.bloc -> AstTds.bloc *)
(* Paramètre tds    : la table des symboles courante *)
(* Paramètre oia    : None si le bloc li est dans le programme principal,
                      Some ia où ia est l'information associée à la fonction dans laquelle est le bloc li sinon *)
(* Paramètre lloop  : liste des noms des boucles dans lesquelles est inclus le bloc *)
(* Paramètre li     : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme le bloc en un bloc de type AstTds.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_tds_bloc tds oia lloop li =
  (* Entrée dans un nouveau bloc, donc création d'une nouvelle tds locale
  pointant sur la table du bloc parent *)
  let tdsbloc = creerTDSFille tds in
  (* Analyse des instructions du bloc avec la tds du nouveau bloc.
     Cette tds est modifiée par effet de bord *)
   let nli = List.map (analyse_tds_instruction tdsbloc oia lloop) li in
   (* afficher_locale tdsbloc ; *) (* décommenter pour afficher la table locale *)
   nli


(* analyse_tds_parametre : tds -> (typ * string) -> (typ * info_ast) *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre (t, n) : type (t) et nom (n) du paramètre à analyser *)
(* Vérifie la bonne utilisation du paramètre et le transforme en paramètre de type (typ * info_ast) *)
let analyse_tds_parametre tds (t, n) =
  match chercherLocalement tds n with
    | None ->
      (* Création de l'information associée à l'identifiant *)
      let info = InfoVar(n, Undefined, 0, "") in
      (* Création du pointeur sur l'information *)
      let ia = info_to_info_ast info in
      (* Ajout dans la tds *)
      ajouter tds n ia;
      (* On renvoie le type du paramètre le pointeur sur son information *)
      (t, ia)
    (* Le parametre a déjà été traité *)
    | Some _ -> raise (DoubleDeclaration n)


(* aInstructionRetour : string -> AstSyntax.instruction list -> bool *)
(* Paramètre nf : nom de la fonction en cours d'analyse (nécessaire en cas de warnings) *)
(* Paramètre li : liste des instructions à analyser *)
(* Renvoie true si la dernière instruction de la liste est un `return` *)
(* Renvoie false sinon *)
(* Affiche un warning si le `return` est suivi d'autres instructions (code mort) *)
let rec aInstructionRetour nf li =
  match li with
  | [] -> false
  | (AstSyntax.Retour _)::[] -> true  (* Le `return` est la dernière instruction de la liste *)
  | (AstSyntax.Retour _)::_ ->
    (* Le `return` n'est pas la dernière instruction de la liste : warning pour code mort *)
    eprintf "\027[31m/!\\ Attention : code mort, le `return` de la fonction `%s` est suivi d'autres instructions\027[0m\n" nf;
    true
  | (AstSyntax.Continue _)::q | (AstSyntax.Break _)::q ->
    (* Le `continue` ou `break` est suivi d'autres instructions : warning pour code mort *)
    if (q <> []) then eprintf "\027[31m/!\\ Attention : code mort, le `continue` ou `break` de la fonction `%s` est suivi d'autres instructions\027[0m\n" nf;
    false
  | (AstSyntax.Conditionnelle (_,t,e))::q ->
    (* On regarde si les deux branches sont des `return` (sinon si la dernière instruction de la liste est un `return`*)
    begin
      match aInstructionRetour nf t, aInstructionRetour nf e, q with
      | true, true, [] -> true (* Les deux branches sont des `return` et le `return` est la dernière instruction de la liste *)
      | true, true, _ ->
        (* Les deux branches sont des `return` mais le `return` n'est pas la dernière instruction de la liste : warning pour code mort *)
        eprintf "\027[31m/!\\ Attention : code mort, le `return` de la fonction `%s` est suivi d'autres instructions\027[0m\n" nf;
        true
      | _ -> aInstructionRetour nf q (* On regarde si la suite des instructions de la liste contient un `return` *)
    end
  | (AstSyntax.Loop (_, b))::q ->
    begin
      match aInstructionRetour nf b, q with
      | true, [] -> true  (* La boucle est un `return` et le `return` est la dernière instruction de la liste *)
      | true, _ ->
        (* La boucle est un `return` mais le `return` n'est pas la dernière instruction de la liste : warning pour code mort *)
        eprintf "\027[31m/!\\ Attention : code mort, le `return` de la fonction `%s` est suivi d'autres instructions\027[0m" nf;
        true
      | _ -> aInstructionRetour nf q (* On regarde si la suite des instructions de la liste contient un `return` *)
    end
  | (AstSyntax.TantQue (c, b))::q ->
    begin
      match c, aInstructionRetour nf b, q with
      (* Attention analyse non-exhaustive !
         L'analyse à la volée de l'expression est trop
         complexe pour être réalisée ici. On couvre cepndant
         le cas le plus général d'une boucle while infinie. *)
      | AstSyntax.Booleen(true), true, [] -> true
      | AstSyntax.Booleen(true), true, _ ->
        (* La boucle est un `return` mais le `return` n'est pas la dernière instruction de la liste : warning pour code mort *)
        eprintf "\027[31m/!\\ Attention : code mort, le `return` de la fonction `%s` est suivi d'autres instructions\027[0m" nf;
        true
      | _ -> aInstructionRetour nf q (* On regarde si la suite des instructions de la liste contient un `return` *)
    end
  | _::q -> aInstructionRetour nf q (* On regarde si la suite des instructions de la liste contient un `return` *)


(* analyse_tds_fonction : tds -> AstSyntax.fonction -> AstTds.fonction *)
(* Paramètre maintds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_tds_fonction maintds (AstSyntax.Fonction(t,n,lp,li)) =
  (* On cherche dans la tds si la fonction y a déjà été ajoutée *)
  match chercherLocalement maintds n with
  (* La fonction n'est pas dans la tds *)
  | None ->
    (* On vérifie que la fonction contient bien un return *)
    if aInstructionRetour n li then
      (* Création d'une nouvelle tds *)
      let tdsfonc = creerTDSFille maintds in
      (* Transformation des paramètres de la fonction *)
      let nlp = List.map (analyse_tds_parametre tdsfonc) lp  in
      (* Création de l'information sur la fonction *)
      let info = InfoFun (n, Undefined, []) in
      (* Création du pointeur sur l'information *)
      let ia = info_to_info_ast info in
      (* Ajout dans la tds *)
      ajouter maintds n ia;
      (* Transformation du bloc de la fonction *)
      let nb = analyse_tds_bloc tdsfonc (Some ia) [] li in
      AstTds.Fonction(t, ia, nlp, nb)
    (* La fonction ne contient pas de return levée de l'exception FonctionSansRetour *)
    else raise (FonctionSansRetour n)
  (* La fonction est déjà dans la tds *)
  | Some _ -> raise (DoubleDeclaration n)

(* analyser : AstSyntax.programme -> AstTds.programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme le programme
en un programme de type AstTds.programme *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstSyntax.Programme (fonctions,prog)) =
  (* Création de la tds *)
  let tds = creerTDSMere () in
  (* Transformation de la liste de fonctions *)
  let nf = List.map (analyse_tds_fonction tds) fonctions in
  (* Transformation des blocs *)
  let nb = analyse_tds_bloc tds None [] prog in
  AstTds.Programme (nf,nb)
