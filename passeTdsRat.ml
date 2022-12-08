(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Tds
open Exceptions
open Ast

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
          | InfoConst(nom, v) ->
            if ecriture then raise (MauvaiseUtilisationIdentifiant nom)
            else AstTds.Const(ia, v)
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
(* Erreur si mauvaise utilisation des identifiants *)
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
    (* Création d'une liste d'expressions transformées *)
    let ne = analyse_tds_expression tds e in
    AstTds.Unaire(op, ne)
  | AstSyntax.Binaire (op, e1, e2) ->
    (* Création de deux listes d'expressions transformées *)
    let ne1 = analyse_tds_expression tds e1 in
    let ne2 = analyse_tds_expression tds e2 in
    AstTds.Binaire(op, ne1, ne2)
  | AstSyntax.New t -> AstTds.New(t)
  | AstSyntax.Adresse nom ->
    begin
      match (chercherGlobalement tds nom) with
      (* L'identifiant recherché n'existe pas *)
      |None -> raise (IdentifiantNonDeclare nom)
      (* L'identifiant est trdans la tds *)
      | Some ia ->
        begin
          match info_ast_to_info ia with
          | InfoVar _ -> AstTds.Adresse(ia)
          | _ -> raise (MauvaiseUtilisationIdentifiant nom)
        end
    end
  | AstSyntax.Null -> AstTds.Null


(* analyse_tds_instruction : tds -> info_ast option -> AstSyntax.instruction -> AstTds.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre oia : None si l'instruction i est dans le bloc principal,
                   Some ia où ia est l'information associée à la fonction dans laquelle est l'instruction i sinon *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme l'instruction
en une instruction de type AstTds.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_instruction tds oia i =
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
      let tast = analyse_tds_bloc tds oia t in
      (* Analyse du bloc else *)
      let east = analyse_tds_bloc tds oia e in
      (* Renvoie la nouvelle structure de la conditionnelle *)
      AstTds.Conditionnelle (nc, tast, east)
  | AstSyntax.TantQue (c,b) ->
      (* Analyse de la condition *)
      let nc = analyse_tds_expression tds c in
      (* Analyse du bloc *)
      let bast = analyse_tds_bloc tds oia b in
      (* Renvoie la nouvelle structure de la boucle *)
      AstTds.TantQue (nc, bast)
  | AstSyntax.Retour (e) ->
      begin
      (* On récupère l'information associée à la fonction à laquelle le return est associée *)
      match oia with
        (* Il n'y a pas d'information -> l'instruction est dans le bloc principal : erreur *)
      | None -> raise RetourDansMain
        (* Il y a une information -> l'instruction est dans une fonction *)
      | Some ia ->
        (* Analyse de l'expression *)
        let ne = analyse_tds_expression tds e in
        AstTds.Retour (ne,ia)
      end


(* analyse_tds_bloc : tds -> info_ast option -> AstSyntax.bloc -> AstTds.bloc *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre oia : None si le bloc li est dans le programme principal,
                   Some ia où ia est l'information associée à la fonction dans laquelle est le bloc li sinon *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme le bloc en un bloc de type AstTds.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_tds_bloc tds oia li =
  (* Entrée dans un nouveau bloc, donc création d'une nouvelle tds locale
  pointant sur la table du bloc parent *)
  let tdsbloc = creerTDSFille tds in
  (* Analyse des instructions du bloc avec la tds du nouveau bloc.
     Cette tds est modifiée par effet de bord *)
   let nli = List.map (analyse_tds_instruction tdsbloc oia) li in
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
    let nb = analyse_tds_bloc tdsfonc (Some ia) li in
    AstTds.Fonction(t, ia, nlp, nb)
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
  let nb = analyse_tds_bloc tds None prog in
  AstTds.Programme (nf,nb)
