open Scanf
open Printf;;
let load file =
  let c = Scanning.open_in file in
  let n = bscanf c "%d\n" (fun n -> n) in
  let r = bscanf c "%d\n" (fun r -> r) in
  let murs = ref [] in
  for _ = 1 to r do
    bscanf c "%d %d %d %d\n" (fun x y dx dy -> murs := (x, y, dx, dy) :: !murs)
  done;
  !murs, n
;;
let print_path p =
  List.iter (fun (x, y) -> printf "(%d, %d) " x y) p;
  printf "\n"
;;

(**
   Type de données pour représenter un quadtree dont les régions libres
   sont numérotées. Pendant la construction, affectez arbitrairement le
   numéro (-1) à toutes les régions. La fonction  (numerote)  fournie 
   donnera un numéro unique à chaque région une fois l'arbre complet. 
*)
type qtree =
  | Libre of int (* numéro *)
  | Mur
  | Quad of qtree * qtree * qtree * qtree (* no, ne, so, se *)
;;
(**
   Fonction de numérotation des quadtrees
     numerote: qtree -> int -> qtree * int

   L'appel  (numerote qt k)  renvoie une paire  (qt', k')  où 
   - (qt') est un quadtree de même structure que (qt) mais dont les 
     régions libres sont numérotées consécutivement à partir de (k)
   - (k') est l'entier qui suit le dernier numéro utilisé
 *)
let rec numerote qt k = match qt with
  | Libre _ -> Libre k, k+1
  | Mur     -> Mur, k
  | Quad(no, ne, so, se) ->
     let no, k = numerote no k in
     let ne, k = numerote ne k in
     let so, k = numerote so k in
     let se, k = numerote se k in
     Quad(no, ne, so, se), k

(**
   Affichage d'un quadtree 
   (vue hiérarchique avec retrait proportionnel à la profondeur)
 *)     
open Printf
let print_qtree qt =
  let offset n = String.make n ' ' in
  let rec print o = function
    | Mur -> printf "%sMur\n" (offset o)
    | Libre k -> printf "%sLibre %d\n" (offset o) k
    | Quad(no, ne, so, se) ->
       printf "%sQuad\n" (offset o);
       print (o+2) no;
       print (o+2) ne;
       print (o+2) so;
       print (o+2) se
  in
  print 0 qt
;;
(* premiere partie*)
let rec ligne tab n =
	if n <=0 then
		""
	else
		let ch = if tab.(n-1) then
				" "
			else
				"#"
		in
		(ligne tab (n-1))^"|"^ch
		;;

let rec affiche_tableau t n =
	
 	for ii = 0 to n-1 do
 		let i = n-(ii+1) in
 		if i <10 then
 			printf "\n %d|" i
 		else
 			printf "\n%d|" i;
 		for j = 0 to n-1 do
 			let x = t.(j).(i) in
 			if x then
 				printf " |"
 			else
 				printf "#|"
 		done
 		
 	done
 	;
 	printf "\ny->";
 	for j = 0 to n-1 do
 			printf "%d|" j;
	done
	; printf "\n"
 	;;

open Printf ;;

let rec addRectangleSupInf_bis x y dx dy tab =
let act = 
	for i = 0 to dx do
		for j = 0 to dy do
			tab.(x+i).(y+j)<-false
		done
	done
in
	tab
	;;

	
	
let addRectangleSupInf x1 y1 x2 y2 tab  n=
	let x , y ,dx , dy = (min x1 x2) , (min y1 y2) , (abs (x1-x2) ) , (abs (y1-y2)) in
		addRectangleSupInf_bis x y dx dy tab		
;;	
let rec addRectangle_bis x y dx dy tab =
let fun_intrn = 
	for i = 0 to dx-1 do
		for j = 0 to dy-1 do
				(*printf ("%d , %d\n") (x+i) (y+j) ;*)
				tab.(x+i).(y+j)<-false
		done
	done
in

	tab
	;;

	
	
let addRectangle x y dx dy tab n =
	(*printf"addRectangle %d %d %d %d\n" x y dx dy ;*)
	let t =
		if (x+dx)>n || (y+dy)>n then
			addRectangle_bis x y (n-x-1) (n-y-1) tab
		else
			addRectangle_bis x y dx dy tab 
	in
		(*let fun_intrn = affiche_tableau t n in*) 
	t 
;;	
let min x y =
	if x < y then
		x
	else
		y
;;
let rec constTableau_bis tab l n=
	match l with
		[]->tab
		|tete::r->let (x1 , y1 , x2 , y2) = tete in
			
				(*let act = printf "ajout rectangle %d , %d ,%d ,%d" x y dx dy in*)
			constTableau_bis (addRectangle x1 y1 x2 y2 tab n) r n
;;
(*construction du tableau 2d à partir de la liste des régions intraversables*)
let constTableau n l=
		let tab = Array.make n (Array.make n true) in
		let fun_intrn = for i = 0 to n-1 do
				tab.(i)<-(Array.make n true)
				done
		in 
		constTableau_bis tab l n
;;
(*prend un tableau , la taille du tableau , des coordonées i , j , et renvoit la liste des coordonées voisice de la case i , j*)
let voisins tab  n   i  j =
	let ret = [] in
		let ret1 = if (i+1) < n then
				if tab.(i+1).(j) then
					ret@[(i+1 , j)]
				else
					ret
			   else
			   	ret 
		in
		let ret2 = if (j+1) <n then
			  	if tab.(i).(j+1) then
			  		ret1@[(i , j+1)]
				else
					ret1
			   else
			   		ret1 
		in
		let ret3 = if (i-1) >= 0 then 
				if tab.(i-1).(j) then
					ret2@[(i-1,j)]
				else
					ret2
			  else
			  	ret2
		in 
			if (j-1) >= 0 then
				if tab.(i).(j-1) then
					ret3@[(i,j-1)]
				else
					ret3
			else
				ret3
;;
let rec nonVisite t l =
	match l with 
		[]->[]
		|x::r -> let(i , j)= x in
			if t.(i).(j) then
				[(i,j)]@(nonVisite t r)
			else
				nonVisite t r
;;
let voisinsNonVisite visite tab n x y =
	nonVisite visite (voisins tab n x y)
;;
(*fonction de "coloriage" des cases visitées (avec effets de bord)*)
let marqueVisite t i j =
	let fun_intrn = t.(i).(j) <- false in
		t
;;
let rec chercheChemin tab visite n x1 y1 x2 y2=

	let rec visiteVoisins t vis nb lCases xa ya = 
		match lCases with 
		[]->[]
		|(xd , yd)::r -> 
			let ch = chercheChemin t vis n xd yd xa ya in
				let ch2=visiteVoisins t vis nb r xa ya in
				match ch with 	
				[]->ch2
				|(xa , ya)::r->
					ch				
	in
	if x1 == x2 && y1 == y2 then
		[(x1,y1)]
	else
		let vis = marqueVisite visite x1 y1 in
		let v = voisinsNonVisite  tab vis n x1 y1 in
			(visiteVoisins tab vis n v x2 y2)@[(x1 , y1)]
;;

let chemin tab n x1 y1 x2 y2 =
		let visite = Array.make n (Array.make n true) in
		let fun_intrn = for i = 0 to (n-1) do
				visite.(i)<-(Array.make n true)
				done
		in 
			chercheChemin tab visite n x1 y1 x2 y2 
;;




(*fin premiere partie*)

(*part two*)
(*let isFeuille qtree = 
  qtree == Libre(x) || qtree == Mur
;; *)
let isaFeuille qtree =
	match qtree with
		Libre(x)->true
		|Mur->true
		|_->false
;;

let laFeuille b =
	if b then
		Libre(0)
	else
		Mur
;;
let rec tabtoqtree_bis tab xa ya xb yb =
	if xa==(xb-1) && ya == (yb-1) then
		laFeuille (tab.(xa).(ya))
	else
		let xc = (xb-xa)/2 in
		Quad ((tabtoqtree_bis tab xa ya (xa+xc) (ya+xc) ) ,(tabtoqtree_bis tab (xa+xc) ya xb (ya+xc)),(tabtoqtree_bis tab xa (ya+xc) (xa+xc) yb ) ,(tabtoqtree_bis tab (xa+xc) (ya+xc) xb yb ) )
;;
let rec compresse tree =
		match tree with
		Libre(x)->tree
		|Mur->tree
		|Quad(f1,f2,f3,f4)->let c1 , c2 , c3 , c4 = compresse f1 ,compresse f2 ,compresse f3 ,compresse f4 in
			 (match c1 with
				Libre(x1)->
				 (match c2 with
					Libre(x2)->
					 (match c3 with
						Libre(x3)->
						 (match c4 with
							Libre(x4)->Libre(0)
								|_->Quad(c1,c2,c3,c4)
						)
							|_->Quad(c1,c2,c3,c4)
					)
							|_->Quad(c1,c2,c3,c4)				
				)
				|Mur->
				 (match c2 with
					Mur->
					 (match c3 with
						Mur->
						 (match c4 with
							Mur->Mur
							|_->Quad(c1,c2,c3,c4)
						)
							|_->Quad(c1,c2,c3,c4)
					)
						|_->Quad(c1,c2,c3,c4)
				)
				|_->Quad(c1,c2,c3,c4)
				
			)
;;
let rec list2qtree n l =
  let tab = constTableau n l in
  	compresse (tabtoqtree_bis tab 0 0 n n ) 
;;
let rec qtreetotab_bis tab tree xa ya xb yb n=
	match tree with
	Libre(x)->tab
	|Mur->addRectangleSupInf xa ya (xb-1) (yb-1) tab n
	|Quad(f1,f2,f3,f4)->
	let d = (xb-xa)/2 in
	qtreetotab_bis (qtreetotab_bis(qtreetotab_bis (qtreetotab_bis tab f1  xa ya (xa+d) (ya+d) n ) f2 (xa+d) ya xb (ya+d) n ) f3 xa (ya+d) (xa+d) yb n) f4 (xa+d) (ya+d) xb yb n
	;;
let rec qtreetotab tree n =
	let tab = Array.make n (Array.make n true) in
		let fun_intrn = for i = 0 to (n-1) do
				tab.(i)<-(Array.make n true)
			  done
		in
		qtreetotab_bis tab tree 0 0 n n n
;;

(**
le calcul des x et y le centre des regions vide
    returne  un tab  de paires de coordonnées.
 *)
let rec set_pond qtn tab xa ya xb yb =
	(*printf "set pond %f %f %f %f\n" xa ya xb yb ;  *)
	let d = ( xb -. xa ) /. 2.0 in
	match qtn with
	Mur->tab
	|Libre(num)->let fun_intrn = tab.(num)<-(xa +. d , ya +. d ) in
			 	tab 
	|Quad(f1,f2,f3,f4)->set_pond f4 (set_pond f3 (set_pond f2 (set_pond f1 tab xa ya (xa+.d) (ya+.d))(xa+.d) ya xb (ya+.d)  ) xa (ya+.d) (xa+.d) yb ) (xa+.d) (ya+.d) xb yb
;;

let mk_coords qt k n =
  		  let tab = Array.make k  (0.,0.) in
  			set_pond qt tab 0. 0. (float_of_int n) (float_of_int n)
  			;;
  

(**
   Type pour représenter un graphe pondéré dans la partie 2 : 
   tableau de listes d'adjacence

   Sous-entendu : les sommets d'un graphe sont numérotés consécutivement à
   partir de 0. Un graphe (g) et un numéro de sommet (i) étant donnés, g.(i)
   est une liste de paires, où chaque paire (v, d) contient
   - le numéro (v) d'un voisin
   - la distance (d) à ce voisin

   Deux fonctions d'affichage fournies
   (print_graph) donne une vue complète, longueurs des arêtes comprises
   (print_graph_compact) 
 *)
type graph = (int * float) list array;;

let print_graph g =
  let n = Array.length g in
  printf "Graphe à %d sommets :\n" n;
  for i = 0 to n-1 do
    printf "Sommet %d:\n" i;
    List.iter (fun (v, d) -> printf "  voisin %d à distance %f\n" v d) g.(i)
  done

let print_graph_compact g =
  for i = 0 to Array.length g - 1 do
    printf "%d:" i;
    List.iter (fun (v, _) -> printf " %d" v) g.(i);
    printf "\n"
  done

(*la fonction qui renvoie un graphe pondéré*)
let rec pNumeroArbre num qt =
	match qt with
		Mur->[]
		|Libre(numa)->[(num,numa);(numa,num)]
		|Quad(so,no,se,ne)->(pNumeroArbre num so)@(pNumeroArbre num no)
;; 
let rec pArbrNumero qt num =
	match qt with
		Mur->[]
		|Libre(numa)->[(num,numa);(numa,num)]
		|Quad(so,no,se,ne)->(pArbrNumero se num )@(pArbrNumero ne num)
;; 	
let rec face_horizontale a1 a2 =
  (match a1 with
 Mur->[]
 |Libre(num1)->
    (match a2 with
     Mur->[]
     |Libre(num2)->[(num1,num2);(num2,num1)]
     |Quad(so2,no2,se2,ne2)->(pNumeroArbre num1 so2)@(pNumeroArbre num1 no2)
   )
 |Quad(so1,no1,se1,ne1)->
    (match a2 with
     Mur->[]
     |Libre(num2)->(pArbrNumero  se1 num2)@(pArbrNumero ne1 num2 )
     |Quad(so2 , no2 , se2 , ne2)->(face_horizontale se1 so2)@(face_horizontale ne1 no2) 
   )
 )
;;		
let rec pNumeroArbreVide num qt =
	match qt with
		Mur->[]
		|Libre(numa)->[(num,numa);(numa,num)]
		|Quad(so,no,se,ne)->(pNumeroArbreVide num no)@(pNumeroArbreVide num ne)
;; 
let rec pArbreNumeroVide a num =
	match a with
		Mur->[]
		|Libre(numa)->[(num,numa);(numa,num)]
		|Quad(so,no,se,ne)->(pArbreNumeroVide se num )@(pArbreNumeroVide so num)
;;
let rec face_verticale a1 a2 =
	(match a1 with
	Mur->[]
	|Libre(num1)->
		(match a2 with
			Mur->[]
			|Libre(num2)->[(num1,num2);(num2,num1)]
			|Quad(so2,no2,se2,ne2)->(pNumeroArbreVide num1 no2)@(pNumeroArbreVide num1 ne2)
		)
	|Quad(so1,no1,se1,ne1)->
		 (match a2 with
			Mur->[]
			|Libre(num2)->(pArbreNumeroVide  so1 num2)@(pArbreNumeroVide se1 num2 )
			|Quad(so2 , no2 , se2 , ne2)->(face_horizontale se1 ne2)@(face_horizontale so1 no2) 
		)
	)
	;;
  let rec aretes a =
		match a with
			Mur->[]
			|Libre(n)->[]
			|Quad(so,no,se,ne)->let ext =(face_verticale so no)@(face_verticale se ne)@(face_horizontale ne no)@(face_horizontale so se) in
			ext@(aretes so)@(aretes no)@(aretes se)@(aretes ne)
			;;

let distance (x1 , y1) (x2 , y2) =
	let a  , b = ( x2 -. x1 ) , ( y2 -.  y1 ) in
	(sqrt ( (a *. a) +. (b *. b)  )) ;;
	
let rec mk_graph_bis arr tab coords =
	match arr with 
	[]->tab
	|(x,y)::r->let pond = ( distance ( coords.(x) ) ( coords.(y) ) ) in
		let act = tab.(x)<-( (tab.(x))@[(y,pond)] ) in 
			mk_graph_bis r tab coords
;;
let mk_graph qt n=
	let q , k = (numerote qt 0) in
		let t_coords , tla = (mk_coords q k n ) , ( Array.make k [] ) in
	 		let arr = aretes q in
	  			(mk_graph_bis arr tla t_coords )
			
;;
	  	


(**
   Fonction de recherche d'un chemin.
   Applique un algorithme de recherche et reconstruit le trouvé.
   Renvoie la liste des paires de coordonnées formant le chemin.

   
 *)
(* let print_dist t n = 
 	printf "distances";
	for i=0 to (n-1) do
		printf "%d : %f ;" i t.(i) ; 
	done;
	printf "\n";
	;;*)
let rec min_non_visite d visite n =
	if n == 0 then
		(infinity , n-1)
	else
		let (dmin , smin)= min_non_visite d visite (n-1) in
			if not visite.(n-1) then
				let dist = d.(n-1) in
				
				if dist < dmin then 
					(dist , (n-1) )
				else
					(dmin , smin )
			else
				(dmin , smin)
;;
let rec maj_dist s1 (s2 , p) d pred =
	if d.(s2) > ( d.(s1) +. p ) then
		let act1 = d.(s2)<-(d.(s1) +. p) in
			let act2 = pred.(s2)<-s1 in
				(d ,pred)
	else
		(d ,pred)
;;(*
let print_visite t n = 
	for i=0 to n do
		printf "%d : %b ;" i t.(i) ; 
	done;
	printf "\n";
	;;*)
let rec tous_visite visite n =
	if n < 0 then
		true
	else
		visite.(n) && tous_visite visite (n-1)
		;; 
let rec maj_distL s l d pred =
	match l with 
	[]->(d,pred)
	|x::r-> let d_ , pred_ = (maj_dist s x d pred ) in 
		maj_distL s r d_ pred_
;;
let marqueVisite v s =
	let act = v.(s)<-true in
		v ;;
let rec dijkstra_bis tla n s visite pred d =
	
	if tous_visite visite (n-1) then
		(d , pred)	
	else

		let ponds1 , s1 = (min_non_visite d visite n) in
			if s1 < 0 then
				(d,pred)
			else
				let visite = (marqueVisite visite s1) in
					let ( tab_d , tab_pred ) = maj_distL s1 tla.(s1) d pred in
						dijkstra_bis tla n s1 visite tab_pred tab_d

;;
let rec estConnexe_bis tla s v =
	let rec f tla l v =
		match l with []->v
		|(s_,d)::r->(f tla r (estConnexe_bis tla s_ v))
	
	in
	if v.(s) then
		v 
	else
		let act = v.(s)<-true in
		f tla (tla.(s)) v
;;
let estConnexe tla s n =
	let rec compte v n = 
		if n == 0 then
			[]
		else 
			let l = compte v (n-1) in
			if v.(n-1)==false then
				l@[n-1]
			else
				l
	in
	let v = Array.make n false in
		let vis = estConnexe_bis tla s v in
		let l = (compte v n )in
		(*printf "sommets accessibles %d \n" (List.length l);*)
		( (l == [] ) , l );;





let dijkstra tla n s =
	let rec suppr lis v = 
		match lis with []->v
		|x::r ->let act = v.(x)<-true in v
	in
	let visite , pred  , d = (Array.make n false) , (Array.make n 0 ) , (Array.make n infinity) in
		let b , l= estConnexe tla  s n in
		let visite = suppr l visite in
		let act = visite.(s) = true in
		let act = d.(s)<- 0.0 in
			dijkstra_bis tla n s visite pred d 
;;
let rec num_region_bis x y qt xa ya xb yb =
	match qt with
		Libre(num)->num
		|Mur->printf"(%f , %f )" x y ; failwith"pas de région libre pour ces coordonées \n"
		|Quad(so,no,se,ne)->let d = (xb-.xa) /. 2.0 in
					let xab ,yab = (xa +. d) ,(ya +. d)in
						if x < xab then
							if y < yab then
								 num_region_bis x y so xa ya xab yab
							else
								num_region_bis x y se xa yab xab yb
						else 
							if y < yab then
								num_region_bis x y no xab ya xb yab
							else
								num_region_bis x y ne xab yab xb yb
								;;
let num_region x y qt n=
	num_region_bis x y qt 0.0 0.0 (float_of_int n) (float_of_int n) 
	
	
	;;

let rec chemin pred coords s1 s2 =
	let a , b = coords.(s2) in
		let s = (int_of_float a , int_of_float b ) in
	if s2==s1 then
		[s]
	else
		( chemin pred coords s1 pred.(s2) )@[s]
;;


let find_path (xDep, yDep) (xArr, yArr) (qt, n) (g, coords) k =
  	let s1 , s2 = (num_region (float_of_int xDep) (float_of_int yDep) qt n ),(num_region (float_of_int xArr) (float_of_int yArr) qt n )in
  		 		
  		let d , pred = dijkstra g k s1 in
  		
  			chemin pred coords s1 s2;;



			
(**
   Fonction de lecture du fichier d'entrée
     load: string -> (int * int) list * int

   L'appel  (load f)  lit le fichier dont le nom est donné par la 
   chaîne (f) et renvoie une paire  (murs, n)  où
   - (murs) est la liste des quadruplets (x, y, dx, dy) donnant les
     dimensions des r zones intraversables
   - (n) est la longueur du côté du terrain
   On suppose que le fichier (f) contient une description de terrain
   valide. Le résultat de (load) n'est pas spécifié sinon.
 *)

(*test*)
  let file = "p32.txt" in
  let murs, n = load file in
  let qt, k = numerote (list2qtree n murs) 0 in
  printf "n = %d\n" n ;
  let coords = mk_coords qt k n in
  let g = mk_graph qt n in
  let act = affiche_tableau (qtreetotab qt n) n in
  
  let path = find_path (0, 1) (30,30 ) (qt, n) (g, coords) k in
  print_path path ;
 (* for i = 0 to (k-1) do
  	let x , y = coords.(i) in
  	printf "%d ; coord :%f , %f\n" i  x y ;
  done;;*)
(*test*)
  
(**
   Exemple d'ossature pour un programme complet, prenant un nom de fichier
   sur la ligne de commande et affichant le chemin trouvé, ainsi que quelques
   mesures de temps d'exécution.
   Note : la mesure des temps d'exécution peut ne pas fonctionner sous windows.
 *)
  (*
let _ =
  let file = Sys.argv.(1) in
  let murs, n = load file in
 (* let t1 = Unix.gettimeofday() in *)
  let qt, k = numerote (list2qtree n murs) 0 in
  (*let t2 = Unix.gettimeofday() in*)
  let coords = mk_coords qt k n in
  let g = mk_graph qt coords in
 (* let t3 = Unix.gettimeofday() in*)
  let path = find_path (31, 0) (0, 31) (qt, n) (g, coords) in
  (*let t4 = Unix.gettimeofday() in
  printf "Temps:\n  construction du quadtree %fs\n  construction du graphe %fs\n  recherche de chemin %fs\n" (t2 -. t1) (t3 -. t2) (t4 -. t3);*)
  print_path path
  *)
