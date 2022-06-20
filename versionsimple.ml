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

type qtree =
  | Libre of int (* numéro *)
  | Mur
  | Quad of qtree * qtree * qtree * qtree (* no, ne, so, se *)
;;

let rec numerote qt k = match qt with
  | Libre _ -> Libre k, k+1
  | Mur     -> Mur, k
  | Quad(no, ne, so, se) ->
     let no, k = numerote no k in
     let ne, k = numerote ne k in
     let so, k = numerote so k in
     let se, k = numerote se k in
     Quad(no, ne, so, se), k

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

let  tab n l= 
  let rec tab_aux t n l=
    match l with 
    | [] -> ()
    | (a,b,c,d) :: ll -> for  i=a to (a+c-1) do
          for  j=b to (b+d-1) do
            t.(i).(j)<-false;
          done;
        done;
        tab_aux t n ll in
  let t = Array.make_matrix n n true in tab_aux t n l;
  t 
;;




  
    
    
let ajoutRectangleMin x1 y1 x2 y2 tab  n=
    let x , y ,dx , dy = (min x1 x2) , (min y1 y2) , (abs (x1-x2) ) , (abs (y1-y2)) in
    let fun_intrn = 
      for i = 0 to dx do
        for j = 0 to dy do
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
          let fun_int =
          for i = 0 to n-x-1-1 do
            for j = 0 to n-y-1-1 do
                (*printf ("%d , %d\n") (x+i) (y+j) ;*)
                tab.(x+i).(y+j)<-false
            done
          done
        in
          tab;   

          else
          let fun_int1 =
          for i = 0 to dx-1 do
            for j = 0 to dy-1 do
                (*printf ("%d , %d\n") (x+i) (y+j) ;*)
                tab.(x+i).(y+j)<-false
            done
          done
        in
        
          tab 
        in
          (*let act = affiche_tableau t n in*) 
        t 
      	
;;


(*construction du tableau 2d à partir de la liste des régions intraversables*)
let rec constTableau tab n l=
          let tab = Array.make n (Array.make n true) in
          let act = for i = 0 to n-1 do
              tab.(i)<-(Array.make n true)
              done
          in 

          match l with
          []->tab
          |tete::r->let (x1 , y1 , x2 , y2) = tete in
            
              (*let act = printf "ajout rectangle %d , %d ,%d ,%d" x y dx dy in*)
            constTableau (addRectangle x1 y1 x2 y2 tab n) n r
;;

(*la fonction qui nous fait les voisins d'un point donné*)
let voisins tab n i j =
        let vid = [] in
          let voisD = if (i+1) < n then(*on peut aussi ajouter un or 
             dans cette conditon au lieu de faire un autre if*)
              if tab.(i+1).(j) then
                vid@[(i+1 , j)]
              else
                vid
               else
                 vid 
          in
          let voisH = if (j+1) <n then
                if tab.(i).(j+1) then
                  voisD@[(i , j+1)]
              else
                voisD
               else
                   voisD 
          in
          let voisG = if (i-1) >= 0 then 
              if tab.(i-1).(j) then
                voisH@[(i-1,j)]
              else
                voisH
              else
                voisH
          in 
            if (j-1) >= 0 then
              if tab.(i).(j-1) then
                voisG@[(i,j-1)]
              else
                voisG
            else
              voisG
;;      

let rec nonVisite t l =
	match l with 
		[]->[]
		|elt::ll -> let(i , j)= elt in
			if t.(i).(j) then
				[(i,j)]@(nonVisite t ll)
			else
				nonVisite t ll
;;
let voisinsNonVisite visite tab n x y =
	nonVisite visite (voisins tab n x y)
;;

(*on cree un fonction pour changer l'etat des cases *)
let changeVisite t i j =
	let fun_intrn = t.(i).(j) <- false in
		t
;;

let rec findChemin tab visite n x1 y1 x2 y2=

	let rec checkVoisins t vis nb lCases xa ya = 
		match lCases with 
		[]->[]
		|(xd , yd)::ll -> 
			let ch = findChemin t vis n xd yd xa ya in
				let ch2=checkVoisins t vis nb ll xa ya in
				match ch with 	
				[]->ch2
				|(xa , ya)::ll->
					ch				
	in
	if x1 == x2 && y1 == y2 then
		[(x1,y1)]
	else
		let vis = changeVisite visite x1 y1 in
		let v = voisinsNonVisite  tab vis n x1 y1 in
			(checkVoisins tab vis n v x2 y2)@[(x1 , y1)]
;;

let chemin tab n x1 y1 x2 y2 =
  let visite = Array.make n (Array.make n true) in
  let fun_intrn = for i = 0 to (n-1) do
      visite.(i)<-(Array.make n true)
      done
  in 
    findChemin tab visite n x1 y1 x2 y2 
;;
let fileVide =
[]
;;
let enfiler f x =
f@[x]
;;
let defiler f =
match f with
[]->failwith "leFichierestVide" (*une exception*)
|x::r -> (x , r)

;;
(*
type point = { x :float ; y:float};;

type graphe =
{ sommet : point ; arete :int }  ;;

let distance p1 p2 =

let float vect = (p2.x -. p1.x) +. (p2.y -. p1.y) ;
sqrt(vect);
in
;;
let list_of_false  = 
  let t = [] 
for i=0 to Array.length tab do
  for j=0 to Array.length tab do
    if tab(i).(j) == false then 
      (i,j)::t ;
  done;
done;
;;

let rec exploitation tab sommetDep sommetArr =
let t = [] 
for i=0 to Array.length tab do
  for j=0 to Array.length tab do
    if tab(i).(j) == false then 
      (i,j)::t ;
  done;
done;
  let float deparr = distance sommetDep sommetArr
match t with 
|[] -> while sommetDep != sommetArr then
  if distance (sommetDep.x+1 sommetArr.y) Parv < deparr then        
  exploitation tab (sommetDep.x+1 sommetArr.y) Parv
else if distance (sommetDep.x-1 sommetArr.y) Parv < deparr
  exploitation tab (sommetDep.x-1 sommetArr.y) Parv
else if distance (sommetDep.x sommetArr.y+1) Parv < deparr
  exploitation tab (sommetDep.x sommetArr.y+1) Parv
else (sommetDep.x sommetArr.y+1) Parv < deparr
  exploitation tab (sommetDep.x sommetDep.y+1) Parv

|elt::tt ->  while sommetDep != sommetArr then
if distance (sommetDep.x+1 sommetArr.y) Parv < deparr and sommetDep.x+1 != fst(elt) and sommetArr.y != snd(elt)  then        
  exploitation tab (sommetDep.x+1 sommetArr.y) Parv
else if distance (sommetDep.x-1 sommetArr.y) Parv < deparr and sommetDep.x-1 != fst(elt) and sommetArr.y != snd(elt)
  exploitation tab (sommetDep.x-1 sommetArr.y) Parv
else if distance (sommetDep.x sommetArr.y+1) Parv < deparr and sommetDep.x != fst(elt) and sommetArr.y+1 != snd(elt)
  exploitation tab (sommetDep.x sommetArr.y+1) Parv
else (sommetDep.x sommetArr.y-1) Parv < deparr  and sommetDep.x != fst(elt) and sommetArr.y-1 != snd(elt)
  exploitation tab (sommetDep.x sommetDep.y-1) Parv
  
  *)
  
  
  
  