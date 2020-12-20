(* no dont look *)
let zfunc s =
  let l : int ref = ref 0 in
  let r : int ref = ref 0 in
  let n = String.length s in
  let z = Array.make n 0 in
  let () = String.iteri (fun i x ->
    if i = 0 then ()
    else begin
      (*
      if (i <= r)
        z[i] = min (r-i+1, z[i-l]);
       *)
      ( if i <= !r then (Array.set z i (min (!r-i+1) (Array.get z (i - !l)))) );
      (*
       while (i+z[i] < n && s[z[i]] == s[i+z[i]])
        ++z[i];
       *)
      while i + (Array.get z i) < n &&
        (String.get s (Array.get z i)) = (String.get s (i + (Array.get z i))) do
          Array.set z i ((Array.get z i) + 1)
      done ;
      (*
      if (i+z[i]-1 > r)
        l = i,  r = i+z[i]-1;
       *)
      ( if i + (Array.get z i) - 1 > !r then begin
        l := i ;
        r := i + (Array.get z i) - 1
      end )
    end
  ) s in
  z ;;
(* let () = print_string ("input smth ") in *)
let inp = read_line () in 
let z = zfunc (inp) in
let z = Array.sub z 1 ((Array.length z) - 1) in
(* let () = print_string (inp) in *)
let () = print_newline () in
let () =  Array.iter (fun x -> Printf.printf "%d " x) z
in print_newline () ;;



