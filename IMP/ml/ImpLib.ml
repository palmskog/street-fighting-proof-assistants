open ImpSyntax
open ZUtil

(* hack to avoid circular build *)
let val_pretty : (heap -> coq_val -> string) ref =
  ref (fun _ _ -> "")

(* log all input lines so we can replay for testing vs. python *)
let lines : (string list) ref =
  ref []

let line () =
  let s = read_line () in
  lines := s :: !lines; s

let extcall name args h =
  match implode name, args with
  | "print_val", [v] ->
      print_endline (!val_pretty h v);
      (Vint Big.zero, h)
  | "read_bool", [] ->
      begin match line () with
      | "True"  -> (Vbool true, h)
      | "False" -> (Vbool false, h)
      | s -> begin
          prerr_endline ("extcall: read_bool could not parse " ^ s);
          (Vbool false, h)
        end
      end
  | "read_int", [] -> begin
      let s = line () in
      try (Vint (Big.of_string s), h)
      with _ ->
        prerr_endline ("extcall: read_int could not parse " ^ s);
        (Vint Big.zero, h)
    end
  | f, _ -> begin
      prerr_endline ("extcall: bogus call to " ^ f);
      (Vint Big.zero, h)
    end
