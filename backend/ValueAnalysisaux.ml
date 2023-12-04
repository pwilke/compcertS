
let trace_calls b =
  if !Clflags.option_display_transfer
  then
    (* Printf.printf "%s call at pc %d in function %s\n" (if b then "private" else "public") !Clflags.display_cur_pc *)
    (* 		  !Clflags.cur_func_name *)
    ()
  else ()
